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
end Nat92GE

def g11Y : Array (Bits × Bits) := #[((bitLimbs [0xb5dfb5dfb5dfb5dfb5,0xdfb5dfb5dfb5dfb5dfb5]),(bitLimbs [0x942094209420942094,0x20942094209420942094])),((bitLimbs [0xeeeeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeeeeeeee]),(bitLimbs [0x281228122812281228,0x12281228122812281228])),(0x0,0x0),((bitLimbs [0xdb7bdb7bdb7bdb7bdb,0x7bdb7bdb7bdb7bdb7bdb]),(bitLimbs [0x38803880388038803,0x88038803880388038803])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g11C : List ColumnInfo := []
def g11A : List (List Nat) := [[],[49],[16],[16,48],[48,16],[48]]
def g11D3 (j : Nat) := if j=0 then 0x7 else 0
def g11L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g11D3)
  | _ => emptyPacking
def g11I (_ _ : Nat) : Option (Nat × Nat) := none
def g11 : Forest := ⟨11,3,fun i => g11Y[i]?.getD (0,0),g11C,g11A,g11L,g11I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g11P3_0 : block g11 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g11B3 : block g11 3 0 1=true := g11P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g11T : checkedTables g11 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g11 0 0 0 = true)
  · exact (rfl : block g11 1 0 0 = true)
  · exact (rfl : block g11 2 0 0 = true)
  · exact g11B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g11G : graphValid g11 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low11 : Lower true (varsX 11) (graphGoal 11) 4 := lower_forest (g:=g11) (i:=0) (hints:=134218242) (before_sound [] baseKnown) g11G g11T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K11 := extendKnown [] 4 [(11,[]),(13,[33]),(14,[16,32]),(22,[16,32,67]),(25,[49,33,66]),(37,[33,83,67]),(42,[16,48,32,82,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V11 : Known true K11 := extend_ok (m:=11) baseKnown low11 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[((bitLimbs [0xfeddffd3dffd3fffed,0xdffd3dffd3fffeddffd3]),(bitLimbs [0xd0809683202a902d08,0x9683202a902d0809683])),((bitLimbs [0xf7af456fe5feec4f7a,0xf456fe5feec4f7af456f]),(bitLimbs [0x3217814f184493c321,0x7814f184493c3217814f])),((bitLimbs [0xd36f6daeb573faed36,0xf6daeb573faed36f6dae]),(bitLimbs [0x4b485da84a1e2484b4,0x85da84a1e2484b485da8])),((bitLimbs [0x7ffbbafd7fbfd7f7ff,0xbbafd7fbfd7f7ffbbafd]),(bitLimbs [0xc39287481402600c3,0x9287481402600c392874])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := [(0,2,13,0,4)]
def g15A : List (List Nat) := [[],[33],[48],[48,33]]
def g15D4 (j : Nat) := if j=0 then 0x1f else 0
def g15L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g15D4)
  | _ => emptyPacking
def g15I (_ _ : Nat) : Option (Nat × Nat) := none
def g15 : Forest := ⟨15,4,fun i => g15Y[i]?.getD (0,0),g15C,g15A,g15L,g15I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P4_0 : block g15 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B4 : block g15 4 0 1=true := g15P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15T : checkedTables g15 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact (rfl : block g15 3 0 0 = true)
  · exact g15B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15G : graphValid g15 (boundsBefore K11) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := lower_forest (g:=g15) (i:=0) (hints:=135006726) (before_sound K11 V11) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K11 5 [(15,[]),(30,[16,48,66,32]),(46,[16,32,80,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V11 low15 (by decide +kernel)
def g23Y : Array (Bits × Bits) := #[((bitLimbs [0xbe66fcef77bdedfdbe,0x66fcef77bdedfdbe66fc]),(bitLimbs [0x12c660108049081112,0xc660108049081112c660])),((bitLimbs [0xdddf0ffbeadfff56dd,0xdf0ffbeadfff56dddf0f]),(bitLimbs [0x81080e071100312481,0x80e071100312481080e])),((bitLimbs [0x51bbc39fabf33e4f51,0xbbc39fabf33e4f51bbc3]),(bitLimbs [0x22d3c160a488cc4a22,0xd3c160a488cc4a22d3c1])),(0x0,0x0),((bitLimbs [0xeb20f7b5bf2d6cbbeb,0x20f7b5bf2d6cbbeb20f7]),(bitLimbs [0x6830974a4382752068,0x30974a43827520683097])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g23C : List ColumnInfo := []
def g23A : List (List Nat) := [[],[16,66]]
def g23D3 (j : Nat) := if j=0 then 0xf else 0
def g23L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g23D3)
  | _ => emptyPacking
def g23I (_ _ : Nat) : Option (Nat × Nat) := none
def g23 : Forest := ⟨23,3,fun i => g23Y[i]?.getD (0,0),g23C,g23A,g23L,g23I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23P3_0 : block g23 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g23B3 : block g23 3 0 1=true := g23P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23T : checkedTables g23 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g23 0 0 0 = true)
  · exact (rfl : block g23 1 0 0 = true)
  · exact (rfl : block g23 2 0 0 = true)
  · exact g23B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23G : graphValid g23 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low23 : Lower true (varsX 23) (graphGoal 23) 4 := lower_forest (g:=g23) (i:=0) (hints:=68720001538) (before_sound K15 V15) g23G g23T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K23 := extendKnown K15 4 [(23,[]),(43,[49,33,84]),(51,[82,50]),(60,[32,49,64,16,81]),(2063,[67]),(2105,[49,66,82]),(4111,[49,33,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V23 : Known true K23 := extend_ok (m:=23) V15 low23 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((bitLimbs [0xdefdfcf7fefffffede,0xfdfcf7fefffffedefdfc]),(bitLimbs [0x880848080000400888,0x8480800004008880848])),((bitLimbs [0x6f4e177c79577eab6f,0x4e177c79577eab6f4e17]),(bitLimbs [0x41c61683e6220c9241,0xc61683e6220c9241c616])),(0x0,0x0),((bitLimbs [0xa9b78bcded7ccf27a9,0xb78bcded7ccf27a9b78b]),(bitLimbs [0x10d781320c92362510,0xd781320c92362510d781])),((bitLimbs [0xf522e75b2feb5e5df5,0x22e75b2feb5e5df522e7]),(bitLimbs [0x3430a7a450709a9034,0x30a7a450709a903430a7])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[67],[49],[49,65],[65,49],[65]]
def g27D3 := limbs80 #[#[0x2b10910ae42042b50810,0x19d43887948421af4244,0x91e61230602790e2]]
def g27D4 := limbs80 #[#[0xfc21fe21f843e887c10,0x48f30918301f887e9]]
def g27H4 := limbs80 #[#[0x80003140002ec6621920,0x8d18000000c5c168004]]
def g27D5 (j : Nat) := if j=0 then 0xf else 0
def g27H5 := limbs80 #[#[0xf0a21980604843e,0xa880014956b4e8100000,0x3800000059adc0028c,0x40c0078c00001ee977c6,0xb4391e341e0030463a45]]
def g27L : Nat → Packing
  | 3 => (7,2,1,0,0,6,0,g27D3)
  | 4 => (7,1,1,0,0,6,0,g27D4)
  | 5 => (1,0,1,0,0,0,0,g27D5)
  | _ => emptyPacking
def g27I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 2 19 3 8 3 1 g27H4
  | 5 => lookupWord 6 37 5 10 3 3 g27H5
  | _ => fun _ => none
def g27 : Forest := ⟨27,5,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : block g27 3 0 7=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : block g27 3 0 7=true := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P4_0 : block g27 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B4 : block g27 4 0 7=true := g27P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P5_0 : block g27 5 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B5 : block g27 5 0 1=true := g27P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact g27B3
  · exact g27B4
  · exact g27B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K23) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 6 := lower_forest (g:=g27) (i:=0) (hints:=68853694978) (before_sound K23 V23) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K23 6 [(27,[]),(45,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V23 low27 (by decide +kernel)
def g29Y : Array (Bits × Bits) := #[((bitLimbs [0x7dff7d7bffdfdfbefb,0xfefaf7ffbfbf7df7fdf5]),(bitLimbs [0x18531044001242203,0xa6208800248440614c4])),(0x0,0x0),((bitLimbs [0xc73a97b4acf3e4e58e,0x752f6959e7c9cb1cea5e]),(bitLimbs [0x400e958b4a1479f680,0x1d2b169428f3ed003a56])),((bitLimbs [0xaaff8bdeed2fffe555,0xff17bdda5fffcaabfe2f]),(bitLimbs [0x88320ae130908b0d10,0x6415c26121161a20c82b])),((bitLimbs [0xffa8feb77ef9387fff,0x51fd6efdf270fffea3fa]),(bitLimbs [0x2628ce088580d2184c,0x519c110b01a43098a338])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g29C : List ColumnInfo := [(0,4,25,0,4)]
def g29A : List (List Nat) := [[],[67]]
def g29D4 (j : Nat) := if j=0 then 0x1f else 0
def g29L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g29D4)
  | _ => emptyPacking
def g29I (_ _ : Nat) : Option (Nat × Nat) := none
def g29 : Forest := ⟨29,4,fun i => g29Y[i]?.getD (0,0),g29C,g29A,g29L,g29I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P4_0 : block g29 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g29B4 : block g29 4 0 1=true := g29P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29T : checkedTables g29 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g29 0 0 0 = true)
  · exact (rfl : block g29 1 0 0 = true)
  · exact (rfl : block g29 2 0 0 = true)
  · exact (rfl : block g29 3 0 0 = true)
  · exact g29B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29G : graphValid g29 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low29 : Lower true (varsX 29) (graphGoal 29) 5 := lower_forest (g:=g29) (i:=0) (hints:=68859985928) (before_sound K27 V27) g29G g29T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K29 := extendKnown K27 5 [(29,[]),(54,[16,82,50]),(57,[82]),(58,[16,66,82]),(2087,[49,33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V29 : Known true K29 := extend_ok (m:=29) V27 low29 (by decide +kernel)
def g39Y : Array (Bits × Bits) := #[((bitLimbs [0xdcbf5f5bfd3fdcbf5f,0x5bfd3fdcbf5f5bfd3fdc]),(bitLimbs [0x8c41a4c9ad838c41a4,0xc9ad838c41a4c9ad838c])),((bitLimbs [0xffffffffffffffffff,0xffffffffffffffffffff]),(bitLimbs [0x7d00291a52107d0029,0x1a52107d00291a52107d])),((bitLimbs [0xebedeafdf3f9ebedea,0xfdf3f9ebedeafdf3f9eb]),(bitLimbs [0xe21ac500b8e9e21ac5,0xb8e9e21ac500b8e9e2])),(0x0,0x0),(0x0,0x0),((bitLimbs [0xb776f5fedfceb776f5,0xfedfceb776f5fedfceb7]),(bitLimbs [0x938f0884698e938f08,0x84698e938f0884698e93])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g39C : List ColumnInfo := [(0,2,37,0,4)]
def g39A : List (List Nat) := [[],[82],[32],[32,80],[80,32],[80]]
def g39D4 (j : Nat) := if j=0 then 0x1f else 0
def g39L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g39D4)
  | _ => emptyPacking
def g39I (_ _ : Nat) : Option (Nat × Nat) := none
def g39 : Forest := ⟨39,4,fun i => g39Y[i]?.getD (0,0),g39C,g39A,g39L,g39I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P4_0 : block g39 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g39B4 : block g39 4 0 1=true := g39P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39T : checkedTables g39 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g39 0 0 0 = true)
  · exact (rfl : block g39 1 0 0 = true)
  · exact (rfl : block g39 2 0 0 = true)
  · exact (rfl : block g39 3 0 0 = true)
  · exact g39B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39G : graphValid g39 (boundsBefore K29) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 5 := lower_forest (g:=g39) (i:=0) (hints:=105553117055494) (before_sound K29 V29) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K29 5 [(39,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V29 low39 (by decide +kernel)
def g2071Y : Array (Bits × Bits) := #[((bitLimbs [0xc4ffcdee6badc4ffcd,0xee6badc4ffcdee6badc4]),0x0),((bitLimbs [0xb8d5f2e59eb2b8d5f2,0xe59eb2b8d5f2e59eb2b8]),(bitLimbs [0x98240c128a0098240c,0x128a0098240c128a0098])),((bitLimbs [0x13772bb9b6c713772b,0xb9b6c713772bb9b6c713]),(bitLimbs [0x1889020108f018890,0x20108f01889020108f01])),(0x0,0x0),((bitLimbs [0x6bed357dd8546bed35,0x7dd8546bed357dd8546b]),(bitLimbs [0x6213420d0100621342,0xd01006213420d010062])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2071C : List ColumnInfo := [(1,0,22,0,4)]
def g2071A : List (List Nat) := [[],[66],[33],[33,65],[65,33],[65]]
def g2071D4 (j : Nat) := if j=0 then 0x1f else 0
def g2071L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g2071D4)
  | _ => emptyPacking
def g2071I (_ _ : Nat) : Option (Nat × Nat) := none
def g2071 : Forest := ⟨2071,4,fun i => g2071Y[i]?.getD (0,0),g2071C,g2071A,g2071L,g2071I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2071P4_0 : block g2071 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2071B4 : block g2071 4 0 1=true := g2071P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2071T : checkedTables g2071 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2071 0 0 0 = true)
  · exact (rfl : block g2071 1 0 0 = true)
  · exact (rfl : block g2071 2 0 0 = true)
  · exact (rfl : block g2071 3 0 0 = true)
  · exact g2071B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2071G : graphValid g2071 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2071 : Lower true (varsX 2071) (graphGoal 2071) 5 := lower_forest (g:=g2071) (i:=0) (hints:=137439479808) (before_sound K39 V39) g2071G g2071T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2071 := extendKnown K39 5 [(2071,[]),(4123,[16,50]),(4139,[50,84]),(4141,[48,16,84]),(6159,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2071 : Known true K2071 := extend_ok (m:=2071) V39 low2071 (by decide +kernel)
def g2075Y : Array (Bits × Bits) := #[((bitLimbs [0xefbfbc7efffaf53bdf,0x7f78fdfff5ea77befef1]),(bitLimbs [0x400990010200090080,0x13200204001201002640])),((bitLimbs [0x53d54fb9b3dd7feca7,0xaa9f7367baffd94f553e]),(bitLimbs [0x32144c862520802464,0x28990c4a410048c85132])),(0x0,0x0),((bitLimbs [0x90fec3ef3f5f8bdf21,0xfd87de7ebf17be43fb0f]),(bitLimbs [0x84a20350c05030c909,0x4406a180a0619212880d])),((bitLimbs [0xfed87a65f6b61443fd,0xb0f4cbed6c2887fb61e9]),(bitLimbs [0x24f06a5a1d4154a649,0xe0d4b43a82a94c93c1a9])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2075C : List ColumnInfo := [(16,0,11,0,4)]
def g2075A : List (List Nat) := [[],[49]]
def g2075D4 (j : Nat) := if j=0 then 0x1f else 0
def g2075L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g2075D4)
  | _ => emptyPacking
def g2075I (_ _ : Nat) : Option (Nat × Nat) := none
def g2075 : Forest := ⟨2075,4,fun i => g2075Y[i]?.getD (0,0),g2075C,g2075A,g2075L,g2075I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2075P4_0 : block g2075 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2075B4 : block g2075 4 0 1=true := g2075P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2075T : checkedTables g2075 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2075 0 0 0 = true)
  · exact (rfl : block g2075 1 0 0 = true)
  · exact (rfl : block g2075 2 0 0 = true)
  · exact (rfl : block g2075 3 0 0 = true)
  · exact g2075B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2075G : graphValid g2075 (boundsBefore K2071) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2075 : Lower true (varsX 2075) (graphGoal 2075) 5 := lower_forest (g:=g2075) (i:=0) (hints:=68853694978) (before_sound K2071 V2071) g2075G g2075T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2075 := extendKnown K2071 5 [(2075,[]),(2077,[48,16,33]),(2091,[16,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2075 : Known true K2075 := extend_ok (m:=2075) V2071 low2075 (by decide +kernel)
def g2093Y : Array (Bits × Bits) := #[((bitLimbs [0x75ef25b6f9ffa3f75e,0xf25b6f9ffa3f75ef25b6]),(bitLimbs [0x110025800680040110,0x2580068004011002580])),(0x0,0x0),((bitLimbs [0x9af9fe4df6c77fe9af,0x9fe4df6c77fe9af9fe4d]),(bitLimbs [0x1480c0834002000,0x1480c08340020001480c])),((bitLimbs [0xd5b2db235de5bc7d5b,0x2db235de5bc7d5b2db23]),(bitLimbs [0x8cb40223a04a40d8cb,0x40223a04a40d8cb40223])),(0x0,0x0),((bitLimbs [0xaf6772f89edee90af6,0x772f89edee90af6772f8]),(bitLimbs [0x87612706102325087,0x61270610232508761270])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2093C : List ColumnInfo := [(8,0,37,0,4)]
def g2093A : List (List Nat) := [[],[83],[32],[32,83]]
def g2093D4 (j : Nat) := if j=0 then 0x1f else 0
def g2093L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g2093D4)
  | _ => emptyPacking
def g2093I (_ _ : Nat) : Option (Nat × Nat) := none
def g2093 : Forest := ⟨2093,4,fun i => g2093Y[i]?.getD (0,0),g2093C,g2093A,g2093L,g2093I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2093P4_0 : block g2093 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2093B4 : block g2093 4 0 1=true := g2093P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2093T : checkedTables g2093 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2093 0 0 0 = true)
  · exact (rfl : block g2093 1 0 0 = true)
  · exact (rfl : block g2093 2 0 0 = true)
  · exact (rfl : block g2093 3 0 0 = true)
  · exact g2093B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2093G : graphValid g2093 (boundsBefore K2075) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2093 : Lower true (varsX 2093) (graphGoal 2093) 5 := lower_forest (g:=g2093) (i:=0) (hints:=35184506568708) (before_sound K2075 V2075) g2093G g2093T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2093 := extendKnown K2075 5 [(2093,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2093 : Known true K2093 := extend_ok (m:=2093) V2075 low2093 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((bitLimbs [0xdffff9fef6e75f7c1f,0xd9673bbffffff68bfaf7]),(bitLimbs [0xc0005d8a81008c4429,0x594000091eb23601d8e2])),((bitLimbs [0x61d307f72dbcfdb7e7,0xfedaf7419d08ddf65fc8]),(bitLimbs [0xd686440ea8a43035b8,0x33ea73001828d0b257c8])),((bitLimbs [0xfefe0cfb6ba347a6c9,0xe0fefe84ff53e7c2adf9]),(bitLimbs [0x1670b234173563e9c1,0xc420fc868141a3c22939])),((bitLimbs [0xf33bffc79d7ffcfff7,0x3f9dcfffb3fcbb7d571f]),(bitLimbs [0x91a80502610429a16,0x241406d6a104016c0615])),((bitLimbs [0xaeceb64ace5dee37aa,0xff6cacfa430b6c7eb07a]),(bitLimbs [0xeb346f6004a496a72a,0x8d2cd8264b8c5c5eb05a])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,2,2077,0,5),(0,4,2075,0,5),(16,0,15,0,5),(0,16,4111,0,4),(16,2,13,0,4),(16,4,11,0,4)]
def g31A : List (List Nat) := [[],[48,33]]
def g31D4 := limbs80 #[#[0xcd550310433554c4010,0x109758c5204275650c41,0xc109d984530425e63148,0xc710ad59021c426e6214,0xd4f109b98a53c42b5648,0x8420ab593200826e62,0x6154c20ab59021082e96,0xb654c030ba189300c274,0x665254430d9549510c27,0x3665294430cd551510c3,0xc3365494430cd552510c,0x4c3645214530d5146304,0x14c3345414530d9d4851,0x514c36752d4530cdd505,0x5539026e6214d40cdd53,0x2a241e18120c06009d18,0x66605a544e48423c3630,0xa29c96908a847e78726c,0xbab4aea8]]
def g31D5 := limbs80 #[#[0x76510c27aa9904f55010,0x7ea8985d145309eaa061,0xd0c410fb880213d54086,0xe298217e52042f8a4087,0xf53042fca6085f54c10b,0xc63887d08710deaa0217,0x14f10bf296217c52c43e,0xa9e217e53c42faa7885f,0x30083f060107bc8020bf,0xa6105f94420f610841fb,0xc320fc186417e53082fa,0x9e417d53c82fca3907ec,0xc3f260186f55320bf2,0x2187d54430bf28061fa3,0x30deaa0617e510c3eca,0xa61f4514c3bc60986f95,0x4c378a8987dd4530be28,0x185f94230fd98461bf54,0x40bea9c617e528c2fca3,0x817d53902fea6a05f14d,0x86fca010df54021bf29c,0x140440e02c05801bd540,0x400f4328be278921f05c,0x6719061164561424b10c,0x95a4a8d228849fc749a8,0xc1af0b92ceb0aaca5a8a,0xeb382db360d2b34ca312,0x1ec470ec24febe4f63c2,0x5253349d073ecdb29c87,0x3180400000110600d5f,0x31040003104300620800,0x88218000031040041102],#[0x1000020041002310431,0x4080104008210401882,0x520c3102000120200010,0x102520c32020001002,0x42188201062080188201,0x20420801006008018]]
def g31H5 := limbs80 #[#[0x1a10000000007400053,0x2d000000,0x7cb1a0000000000000,0x16ff2c00001058,0x10840c00394000,0x33327800000,0x424004a3208,0x218005de2a800000,0x6c6c00041b8a00001a75,0x73a000000057a000,0x11200000000,0x664f000005d000000040,0xea8380000000004ce76a,0xa6c2000004ca00000fd9,0xb11640000000000003,0xa8ae0013d000000,0x7372b8]]
def g31D6 := limbs80 #[#[0xfc30ff20fc20ff10fc10,0xfc21fe40fd40fe30fd30,0xeeccaa947e684e341a00,0x54c840543210150c8405,0x404321010c8404532101,0x950ca440754321801cc8,0x43a2101]]
def g31H6 := limbs80 #[#[0x8254324200256a11c280,0x1ae00001c018f24a0203,0xe0018853e12ccf584887,0xf02dd880004a40000026,0x97ddf73b2c0000fd0011,0x2e9000003c2800001cae,0x0,0x6a4d188950f350130f00,0xf335498aed1d,0x912a324da00292270aca,0x1211c043fddc6809d6d,0x84feab570009269640,0x363598e4e025591bcb38,0x80008dc8cd300b503000,0xaa4b93a52442d9c23978,0x10e428002245540001,0xc03f859b810123001a28,0xd197568001bc03ea8839,0x12a293000a670074e10]]
def g31D7 (j : Nat) := if j=0 then 0x2c440bf else 0
def g31H7 := limbs80 #[#[0x9d262f68884c84a00a43,0x6e28fa490c18ac918,0x1600060bc60]]
def g31L : Nat → Packing
  | 4 => (32,3,3,0,0,8,0,g31D4)
  | 5 => (63,2,3,0,0,10,0,g31D5)
  | 6 => (10,1,3,0,0,8,0,g31D6)
  | 7 => (1,0,3,0,0,0,0,g31D7)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 11 127 3 10 5 1 g31H5
  | 6 => lookupWord 23 127 6 11 6 1 g31H6
  | 7 => lookupWord 4 23 3 9 4 1 g31H7
  | _ => fun _ => none
def g31 : Forest := ⟨31,7,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P4_0 : block g31 4 0 32=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B4 : block g31 4 0 32=true := g31P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_7 : block g31 5 7 56=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 63=true := (@block_merge g31 5 0 7 56 g31P5_0 g31P5_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 10=true := g31P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P7_0 : block g31 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B7 : block g31 7 0 1=true := g31P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact g31B4
  · exact g31B5
  · exact g31B6
  · exact g31B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K2093) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 8 := lower_forest (g:=g31) (i:=0) (hints:=343732390406) (before_sound K2093 V2093) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K2093 8 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V2093 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((bitLimbs [0xb373fffb7a9ef738f3,0x7799ef9fffeffe7776db]),(bitLimbs [0x8080f8901001c201b,0x2000a219c5a65a0734c2])),((bitLimbs [0x7edef3ffefe17fd77f,0xbcef3e63f551f1bbdfe4]),(bitLimbs [0x962c01824c42254c6,0xdad0c42440520b1cbc4])),((bitLimbs [0xedbf9aeeade3cfc71c,0xbe779b676dda3b98bdb5]),(bitLimbs [0xc15804739b30c1af18,0x7602b32d20482b18b531])),((bitLimbs [0xd53fad9c173ef4feb7,0x6b78ddbeaeffafed2b1b]),(bitLimbs [0x12b7c060a25440d9a4,0x41d819c62a5081e80a19])),(0x0,0x0),((bitLimbs [0x4ee9d62bc659de154f,0xf7b633fa50d1dceae476]),(bitLimbs [0x96be19200aa42ec109,0xf3b8a06f12f194ea6436])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,2,2093,0,5),(0,4,2091,0,5),(8,0,39,0,5),(32,0,15,0,5)]
def g47A : List (List Nat) := [[]]
def g47D6 (j : Nat) := if j=0 then 0x7209f else 0
def g47L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g47D6)
  | _ => emptyPacking
def g47I (_ _ : Nat) : Option (Nat × Nat) := none
def g47 : Forest := ⟨47,6,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 1=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact (rfl : block g47 4 0 0 = true)
  · exact (rfl : block g47 5 0 0 = true)
  · exact g47B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 7 := lower_forest (g:=g47) (i:=0) (hints:=105553251273222) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 7 [(47,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((bitLimbs [0xfffdb97affffe7fdcf,0xeafc7dfbb7fffebf37df]),(bitLimbs [0x431c2888c0d0d8107,0x2b81b70106fca2936da])),((bitLimbs [0xe9dfdeafcef799f739,0xd5dfff0efd6bd755ffe1]),(bitLimbs [0x8564506357acb81100,0x1656689ecd189715ada1])),((bitLimbs [0x9b265effbeff5d2ff5,0xb58fbe7cff3e3ff2fab3]),(bitLimbs [0x22910f027070030e63,0x89890724f3103cf2da11])),(0x0,0x0),((bitLimbs [0xf6696f7d736e6799c6,0x6fb5c4f17fbd6dafe01f]),(bitLimbs [0xa12ec85257039218a0,0x6b4684d52f399387e00f])),((bitLimbs [0xf7fbef8f5db4bff27f,0xfff3dbcfefc9c9cddd7c]),(bitLimbs [0x7183139ca20020287e,0xeccbd3a8248041cc5174])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(0,16,2087,0,5),(16,0,39,0,5),(0,2,37,0,4),(0,4,51,0,4),(0,18,37,0,4),(0,32,23,0,4)]
def g55A : List (List Nat) := [[],[82]]
def g55D4 (j : Nat) := if j=0 then 0x4f95020 else 0
def g55D5 := limbs80 #[#[0x4a0e140fc42ff20fc20,0x6088]]
def g55H5 (j : Nat) := if j=0 then 0x3 else 0
def g55D6 (j : Nat) := if j=0 then 0x163440df else 0
def g55H6 := limbs80 #[#[0x20000000000000002e98,0x18803c00000001]]
def g55L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g55D4)
  | 5 => (3,1,3,0,0,5,0,g55D5)
  | 6 => (1,0,3,0,0,0,0,g55D6)
  | _ => emptyPacking
def g55I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g55H5
  | 6 => lookupWord 1 29 0 7 2 1 g55H6
  | _ => fun _ => none
def g55 : Forest := ⟨55,6,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : block g55 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : block g55 4 0 1=true := g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P5_0 : block g55 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B5 : block g55 5 0 3=true := g55P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P6_0 : block g55 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B6 : block g55 6 0 1=true := g55P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact g55B4
  · exact g55B5
  · exact g55B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 7 := lower_forest (g:=g55) (i:=0) (hints:=105896714439174) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 7 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((bitLimbs [0xd7fff7efbfbfbfbdfd,0x7dbf7f7ff77ef3e4fddf]),(bitLimbs [0x180418686418268901,0x382dc01c84784044385b])),((bitLimbs [0x7901bfb6cedf567fff,0xbe619384ba9d1e3b2fea]),(bitLimbs [0xd8370acc1107446fd4,0x2ea1f3b818040a310fea])),(0x0,0x0),((bitLimbs [0xbffb7dfd7bd7fffa1f,0x9fffbe9b69f7dfdb53fc]),(bitLimbs [0x249aa4170ba410304a,0xc492340329829f9b4184])),((bitLimbs [0xb885eab5736eea663a,0xf67fcff1ecc92cff822f]),(bitLimbs [0xc4498c08d6e284893a,0xd25bcbb0f003a0ea822f])),((bitLimbs [0xf6558f63a73d5d07e4,0xeccb57e4ffda70a7fd23]),(bitLimbs [0x80ca95368942a90666,0x46d0066272fa1aa7f520])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,32,27,0,6)]
def g59A : List (List Nat) := [[],[65]]
def g59D6 (j : Nat) := if j=0 then 0x3f else 0
def g59L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact (rfl : block g59 4 0 0 = true)
  · exact (rfl : block g59 5 0 0 = true)
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=106240445263880) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 7 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((bitLimbs [0xbfffffd67fffffffbe,0xbffff7fffffeefffc7df]),(bitLimbs [0x47404440140401260a,0xa1390004920a4f6a819c])),(0x0,0x0),((bitLimbs [0xfb9463b9d2e9f38de3,0xf18a2cf0c377bd633f33]),(bitLimbs [0x72e138f616f13cb8c3,0x999265c4c19dac633f03])),((bitLimbs [0xe7eebf7fb7776abbdb,0xdf55fff71e37d7d5bb6e]),(bitLimbs [0x1026230a2828dad910,0x5c44edbb092500953262])),((bitLimbs [0x7eb9c9ffd8aef5e5ef,0xfcea3a5afbcd3a3efeb1]),(bitLimbs [0x38222f14a90bce03ec,0x4c4e32d903c03014eeb1])),((bitLimbs [0xfc75a76dbbb1b5587f,0x75bf6a7aa489931b7de8]),(bitLimbs [0xc313c2d50557f0c023,0x30d4ce7a2488ff1b5d68])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(0,16,45,0,6),(0,4,57,0,5),(0,32,29,0,5),(0,36,25,0,4)]
def g61A : List (List Nat) := [[],[82]]
def g61D3 := limbs80 #[#[0xc229a41851906194c20,0xc30a32]]
def g61D4 := limbs80 #[#[0x9d98452042756508410,0x108f990520425e631481,0xb109798e52c423e64d48,0x4b109798f52c423e6494,0x48020b618d200823e64d,0x348020b9185200827b65,0x64884209bd9520082cc6,0x65454420d594d51082ae,0x365494420d594e510833,0x3576194c20d518653083,0x834c5388120d91462048,0x483545314520d614f204,0x1483375414520cd15051,0x53483546114d20d514f5,0x2218825e6394220d5d84,0x9251c825c6354a20ab99,0x191500865c63540218f9,0x302a241e18120c06008f,0x6c66605a544e48423c36,0xa8a29c96908a847e7872,0xd2ccc6c0bab4ae]]
def g61H4 (j : Nat) := if j=0 then 0x21f else 0
def g61D5 := limbs80 #[#[0x5e53082eca2104f95010,0x7ca910d714d20ba28a41,0xf14810fa10821f710042,0xfa90217e52042faa4085,0xc52c43ec43886f95010b,0xea5885f94b10bea96217,0x88020f690041f920082f,0x108417e50083de40107e,0x51083eaa2107b88420f6,0xa6105f94820bf28841f6,0x4520fd90241ee20483bc,0x9a41f751482f8a2907d1,0x883de41107ec8220ee2,0x3107b88620f610c417e5,0x21bf28e417d52882fca,0x443f621086fca010df54,0x37ca910df94221bea8,0x2d130843415090341405,0xac4f24114843d1c0cc60,0x4f473371a4cc612e164,0x629d409d4b2451887422,0xd6a33d8cc35f2ed64af5,0xc040c0701ef7639dc0d,0x81204000802a06802c04,0x4010002008802000604,0x40007023c084110400,0x3000004f020070200401,0x84032048403004100840,0x204010580200]]
def g61H5 := limbs80 #[#[0x905c2e971c5200078337,0x48700044d07800001,0xff9e019010e000000000,0x4240cc81144c59c,0x4a0c342d91c83a608470,0x6e2c00412241a566d000,0xdcd05dea200205000a4,0x25800001e85aaf98a9e2,0x800d2906ec8986020f50,0x2403088b0172a9]]
def g61D6 := limbs80 #[#[0xfe20fd20fc20ff10fc10,0x3f2d1500fe21fc21ff20,0x8f2300cd18058d756351,0xc8c02230088c022300,0x1a300af23]]
def g61H6 := limbs80 #[#[0x8000a5510c22080150c1,0x6a80028200164ea0110,0x253ca8000a6b8bb6900,0xe02216312260000,0x559d30000cd8250014ac,0x6f5a210007912c22c000,0xeb39d7b0c61aab30e58,0x311743f1760c847dbe,0x2b3d0a128003ab9da71e,0xeec8000086e0c4b84656,0xa4000b820039e0000030,0xa4914851e212b9874,0x2480f5f68963e590af19,0x69f01]]
def g61D7 (j : Nat) := if j=0 then 0x7209f else 0
def g61H7 := limbs80 #[#[0xd26021a500d3865fe800,0x296e14070000]]
def g61L : Nat → Packing
  | 3 => (2,4,2,0,0,3,0,g61D3)
  | 4 => (36,3,2,0,0,8,0,g61D4)
  | 5 => (50,2,2,0,0,9,0,g61D5)
  | 6 => (8,1,2,0,0,8,0,g61D6)
  | 7 => (1,0,2,0,0,0,0,g61D7)
  | _ => emptyPacking
def g61I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g61H4
  | 5 => lookupWord 12 67 4 11 6 1 g61H5
  | 6 => lookupWord 17 89 6 11 6 1 g61H6
  | 7 => lookupWord 3 17 0 8 3 1 g61H7
  | _ => fun _ => none
def g61 : Forest := ⟨61,7,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P3_0 : block g61 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B3 : block g61 3 0 2=true := g61P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P4_0 : block g61 4 0 36=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B4 : block g61 4 0 36=true := g61P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : block g61 5 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_6 : block g61 5 6 44=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : block g61 5 0 50=true := (@block_merge g61 5 0 6 44 g61P5_0 g61P5_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 8=true := g61P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P7_0 : block g61 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B7 : block g61 7 0 1=true := g61P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact g61B3
  · exact g61B4
  · exact g61B5
  · exact g61B6
  · exact g61B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 8 := lower_forest (g:=g61) (i:=0) (hints:=598478061568008) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 8 [(61,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g62Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xdfffbfffffeffffc5f,0xfbffedeeff7fffefcbff]),(bitLimbs [0x5008c8073590490479,0x23fd6c888149d0e183af])),((bitLimbs [0xbfebf8fedf7dff97ff,0x2e67ff7fdf9ff95f76e7]),(bitLimbs [0xc3311c90e26a8888a0,0x882203b39e1fe95e70e1])),((bitLimbs [0xf5ff6ff5fb9eed7ff6,0xffbe729d7feefebcbf7b]),(bitLimbs [0xb6c0d6688424b13806,0xdf46720458520e2cbe52])),((bitLimbs [0x751f5fc9bdbba3ffac,0xfd9e3fd1f4ec57f0fd5d]),(bitLimbs [0x849b159e6957485225,0xe09215d264ad9c506d5d])),((bitLimbs [0xbf2eddaa74f7fea3e9,0x2f7f9f77cfb9075bf49e]),(bitLimbs [0x1474209d736775111,0x6cccc84747f2031bd41e])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g62C : List ColumnInfo := [(0,4,58,0,5),(0,8,54,0,5),(0,16,46,0,5),(0,32,30,0,5)]
def g62A : List (List Nat) := [[],[50,84]]
def g62D6 (j : Nat) := if j=0 then 0x7209f else 0
def g62L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g62D6)
  | _ => emptyPacking
def g62I (_ _ : Nat) : Option (Nat × Nat) := none
def g62 : Forest := ⟨62,6,fun i => g62Y[i]?.getD (0,0),g62C,g62A,g62L,g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P6_0 : block g62 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B6 : block g62 6 0 1=true := g62P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact (rfl : block g62 4 0 0 = true)
  · exact (rfl : block g62 5 0 0 = true)
  · exact g62B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 7 := lower_forest (g:=g62) (i:=0) (hints:=211794235234304) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 7 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)
def g2079Y : Array (Bits × Bits) := #[((bitLimbs [0x69d8fff7ddfe3f3ff8,0x5b9ef8f9b929bf66385d]),(bitLimbs [0x801020001000b03a40,0x8800003021090122004c])),((bitLimbs [0x947f23e47a7fe7759f,0xa779e3154fff11898db7]),(bitLimbs [0x3601c480110400198,0x261182018e1004888991])),((bitLimbs [0xffa470ede2b9f1dd47,0xc4b597c666fd5917d7a8]),(bitLimbs [0xb81501a6bc200b3e22,0xc0a0016650a119171628])),((bitLimbs [0x72b3543ae7e136982e,0x7e48dceeef42da9d634b]),(bitLimbs [0x4c4cd2c8454042003c,0x6bd4cc8240921d6103])),((bitLimbs [0xcb6fa92df7c258cacd,0x7ade37565623e4faf232]),(bitLimbs [0x330941304294010005,0x521e300954b244c0f232])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2079C : List ColumnInfo := [(4,0,27,0,6),(0,4,4123,0,5),(0,8,2071,0,5),(0,16,6159,0,5),(1,0,30,0,5),(2,0,29,0,5),(1,8,22,0,4),(1,16,14,0,4),(2,4,25,0,4),(8,0,23,0,4),(16,0,2063,0,4)]
def g2079A : List (List Nat) := [[],[67]]
def g2079D4 := limbs80 #[#[0x88690221785c44348110,0x29056a7510d20442b4ba,0xa5c064cc520b92e021e6,0x804348275b8ac021a413,0x208d8eab0886906c8535,0xbaac221e41395c46510d,0x6629861c5498e214c237,0x1c59c454cc530e2ae22a,0x550c4348697b92c22a26,0x4443a3eeaa188710e1e6,0xcbb8a86a8887a350f625,0x312a221c9f7650d5110e,0x88765dc54394443ad2e0,0xd71d954310e4fbb28728,0x28211a17140d0a030049,0x4643403d3a3734312e2b,0x4982000020524f4c49,0x2a608]]
def g2079D5 := limbs80 #[#[0x3c7153314c2e96010d20,0x10a7d954310e9f6150c4,0x110fa14d20443e843481,0xd10be58331443ea5348,0x10d10bd58443442f9601,0x110f109f994434427d65,0x6010d209f59443c42f56,0xc43cc5209f99443482f9,0xee64cc520bb19331483c,0x2ed6110d20fa58043482,0x82ec6510d20f314c4348,0xc82ee6414d20bb994434,0x1c83cc43cc720bb99031,0x43c82ee64cc720bb1933,0x1210c3755148430bb584,0x95210c33e5448430cf55,0x552210c37551884309fd,0xf596210c33e5488430cf,0xddd89510c37562544309,0xcfd51214c33c5448530,0x30b798e214c27c654853,0x530cfd52214c33c54885,0xc530d7153314c27e6588,0x10530be580414c35e65c,0x3d05309f994414c2de63,0x63d09309f997414c2de6,0xd61151309f997424c2de,0x3e6115130cf584544c27,0x2dc6348630cf588544c3,0xc27d65886309fd95218c,0x486f56110d219f58454c,0x34867e6510d21e750c43],#[0x434867c6550d21d714d4,0x4438867d6014d219f996,0x94438879d4310e21bd58,0x952438867f6550e219f5,0xf582538867d6590e21cf,0xe710d414c67d60950319,0x19f195414c6dc6350531,0x31b798f414c79c43d053,0xf31e710f41cc75e6510d,0x5331b759743cc6dd6010,0x953329f58254cc67d601,0x2544439fd855010e7d60,0x6054443e750d5110eef6,0xf6254443db1895110e7f,0x9d4354843e750e5110f6,0x8cc1622583a059060003,0xe2945109f11c2023986c,0xaa704cf9993185fcb915,0x8dd18a2443c861021e93,0xd4ca934fe9e532a4a47a,0x2adf5b2b4d66ab954aa7,0x2462ec45822fe5f0bad7,0x728dc9b2b58696cf998b,0x102dfbbea7baf41e53b6,0xb22fc4487d0e215c2583,0x55c9e93124a464868f31,0x514a013ce734d998b2fe,0xcac356eaad48a774d694,0x29d20035b7b55676c857,0x280830e1a213042870c9,0xc830e1928618a0260206,0x1030e182860010c08608],#[0x40040000c1010020a12,0xd2100080930408218004,0x800326042080420c129,0x60010002608000400115,0x280008013082130800,0x4000000012882a000200,0x8114085040260800020,0x4040094011408204502,0x20801c104289826020a,0x40120800408008002001,0x10408004503021800090,0x2002820810200000004,0x41030410207002081020,0x40300004082040040c30,0x4102001020810010905,0x50]]
def g2079H5 := limbs80 #[#[0x3cd620c312400000052c,0x34c000cff980093800e5,0x24af4800003d600,0x244d0b91f4c000029000,0x6950006311c009018b00,0x5168620]]
def g2079D6 := limbs80 #[#[0x5e53042baa6085b54810,0xdaa5087a48210f490221,0xd94430baa88616d52882,0xf2a0613d540c2daa4185,0xd528c27ea8984f151309,0xca918cf55231b7a92636,0xc8110f6902219d4310e7,0xa8c217e53442f8a6887b,0x53482fca7887bc8310be,0xa6907b10d20f798a417c,0xf20f798e41ec31c83d8,0x8a61df314c2faa2187b1,0x1cc2faa3185f15130bfa,0x690dfd4121be2a661df3,0x31bf29c437d50886f8a,0xa637e540c6fca618df54,0xcc6fca918df15131ee21,0x98f7d0f31ee21e637d50,0x32be2a2657e54cc6f8a9,0x877d5010efca9995f543,0xefaa321dfd4543bea88,0x87f10d10ff98a217e539,0xfe21e21fe53443f8a68,0x1fe210c3fa42187f10d2,0x3f882987f88530fe90a6,0x7f48630ffa1261ff414c,0xff10e61fd21cc3fc4318,0xff42cc3fe83987f10730,0xfc8690ff50d21fe21a43,0xf90e21fea1c43fc43887,0xea8663ff414c7fa8298f,0xe54cc7faa998ffd0731f],#[0xca221ff54443fea8087f,0x7202700a8001fd5210ff,0x5e82a012c08103481500,0x26a12008703e41ce0d50,0xdf868430016e0ae0528,0x84f825b11b88703f61e3,0x21920c185dc2d615c0a6,0x907863ab1cb0dc86ae34,0xa123e917087c4202010f,0x524a62510279135c97e4,0x5e82e516b0b225732b09,0x9a28cea65431c9890c18,0xa70e37c9b6cd866b7352,0x71d88ea67443991c98e3,0x967bc3d39e60f0c77a3b,0x12a06501a7f53f31f68f,0x128885439a19109e83a4,0x61440500068d646222bd,0x2071851301471440b014,0xc69444462071a5111400,0x40401871a51014001c81,0x122c061c6122c0520718,0xb01471848814001c7185,0x40b01871848b01461038,0x500061a40c2c052871a,0xc2c05206942050187102,0x6502c05206142c051850,0x2481c69448e205000a24,0x81c002c81c69448e2400,0x60d20401ca2461440d20,0x20718510308140028a24,0x820402c71a5123890008],#[0x308180028a2481851034,0x5444d284180928920614,0x91c6564113481809206,0x34a00072065444d20600,0x91951134a000719511,0x820700091c65641134a0,0x2061444c28461c61038,0xc207000b286103081c0,0xc7103081006287185913,0x44e20402891851130a11,0x2040c20600092891c616,0x92892040c2060009289,0x20600092891440c20600,0x1440e208100a2891440c,0x481851030814002ca206,0x11ca2481440c204024a2,0x1840c204020918590309,0xa2061440c2070009289,0x30911ca2461440e20810,0x1491859030911c918590,0x45103081c0024a244040,0x920614408180020a2,0x1020600092881850c206,0x855230e208100b289205,0x10062891030810072471,0x247103081c0020610308,0x8218a2461440c205000a,0xa2471851030882481844,0xc21c91820c918448214,0x4610308180024a247185,0x510100424510204018a2,0x28510308508100308108],#[0x8100328308110a1c3084,0x60810052460430810030,0x2891c60c218918508424,0xc2043245040109182044,0xa2450c20401c90c20440,0xc28101830400c20400c,0x4488218a2480c2806205,0xa2450c214a2430842461,0x1c61230e20882450c210,0x89143085289143090189,0x500032]]
def g2079H6 := limbs80 #[#[0x23011003000000300112,0x80110421,0x63700005c,0x90000008310001d60000,0x506910f20f3073e00042,0x491cb00000000031c000,0x2000000000b9a627000f,0xd3923a51311413dbd,0x100015fd4b543926000,0x961000000b,0x41bc4533f00000,0x2f79500000000000d000,0xe46e05000000a4ec0a2,0xcb475e00000000000000,0x0,0x370092b0000000000000,0x41800000070b000d09f2,0x585e1e753000000,0x941f17000000419d030,0x840000000000f3300000,0x12c715a3b000,0x44200085b0000,0x7b120445900024a00000,0xe4f000000,0x6000a580000000008560,0x655000000000e5d73,0x2d00021a000000912000,0x1190db2d32f60424e0c9,0x52a000bd3000000000e5,0xa1d000d4dd5a000,0xc00074493c0000000000,0x421000000000000e4],#[0x7000000a11535a38000,0xc86000e340009c30002,0x62e000e57e5000000000,0x762000000,0xeb60000000000,0x91f00000,0x80e000000c54000,0x316c0f0,0x32200,0x52000e48b28802000000,0xd471251080009,0x0,0xdd0000000]]
def g2079D7 := limbs80 #[#[0xfe10fd10fc10ef20ed20,0xfd30fc30fe20fd20ff10,0xfc31fe21fd21ff30fe30,0xff32fd32ff31fe31fd31,0xf812000fe43fd43fc43,0x4d917f298464708a90e2,0x8afe596a4d37a4642679,0x8100d0d603bca72eda59,0x90620c0049cc40088398,0x2907314831060028e62,0x83106002907314831060,0x128398a4188202507314,0x20c41800941cc520c410,0x20e6290620c0049cc5,0xcc520c41800939483106,0x29062080641483104039,0x4180094a0c520c41800a,0x906290620c004a0c520c,0x18820212831483106002,0x5a506290620809418a4,0xc418008524e6290620c0,0x127314831060028c520]]
def g2079H7 := limbs80 #[#[0x715628d18900e781000,0x3450490401e814100c1,0x3a640018fc0bc10e445,0x110ec6849c0,0x2bc66c00181400000000,0x342a158f60818000002,0x400001c098000f1dc640,0x525c2ed18d2146c16674,0xb86cc0034ac001144002,0x9ca3c4f08e408d1cf55c,0x4ea14e56927d81083ad7,0x6e690710bc8d48dc561,0x57390cb8b173e07dd7ec,0x13e15d34ad15cc48538a,0x5a0d8003105d6dc74001,0x2940556151174003c56a,0x1a040f400000,0xc1f08060820002a78324,0x1c8092cb340000000010,0x1858002ad08a800,0x3536e5513880c047090,0xb40003f6803c0000,0xa74d080028ec00280000,0x3704b31a304afc001c25,0x8000000c5cb312080028,0x21700000024b7510d4,0xe4000ccf9848e0000000,0x10420978d35310,0x18143000000000092800,0x220f847b314001b2b88b,0x55012a472fcf3aac588b,0x48]]
def g2079D8 (j : Nat) := if j=0 then 0x3f else 0
def g2079H8 := limbs80 #[#[0xce2c4cb00330b0314000,0x1,0x3cc000014500000000,0xf33087a40000000000,0x528aefbc0004000000,0xaa10c00318d1a48,0x0,0xab0000000080000d5000,0x8040000000ac847002,0xcd6da0f510d600000308,0x94c00124,0x75000ea0]]
def g2079L : Nat → Packing
  | 4 => (23,4,4,0,0,8,0,g2079D4)
  | 5 => (99,3,4,0,0,11,0,g2079D5)
  | 6 => (99,2,4,0,0,13,0,g2079D6)
  | 7 => (23,1,4,0,0,11,0,g2079D7)
  | 8 => (1,0,4,0,0,0,0,g2079D8)
  | _ => emptyPacking
def g2079I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 6 41 3 10 5 1 g2079H5
  | 6 => lookupWord 28 293 4 12 7 1 g2079H6
  | 7 => lookupWord 33 191 6 12 7 1 g2079H7
  | 8 => lookupWord 8 89 4 10 5 1 g2079H8
  | _ => fun _ => none
def g2079 : Forest := ⟨2079,8,fun i => g2079Y[i]?.getD (0,0),g2079C,g2079A,g2079L,g2079I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P4_0 : block g2079 4 0 23=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B4 : block g2079 4 0 23=true := g2079P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P5_0 : block g2079 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P5_4 : block g2079 5 4 95=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B5 : block g2079 5 0 99=true := (@block_merge g2079 5 0 4 95 g2079P5_0 g2079P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P6_0 : block g2079 6 0 19=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P6_19 : block g2079 6 19 44=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P6_63 : block g2079 6 63 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B6 : block g2079 6 0 99=true := (@block_merge g2079 6 0 19 80 g2079P6_0 (@block_merge g2079 6 19 44 36 g2079P6_19 g2079P6_63))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P7_0 : block g2079 7 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P7_2 : block g2079 7 2 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B7 : block g2079 7 0 23=true := (@block_merge g2079 7 0 2 21 g2079P7_0 g2079P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P8_0 : block g2079 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B8 : block g2079 8 0 1=true := g2079P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079T : checkedTables g2079 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2079 0 0 0 = true)
  · exact (rfl : block g2079 1 0 0 = true)
  · exact (rfl : block g2079 2 0 0 = true)
  · exact (rfl : block g2079 3 0 0 = true)
  · exact g2079B4
  · exact g2079B5
  · exact g2079B6
  · exact g2079B7
  · exact g2079B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079G : graphValid g2079 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2079 : Lower true (varsX 2079) (graphGoal 2079) 9 := lower_forest (g:=g2079) (i:=0) (hints:=68854219266) (before_sound K62 V62) g2079G g2079T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2079 := extendKnown K62 9 [(2079,[]),(2095,[49,33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2079 : Known true K2079 := extend_ok (m:=2079) V62 low2079 (by decide +kernel)
def g2103Y : Array (Bits × Bits) := #[((bitLimbs [0xeffe7feffb81efe56,0xd11917dd777d3d66cc64]),0x0),((bitLimbs [0xf617fa6995efe159f7,0x2ef6bfa1e982cf1811bf]),(bitLimbs [0x58921802402200a40,0x2068e4101010708013c])),((bitLimbs [0xdf72790b2ffaec2938,0x7bff6c2aa93088eb6783]),(bitLimbs [0x42728628402c1905a0,0x107960282a8c88636483])),(0x0,0x0),((bitLimbs [0xf7470ed2ceb76b47d9,0xdf7de316c08a5393b25a]),(bitLimbs [0x82240a05cacc049033,0x5d102114ccc800b39242])),((bitLimbs [0x7e46deb52a5f3a16b,0x52c3618e8721ff85b7b0]),(bitLimbs [0xed1955f788a2490806,0x46c189b397215944b7b0])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2103C : List ColumnInfo := [(0,32,2071,0,5)]
def g2103A : List (List Nat) := [[],[66]]
def g2103D5 (j : Nat) := if j=0 then 0x3f else 0
def g2103L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g2103D5)
  | _ => emptyPacking
def g2103I (_ _ : Nat) : Option (Nat × Nat) := none
def g2103 : Forest := ⟨2103,5,fun i => g2103Y[i]?.getD (0,0),g2103C,g2103A,g2103L,g2103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P5_0 : block g2103 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B5 : block g2103 5 0 1=true := g2103P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103T : checkedTables g2103 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2103 0 0 0 = true)
  · exact (rfl : block g2103 1 0 0 = true)
  · exact (rfl : block g2103 2 0 0 = true)
  · exact (rfl : block g2103 3 0 0 = true)
  · exact (rfl : block g2103 4 0 0 = true)
  · exact g2103B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103G : graphValid g2103 (boundsBefore K2079) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2103 : Lower true (varsX 2103) (graphGoal 2103) 6 := lower_forest (g:=g2103) (i:=0) (hints:=703824881256448) (before_sound K2079 V2079) g2103G g2103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2103 := extendKnown K2079 6 [(2103,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2103 : Known true K2103 := extend_ok (m:=2103) V2079 low2103 (by decide +kernel)
def g2107Y : Array (Bits × Bits) := #[((bitLimbs [0xb7e7dfd2dfff149ecb,0xbafd7c7b516b1b07c4cf]),(bitLimbs [0x420002002000018808,0x80742102280b05004a])),((bitLimbs [0x584ba4bfcb79efff7f,0x4732c35dceb56ebaa372]),(bitLimbs [0x10120c940092102464,0x12080488041402aa100])),(0x0,0x0),((bitLimbs [0xf3d40ffdb925f6e1f1,0xfecdadb4ac11ce5c1db9]),(bitLimbs [0x8d80b00887280c0011,0xda0d03140500845014b1])),((bitLimbs [0x9f375e447dcaef1f8a,0xcfe6d1a2b14bb5fb5884]),(bitLimbs [0x3498093ad8d84a23b6,0xe680008b1c134ba5884])),((bitLimbs [0x7ddff2af39d0c9a08f,0x4d270ee1fe8ee6e57a23]),(bitLimbs [0xea659022692483488b,0x54063aa44aa212c54a23])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2107C : List ColumnInfo := [(0,16,4139,0,5),(0,32,4123,0,5),(1,0,58,0,5),(2,0,57,0,5),(16,0,2091,0,5),(32,0,2075,0,5),(1,16,42,0,4),(2,32,25,0,4),(8,0,51,0,4),(48,0,11,0,4)]
def g2107A : List (List Nat) := [[],[16,84]]
def g2107D4 := limbs80 #[#[0x9799731483e12148110,0x3]]
def g2107D5 := limbs80 #[#[0x7f52442faa4887e48110,0xbe62907bc8520f690a41,0x7cc720ee29a417f51483,0x549109b302402faa3907,0x401440401060c2f1cb3,0x5042000044002101002]]
def g2107H5 (j : Nat) := if j=0 then 0x701d else 0
def g2107D6 := limbs80 #[#[0xff20fd20fd10bf40bd40,0x7352620c07c794572900,0xc510c005a4c5a4c41810,0xa0c520c41800941cc520,0x106290620c004]]
def g2107H6 := limbs80 #[#[0x34005a4c,0x40de0000025400000000,0xe10000127b4002f00000,0x103c200f20028c00,0x8a]]
def g2107D7 (j : Nat) := if j=0 then 0x2a19080df else 0
def g2107H7 := limbs80 #[#[0x4100003300,0xe80000000000000000,0x294200003b0000006c00,0x74002000000000]]
def g2107L : Nat → Packing
  | 4 => (2,3,4,0,0,3,0,g2107D4)
  | 5 => (10,2,4,0,0,7,0,g2107D5)
  | 6 => (5,1,4,0,0,8,0,g2107D6)
  | 7 => (1,0,4,0,0,0,0,g2107D7)
  | _ => emptyPacking
def g2107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 3 0 5 1 0 g2107H5
  | 6 => lookupWord 3 37 2 9 4 1 g2107H6
  | 7 => lookupWord 2 37 0 8 3 1 g2107H7
  | _ => fun _ => none
def g2107 : Forest := ⟨2107,7,fun i => g2107Y[i]?.getD (0,0),g2107C,g2107A,g2107L,g2107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107P4_0 : block g2107 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2107B4 : block g2107 4 0 2=true := g2107P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107P5_0 : block g2107 5 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2107B5 : block g2107 5 0 10=true := g2107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107P6_0 : block g2107 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107P6_2 : block g2107 6 2 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2107B6 : block g2107 6 0 5=true := (@block_merge g2107 6 0 2 3 g2107P6_0 g2107P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107P7_0 : block g2107 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2107B7 : block g2107 7 0 1=true := g2107P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107T : checkedTables g2107 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2107 0 0 0 = true)
  · exact (rfl : block g2107 1 0 0 = true)
  · exact (rfl : block g2107 2 0 0 = true)
  · exact (rfl : block g2107 3 0 0 = true)
  · exact g2107B4
  · exact g2107B5
  · exact g2107B6
  · exact g2107B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107G : graphValid g2107 (boundsBefore K2103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2107 : Lower true (varsX 2107) (graphGoal 2107) 8 := lower_forest (g:=g2107) (i:=0) (hints:=70437597872642) (before_sound K2103 V2103) g2107G g2107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2107 := extendKnown K2103 8 [(2107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2107 : Known true K2107 := extend_ok (m:=2107) V2103 low2107 (by decide +kernel)
def g2109Y : Array (Bits × Bits) := #[((bitLimbs [0xb95676d56d5bd2ff82,0xf1799fef3c0cde54c36b]),(bitLimbs [0x420100220804803082,0x900007c110000344c022])),(0x0,0x0),((bitLimbs [0xe7bccc79f795ddb4b7,0x6fc461f641cfaeca5c55]),(bitLimbs [0x103401050001740101,0x6106200401c8080a1051])),((bitLimbs [0x2f3f3f9f7af72f1379,0xadbba692ff7603ada698]),(bitLimbs [0x1008210c388000e30,0x940026a1610a02608])),((bitLimbs [0x6f9d5f9e8eaa64e2ea,0x26979221db78eb6ba9a1]),(bitLimbs [0x6a706ccf1040b8804b,0x7492872800c1eb4b89a1])),((bitLimbs [0xd4f0e6fa9a3bf77c2e,0x963d7a5f80d3fc331f26]),(bitLimbs [0xc022c50d09a008670,0x631501aa20194310f04])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2109C : List ColumnInfo := [(0,16,4141,0,5),(16,0,2093,0,5),(32,0,2077,0,5),(1,0,60,0,4),(4,0,2105,0,4),(8,0,37,0,4),(8,16,37,0,4)]
def g2109A : List (List Nat) := [[],[32]]
def g2109D4 (j : Nat) := if j=0 then 0x4fd5110 else 0
def g2109D5 (j : Nat) := if j=0 then 0xc8404fd10 else 0
def g2109H5 (j : Nat) := if j=0 then 0xa else 0
def g2109D6 (j : Nat) := if j=0 then 0xd63440ff else 0
def g2109H6 (j : Nat) := if j=0 then 0xb else 0
def g2109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g2109D4)
  | 5 => (1,1,3,0,0,0,0,g2109D5)
  | 6 => (1,0,3,0,0,0,0,g2109D6)
  | _ => emptyPacking
def g2109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g2109H5
  | 6 => lookupWord 1 2 0 4 0 0 g2109H6
  | _ => fun _ => none
def g2109 : Forest := ⟨2109,6,fun i => g2109Y[i]?.getD (0,0),g2109C,g2109A,g2109L,g2109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109P4_0 : block g2109 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2109B4 : block g2109 4 0 1=true := g2109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109P5_0 : block g2109 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2109B5 : block g2109 5 0 1=true := g2109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109P6_0 : block g2109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2109B6 : block g2109 6 0 1=true := g2109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109T : checkedTables g2109 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2109 0 0 0 = true)
  · exact (rfl : block g2109 1 0 0 = true)
  · exact (rfl : block g2109 2 0 0 = true)
  · exact (rfl : block g2109 3 0 0 = true)
  · exact g2109B4
  · exact g2109B5
  · exact g2109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109G : graphValid g2109 (boundsBefore K2107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2109 : Lower true (varsX 2109) (graphGoal 2109) 7 := lower_forest (g:=g2109) (i:=0) (hints:=35734262382596) (before_sound K2107 V2107) g2109G g2109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2109 := extendKnown K2107 7 [(2109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2109 : Known true K2109 := extend_ok (m:=2109) V2107 low2109 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((bitLimbs [0xde2fffecdfefb7fe24,0xfd0134df79125f96f973]),(bitLimbs [0xa06242024e9910024,0x6100748d00121f84f140])),((bitLimbs [0xf5503c3b283fcee9db,0xc7fedeaad4fda56597ab]),(bitLimbs [0x7018380b000fc7495a,0x8426d28ad4f42520162b])),((bitLimbs [0x2ff76a2be05e6c1477,0x90d689a536f5605be5de]),(bitLimbs [0xf72ca28e016780415,0xf09028243665405be1d6])),((bitLimbs [0x9ba2cff09f04f9c7d8,0x2fffdf7e8f8ddb39423c]),(bitLimbs [0x81a0c1d14a1028c140,0x65d03720b89c011023c])),((bitLimbs [0x31cfad16d8cbe79bed,0x96abe3c1f34fc3ea3e44]),(bitLimbs [0x50dd8c46d808459a8a,0x929bc1c1f34dc3ea1c00])),((bitLimbs [0xe3dc53df34f95ef91f,0xde42373243e2b4ee5dd5]),(bitLimbs [0xe9280351325016b003,0x4c4f27324182b06e4dd5])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,16,2095,0,9),(0,32,2079,0,9),(0,4,2107,0,8),(2,0,61,0,8),(32,0,31,0,8),(0,2,2109,0,7),(1,0,62,0,7),(4,0,59,0,7),(8,0,55,0,7),(16,0,47,0,7),(0,8,2103,0,6),(2,16,45,0,6),(4,32,27,0,6),(0,18,4141,0,5),(0,20,4139,0,5),(0,36,4123,0,5),(0,40,2071,0,5),(0,48,6159,0,5),(1,4,58,0,5),(1,8,54,0,5),(1,16,46,0,5),(1,32,30,0,5),(2,4,57,0,5),(2,32,29,0,5),(8,16,2087,0,5),(16,2,2093,0,5),(16,4,2091,0,5),(24,0,39,0,5),(32,2,2077,0,5),(32,4,2075,0,5),(48,0,15,0,5),(1,2,60,0,4),(1,20,42,0,4),(1,40,22,0,4),(1,48,14,0,4),(2,36,25,0,4),(4,2,2105,0,4),(4,16,43,0,4),(8,2,37,0,4),(8,4,51,0,4),(8,18,37,0,4),(8,32,23,0,4),(16,32,2063,0,4),(24,2,37,0,4),(32,16,4111,0,4),(48,2,13,0,4),(48,4,11,0,4)]
def g63A : List (List Nat) := [[]]
def g63D5 := limbs80 #[#[0x10d60085766074310c21,0x1019710d610844064743,0x18d304811010d615c021,0x6992d10c825c440c8084,0x438c391d02c2dc27a2d9,0x2d4d5d0074bc4d]]
def g63D6 := limbs80 #[#[0x58c41480209cd6310420,0xa0c41480206004148020,0xcc740480200c74048020,0x58c41c80205944358420,0x10f41c8020a0c41c8020,0xd8c43d042059443d0420,0x6017610c219d17010c21,0xe017610c21a117610c21,0x6074310c215db4310c21,0xa00435802161c4358021,0xa005358021d0c4358021,0xdcc73580215cc7358021,0xdcd73580219cd7358021,0x1d0214c0306074358021,0xdd8214c030600214c030,0xa08744c030a08714c030,0xddb214c0301c7214c030,0x213764c030207764c030,0xa0854580316002198030,0x5cc72580315c87258031,0x1c93158031dcc7258031,0x5ce72580315c93158031,0xa0b5358031a035358031,0x5d8430844058c4308440,0x61c43084406004308440,0x10d700844010d6108440,0x10c72584405857008440,0x99271580436066458043,0x9cd62104501c96258443,0xe1d63d0851a0f4258051,0x61c630811061a73d0851,0x18d200811010d2008110],#[0x60043481102097010d10,0x18d30481101893048110,0x21130481102093048110,0x18b304811018a3148110,0x1d0724c11018c724c110,0x18a31c811018d30c8110,0x5c5300c120209300c120,0x6003110120209700c520,0x61c63145206027310520,0x600414c1201c8314c120,0x1d0724c12018c514c120,0x1cb414c1201cb304c120,0x6044208530604548c920,0x191700853061c6408530,0x991700853020d7008530,0xe0d7008530d0d7008530,0x6002110130a126408530,0x600218c1302097119130,0x21130c8220087308c130,0x20d700863060331c8220,0x60d700863058d7008630,0xa0a61cc230d0d7008630,0x9897110310989300c310,0x98d304831010e6210310,0x9d2624c3106074348310,0xdd8724c710600424c710,0x19170087302097110320,0x2097098f41d0d7008740,0x1cd6348750a097098f41,0x32de57cad8fb1be1fc2f,0xde97d2da3f46e5f4bb97,0xbd576add5b6af53ea774],#[0xe1fb5b6aed3d9db375f2,0x7cb78fb1be2fc5b8af13,0x3da6b47e7ccf59e33b66,0xae759eaed5baaf556a7d,0xf8df1ae2fc2f756bcd75,0xe73ae73cd79772de57c9,0x5db29f5d88f8bee5da79,0x4661a9d61d72620a6ad,0x983a58d9ac21218c65d9,0xa5c993a52e2c2125205d,0x1ca55e8f641c20a10789,0x210566059ca14b391d61,0xe40844988501e41e2e21,0x98a554be2450a0662d8d,0x2a1664752961853ba5aa,0xdd8fa5dce0b358c10666,0x18255522e1f6016428ba,0x8440dd8230990e21dd8f,0x647b3019318b254b0865,0xb2a1a331a0c0bca11a12,0x3c99250b1ca14ba85c70,0x641d8325f80da52e8e64,0x225db5a0213c3add8d81,0xd1b661abc10da09a5d6,0x25749ca1c313a52eaf9d,0x371d61c0dd8293253491,0x91271ca9ba192e0ea600,0xd871ba1d243f64b98ea4,0x26619b118e2285c67b4,0xe1a0a10b11a57396646f,0x642d9b644a41e4740ea5,0xa0a1a48165dd0da4073d],#[0x81baa491ae6431391d63,0x584e206598ba5cf70865,0xd2513a41d0f096412b4,0x313edd900525db335db3,0xa15409a5ca9465f22ea4,0x82e418a025093321a21c,0x3a9ca1538964169b645b,0x6584c35cdf91a56e1064,0xb71d77a0213bbfa4b99a,0xba25cd213a533a06617,0x255320a106ba192fa0a1,0x8325f901e428ab994e17,0x4c0da538b2a1a5b9196b,0x250e9565df2061ca1c21,0x23a1692760a03919673a,0x159264462c210c9b6419,0x25ac8065f01e24ad0d25,0x31a0c38a25532a196607,0x683021a29b641ab52122,0x10f6c210fa0f641c9c19,0x38196b36196a8825ac3c,0x849864b7cb0f12100000,0xe4605034d0c4da87704,0x200c0dc0fa082d20187,0x2f924d043f043c08c08]]
def g63H6 := limbs80 #[#[0x130280000001ef0]]
private def groupPage0 := limbs80 #[#[0x10c105c043041700c810,0x4043440100c91004176,0x58d1004130440101c910,0x4c01098d200416348010,0x4073c80109ca3204074,0x58f5204163d08101d330,0xc42058c31080540c420,0x82730c4209883108170,0x5c0410816310420d8c31,0x1042098c410826210420,0x817010c205944308273,0x994430817610c205c443,0x10c209d8430827110c20,0x8031480205d85108363,0x14520080434802010520,0x48020cc5200833048020,0x835148020d052008340,0x98930080744c02010530,0x584201cd610804358420,0x807158c2058d6108074,0x98a310837158c201d163,0x9842058e610804398420,0x8041c80209d26108273,0xd072008331c802010f20,0xcc0201d33008041cc020,0x8163cc4201533108341,0x98f3108176cc42059731,0xcc4209d73108274cc420,0x8341d0020cc74008363,0x5974108163d042010f41,0xd042098f4108170d0420,0x8163d44205c74308273],#[0x5d8430857010c219d353,0x15021d0c430867010c21,0x84535802110d6008570,0x1d160084735802115160,0x580215cd600847558021,0x8675580219d16008673,0xdcd600875358021d0d60,0xd0c2110e600845458c21,0xc274d4c215db5308576,0x588210c1610843019021,0x84305d8210c17008430,0xc17014430584510c353,0x85300c170148305d851,0x4c030145300c0414c030,0xc0724c0301c5300c052,0x589300c1614c0301d130,0x4c030985300c2214c030,0xc3404c030c85300c262,0xd49300c3514c030d0530,0x4c030dc9300c3714c030,0xc0724c430dd9300c374,0x1d5610c0725843014961,0x88430d4d610c23258430,0xc1618c430086300c353,0x5c3210c3519803008660,0xd4030147300c021cc030,0xc170d4430c87500c021,0x5d8520c570108319cb51,0x4c4319c8540c57015031,0xc7524c4311c9310c452,0x1c1320c7764c431dc931,0x58031109600c7704c831],#[0xc47258031151600c452,0x4c5600c475580311d160,0x580315c9600c53258031,0xc674580319c9600c632,0xd49600c742580319d560,0xd4c315da320c75358031,0xc970190329cb530c576,0x1c5600c85458032dd932,0x580325c5600c96158032,0xc96198032d4d600ca71,0x5842110043084409c660,0xc4405d8211017008440,0x1017010c4058c4310170,0xc96110170148405c051,0x58440149611004358440,0x10232584404c96110072,0x9cb3110170cc4400ca61,0xd00405874010021d0040,0x106325804198c5210563,0x5da321075358041d4960,0xd48415cf5210570d4841,0x10871580429c35210663,0x1c56010f73580421cd60,0x580435856010c7258043,0x10e61580435c56010d62,0x9956010e645804398960,0x580439c96010e7158043,0x10c7258443dc56010f53,0x5866010f705844358961,0x980439966010e6198043,0x141700845058c2114271,0x5c03114273084505d821],#[0x1045058c411416210450,0x14273104509884114170,0x58d2114073484505c043,0x58c5010d621426248450,0x1416388450dc56314071,0x58a31142738845098a21,0xc845058f211404398850,0x14170cc45058f3114273,0x58f4114162d045058f32,0xd08509cf4114170d0450,0x14673d085098b4214163,0x58c42145700c8514c832,0x10c519cc421457010851,0x14442580510c96014570,0xcc960146325805110d60,0x980515da321474258051,0x14563cc85110e6014432,0x9cf4214570d085158f42,0x580525c0431496310c52,0x14b43580521d16014843,0x10e6014b7058452dcd60,0x580531c56014d7099052,0x15072580541c56015371,0x18c204404308110dc960,0x81105cc204412008110,0x440520c1109c82044263,0x9c832441700c91018830,0x141109c8434417010d10,0x441721411018c5044032,0x5cc5244170149109c850,0x1891018c624404318910,0x44043481101946344363],#[0x18920440544811014d20,0x481104c1204406348110,0x44231481108c12044131,0xcc12044263481108c920,0x48110d4d204434348110,0x440524c110dcd2044363,0x1c530440634c11018930,0x4c1101d130440724c110,0x443624c110d493044262,0xdc930443714c110d8d30,0x881101d932440654c910,0x440648811018e2044043,0x98e20441308811019620,0x8c11014a304427688110,0x442628c1101963044062,0x18a31442768c11099230,0x98d105c232440638c910,0x44062c811010f2044170,0x4cb2044130c811018f20,0xc81105cf2044163c8110,0x44263c81108cb2044231,0xd8b2044353c8110d0f20,0xcc91014b3044373c8110,0x44032d41105c34244170,0x18f5244332d41105cf50,0xd4d105c35344170d4910,0x480510c12018f6244272,0x9cc30481710c1204c030,0xc5204c431483510c120,0x482730c5208c83148170,0x5c4404803110120d8c31,0x101209cc404817310120],#[0x48173105205c04148331,0x5c04348273105208c841,0x141209c8434817110d20,0x48331141209c85048063,0x5cc51481701452018c51,0x14d209cc514823214520,0x48273151205c45448171,0x10d30480414c1200c530,0x4c12015130480514c120,0x480724c1201c53048063,0xcc130480764c1201d130,0x4c120d0530483314c120,0x483634c120d853048351,0x10d31483744c120dc530,0x4c5201d131480544c520,0x483704c520cc53148076,0x5ce30480518c1200c630,0x8c120cc630483308c120,0x481708c52010e3148351,0x10e32483318c5205ce31,0x8c9209c632480548c920,0x48041cc1209da3248274,0xd073048171cc12014730,0xcc5201533148351cc120,0x48272cc5209c33148170,0x9db3148275cc5209d331,0xd0120d4f3148343cc520,0x48272d01204c74048031,0x5cf4148170d0520cc740,0xd05209cf4148232d0520,0x48171d0d205c34348363,0x9cf5048173d41205c750],#[0xd8d205c75348331d4120,0x48674d8d209c76348054,0x5c0544857014d215c043,0xd812114f6048443d8121,0x48753d81211d76048473,0x10c214c04208530dcf60,0x8530188214c05408530,0x4c264085305c0214c064,0xd0c214c342085309c821,0x8530d84214c35308530,0x4c0620c530148314c362,0x84404c1710c930d8831,0x10530188414c17110130,0x4c170109305c0414c132,0xd4c424c273109305c442,0x10d305c4434c06410d30,0x4c04114130084504c272,0xc8514c34114130c8450,0x1453010c514c04214530,0x4c34214530cc8514c062,0x188524c04314930d8451,0x149305c0524c06414930,0x4c171151309d0524c171,0x10c614c042185300c861,0x18530188614c05218530,0x4c35218530d08614c332,0x150624c04318930d8c61,0x189305c0624c06418930,0x4c170191309c4624c171,0xdc0644c272191305c464,0x48530d4d214c37219130,0x4c0704c530189314c370],#[0x10e214c3704c5301c931,0x8853018a214c05488530,0x4c0218c130d4e214c170,0x106304c0328c1300c630,0x8c130186304c0518c130,0x4c2728c130192304c062,0xcc6304c3308c130c8630,0x985305c6324c3418c130,0x4c074c8530d0a614c042,0x887304c021cc1305c321,0xcc53018b314c052cc530,0x4c276cc5309cb314c064,0xd93314c362cc530d4b31,0xcc9305c7324c064cc930,0x4c021d0130d93324c276,0x18b404c061d013014b40,0xd01309cb404c171d0130,0x4c043d0530d07404c273,0x98b414c132d053018b41,0xd0530d0b414c272d0530,0x4c065d0930193424c362,0x997424c171d09305c342,0xd0d30d4f424c276d0930,0x4c041d4130087504c171,0x187514c342d413048750,0xd45305c3514c062d4530,0x4c062d4930d87514c272,0x18b614c052d85305c753,0xd85309cb614c132d8530,0x4c5700c931d8b614c352,0x9c8434c57010d315c042,0x151315c0544c57014931],#[0x4c443181310c8604c672,0x10c624c6721813118860,0xd81315c3324c57018931,0x4c443d813110b604c432,0x1cb604c462d813115360,0xd8131ccb604c474d8131,0x4cb72d8131d8b604c742,0x5c0544c97110d325c043,0xd0d3210c604c97115132,0x4c843d81325c7534c971,0x5c03284071d813215360,0x482105c0528417010e10,0x842634821058d2084130,0x58e62841325861098930,0xc821010f1084032c4210,0x882730c6205c03188163,0x5c4438817010e209cc41,0x982201d163880414c220,0x88031c82201066088031,0x4c32088043c822010720,0xc8220d032088331c8220,0x88176cc6201533188351,0xc74088275cc6209d331,0xd0e209cf4188331d0220,0x8857010e215c75388171,0x10d6088570152215c053,0x58221151608845358221,0x8c0430863010e6088753,0x58c218c0540863014c21,0x86305d8218c17008630,0x8c35308630d0c218c265,0x5c0318c1620c63014831],#[0xc630988318c2320c630,0x8c17010630148418c353,0xd4c428c353106308c841,0x146300c8518c17610e30,0x8c1761463010c518c042,0x10c528c34214630cc851,0x14a305c4528c17014a30,0x8c3534863058d218c274,0x1c9618c0525863098931,0x58a30589618c13258630,0x8c1638863014e218c163,0x5c6328c0328c630d4e21,0x986300ca618c2748ca30,0x8c265c863058e618c043,0x147308c021cc230d4f21,0xcc230987308c162cc230,0x8c162cc63014b318c262,0x9cb318c262cc6305c331,0xd06305c3418c043d0630,0x8c342d063098b418c232,0xd4f428c163d0a30d4f41,0xd4630087508c171d0e30,0x8c171d4e309cb518c262,0x5c0428c5700ca319d353,0xcc6319c8548c67210e31,0x8c97110e325c0438c970,0x151608c843582325c454,0x582325c5608c96158232,0x8c843982329d1608ca64,0x992618ca649823258660,0x83105c6648c97099232,0xc4263083105cc20c4043],#[0x5c430c41300c3109c820,0xcb101d032c42620c310,0xc41760cb105c032c4132,0x10c40c43530cb109c832,0x10f1098840c417110310,0xc417210f105c443c4170,0xd0c43c427210f105d843,0x143105c850c403214310,0xc42721431098c50c4176,0x4c120c40734831010d20,0x4831058d20c413148310,0xc42634831098920c4232,0xc930c434348310cc120,0x4c3101c930c40434c310,0xc43324c3109d130c4074,0xdc930c43714c310d0930,0x4c71010d31c40424c710,0xc43324c7101c931c4054,0x15163c40434cb10d0931,0x58f101d163c407258f10,0xc42638831010e20c4372,0xcc230c42628c31010e30,0x8cb1015232c40438cb10,0xc42748cb109ca32c4176,0x10f20c434398b1010e62,0xc83104cb20c4130c8310,0xc4353c8310d0f20c4232,0x98b30c4074cc310dcf20,0xd03104c740c4163ccb10,0xc4272d031098b40c4232,0x5c342c4163d0b10d0f40,0xd43109cb43c4273d0b10],#[0xc4272d4f105db53c4032,0x4c030c80510c3209d353,0xc72015031c81710c320,0xc81700c7204c831c8131,0xd4c31c82640c7208c831,0x103200c440c83630c720,0xc8170107205c440c8043,0x5c043c816310f209cc41,0x10f2099043c817110f20,0xc833114320d0c43c8271,0x10530c80314c32098c51,0x4c3201c530c80514c320,0xc81614c3201d130c8072,0xdc530c83314c32098d30,0x4c72010d31c83724c320,0xc80434cb201d131c8054,0xc630c805458f2015132,0x8c72010e31c80518c320,0xc8054cc72098e31c8054,0x58f31c8132cc7201d331,0xcc7208cb31c8170cc720,0xc8274cc7209cb31c8270,0xd8f31c8353cc7209d731,0xd0320d0740c8131d0320,0xc8232d072010f41c8343,0x58f51c8171d0f209cf41,0xd4f209d351c8273d4720,0xc8570193215c043c8674,0x15160c84535832110d60,0x98f2110e60c875358321,0xcc1700873019021cc170,0xc8450cc0411433008450],#[0x193305c052cc34114330,0xcc272d073014b40cc170,0x88750cc121d433008750,0xd4730d0b50cc321d4330,0xcc67010b315c042cc672,0x9c052cc57314b315c052,0x153319c054cc57015331,0xcc442583315c064cc672,0x1c960cc4545833114960,0x583314c960cc47558331,0xcc660583318c960cc562,0x9c960cc6655833198960,0x8cb31d4d60cc74258331,0xcc572983319c232cc570,0x9ca60cc6659833198a60,0x98b3199662cc57098b31,0xcc670d0b315c342cc670,0xd4d60cc970153329cb53,0xc740d0c21d017008740,0xd03704c7401c931d0170,0x5cf41d0272cc7405c331,0x10f415c032d0632d0740,0xd057314b415c052d0570,0x5c053d067014b4198c52,0x5834114960d043258341,0xd04438cb414c960d0453,0x5c263d06708cb415c232,0xd4b419cf42d0570d0b41,0xd097014f4298f52d0573,0x5c263d0b535834214d60,0x87505c021d416308750,0xd416310f509cc41d4273],#[0xdc121d4163487501cd21,0x887505c221d437158f50,0xd4273c87505c321d4273,0x9cf41d4163ccb5058f31,0xcb519cf42d4163d0b50,0xd4432583515c043d4570,0x10e60d45708cb5110d60,0x983525c043d4970d0b51,0xd4d72583535c560d4c43,0x9be3f8bd70993539d160,0xaae9fa3e7f9fa7d9ee77,0xb76bfafabdaeeb7abead,0xbdef6bbeedbaae7b7ede,0xc6f0fbfafdbf2fbbeaf9,0xceb37cbf2ecb72bc9f1f,0xd7f5dd6f4fcff3ecf73b,0xdeb79ddf76dbf6ddaf67,0xe779be5f8fdfb7ddf37b,0xed7b3ebfadeafa7e7f9e,0xefbbdef3bbeebb9edfb6,0xfdbf5fd3f3fbbebf9fcf,0xea55d210822ffcfebf9,0x49353eec22956ec0a91,0x822d3eec1f524e636851,0x22cb108b7d26ec229390,0x9938c895126ec1f52708,0x9a886eed30e81f920e85,0xc90469cbb02e9518ca68,0x4ec9c9a0e871140c8949,0xec8a158e43a8130f0c54,0x6d814ae66c8730c0f544,0x2c00f0ecd8bb02165a88],#[0x6a74c6500370ed588700,0xc4d0a1791cea87140c89,0x290edc00f0c4155ac43f,0x90a18518ca67c090c774,0x81844d0aae558e43d44,0xa7ec85002e0090c6ec61,0x166c284d40c884d18c,0xd47b002340b0e52d44c8,0xc090c8140b0d0b0230ee,0x90c8f061083059ae6fa,0xec74c81002c06508178,0xe81ed18ca6a4090c8196,0x6f0518ca6bd40ec73998,0x6d485004c84d0aaf0ab0,0x80730c0a463023b80b0e,0xdd0e471d5cc43fce300b,0x2d0ee100f0cbb544eca2,0x8ea0251cca0480b0eb04,0xecca564ec5fd18ca6a11,0xcaa07b003462ac63196a,0x4c8490a304290e568090,0x959ae6ee86b0cc980d0e,0x518eadc4730c0980d0f1,0x83004c8090c81c730042,0x8ca6b962c21c0090caa4,0xc14c7b022d8490a2c51,0x27d40ec7159ae6d7c0f,0x16d40ec5a4090c6dc0f0,0xe8130e3180d0efd48500,0xc630c1355ce6400090c6,0x18ea58942ec318090caf,0x8eab300b0cdb88300ac9],#[0xc651918eadd140c89b51,0xc06962c2320090c7f14e,0xe814ce64315cec7840b0,0xbd42ec16544c81d91cea,0xb0c4100f0cd140b0c4,0x388634a0cc406d1cca1c,0x2ecb7c670093518ea562,0xc668865088354ce64067,0xeb39410911d5cc6da54e,0x3547b02195d2e6500090,0x30730ce680d0e8307b00,0x44d0a2b00b0c4180f0d1,0x4ce64680f0d0b80b0e08,0xf0e4b518ca7a942ed0c5,0xe089d46468966ece0c0,0x82c51eec06d58c65300b,0xe2944ec9e11aec06c610,0xfce104674090c8944d0a,0x5490222c0b0cea00b0e4,0x44c81c14ce60591aca0d,0xc8a65450815c65082fd,0xe715a4ac60a518ea0214,0x657540c88e54eec1ed48,0x7711aec07d66c268a48c,0x50850017118ca75118ca,0xe388631c730c0f95ac44,0x70c6500090ca947b0033,0xb0c10562c2328710c61e,0xc27144c8cf8730cb800,0x46acc108e6222ca0e00f,0x40970ec5a10300551dc6,0x5e22ca0c08b0036d72c6]]
private def groupPage1 := limbs80 #[#[0x220ca7248d042ad72c60,0x8d042e1b0e8f25b0e85a,0x4ec9c48b0c0c1f104520,0xc488e60c6564c1085657,0xe543b0e4f9f0a488d70,0x606430d0e03b0c1208b0,0xda7b04e54d5041ed74c8,0x9770d1a660c670d770ec,0x3001dd71031b88d0e2d,0xeadd48f0015cfb00e01,0x2920c50493d77043d99,0xca303b0ecac8d0e3ca45,0x13577064d9770cfcd74e,0x6d74c404977063f646c6,0xdd9046d88b0119646861,0x74ec9d974c884d70e82c,0x2ecbd5c6e65503b0e4fd,0xcc8a60a81103b004857,0x42cc3b0114a7ec4a1c8b,0x179eae269a7ec663c8d0,0x7972e62fdd904bb2230a,0x10300672d8c46283f008,0xb0c896974ea19e78c491,0x4ea18974c70ed92ca121,0xe618574ecf8974c4bfd7,0x8195c10684ea5041f574,0x2d2e682b7c8b004ca44e,0x49c706ff1d904bb48d04,0x172ec16171041d48b0cf,0x66e616c890e16cc300cc,0xb00abd72c6f0172ec002,0x47d57304c3240e85948],#[0xe0c266e6188c3010e0ed,0x478d3069608d0e30c3d0,0x9972ecc348b01059770c,0x9dce47ce88c45b972ecf,0x8b0c8408d010a48d0425,0x4c914572ecc3ddce49d8,0xe82b176ecde4c3003197,0x909c3b0ecde44c83a170,0xc5642c6fac3b0046574c,0x208b0ce4574e818570e8,0x624ca0e174ec7643b00a,0xf508b4d70ea39ab8c657,0xd0e59572ec3ea4108139,0xd003d0ef1e78c663c3,0xabe4ff02e6170ea19c3b,0xde0ed0455176ecf4d710,0x3d72ecd9220ca6fcfb02,0x176e442c8d0c8bd710b1,0x770511deee2701030059,0xc8a04c300fae8ec4a6d,0xecc9174c9199e90a679b,0x470c390edbc3b0e8e172,0xfe88d0e2dee0c6501d8e,0x927ac4a1572ecd79710a,0x1770c4c48d0c6a976e63,0xe90c61d7106ac244e892,0xf004b4890818572c6cc4,0xeca148b0cf6574ec7a48,0xce5d76e64ec8b0107974,0x8fd70c884e40c8a148b0,0x4df10ab1ed6c65648d0c,0xc8d0e179eec284db0c88],#[0x8b0c2497306be640c891,0x70d0fe22ec06cd5068f8,0xc888d0300651b6e8f3d7,0xc75664c6f21770e059b0,0xd11730e16e60c658574e,0x95750b13c8b011383f00,0xe7a6430a450c7143b0e9,0x7104c2170ea18a8ae22f,0xd0c7667ce4a8c8d0c8cd,0x3fa7b0417971042e88,0xcb4c8b00495770e45c3b,0x49ced047c6c8e220d770,0xbe9300ad9f10a5188b0e,0x28ac601688e272d750c6,0x71029e88d0c7a0390c8f,0x2ec15974c43588b0f081,0x34974ec7b48b0cdf57,0xcc2972ece4571051ba8b,0x84d750511d010088972e,0x7976ec39c8d0eacd750c,0x1b4e81583b00e508d081,0x7ec655c8d0619174c61c,0x86a148b0cf6a46c89c6,0xe654970e80cc3b0035e4,0x67003f070edf4ec5da62,0x81750ac21770cb1e60c,0x172ecc6c3b0e8ac8b01,0x170ea2ce270a1848f003,0x710271a8b0217d72ec8c,0x50e16cd5069610300c19,0xc659678c8964ed0c5757,0x80443b001b1030070266],#[0x3e174c71448b0ce1974e,0xc48b001948d0c9ad74e4,0xc8b02d1975022f1710a5,0x3b00eb1710e1383b00cb,0x300ab4ed060ad72ecbd8,0xec070ed080f970c8aba9,0x74ae6620a88f02c6972,0x7c172c43da66c68fd730,0xa174ec841710500974ec,0x171001ad750caf574c90,0xd8c4968fb02df67ce42b,0x4ca8983b00fc977049d1,0xca0c8b002f90300c95c,0x64f172c715c3b00ba4c5,0x78c390ca3a66ec21576e,0x59b087115b5091167d08,0xd506a4d72eccdced0c8,0x72ec10278e42a970ea2b,0xec462974ec7b83b0e9c1,0xc656570ea3083b0e87ed,0x2ac8b0cea88d0819ad0,0xaae9025648b005788b0,0x88eb02f527886966e062,0xd770e4b48d04ae1770d1,0x8b01109710f15ac8c659,0x300c9972c63f278c862c,0xf0174ec791c4e69f90,0xc7468ec48d5f506be03f,0x71710ca948d042b970e,0x108b011008b0e2c88d05,0xdf086be08b00fe0c30f1,0x3b00fc5030052889043d],#[0x904ed08d0c58176e6490,0x870a03b0ebf27ce43a1d,0x3009770e0388b002dd76,0xfe83b0117266ec1dd710,0x3970e894e7e8655d750a,0x5f508be103009f28b062,0x8d0817174c63208b02b1,0x70074a78c655c8b00ae8,0x22f1b4eca2c8908d357,0x6e608b0cde27cc42fd71,0xd99730d18d710ae4a64c,0x1297001867d0278c3b00,0x972ec26d74cb0a278c86,0x76e43ae88c459de8e4df,0xf010f28f023ed72ecbed,0xec30974c63f08b0c1dc3,0x5aa62e6545d8c484d76,0x134d50899d750a7488b0,0x9640c892971063f69aca,0xd710400a66c672660c65,0x74ec0803b0ebf574c8d4,0xea57c8b01135710a9e9,0xeb67b0c0f5c2e66d19,0x6be08d050788f0e1943b,0x94fb02db5c2e64fdf6a,0xc9730ee548908d267ac6,0x48d0617d74ec5ec8d0c5,0x8f00185750ca903b010b,0xd045848b0016c8b0e198,0xea179710c81972e6178e,0x91183b010cd74ec12174,0xf0970ea83572c7165b4e],#[0xc3b0eeb974ec7a974ec,0x571090a10300c148b0e3,0x8d0e2ac8d0e2c83b00fb,0xf041848b00fed74c4328,0x68c176ec3c08b0e1967,0x8ff03b011688b002d8d5,0x805c706cfc3b0102970c,0xb5b6e85a08b0e2d83f00,0xc3d0ef183f00a39b6c89,0x750a9d1dce47ac8d0c73,0xb0ef60ef0cf788f0c0e1,0xf910300b9d770cb203,0x618c8b00fdc3b002ec3b,0x7203f00af970c85a08d0,0x857508be5c2e70188d0c,0x5770cb5976c6ef170e81,0x76ec1388d0c9f5770d0e,0xae26703b008aa60c6591,0xc99572eccba64e6179e,0x10f5c2e70148d0e1708d,0xf9c8d0c7a48d0e8308b0,0xd1ece4d8e8ae42bd74e8,0x489043a4ef0cecc3b0e6,0x70c8ac172ec081c1068e,0x10511c8b0018a60e616d,0xe43b0ed06094d5068ad7,0xc814c300135c106ff170,0x5608b010508b0c0e1750,0xd2450498c8b0c144a50a,0xd03009bdb6c89cd71049,0x770015c8f0c075730511,0xb010748d0505a66c65b1],#[0x80e68ac21dddce8f8c8,0xca4688e23a5770d04089,0x5cd77002ea60c661974e,0x2cc30ccc1b4eca103b0e,0x48d04ad172c63208b02d,0x70ec73d70e442a40c89c,0x82b7c3f008a48d0e49d,0xfa03b009cd72ecbeae,0x67003b0044970ea17907,0x2cd03006448b0cc2cd50,0x443b0118570c86067ee4,0x5b4eca25f108b4d72c71,0xf70684d7306fd278c456,0xf06bb90300cdc8d0e2a5,0x45f9710c81d7102c203,0x2397704c3170ecf4d71,0x9310300ce572c6e928b0,0xb48b0cc59d90415a4504,0x8b00fd8fb02ddd770cb,0x710caa574e8112d8c457,0x8e43aa22ca0c43b01011,0x4ad48d0c60c8d064a27,0xab1c3b0e97240c88708d,0x188eb0277d7503009f50,0x9d750313c8b010a48d06,0xe22ca13972ecf0174ec8,0x72ec10c8d064cc8f0047,0x4eca2ae0ca5008d0c90d,0xeae88b0ce708b0cc397,0x41d68b06349710ca988d,0xe7a78e449db0c8a35730,0xba7ae43a1f50684c3b00],#[0x174ea18646c6fa503009,0x8d0c76c3b0e861df04ed,0x5041d576e707df08684c,0x2519750ab9103006997,0x43c662c612dd904efde9,0x884ff02dbe66e61867ee,0xd83f011288d0819e40c8,0x48b0618dd8e47248d080,0x60ca6008b0f086e662b8,0x50a51974ea2cd72ecb8e,0x2fcd710608d71085e1f,0xcf92a8860fd7508119e9,0x5067d0c7e03f00d1574e,0x9d73020788b0cf7174c8,0x9750aa4241049328cc45,0x74ec8c172eccb03b0066,0xa642fd70eb07cc50ca11,0xc7d574ec8e172ec1227,0x8925c2e65cd770e4308d,0x9d974ec769910aac240c,0xf576e64f570c653a46c8,0x43f00fba60c65b03b0ef,0x3b0e9dae062b848d042b,0x50884d74c6db08b00acc,0x15cfb02df278c4889f,0xc9c10300e897704d9573,0x50224ca1388d0508574e,0xfc8b0cec57086ac2e0c8,0x88b0c1c83b004be40c89,0xfb02bec3b0e86d72e6e3,0x2c64628ee23097306324,0x37d0300795f6a684d7],#[0x6131f106be172ecb948f,0x73574ea2b1b504dea42c,0x883d0edf08d0ca59b6e8,0x3b0ebd08b0cdb48b0ce,0x7504c3176e630972ed09,0xb0e2a574ec4f9710ac21,0xeca3c3d0ee197508c308,0x2905770c4148b0049d74,0x8d974ea309b4e8f6e8b0,0x20a10acb03d0ef3974ec,0x90300c75c0e6dbe430e9,0x72ecf903b00d0572ecd9,0x1029303b010d970ea185,0x2a5f108be1e9025224,0xc31660e60cd70e439c8b,0xd89dae4f80a10abf972e,0x5f6866888b0cdf1eae2,0x88d0e825dce4f8172ecc,0xeae2d6d70ea2fc8b0f05,0x865003b00f748f0e2c1,0xec12666ec1e1f0a6be2e,0x52664c8112a0869a172,0x3f678c88de7ee45943b0,0x3d0c85574e81517506,0x4ed047428b0219696ec2,0x62c6df574c70f9b0c89b,0xf04d0ae8e4019eec29b6,0xc88a88b0e2dc8b02809e,0x608d730cff278e42ddb0,0x84974ec5cdf508689750,0x4573063f48d0e72e4300,0x8b0e171b0c893a78c88],#[0x3b0ec2d03007048d0818,0x50684262ecc9972ecb98,0x90c0890ef31eae287cd,0x8f2a430292266ec20db1,0x5a1710cafcfd0c629d8e,0xfe89041f9f504b2260c6,0x5710c81666c660cfb028,0x8b06181750cac48b0105,0x3071208908d2266c679c,0xe44e9750a1c572ecf95b,0x14a250a2b1df0415976,0xe5170ec70e450a9203b0,0x2d70c65348d0c8d0fb02,0x1770d18db0c89cdb300f,0x4102922a0e81dc3f006c,0xb0012278ca55e4708186,0xc6fac3f008e88b0e4943,0xe8b5dec484d0300a4646,0x18174c905d0300a4c3b0,0x6266c66fa79041848d06,0x9750a9e88d0c961c6e65,0x7104eae66e619622ca0c,0x6e639e93001a688e2301,0xc1c176ec2fd76e61897,0xe16d770cc4170e8e2177,0xbe4e904dbe20ca7648d0,0xfa250a17977002e5750a,0x574ec7588b0cc3d710a5,0x8b0112e60c6581730e1a,0xb0cbd1f5045217504608,0xc66d83d0edb48f002c48,0x4d59d90468976e62cd70],#[0x749f50abe08d0c8c294c,0x18a50af5d74c908d710a,0x8d0c6588b008310700a,0x74e819dc706279f104b2,0xb0e16e89024464702921,0xe58572e707d74c43d88,0xc76976ec1dc3b00ea43d,0x5e244c813a20ca7548d0,0x5dc2e702172c60757106,0x5f7050d08b02b1278c85,0x72ec0057502c2177004a,0x10b11df306be1710a7bd,0xb003f00d4594eac057,0x889240c8919eee2dbc3f,0x32572eceddb4e9115b0c,0xe03d0e5617102d417706,0xd72ec1c83b0e909710a5,0x7108ac03b0e95d72ecc0,0x108a4174e88708b02f59,0xc61417102079eae2ee5b,0x64f28ce42bd71043d972,0x134c30c135c10700570e,0x6c8b0110574e80e642c6,0xee0c456db300de88b0ce,0x76e62b260c65ad710015,0xb0e6708b0682e4502931,0xecf8170e80d03b0ed483,0x62803b007e5030058572,0xda170e8add7502a41c70,0x1970e43c1770cd0d72ec,0x88d0c6fdf10684d76ece,0xed046a83b006e640c89d],#[0x6c66ac3b0e7597702078,0xc44508b0c9603b0e83d7,0x63088d0c68174ec7c574,0xa0278c457c8d0c4f972e,0x208b0c06678c4900390c,0xe66c67c975049d27b049,0xe90aec0fb0285e788655,0x2ecc990300c1d71087bd,0xe82cc8b01191c0ca899f,0xabe1b0e8734fb0290d74,0x90574e8cb9f10884df10,0xbe4686e56450883574e8,0x172ecd89d8e472288e42,0x710e41df0a8be17504c2,0x508179750207903008ad,0xecbd1f1050d08b06bc64,0x504c8b00fd5d8e4f2572,0x19730d1a69300add750,0x4d76ecc508b0cddd0701,0x260ca598ed04765f0a68,0x7d0c6b640c892deee2f2,0x10caf48b0e1743b0ee36,0xc6257104c31dce87b17,0xcc988f0f06572c6e9c39,0x179c6e6db5c70684c8b0,0x9ed0c65d9770ee9a62e6,0xd710a9d240e816cd5049,0x8b02b65710a2e570c650,0xc663a22ca05977064e0,0xec743b009b107007ce6,0x8be574e8129750a5c43b,0x17d72ecce974e82b1710],#[0x69d8e46f43f061688b06,0xc3b0e8c5ef02d6c8b0c2,0x3b0eedd74ec7ad77001a,0x4e8c008b061908d0e2e0,0x5588d0e199e8e459dc,0x817c8b0cc8570c864103,0x1548b00bc9750a11a44e,0x4db5040288d081903b01,0x88d0c551770d02c8d045,0x410a9203f003848b0cbd,0xb02ed8c50ca2572ecbf2,0xe63c174c8ff1d8e46f8f,0xc12e43009203b003d176,0x56dde867b2950016c8b0,0xb5750b11d0100a19050c,0x67ec661172e65e9e8c29,0x72ecc2c8b008248b0109,0xce8f85770d0b9dce4a29,0x4ca43b0e8f48d0e175d,0xcc983b00cedd9046bd05,0x1c4fb00e15f686be1030,0x3974e6d6174e8f7d710a,0xa210a184390c89572ecc,0x8b001988b0617503007c,0x8c4a8a40c8a608d0c800,0xcba241081848b02d1e7,0x8a7d750015d72c6b5c8b,0x189730c4c48d0e4d174e,0x7574ec9d620ca7208d08,0x224ca0588b0c10d72ec0,0x4700921710874a7ae42b,0xb003788f0e16d730c47a],#[0xcfcddcea7b08b0e2e08,0xe4a1710ca9172e62cd73,0x48df50a84d72c716c8b0,0x388f003a68f021848b00,0x9f30452174c50d5770e1,0xc300941730d0e6430817,0x108c308d05100a50af18,0xc729770d13175027197,0x7f172c648174ec9608d,0x41c0c660678e43b43f0,0xd576e62fd76e51608b0c,0x8390c8e83b00ea08b020,0x8d0c5bd74ea2fe7ec4a7,0x4ec5e83b002850300cd4,0xc8505b6870c172c6be17,0x625572c6d99030055570,0x4a03b002748b0281172e,0xb88d0e4948b006308b00,0xed0429997508ac1eee45,0x770c1d9f10868974c43f,0xd0c635770cbe172e62b1,0xe47c8d0e196e0c45648,0xc5a17508748d5069a977,0x2ae94c4e3d70ec5c08d0,0x71d8e473646e85948b0e,0x572ec8d174c4cb678c8a,0x3d0e7208d04e1ce90456,0xb008ed03005e57104da8,0x16d0300bf176e61783,0xc5d572ec10a60c65be93,0x9c570e819d72c6c5d74e,0xe5b6c884c8b00bc174e8],#[0x678c6610890e1948b0cc,0xf4cabe1030087cfb028f,0x871183d0e551770e405,0xe4c650300c51f0a884db,0x4d8ddce47a975029ea78,0x6174ec5e48b0e2f9eae,0x288d0e4ca96ec1dc8d05,0xe60e619574ec79d70ea8,0x710ad708d0e4a28ee42b,0x104d948d042d43b0effd,0x17666c67908f010697,0x43cdb5050e97508b908b,0x17640c8970fd04e0576e,0x4a40c88c9f10a84c8d06,0xe88c48d4ed047217108e,0x8ec297172ecc25b0e85b,0xd041783f009e43b0e8da,0x400903009708d04e267,0xc268fb02e5d7106da975,0x4e5b0c894a7cc430972e,0xd177041d48d0c74170e4,0xc3d0edf693001888d0c6,0x74ec5d28b021788b003b,0xb00fc172ecc74c300a25,0x51174e8fbc3b0e8fc3,0xe96d710313e66c655103,0x8976e64a1f70cbe03b0,0x7de8e6015d8e871174c9,0x4fd0c57173049d03b011,0x3d0c58d76c67d88f003d,0x2e701db0863203b00d64,0xc50d1dce4efced04561c],#[0x290a7ac60adb50832174,0x6c08d0e2f977007bcfb0,0xa7ec086974c90a976c6,0xc3b0ef11b1050e972ecf,0x8b02d288b001703d0c8e,0xb00a9d750c68a64c6f24,0xe2eb8890e2c1b1043303,0x811190ea565f2e2675ea,0xccc8d0c90970c6662610,0x9640c4a0c8b003724086,0xa230a2b1030075970ea3,0x770e4688d0c8410300cc,0x30d18974c50c88b0ce41,0x867127b0278dc0e41ed7,0x256576c6a85f68684dd8,0x5ca7d049208d080d2ef0,0xf9770c33a88c4a5d74ec,0x97304608fb02e183b070,0x6f0422c8b0cf443b00a6,0xb0c02c610493485003bd,0xe4a8c0d0e30cf30000c0,0x6178370eebc8300ab15c,0xed562ec31c0f0c4514ae,0xa94ec66bc0d0e19984ea,0xd450cf2d98c88996aecc,0x5ac4460750c5754f0222,0x8c65340d0c8ec0d0efe1,0xcb4d5aec1bd5ae43a15,0x22fe3504921a8e859c0f,0x3dd58c46494ae6f1562e,0xb14eec1e564c4d5c8700,0x1bf0684d4ee661518ca6]]
private def groupPage2 := limbs80 #[#[0xb0cc81430cf2c610493,0xf0ccf11cea4fc7d04244,0xecca00b0c03158c66cc0,0x26742f0e6841b0e9716a,0xca00f0cc41490422de2e,0x7140e85940f0cbe0990a,0xc0f0e44c85010780f0ec,0x4108c2140e839c83004a,0x10030198c8a091cca25d,0x30c0b0e2c95cc44508,0x48d5cc42706b0c1e485,0x7dd66ec29483010bc830,0x9c83003e487003a518ca,0xb0eee0090edc4bb02d,0x1b0e98146ecf2c650885,0xeec1f00f0cbad4ce63ec,0xe80bd6ac6be0370cbe16,0xee81410913c0d0c6e540,0x99228c89796f0cbe00f0,0x6618ca7600b0f08140c8,0x88300174630cface1045,0x1aca0ec090ec600f0e03,0xf0ea80870106a30c8965,0xc6847b029154ae6e300,0xc21483003bc0d0e49479,0x8586b0c26164c4d814ee,0x6940e8b3562c21d0750c,0x918ca7e542e493558c49,0x790e01c0f0cce0090c7f,0x300bcd6eec21c1508dec,0x1087011b140e83c08,0xe4a083001715ee42ccf3],#[0x17483010854eec1e80d0,0x394eec1dc8300d380f0f,0x86b0e6000b0eb68750c8,0x90cb0d44c825e3d0834,0xb0f1388300ae40b0ccf4,0xe665d46ecde86b0654c0,0x1a41f062787f020e54a,0x3f8370e676c0e6018830,0x88300b1184ea68c0b0c,0x4db0283875048201d0ca,0x58c464d5eec0ac0b0e1a,0x90684c1508e740b0e695,0x11ac7b02e580f0d041b,0x1a80d0eae8850049487,0x458090c9a4cb002180f0,0x60cb001e8090e41d5ce6,0x84d0a80c830c24c630c3,0xe2626880f001ad66e230,0xb0ebc82d0ee140b0c155,0x10780d0c51d4ee65600,0xc264830106c0f0e2c083,0xd188eadc11cca2306b0,0x7566ec28c0f0cb244d0a,0x562c233485003c885010,0x6b0cc9c0f0ebdc830049,0x90c53d40e8208e300b70,0xe3708700d201d0c8980,0xb0481010680b0e5400d,0x5f47b0c0116eec224830,0xc639043647b029040b0e,0xd690222d610e1f91aca0,0x750466c0f004a648c662],#[0xb0e4980b0e1980f002e8,0xb188300bbd48c66640,0x3a883002ac0b0e05483,0x6556eec1ed4eec1f0810,0xf8ad08c986108c8c090c,0x91cca0c47f02c8c83002,0x8300d30090c625ab02de,0xcea0454eec1e230c88dc,0x44210ca68630c88451,0x97c0b0d03d450832473,0xad944c82700b0e4accb0,0xec830c1dc8300d288300,0xc830016d1cca2a1c904e,0x770ce654ac64894eec20,0xce6a0da0e8f294ce603c,0xe60cc0f0eef940c89cd9,0xe4696eec200cb0097148,0xa747b02d3d48c65a00f0,0x4160e41f88300aac090c,0x8630ccc0090ef30f300b,0x750c62d1cca070090c79,0x300ab63b0823883011b4,0x784cb001dd6f0cb208,0x4bc944e80dc87003a8e3,0x604830018885002d8750,0x7a2ee87081f0628148c6,0x48301074090c7f59ce8c,0x7d0e24286ec0195ce643,0xeec22164e41cc7b0cb44,0xe61386108b495ae42b14,0xe2e00b0ebcc33009cd4c,0x211aca0c8090ca000b0],#[0x8c2f0eec8950ae1148e6,0x80b0e4dce30009c0b0e4,0x45081c56eec1e40b0e50,0xd0a545690422e3304921,0xec1f63ac2360090e0204,0xcb7883003c942e29314e,0x1c40d0e49ce300b78730,0x180d0eb115ce640d4308,0xd0c58c6108b3de1025,0x58e64200d0eae40f0e4c,0xd0e3795cc51a1e2e2d59,0xe6e11cca0680f002e40,0x37c0d0c6b8850019823,0x23988ea57144e8bdc0f0,0xba28c898a28c89763d08,0x883002a4250ef5162ec1,0x830109a28e8f340f0f17,0x3004dcbb030c5470d0e8,0xea04d98e81f1e1025208,0x822c6d0ef351cea6951c,0x380f0d035190aac1490,0xc00d0c7355ce646c0f0d,0xc7d0423c8701064090c6,0xd0e2d95eec0991eec13,0x300d188300ad118ca7d8,0xc8868090e34e5eec2108,0xf1526ec48655cc50ae30,0xdb230c8a714ec65200f0,0x80d0e82140c89555cc6,0xc0b0e16c090c8ea28e87,0x42ecee9a0e8f400f0cc7,0x1003a40b0c03650e601d],#[0xec1e887003114ae666c8,0xc1dd4eec2196eec1dd6e,0xa2a886fb222ca0646b0,0xeddae4f01dce4f0ae682,0x3b00b56e104565e906e,0xeb02789b0e8f3a20ca79,0xb0ea450301025b0e8f18,0xe8de6a086cca60c66343,0x100ddae4ff83b00ef5b0,0x61903006f9b0e8f3d030,0x2d76ecdfd70e84d4c108,0x3b0ee2e7886dcdb302f,0xd306841c2e68d2e0820a,0x686e8d0300754c108dbc,0xc638db0e872174e60624,0x86f64086d85dce8ed574,0xdfc8b063748b00389b0e,0xf8ed06b750300a51b0e8,0x264c6dbd72ecbf9eee4d,0x3b0c068fb02e6e62c6cb,0x2c64ba910c5643b006b8,0xc6d543b0e5c903005c97,0x887574c638222ca14574,0x8c1f0a4c11030656e40c,0x648d06b6db502f2dc2e6,0xddc64ef0c302faab7085,0x92ca0683b01049030060,0xd06bc5030101ddee4f3d,0x2f5620ca79db086eec8,0xa069f7045210300b60eb,0x14e60c4986ac64fa594c,0xcfd04e09c4e60583b01],#[0x170e8e7cc302f04c302f,0xdae5001b0e870cc30111,0xd060f2b1085650300f1d,0xcdc885010854ae652ce,0x2f48101064630ce9473,0x6c830109559022f55f0,0x294ae64fc0f0e4308501,0x4e3000908700d34e104b,0x4ae65cd4ee616d58e4c6,0xce7140630d0e14ee6189,0xcbc0f0d02d42ec1314,0x645c230e68c0d0e35033,0xd68130f1114ae65454ce,0x9c630ccd22ee8598270e,0xc6d0e599a6e87111cca2,0x4ae6dae28e8598730c09,0x7002980b0ebbdd104689,0x2f54ce67e80b0e4956,0x43c566ec2915eec0b15b,0x2d95d0a2f40b0e4a15ee,0xed590a2f4270e4740b0e,0x461086200b0e49c8300a,0x67042995d022f544e8ab,0x4c8231610a29a68c4865,0x8a4166ec28a10ca7794,0xcb8944e85155ee507d41,0xa55610429865081b4730,0xcd0300944eb02781c2e6,0xed0473c3b00aa8890c7,0x3b00410fb02dd970ec74,0xb0054174c716503004f8,0x2e45e90488103000b48],#[0x49743b00069ece4e84fb,0x8b9b3020ba7ac60fe60c,0xa7ac60f103008b1dae4,0xd28e81fd20e8708d504c,0x270e32d30e8204070e32,0x8c89592ce843d34e8251,0x254570493520e85b53,0xcb5c0b0edac0f0c47883,0x175f8ca71518eab2c0f0,0x440b0c4397cea9ec8500,0x83001980d0edd00f0cc,0xd0c7fc63003400b0e5f,0x8ca7100f0e4540b0e5cc,0xea9e085002c8830082a0,0xc1d80b0c470090cb017c,0x2f80d0c6900d0c6f00f0,0x7485002ae18ca71c8500,0x40b0e5dc830030c0b0cd,0x83002e07104c680b0e25,0xd0e56087003000f0c338,0x18483002c80d0f0800,0xe2e083002d944ec9ec87,0xc680b0d0300f0cba80d0,0x5c090f1580b0cb5118ea,0x40b0ce4d44ec9dc0f001,0x18ca75c83004a885002a,0xf0c1c00d0e16c090ca49,0x2c5f8ca7380b0ee300,0xa7d134e6364090c80487,0x3410cca1f508ca71510c,0x3510ca7b110ca6c45b00,0x920e8730070d0dc410a9],#[0x4ae6d500b0ed5128e820,0xb0cc494ce647c090cb09,0xed311eec1140f0ee980,0x61a00b0efe604ca1100b,0x10c0b0f19d58e50686d0,0x440d0f0840b0cb54090f,0x602ca11c0d0e3c80b0d0,0xb0c0500f0e4b15eec0a,0xf0f1800f0e0451aca0d8,0xca0e80b0f1a8650ca240,0xa1114ce60454ce60e51a,0xa113f0822d34e81ba02c,0x4c5d082381301124650c,0x374000110ca710090ec,0xf0d8e16b4250c3608448,0xeb4cbf170c293849687f,0xc0b81d84000201b3c266,0xa4c891ea7099a5892a3,0x39022686000316bc2b8a,0x839acd2f0a02307e1a25,0xfc28858004cd20c1ef,0x5b36b528c8e9fa6f17a5,0xb9042c068004ab143f6e,0xa392d22f4a7a34809b65,0xa0a21c834004bd17c32f,0xa2b093a0a73198599183,0xc9002f868003d4e2b3ab,0x1318b7aa69a22e7b98e4,0x60e22383400420fcb9cd,0xbb58c2abe992166e97e4,0x18ce1b02a004890dbe8e,0xab06ad254819c26514e4],#[0x60ca1f03800481073b6d,0x6304a82487a9ae601404,0x80da2283200439013c0d,0x5378c12a09aa227417a4,0x50e8270520049b17c22f,0xb36cc9ad09fa2e701684,0xb1142c06e0049512404e,0x30ab7a9494a167399a5,0xd0cc240460042ef9b96d,0x536aca2c094212709764,0x60d02584e0048915c1ef,0x1adea4a56851da629504,0x98a81683a003bedd33ac,0x8060530404487a000e0,0x1703a081210d8002489e,0x2034028020348524f800,0x405b81a890303d23836c,0xc988a1a841410c007052,0x1f098384109d0624c100,0xfc8b200562418540582c,0x102d82d12a2c24090380,0x288c2010244f07414838,0x5087c03024291161a826,0x2846c4b118221023b010,0x140ee004e60d854420c8,0x4aa4d0b04d0e890201,0x3204a408a07e1063d886,0x289483830a3c36e0c0b8,0x1884649244388225936c,0x62140583a6184817689a,0x230e4551887e001343c6,0xa30dc2a12e4438a06854],#[0x24970010041404e13860,0xaac82120fbf5193543c4,0xe064024ead1e39b04193,0x788287882b68e0832d3,0x3c70f1060f1051cd3164,0x19edc4133e5ec1c3db18,0xfb7a81a4cd15fb580bf8,0x3f83788c81a3a8be0c89,0x80659f066a4d83295980,0xd05ed1469f6fe64f19bb,0x9635d0eaed25f573daec,0x1f37bcb403cbd0109587,0x41c070980d7ce118302e,0xe183a14bfd028094e68b,0x81e06c3375ee2c8339b4,0x2d0d767ecbaa23330b03,0xb2be213cac1d5e8dd0e1,0x60464e9fc0c8765cc028,0x2e728e17f651d6481f88,0xe61cb6ae09b0f0d12b2,0xbbf14420cb1a05a7a311,0x6cb8bbf33db67c800221,0x3850246689ef9e84460f,0xe2c10678fc302c650fff,0x8b2970fc4482a89a603a,0xef04a087d7a8c2861d27,0x2e04347fe98160091a23,0xa2652ca63c1859e9e884,0xcb8567e0842610ddffc2,0xed28d80a4f7c0c66e1ca,0x84461e20e7fa7a11187f,0xc4fcb042443bb1c3b12a],#[0x230654f6a5099b23dd8f,0x422477f064c74820f5f,0x193be3fc0aa00ceaf77e,0xd80a4074c3bd5d9b29e0,0x504e672cbacb1b2aeba8,0xce5fff2198400d05fe00,0xcc73de37e458e9cae08e,0x1ec67a861fbe0c19e38f,0x61164b51c78840c6ffd6,0xa45c442f64aaffc0c99c,0x76e0bbf033e181453888,0xecdb9a112b2fb444133e,0x4600a2403e41069a0aea,0xfa691173ff7a62471fff,0x9e844603f9e3d18c293b,0x61776850ff1a1ca2d9f6,0x97906697f429c204313e,0x6c490cd1dad4e0199b80,0xf982700cde7100a32ffc,0xe00c614911b7f6442668,0x8243d3d10621084f05bf,0x52247cfdc064176ed151,0x932bbb1e3c5b6c849fd1,0x3b42f8e964d47934680a,0x91fe5cae4a3a63a72b82,0x7dd08021623b66570476,0x7c3424d7fe494060268d,0x6c7c106776044e27ff14,0x9930947abb35dcd63d49,0xf18788b51ec51f686961,0x5419a2e1f02272bd745b,0x10e637b398810c5d3095],#[0x5e7ea923b3005feca690,0x9364108186b9b8dbded0,0x12c27120c2cc9c8eb25b,0xead85060f6c3196703f2,0x8810432ffb4584637928,0x50437570f242c67c7cad,0x1e083cecc61866d699c3,0x5490d21ff95411043461,0xd6fc285e933f7ff8cb0c,0x192e70122891c4e08491,0xa8eb244df4148a42ce1d,0xd03010b6ec981e850bde,0x38f1c4e08491c605103f,0xe94a0781348357f86283,0x3f8011c5f4500c21438b,0xca2d98a85ac39e33ce63,0xf2930010deeed2909901,0xbf000f623c78c092ca6f,0xb46c7085100a747e310a,0xc7c30c9352cb02658708,0xd4d12bf850818432e7f8,0x644e5704766ae645936,0x1f00b42e341b0613a3e9,0x5950cee4820e2b16304,0x1d64657aa6c4085e6efa,0x3565f44265897a635ef5,0x501a23bfd0641bfe2c42,0x1240b2488e13a91e35fa,0x41081d56fa60cd3c5644,0x69cf9635d2b0a569a430,0x12e92e0848f2b60504a2,0xee2938a63fc3ccc5820d],#[0x16284c0b8c1d7e733217,0x745854958f0ea359a597,0x92085d00a9036c38c806,0xded51428654f19338f99,0xc80f5360847bc7251b3f,0x9e8c5afdabb142d153e0,0x3b5066c390151c3d2d07,0x7d4f190bf9134b0ccde0,0x6b8a0f2121f48335dd0d,0xc]]
def g63D7 := groupedPages #[groupPage0,groupPage1,groupPage2]
def g63H7 := limbs80 #[#[0x448600658600c100002,0x110d2031c60411002010,0x44031e0190007c103f0c,0xff29b1b90030c85c0082,0x20081fff9c77ffffdc7,0x7fff9998908b07060000,0x400020ff937fdfdfb3,0xfbbfef9a98918c200601,0x2400000102ffbbfefff,0xdebfffff9a98928d3907,0x70401050000deb8ffff,0x7bf7f92f7f9a98938e53,0x6d070520082084d7d12f,0x1d7f00000d7f9a98958f,0x90810706000010000000,0x12bc00bb0873849b9898,0xd40f3906d3f206bf42dd,0x3016eb8ee145ef902508,0xbba177dbf2900100da6d,0x515b8389f11b76e20ee0,0x24da02000aa581147644,0x7e05164438cbc0d1]]
private def groupPage3 := limbs80 #[#[0x1481010c10108100c810,0x4c010480104401014c10,0x980108c81058c104c810,0xcc810cc010c801098810,0xd4010d0c10d0810d0010,0x104200c420d4c10d4810,0x18c20150201442010c20,0x584204c4204c02048020,0x98820984208c42058c20,0xcc020c80209902098c20,0xd0c20d0420d0020cc420,0x10821d4c20d4420d4020,0x580211502114c2110c21,0x98c21988219802158c21,0x1043008430d4c21d0c21,0x15030148301443010830,0x4c4304c0304843019030,0x8843058830584304c830,0x980308c8308c4308c030,0xc8430990309883098430,0xd0830d0430d0030cc030,0xd4830d4430d4030d0c30,0x150311483110831d4c30,0x8c831580314c8314c431,0xd0c31d08319883198031,0x1903215032d4c31d4831,0x9803258432580324c832,0x8440d4c32d0c3299032,0x1444010c400c8400c440,0x4c8404c44014c4014840,0x8c440884405884058440,0xcc440c84409884098440],#[0xd4440d4040d0040cc840,0x148410c841d4c40d4840,0x58c41580414c84114c41,0x98c4198841980418c841,0x14c42d4c41d4841cc841,0x9804258c425844258042,0x5844358043d4c4298c42,0x98843984439804358843,0x8450d4c43d0c4399443,0x10850104500c8500c450,0x4c8504c4504845010c50,0x8845058c505885058450,0x99050988508c8508c450,0xd0450cc850cc450c8450,0x108510c851d0c50d0850,0x58c51580514c85110c51,0x98c5198851980518c851,0x10c52d0c51d0851cc851,0x9805258c525845258052,0x58053d0c529905298c52,0x58054990539885358453,0x988549805458c5458454,0xc9100c1100811098c54,0x1411010d101091010110,0x189101511014d1014910,0x4c110481101911018d10,0x8411058d104c9104c510,0x8c9108c5108c11088110,0xc81109911098d1098910,0xd0910d0110cc910cc110,0xd4d10d4910d4110d0d10,0xc5200c120d8d10d8910],#[0x1412010d201052010120,0x191201512014d2014520,0x8c5208c1204c5204c120,0xd0120cc520cc1208c920,0xd4520d4120d0d20d0520,0x10d21d8d20d8520d4d20,0x1912118d211512114d21,0x8530d8d21d8121d4d21,0x10530101300c9300c530,0x145301413010d3010930,0x185301513014d3014930,0x4c530485301913018930,0x8853058930585304c930,0x985308c9308c5308c130,0xcc130c85309913098930,0xd0530d0130cc930cc530,0xd4530d4130d0d30d0930,0xd8930d8530d4d30d4930,0x10d31109310c931d9130,0x18931181311513114931,0x991318c9314c93119131,0xd4931d0931cc931cc531,0x10d32d8931d8131d4d31,0xd0d32191321813215132,0xca10d8532d8132d4d32,0x192101521014a1010e10,0x586104ca104c21048210,0x98a108ca1058e1058a10,0xcc210c8210c421099210,0xd4210d0e10d0a10cca10,0x106200c620d4e10d4a10,0x1522014e201462010e20],#[0x58e20586204c6204c220,0xc822099220982208c620,0xd0620d0220cc620cc220,0x10a21d4e20d4620d0e20,0x582211522114e2110e21,0xd0e2198e219822158e21,0xca300c63008630d4e21,0x1463010e3010a3010630,0x192301523014e3014a30,0x586304ca304c63048630,0x8c6308863058e3058a30,0x98a3098630982308ca30,0xcca30cc630cc230c8630,0xd0e30d0a30d0630d0230,0xd4e30d4a30d4630d4230,0x14a3110e3110a310ca31,0x582314ca311523114e31,0xcc63198a31982318ca31,0xd4a31d0e31d0a31cca31,0x192321523210e32d4e31,0x98632982325863258232,0xd4e32d0e32cca3299232,0x103100cb100c31008310,0x14b101431010f1010b10,0x4c310483101531014f10,0x8831058f104cb104c710,0xc831098b108cb108c310,0xd0b10d0310ccb10cc310,0xd4f10d4b10d4310d0f10,0x10720103200c7200c320,0x14f20147201432010f20,0x4c7204c3201932015320],#[0x8c32058f20587204cb20,0x98f20987208cb208c720,0xd0320cc720cc32099320,0xd4720d4320d0f20d0720,0x14f2110f21d8f20d4f20,0x583211932118f2115321,0x9932198f219832158f21,0x8730d8f21d4f21d0f21,0x1433010b301073010330,0x193301533014b3014730,0x88730587304c73048730,0xc873099730987308c730,0xd0f30d0b30d0730d0330,0xd4f30d4b30d4730d4330,0x193311533114b3110b31,0x8cb3158b31583314cb31,0x997319933198b3198331,0x15332d4f31d4b31d0b31,0xd0f32993325873258332,0xcb400c74008740d4f32,0x14f4014b401474014340,0x58b40587404cb404c740,0x98b408cb408c74088740,0xcc740c87409974098f40,0xd4740d0f40d0740ccb40,0x10f410cb41d4f40d4b40,0x583414cb4114f4114b41,0x98b41983418cb4158f41,0xd4b41d0b41ccb4198f41,0x587425834214f42d4f41,0xd4f4298f429834258f42,0x9834358b435874314f43],#[0xcb500c7500875098b43,0x4875010f5010b5010750,0x58f50587504cb504c750,0x993508cb508c75088750,0xd0750ccb50cc750c8750,0x10b510cb51d0f50d0b50,0x58f51583514cb5110f51,0x98f5198b51983518cb51,0xd0f51d0b51ccb5199351,0x58f52587525835210f52,0xd0f529935298f5298352,0x9935398b535875358353,0x77b7d7e7f3e9ecee6f2f,0x5fadd3e7eff7ebedeef3,0xbfdde7efeff7dbdddedf,0xfffbfbfcfdfebeff6f9f,0x4dd842027484409d139f,0xd7168c3dd85c08723a8,0xcf58c7200743a9010c78,0xf00745b41dd8423d6399,0xa10584810d7159c95c42,0x4015760b055d8850b761,0x11855d851157687c59d9,0xea63a6508055d83f4f53,0x6435458442297288c5dc,0x8c051770a9c55da2f167,0x7089c55d818157667945,0x5da8615762a0a1c98115,0x67645055d8194b761085,0x55d9891576a445dccbe1,0x15765f055d9917343108,0xc55cd392a723693d0cad],#[0xa17739ad3989c2157628,0xccc5c16415766405dc0c,0x963a6507ce1950d17730,0x8c055d83249637b05dc0,0x45553731e0e594242173,0x257c55da8e1476425458,0xc0db51631e055d99c2a7,0x7073c5dc0957b40070c9,0x5d9e15376170c5c1ac15,0x5762d459d94c1570ab85,0x55c1d46074109298dfe1,0x15769ec55d87b2d717d0,0x455c0d115766d85dccac,0xf2273490e19511167649,0x2455da2244644e855d9e,0xd813001455d9b051611,0x82055d84a15760e455d8,0x215157688055d8301573,0x597055da2414763a455c,0x88aa15760e1258c1e1a7,0x704c145843d157359d35,0x5d9f515760e9158c7230,0x57670119c92d15768ac5,0x55da1017702fd3588b51,0x157033451d9081c745a4,0x859d8ec157606855d999,0xb466410c55da92516120,0x9c55d83d3a6507855c23,0xe9734010855cd1d15701,0x3859d8ef466411055d9,0x9bd1e7481055d9751576,0x33c944c45e2a7243855d],#[0xc5f617700d0a5ca50157,0x7663875c2671573618b5,0x191344c623985dd84215,0x57693455c241157054d1,0x59d8f7157697d41c8781,0x1676390a5c9de3865424,0x859d913507211455cdea,0x415761cd218ce7157682,0x6459d90a51611ec85ce3,0xfa44644b0e1950e15769,0x4055da9045734b455d9,0xd05343115458c7c1576,0x11cc55d8c631703785dc,0xd82e16764e9119147516,0x767394584b0327037855,0xdc0d515767e0e9945415,0x5733c0e1950f15738585,0x3588551576a8c71d0421,0x446448455d8b11576779,0x855da82177660455da25,0x15768505dc26c15730d,0xd258cbc2d7188071d18,0x451576594c5d9b14e621,0x43459d956157677548c8,0x8aa4e621a485ce264b63,0x61c55d9b91576681398,0x88b751616105dc2187b4,0x521158dd042157623135,0x5da9815765b95dd84250,0x5762d139885117733205,0x55da814a6307871d1081,0x31706ed45843a1c7439c],#[0x455da04486342071d1fe,0x4157666055d8021576a3,0xc134c8693a6510c5dc19,0xe16763b455d85815709,0x5d855d828287242059d9,0x26f177334c55da581576,0x62f055d9f315766a855c,0xcdcf15739bc55d875157,0x764f055c098317067055,0x58451167656c55d86f16,0x576634adda0015767694,0x85ce222a7245055c2161,0x386544055d82d1576300,0x455da26177325085ce1f,0x150751e191d0422d7176,0xd489cd3e52631e059d91,0x8c5353114e9945116763,0x5a085ce241570a7855da,0x827792036455da511875,0x669055d99217731e055d,0xd93d157396d1d8d48177,0x632a9110c78317066459,0xdc09b157694c55cda34a,0x5762c111913b15709e85,0x55d9dc15765d115c12d1,0x15760f941504551611bc,0xc55d984157087859d921,0x23170595218cf81770a6,0x8855d80115737f455d81,0xaa46640205dc0ea1576a,0x67c75c4a138654285dd8,0xa1c496331855c2af1576],#[0x35c5dd81e15767b455d,0xce8f16765545dce9a157,0x632048dcda4177032455,0x10cad177335055d85545,0xd7176c59d92439650813,0x55d8b9177035069d5b32,0x227353059d8d91576630,0xc75c272157678055cce3,0x615767dd4d4c7848633b,0x9055c2807b3007059d90,0x5a2a7241475ce6115765,0x7f0e59422157619455d8,0x5f02f7102055da391576,0x679455daa14d63070b5c,0xd85415765e4cdc1a5177,0x76408e19502177360855,0x588b0793061ce5941f16,0x57684859d8de50751153,0x15c52d157086879d0da1,0x16763e05dce172a7245d,0xc5dc06a44644bc61d5a8,0x44644f05dce77157617,0x455c09f15768e911913,0x4f4e76430bdc5c215767,0x5b455d824167641455c1,0x69157612455da4f1c74,0x2950d9d13c68439b569d,0xc11459630a4d9c2a25a6,0x71450d5c15b3573818d5,0x9c0c735703ed6dc42035,0x87460d61c4cf3570680d,0x65c516367090cd1c23c5],#[0x8531399698caf3673a15,0xd5c2843674680d5c10e,0x858545856d850a367028,0xd4d5c106367340df1c90,0xf33670998d5c03a35709,0x88d5cd01357376214c4,0x8783573190d5c0e25a63,0x3475610e9d893076568c,0x91d0357364961511d5b5,0x73418ddcce6357142969,0x5c2965875268d1d02035,0x6764f168c9465843030d,0xd0c9ab357096965d9893,0x6b414f8d5d99b35737f1,0x8d1d01d58633f16190ef,0x8357156cd5c07e58742b,0x55f8c90e5862481658df,0x9458430cdf9c9f858436,0x4b0d5c52a35704a0d5c2,0xc693570979658cc73674,0x2534d9d1287f510716d0,0xd9095b637e0d5c5d6367,0x624ad6d8508377169961,0x98d683672194d5c19158,0x85408169901d35704156,0x61c4205b5364d658ca45,0x5b7226969d0333570385,0x4d9cd043570a05658cbb,0xb5b767fcd5c0f788526c,0x68d5c08359321e0d9d19,0x9a58633b0d5c03e5b532,0x808d9c23f357028cd5c1],#[0xc3036764f5658d905b71,0x9a96194e459632e9658,0xc0a05b5385d64c946377,0x70888d5ccf35963a48d5,0x5c26359637b961cc3335,0x8547422085b13571680d,0x6151933570a916988435,0x357338161894e5853475,0xd5c0188472170d9d20a,0x85963315f8c9e25a7474,0xa5614e6b5a631d0d5d81,0xb7d32828ddc5305a751,0x2fcd5c0865963a90d5c1,0x94e6b43935658cbc5872,0x3320d5c55f36763b5614,0x904a585485d6991d2584,0x708996988aa586453969,0x18cf959635f16dca3d35,0xa74ab169cc33586337d6,0x65caac587639cd9d1215,0x59636a0d9d1bb5b722fd,0x8d9c2445842565610d2c,0xb5b63061658c2a5b422f,0xf5618ce636735ed69846,0xbe8a616c4d5c52868644,0x44d61085e377026d610c,0xcf36b4182cd1d2095b63,0x266961d63d58437a9618,0xce94587417a2cc1e8763,0x766c8d9ccb859636d8d9,0x9cd065832564d5c5b635,0x9632e0d5c1113570930d],#[0x6dc5833573410d5c5065,0x3570524d5c0e03570849,0x21188ee5a64a71a10c2a,0xc5a641ad6d0e3d59632a,0xb16151e635716b0d5c5f,0x5e5b4256561d0bf35733,0x5e8d5c2476b437e161c8,0x2126b437b8d5c5243570,0x2179614d938571774d9c,0xc05d3674515658e875b4,0x635b0d5c232587385cdd,0x5cdfa3673a10d5cd0059,0x4709a8d5c15a3673298d,0xd5cdf636708e5610d593,0x58430d4ddc41d5971ab0,0xd698c033570411619134,0x2357087d658c01585385,0x80d5c07158436bcd5c2a,0x40586438df9c90e5b633,0xa45658caf3673404d5c5,0x59b3573429fcc41c5963,0x37dcd5cced357340cd5c,0x8e0f36744f4d5ccdf367,0x7139cd5c0a4357090565,0x5c24f35714d8d5c28284,0x97682961912c7e71430d,0xd5c1643670a5cddc1095,0x35710acddc12e5a63210,0x9658c1137707fcd9ccc5,0x65874650d5c1da596305,0xc16d8d015a640816dc9e,0x86b7439cd5c0ff34744],#[0x529dcc53435707d5add1,0x11c3673761d10dac3570,0x17416d0c335a32228d5c,0xc5215b531a5698e68597,0x63448d5c2385872564d5,0x1913c3570464d5d99e58,0x9305a169889a3570895a,0x69963d5b730ccd5c19e8,0x357338cd1d1d1586340d,0x1610c233470271f5ca0a,0x93670919610d6135706c,0xd5c56035705356dc95,0x4637708f8d9c89d36765,0x42565844258741a4d5c2,0x88347017569889d8731,0x112d64ca3d5963018d5c,0x50695843475dd4d9a5b5,0x762321cc5ff357397561,0x10e195852228d5c15c59,0x963035658d8d35708e96,0xd9ccaf36709a4d9d2105,0x37709f964c9a73673a30,0x8d9c94e59611ad6d8d0e,0xe3571678d5cc32367344,0x1d6d81475843a95a1913,0x7f35706e4d5c1333770a,0x461698c7d59711a4d5c0,0x56868436d56d0cc83570,0x3311698c145a648fd658,0xc8ff5b633e8d5c265596,0x63061a10df637703a5f8,0x8c9f55843304d5c25f59],#[0xb6338cd1ce8735704e9f,0xd5c15634732a561d0cf5,0x5a631e561cc943673a40,0x16d8d0f586341214c5e2,0xe596107561d0ca585218,0xacd9cdde5a621d96cc8b,0x25587334cd5c04f85317,0x5f16d85343570910d5c5,0x2663773788d1d1fe3570,0x3475a8ca616b424fcd5c,0xcde158437416d89595b7,0x633b169d4335963828d5,0x58cb668434fd610d935a,0x6744d16d4e3d87623b96,0x61ce9a35703d4d5c1433,0x36708e0d9c2965976061,0x4d5ce3936709a1618946,0xd3571434d5ccd9357324,0x78d5c5b75843575adc92,0x175b32564d5c5ce59721,0xccd5c05635713f9610e,0x90e5b53228d5c5b35973,0x526965d8283570a3169d,0xc5e357094d6dc68b5a6,0x76735fd041c5b712b96d,0x5d9b06b644f4d5c57c35,0x5710e1698de758548f4d,0x6dce9a5b62518d5c5228,0x35702a161d0203570a19,0xd5c06f357058d618ce0,0x7d727e1698d6c35717d,0x5961892389303b0d5c1e],#[0x8035703bcd5c29058544,0x39969823d586439d6991,0x5d059637bd69949d8a30,0x408d5c24d36733f9658,0x8ddd347469561c4ae357,0x70530d5c0de5843a6965,0x58ca63676494d9c94b35,0x571498d5c1f87c438156,0xd5c5415b539d8d5ce523,0x37708a1698ce636744e8,0x1d149b134708f8d5c239,0x9357066d698df1357157,0xf5658c745a63778d5d99,0x893771600ddc09c35714,0x4bd6585fe6b430c1658d,0xc3359628f561d4695862,0xa64d5ce5835739356d4,0xc6076a647e161d1e6377,0x6339dd085b13571750d5,0x5c50259632a568c85e77,0xb7385d698de25843748d,0xd5cddc586256624c0e65,0x5a6321cd5c0743670a84,0x8d5c243377606161488d,0xc3674780d9c958596378,0xb0d1d12f7e32398d5c58,0xe658734756990ed36746,0x905f5c50c585480a18c4,0x89a5873321a10e0c5a64,0x40a21dc9e486313ccd1c,0xce515963089615033367,0x435bd6149593570948d5]]
private def groupPage4 := limbs80 #[#[0x1d43359632d56d8d1058,0x96362969846958645656,0x658e68587642169923d5,0x5b4347569d81836746e5,0x161d0345a6410961485e,0xd5a649021cc9e4357140,0x2161d45e5875475658c2,0xdd5961600d5c5f658743,0xc0ddc5083674499ad0d,0x12d584353d69c4695976,0x14496990695a62695adc,0xc2515932178d9d1d7357,0x6307dad913c37717f8d5,0x585d236737bcd5c22b59,0xb7334d61503458546516,0x2cc2035a751796dcc945,0x347409da991b558633ea,0x56d0e485a6439cd9d136,0x3586336561954f6b410a,0x9d618ce336735e961d03,0x6959636d0d9c23a87713,0xa71f4c8f33573940d5c2,0x9f83571444d5c22f3570,0x506169806937709f569d,0xe0b367450d6d8cfc5d6,0x539d8d5c0703571835ad,0x58d685a60268d5c5bb58,0x673401658c0377324bd6,0xd5cdde3570a60ddc2543,0x585460cd5c1b23470a64,0xcd5c24e3570000d9cdf6,0x85963210d1d8e958530c],#[0x222cc1083670904d9c29,0xda584332d65849a35738,0x8d614c5f55b4364cd9d1,0x12458644d8d5c2833570,0x3804d5c0a55963a50d5c,0xcd0b58711a56d8cff347,0x4307211c9e45961274d5,0x5d85f5a72179658e867c,0x673a056d0e175a620796,0xd9cca35b71585698c913,0x5b53178d9ccff367305c,0xcd5c545596305df10c26,0x868431bd64c96b347226,0xf0d5d9a0367383cd5c60,0xb5357036d61c56137708,0x4a8d9d8ec5b52564ddd9,0xc1035766e568c8453570,0x456565889a35714d1658,0xca6b58767fd6d485e585,0x71108d5c016357055d64,0x10d345a74179610ea874,0x57048d61505e3473789d,0x658ded5b43a68d5c2683,0x3670a7169c51635706f1,0xd5c5055b73320d5cd12,0x95a645a5a1914037716a,0xf961c89a3570554d5ccf,0xe6357053cd5c58e35714,0x7eda191255a63019f188,0x1b23570734d5c1993571,0x3034d5c189596269cd9d,0x910835709ed6d8ce65a6],#[0x7483d65d9f859611a561,0xd8cf3596226d6991fe36,0x9631f4d5c0ba58436156,0xd5c0a236702896d0a3d5,0x684376d658c285a74458,0xd6dca8b377395dd18ce7,0xe357059561d159584338,0x15658c143770794d1d12,0x175b72178d5c14059321,0x1a561500936740b8d5c1,0xc7959632dd6d8d025b71,0x133d799418357031d658,0x8e0e6874420d5c0dd5b7,0x76668d1d1e56b416d169,0x5c23f35702d4d5c14b35,0x976774d5c11f687439cd,0x3d493f3570a45f8c9f75,0x8f717fa3d893c8c624f2,0xa3105fe8c434a23cc0e6,0xe8f317fa3cc5088f4339,0xae31893f8c644a238c9e,0x338f624fe3151e98d307,0x7ae3188e78e326723151,0xcd98e6266a3d8ce68c43,0x10623d05fe8f41422310,0xc228f307ae30c6038e7,0x524fa31c8e78c317fa31,0x5c4188c717fa310c1f8c,0xf437ae3d88e78f7239e3,0x31511f8c6339a3151998,0x8d303ce34c0e68c4249e,0x235c10e8c4339a31493f],#[0x78f5039a35c20a8c4376,0xd23d4d3a8f503ce31912,0xec8c428d238853b8c517,0x7ae39d93a8e746263149,0xcff8e656663991ff8f53,0xa3d45088c214d23d0,0x45fe8e6482a3149208d7,0x513fa3d4e1f8c547ae3d,0xd45f48f434ce35c12c8f,0xe7443a3cc99f8d6382a3,0x310d998e7482a35c1f88,0x8c624fa3d499a8e65492,0x231853e8c2110a31d5a7,0x78c523b630c9ae8c216e,0xae3d4d9d8c327a23cc92,0x698c3162a3995408c537,0x6ba310d1f8f527b239c4,0xec8f323e6310de88c43,0x44b23109e38e72776319,0x85268e624fe3085428c5,0x5349230c9e38c5239e30,0x194ef8c5182631450d8f,0xc5451e35c0e38d700023,0x3c85348e656c239d1e98,0x8c5236a3d09e38c21156,0xe310de38c3143e30c5f6,0xf8e620f631c4698c3182,0x9a39c1da8f414d231d01,0x9a8c6447e3190f38c643,0xa23d4df58c6336639c4,0x5b18c435123194e98e75,0x18263188ed8f51436308],#[0x48458c3277a30c9f18f5,0x658ae31cc1f8f216e231,0x1c89a8c7478e3d4c478e,0xc214ee3d48e78c514fa3,0x3cc4298c544223d0d998,0x8e744b239c65a8c547fa,0xa39ca3d8c645123991f5,0xa8f507ae3c85268f2150,0x563194d98f4347e39c89,0x6b8d700c2358df58f211,0xa238c50f8d7338e39c4,0x60b8e700c23d4ce68c54,0x188e3086348e704ea38c,0x943a8c523d23d4cf38c2,0x5439a31092b8c526ca39,0x1953a8c543ce3cc9e38c,0xe754b635c1dd8c324ae3,0x39c92d8f424ae310d2c8,0x8c524f2310d2b8e70776,0xe3149ae8f4343a398e04,0x18c527a2310d478c7269,0xa235d8188d700623dc1d,0x2b8d620f635c13a8e740,0x39a318cec8e7200a3d4e,0xcf38e7562631c49a8c53,0x28f63d4d998e64812314,0x48f48d727763085228d7,0x4250a31510d8c424de3d,0x853e8c548263149e38c,0xc5269e31912c8f526ca3,0x3194ed8c437a631912b8,0x8c7639e35d93a8c52766],#[0xe3c86348e640a2318927,0xf8f2188e3191478f424d,0x7e3d4d1f8c3267e35899,0xe8f3162a31d1ff8e626,0x87e3d89278c6539e39d5,0xd338c3183a39d60a8e65,0x24f235c1da8c317e6310,0xd9f8f530ea310d088f5,0x437fa35c14f8f4078e31,0x10de58c6549230c4298c,0xc643663194ec8c3249e3,0x3589b98c536663189438,0x8c4349e3989b98c54626,0xa39c49d8c5180e31450a,0xd8f5278e3d89438e654e,0xce3d4dda8c5478e35c92,0x2b8c5213231d1088c644,0x7fa39953f8f5343a3cc9,0x4e68f536c23d4e0a8c74,0x14d23145088c653ce319,0x51ff8c517fa35893f8c4,0x5443a398dff8c5266a31,0xd450a8c513fa31520a8c,0x6720f61148458f5180e3,0x69d49a68747f8d9cdee3,0x35700c0d1d9243673441,0x5f5883d5a719da1dc85c,0xd7c624cdd1913436724b,0x1cd9cd7d3570649a9c52,0x3f35706f4d5c0a636745,0xe8d1d1a77c727f8d9c9,0x8c68714b4d5c1fc8561],#[0x42fa1d49e435700a8d9c,0xc10174514d1658ce65a7,0x7449e1148ee8454790d5,0x9943a357067cd5ccc536,0x5702ecd5c1f736721497,0xd5c1d45874a69fdc9fe3,0x3570704d9c99c686449c,0x16dc809587233d6d8c16,0xd7c424cdf0c587367022,0x95f4c9f7873142dadc52,0x45a620ed65d80236724,0x7762d48425a322b21cc6,0x1356a640a969d6483570,0x32f8d5d99f36727b8d9d,0xd04259304b0d5c1fb587,0x74431dd8cef5b63411d1,0x5c1275a644b0d5c21a7e,0x8716a56989e33672370d,0x11c80569704b5f8c90f5,0x6b64480d5c547367248e,0x8d1c8423672515d14442,0xe36764856dc9a9347403,0x64d5c2976b644b16108b,0xd959322b0ddccf35a627,0x975943a6b644ad698c,0x858596367560c8be3672,0x60fa11485c596329cd9c,0x493b5a739d8d5c03d357,0x722f961c49a35705f621,0x9d59336723d1ad91475a,0x963294d9cc1136740596,0x1149715a763bd6191385],#[0x597364cd9c934347201e,0xd658dfa5a7364df10d87,0xe36724d5fd88f35a643b,0xb561d2177c544321d48e,0x263676491dd0d9b35700,0x5561d23d77614d1f104,0x4943672378d5ccfa3672,0x448561893736702ed6dc,0xd4947751108d1c8766b6,0x6451a20853b7d327ad61,0x9c941357386569903a68,0x4414d1658c7a35732ecd,0x61c88a36700e0d1c8e77,0x36740016990a35871251,0x8d5c544367277a2d49b1,0x958720256dc8ae35707e,0x8cd9c80a686448d6190d,0x2859636a8d9c8fb8b307,0xddd82a7d620f8d1d0,0xdf95841614d5c0c65963,0x480161444b5a62074d5c,0x8d7d36747f8d9c0927c5,0x644acd9c8e47d620e965,0x5c13f8473015f8c91058,0x570739ddc44274516c4d,0xd149343674764d5cd103,0x59631cdad913369714b5,0xa2d493b68644a21d485c,0xc347301961d1a96b747f,0x9d0853484721e161952,0x123570511658c0288721,0x748d9d1de36723b4d9c8],#[0x528442790d5d82a3571,0x447dd104428871108d5c,0x848136721c1a9920c686,0x624a21d853a36764fda0,0x9d8d98b721096dd9fe7c,0x8722b8d1d93f596367cd,0xd9c0395a65900d9cc2d5,0x596321d69d67674633bc,0x1698a4e58516b5699022,0x87c6247dfd89285a6476,0x30d9d1446b6449d69c64,0x248742790d5c0327d328,0x1096d812b8443790d5c2,0xdf777516c4d9c87f7452,0x26d5d1445036702e9658,0xc88a586237161c8be6b4,0x6247cd1d007367383964,0x5c0b75a64365a9903d7f,0x87478dd084423570770d,0xd9c8d936724f96dccbe6,0x7c4247d6d8df736740b4,0xd5c1105b53251619137,0xa3674480d5d99c36732d,0xc569ca3d5d650a8d1d93,0xfa35707856d0cbe35700,0x3b6110c053674838d5c0,0x1445874025a5903d5864,0x2131fd091f3672385a19,0x44b347407e288442845,0x746c0ddc0bd89303f961,0x5d8ef3570008d9cc2a36,0x85112224c1f459719216],#[0xd1d13a36724a9f189448,0x3473034d5c1d37d327d4,0x8d9c0c45963245d105b1,0x25a639456d8c177f4109,0xadf1058777214d0d1d1e,0xbe59722f8d9d02236764,0x290d5c0b45b5222968c8,0x190357005d6dc8d35a62,0x53b9f10d0c3670188d5c,0x8d9c5a6210961d0be846,0x722f8d5cc975a625a565,0x1893b5875229ad91465b,0x8644e9dd053436723da2,0x658c195a633ce2144426,0x3670875619199347307d,0xcddcdeb7e620f62589b1,0x1596303cd5d86f88614e,0x50d1c92f367249a2989b,0x3f3474000d9c9f158532,0x268d9d1ff35706f9a191,0xc198b624ed69952c5a61,0x2964d5c21485717c0d9c,0xc52d357030169899c5a6,0x754b4d9c0865b41614d5,0x4c8be5963680d9d11f6a,0x47210e2d41f468724b56,0x658c6f6a724b5698c3d3,0x34702f4d5c0bc7e323cd,0x615843d7c43801dc8442,0xd596328d618922596366,0xf0d9cc145e650a96149a,0xe25a6447df0c42636702],#[0x78d6989db35760e8d9c8,0x2136b644a0d5c0735a64,0x214210c9717741108d5c,0x846f8a216c5610d4e745,0x7134cd9d1d859732fa15,0x5ca3d6a640fa2cc10a58,0xe324116085ad6b6447d6,0xd9d019357376d6190f37,0x347482965c89a74314d0,0xcd5d83d7421141658e51,0xb6a640e9d18934357140,0x6569881784435c4d9c8d,0xda3770224d5c5f935701,0x4d1a1912035733f0d9c8,0x92035737a1658dae7461,0x237cd9d1e368644b0d9c,0xc8cf367024160c585367,0x214ecd9d02136703016d,0x5903e85313fda1912b8a,0x9719d96d8e0c5a6239da,0x2cc1fe357016e2145b15,0x357006569c49a3570246,0x9a191473570671add1e3,0x69640e9698e8136764e,0x216988b059636e8d5c09,0x1336724f1f4c9fa88521,0x3f56188e774324d1f8c9,0x9e35a732f9a191245865,0x1269698c7384527916dd,0x8448847401611d1e45b7,0x216c5a19121747210a20,0x9c0c55b624c5ad914477],#[0x6763bd6188da88514ecd,0xd9c9435b72228d9c06e3,0x5a64a0561911f5a63934,0xa2148425a643cd698d7d,0x977416c569d23d357019,0xf965ce767c623ccd1c08,0xb4367247d6194e37e620,0x61cd9c8565b630a9658c,0x4427d3283e11853a7f41,0x20e8d9c0c658647fa208,0xc285367249d6d8df57e6,0x6201e14c5ee5a63064d5,0x5c17b36744cd698a825a,0x6732dd658db569724b4d,0xad913a36724896dc4d33,0x7f32300d1c09b357024d,0x9f8c9015a758f4d1d8ef,0x368644cd61c8d3597126,0x1a310d0b5a72268d1d1e,0x48e7082a314a308f625,0x48e3d4a218e717e2310e,0xa348f437d63d4d3f8f62,0x26ca3589b28c416023d0,0xc26d8e218d2310da08e6,0x717e231c9e38f7142235,0xcc50a8f303ce3105088d,0xf3180e314a318f7278e3,0x39c26d8f433ce3d4db68,0x8d630aa3d4d408f536aa,0x634c1e28c4379e310dff,0x78f534ce35ca408f528c,0x223cc5038c547d63d042],#[0xf98f3183a3cc5128c416,0x8d23d05808c4378a3cc5,0x99c8c536aa3106238c41,0x182631050d8c62482314,0x86348e3248e35899a8c4,0x624ae3d8cf38f4150a34,0xd892b8c534ce3d89208c,0xd3248e35c60d8e729023,0x3152048f5367230c50a8,0x8f4382a39c52c8c654fe,0x23d4da48e630aa3cc1e2,0x28c7142239c60d8c3142,0xa31099f8f416223d0de,0xf38e326d635c08c8f425,0x88e3d099f8f418d2318c,0x9b58f414363885428f41,0x288638c93f8f41826314,0xcec8f317da3cc5008c5,0x714b23cc50f8d3182e31,0xd09278c655023cc60b8d,0xc5214a34c93f8e702323,0x3d4db58c433ce3189468,0x7c5107239c10e8c6248e,0x1fcc9d37f327a5f1041c,0x3157345548c84c7c3107,0x8941484c15764a9658cf,0x7c15705893988473a650,0x3fd2d8cdb4e622bd4d48,0x5ee15764e93988494b63,0x20f53988b04e712c8b5c,0x904a1576490e994474e6,0x5213149887c3a6505d19],#[0x1903a4664000e9944953,0x67213919903a46640f96,0xf14587157649d3d89384,0x15764a119900d47644c9,0x939883b1a757612d8d0b,0x74e6229a1149c7157057,0xcd40c87c466415dfd458,0x313a650ec55d94315764,0x7652d8cef466413d1d91,0x5f63a650a941084c2a72,0x277a1d49c73a650e8b9c,0xd5d946640291d91382a7,0x717d1f4c8ba157650069,0xd912c466400ce994162e,0xe622dd398852536147d1,0xe994524e711356189314,0x466405055cd0752321f0,0x79d1f44e6229055d923,0x78c4109ce9942150521f,0x2631483b8c43426398c1,0x98c5405a34c50f8c744,0x49a3d041d8d6305e3151,0xcaa15765991dd16d8f41,0x51c1414c78327047d258,0x88894d732c879d21f1a7,0x7695069d64e4e6214d39,0x5d86d15765dd31504617,0xe622e0c1c25431705e85,0xbcc936157688c55d9f64,0x534211455d8a21573865,0x45dce011570478a9c8fe,0x8177617471d01d1e748b],#[0x88e9945351611c1258c0,0x4e31703fca9c90315766,0x14855d829157699515c8,0x1313a650ac5dce8a4d62,0x111c55d9a11a75869119,0xd9ff1576a5079d135516,0x6114519c44e4b633785d,0x5c5222d713f855cc9752,0xd6229855c24a2970754b,0x5dd843457113879d0494,0x46646f11990071a753f8,0x79d18450321e055cc0b,0x4177395855da5e177611,0xfd1990413a6592dbcc9c,0x8e52651e055da1d2a723,0x65d458421507411455c0,0xd2157672535c4b21576,0x178479d10b4f4313455c,0xc08b5372115158e672d7,0x432c885cd1f21734905d,0x5cd954e622d85dda554f,0x17058d11912046640185,0x2d8cf432704d8c1c2893,0x15739e455c1fd15732cd,0xd258e956f4375469d555,0x84e621045dd81d30704b,0x7059d8fe1e748b12d8cf,0x374e732c869d4801576a,0x2a545843b297236855da,0xd704675138e994624e62,0x698cb5c5dc4e6211055c,0xd0071a7598055da33157],#[0x625a85dd807466403871,0x988ab157086c55cc354e,0x66472131895115769f13,0x55ce1b33701d94cc8784,0x15766292d8d115132114,0x111d16d466403d358d87,0x244644d455cce5337095,0x191991c415768d455d88,0x7815769414d084c17760,0x158c5c0db157046d48c8,0x9b81573234b5c5cc4d62,0x307c5dc2784d6229055d,0xd671157673455d9df177,0x52114b5c4904f4311869,0x9c620167636855d9f053,0x573030c5c1ab1773324b,0x69d57415765fc79d03a1,0x38653fc55d99d476451c,0x911913d4d620ece99463,0xc496320055c150157696,0x3c5dcc951570aa94cc87,0x82d717c455c06115768,0x10c85ce3915769193988,0x212d71188e194fe4d62,0x113455c2a0167653479d,0x8c2644644d941cc784d7,0x73104b5c5eb15701b135,0x5d9db1576a5455cd1b23,0x2631f11990471573aa85,0x55cc251573a8139d0b25,0x15766d079d0fe44644b8,0x9358851534313055d9f9]]
private def groupPage5 := limbs80 #[#[0xf4e62109218d1115765f,0xfc5dda884e74135258c0,0x49157683519904915766,0x9c9298e9515766f859d9,0x1f235706616991ac1e73,0x3830d9c9e05a630e8d5c,0xc9793570840d9c99e367,0x700c16d4a6b35707b4d9,0x5c20a36746acd9cdf936,0x8624d16d4e4835737dcd,0xf8c9da596377d658e525,0x36747c96d8d2b5a627a1,0x4d9c9bb5963934d5c1e9,0x88571769699199377074,0x51d10dab367376561524,0x7234737ad65d9da37732,0x4d1f4c9da377385d698d,0x2715a6315d6191527751,0x7256991ae7e3282cd9c,0x8d655a62668d9c05b357,0x700c4d5cdee58623d165,0x1914336747a0d9c9ab36,0xa631bd61914f7e327ada,0xd1d1da36726dcd5c2045,0x5a642c4d5c2713570314,0x56995af36728d565d9e9,0x435716e8d5c418367278,0x9cd5c19759637c9658e8,0xd0367293da1d52d36747,0x9b4d9c9d935708356985,0x663672890d9cdf23570,0x295169880e3672768d9c],#[0xd20435706d5698816347,0x72880d9cddb58728f4d9,0x5c092367379d658e8136,0x6728c56149c53570190d,0xd5d9b55a328f5658d783,0x5a645b8d5ce0c5a76968,0x961c68b5a329596985d2,0xf36709b560ca6b347407,0xc4d9c21358528f4d5c05,0x40357062d61c9e635737,0x7b0d9ca4e35700e5614a,0x93b7c42665698d6f3674,0x27b0d9d19a5a6328d618,0xc8c136728dd69889b5a6,0x7297cd5c2937f4266560,0x9d1ae58623d9698d6536,0x5707ccd1d1b059636e4d,0xd5c292347269cd5c20c3,0x34747a4d9ca2e5a626c4,0xd658e906b6450cd9c05f,0xc5842a69a1912a585270,0xf5698a3d3571825658dd,0xda36747acd5c0285b528,0x720d1c9a55832a69658d,0x1eb5963a4cd9d1993570,0x7bd61ca8b5a62900d1d,0x921f3570339698c47357,0x6209cd9c9db585212d61,0x5cdeb5b6382cd5c0c45a,0x57087560844b35700e0d,0x6991e85a635e0d5c2313,0x35708d961c6025a628c1],#[0xd9c2745a71740d9d1f5,0x85976968d9c9ec35709d,0xb1658deb5a61274d5c5f,0x823573990d5c20f34747,0x7c0d9c9dd5b5270d658e,0x56f35737c8d5c2a13570,0x27b961893e3672669699,0xc60e347278d6988ed5a6,0x70aacd9ca3036700c8d5,0x98c7a36727cd6995ae35,0x6726c96188ed5963a156,0x658e833670869658e0c3,0x367019568ca6b3570195,0x8d9c9b934728a8d5ce68,0x834747fcd9c9e95a626b,0x996151a95a72ab0d9c9e,0x9f5b2112d614a6b36728,0x12d610a3d3570264d9c9,0xe8c36727c0d5c08c5b41,0x188d5c06e3674749658,0xce0e5a625ccddd9b0357,0x637d5698870367362cd5,0x9c0598b50824d9c9ae59,0x4728a4d9c9d88850824d,0xd9ca2336726d4d9c9643,0x3571735698c3e3673a4c,0x8d1c9693670850d9d19f,0x5a71ab0d9d1f15a32a6,0x531893044644c91991c,0x48157335d19903d1e732,0x381218cfb2a725811195,0xcb24c6255869d4f53170],#[0x50f0e994274464515310,0x905653531f13988553a6,0x7237c75c072446451119,0x9d5f41a75369258e862a,0x4644a4cdc28953531306,0x19d52d4e62911414c7c4,0x2a7288d3188f75054131,0x79d28d4b63409398856,0xf1a7581ce195011e742c,0x2055ce9e4e62a8855d91,0x90466404ce9942846655,0x44d1990393a6509069d4,0x582d71728e994292a72,0x5128b5c4c63a65165199,0xcc8e4e622d51990313a6,0x61209119142446449855,0x9d5f54c623d549947c52,0xa651113189332a729406,0xa9c9984e62a853d4c4d3,0x44654b531504d446449c,0x11991bf5261154c9c0e0,0xb466470869d49850521e,0xc8a5d9d5446450d2d8cf,0xcc4a632f4b5c43815732,0x53079d0a31e74a051991,0x1cb1573308e9944f2173,0x237d1990153a65061199,0x909a4664154e9945f297,0x7539061d4064b6338519,0x58cbd44644a069d4d91a,0xa6517519952d2a7243d2,0x61d4e61a7503c55cccd3],#[0x357383d65da3f5b539ac,0xd6989b55a6297cd5c610,0x359635e9698ddf5b4353,0x19f8ca0a3673818d5c60,0x3d59635bd698dfa36722,0x820d9cdfa36728e8d1ca,0xc225a620a8d9ccbb3673,0x69b56d0c615a621ecd9c,0x88b55a647a4d5c273597,0x747e9698df236747ed69,0xd0e413673649698dd836,0xb4338d61c5835d650a16,0xd9c9be5a62278d9cdfc5,0x58624d5fcc4267e72828,0x16d0c0c5a6487cd5c5d7,0x77e3283169da0a367273,0x4d9d015367091568c9a,0x1636747a5d58c285a659,0x9016988525a626acd9cc,0x4283672999698e8c3672,0x1080d5cdef3771809799,0x8a215b434b0d1ca7d377,0x7216d6d0dea36737ad69,0x990c06a749b569882136,0xa639ccd9cddc5a621fd6,0xd5c42e5b6382969d8285,0x357072d658d7b5a6474c,0xcd9ca435a64711698a91,0x337760a0d9d0315b436b,0x1569da6d36709ccd9d1d,0x2858624f0d9cc3235739,0x805698deb7f3161d6d8c],#[0xc2836729196d0c233773,0x379cd5d8283673785d98,0x89b25b43a956cca6b357,0x62125658d72367270569,0x98a313674028d9d0395a,0x9639cd69882836729fd6,0xd9d1f335739cd6991eb5,0x36737c5658d8b3570914,0x56989a7367482561893f,0xd5b435bd69905f36747b,0x50b5c5e051321f16d0c4,0x42177364d258cb52d705,0x6991990044e625d59dd0,0x1e3504211489cd1f3370,0x5205dc2ad2a7241871d,0xd416513213079d1ab476,0x645185dc1d1774366869,0x5848133702ad198e6147,0xd6210875c66249630a11,0x25d9b11a7566879d14e4,0x44644ad4d85358432791,0x479d1d9537679055c242,0x62e714894d85271773a9,0xb869d57a15703c45dce7,0x8a2a72449298c7744439,0x7bd3588492a724345dcc,0x44244644cd15c92d2d71,0xdca9c902157308d498,0xc52d32704d5258e09157,0x63020b5c5da207369119,0x5c5ec4a6331879d1994a,0x17048cb5c1c715704e4b],#[0xc5c11f15735bcb5c5dd3,0x2f7178d298de331706dc,0x479c0a152611e1119146,0x651635c459d9202d717b,0x3d11911f297276455c19,0x1c17709f5d4c93c15702,0x3a029c81b02741002dd8,0x50b2f712f54988780c76,0x41055c0f051621e0e19,0xc1c61a757213989a6317,0x7663d4d85012d7171055,0x5c50051611e945887c4d,0x570308bdc5e23270410b,0xa9c9043865400b5cceb1,0x1a757b45dc2771875788,0x69d4ff4d620f54dc878,0xf1770a993989e22e7140,0xf94585ab17709254d84f,0xb2e763b944c8782e713,0x1e13988774963311218d,0x12315731f4c9c0ff5352,0x2499258c7731705f4c9c,0x892c1570aa455ccc12a7,0x73508e99442157335935,0x5c11a4b6339d81913421,0x1734a92d8d0833704c05,0x89cd2731704d855c0cc2,0x49637f99d913b44644e0,0x485cd2722734a9a1912e,0xc63644d069d52045304b,0x51191371570360d5c52,0x45227350945857d3a651],#[0x4b8c9c1455963690c5c1,0x9297249879d11f6b64,0x50751dd1a9466410855c,0xc135157332c55c29f3a6,0x734f9258de33865420c5,0xcc1341a754f4c5c14121,0x57030d91913b17764b9c,0x454011080000cdc12f1,0xe480cd305548226c0d00,0x6830ec162b09ec846081,0x8ca041a41ec30e5606a,0x70a0afe853b627cc12bf,0x4f1b930d3f0654a306c1,0x443c20be0fb9477f239,0xa5824fa12686927a48e4,0x57cbc765b482c2415584,0x81b1b0d33e66dd320498,0x3d761e030ea66722337a,0x95a433620d9d015a7dc1,0x54954c495723ef1190e8,0x147e4a1144f13a6d2530,0xc8015dfeac0d54b829b1,0x2caf5497526b7c55a742,0x365c2322698bdac30960,0xd8d56b24b4f2da25ece9,0x8891dc5611023001b722,0x5bb6797455d30420e42c,0xb42547611c1e0020f79,0x5ca69d835753b454f036,0x8af26c761502c002087b,0xdba67d8c5853b444e52f,0x4af21c5e1141c0020878],#[0x1c9681845894544cee34,0x8ac2247013825001f576,0x5a75fd6752528420ef34,0xcb22306f0cc12001e873,0x1c869d8d5a1414990135,0x4bf24c60104220020c7b,0x9d86a1975b54b4a9133a,0xcb323c5d114280022d80,0x5d66c59d5c146498ff35,0x4b4234651102d0023784,0x9ea6dd9057d4748d0336,0xc941e45e140250022581,0xdd66b58354d34404df2d,0x8be268741603c0022d7f,0x9da715a15e9544e4f935,0x8bf25c7b174260022780,0x5bb6657857d434750237,0xc9e2185b1081a0020677,0x9ad6115a4e51f3e4d52e,0xa52306e12025001f174,0x9c3699765212d43cde31,0x8a61f8610f01b001fa78,0xda76496b5352a46cf932,0xcd2447114826001ed73,0x9ea71d9b5e1564d51238,0x8dd2b48c1582d0022a85,0x1f6789c4651745312340,0xccd2b08a168290023986,0x1e8701985f5574d51a3e,0xc9920c5f12c1b0022a84,0x5ae62d624f91b40ce02f,0x4ac2346a13428001df70],#[0x1d1681845993d42cf033,0xc42a87113c280020c7e,0x5bc669855ad584d5113b,0x8c1274781682d001ff77,0x5ec719a75f95c509253a,0xcb625c71118220022882,0x9d36a58a5dd4f4acff35,0xd52b08c1a836002177c,0x1f573d9a5bd554c9103c,0x4a4218601182e0023687,0x5cb6a58957133438e733,0xae2107013821002157c,0xdbd67d8259139428ee32,0xcb4230711081e0020075,0x61d795b36295a4b4fc37,0x8f23089518c2d0028996,0xa678da05779ac5f1554a,0xc0278690f822002cea5,0x21b809d56a56e50d1d3b,0x8d82e47c144300026c90,0xa3a805e06d989571213e,0xcb7250691382b0029a97,0x657899ef6d998581273a,0x8f0318851942e002b9a2,0x63b819d66c1925bd4c47,0x511388ad1e8350029f9e,0x6989ba3b855da6957d50,0x4b5270771602d002f9b4,0xa317d5cf685664dd0c36,0x8f33049217c2e0027492,0xe8b98e2e7d9c863d564c,0xce12ec7d1382c002ecac],#[0x6227f1d76d58e57d3c41,0xce02f88816c320027292,0xa5c875e570d9f5b13441,0xe9300861241b002bfa1,0xa618b60774da55dd4848,0xeb32c9312024002cda6,0x6778f603779ac5fd5c46,0xd10370ba21049002c8a4,0x68f98a1b7c5cb6716f4d,0xd42ac7212827002feb1,0x61e7c9d96b9705353041,0x4e62c8781241e0027d93,0x642861ea6b9835412840,0x8c0258711302e002a4a0,0xa3380dd76c5885291938,0xcdf2e4831a0280029599,0xe3c865df6b18956d3b43,0xe72e49719c330029b9c,0x248895f7745a95e94c46,0xd32a87e1b431002b69c,0x6237eddd6ad76545273f,0x4eb2e482154310029596,0xa81936267b9b55dd4f49,0x8d329c881a83d002ebad,0xe458b5ed6cd845914444,0x8fb2fc831782e0029b97,0xa648c20b739965c94e49,0x4d52e07d1001a002b8a2,0x639825e76bd905a53341,0xff32c9419431002a29c,0xa6b91607791b56315f4a,0xce52d88a14425002bea4],#[0xe5b8f610781b95d54347,0x8e12e09c1b42e0029d9d,0xa8b9a2277b5b967d6348,0x8e12a06e1502a002e0ae,0xe5f8b1f86e98b5653442,0x4ed2fca41bc3a002c1a0,0x28a95a1e7a9b26455a4b,0xcfe2e498198410030cb3,0x68d97a327d5c26596449,0x10e378af1d432002f0af,0xe618de0b775b5619684f,0xcc2b08f17832002bea4,0x644875fa72d8c57d353f,0x4dd2b87b150330028c97,0x25b8b9ee6c5885652e3f,0xfe3348818c2b002ada2,0x67b8fe237f1d3689684e,0xcee2c09519027002ebab,0x64d8be01761a15f94644,0xce32e49518439002b3a1,0x27b94e217adb45e14845,0x8ee2dc7f12425002bea8,0xe6d92e0e785bb639644a,0xcf5358a41a837002ada3,0x649885f6741b36295947,0xdd2947b15430002ac9b,0x639839d9671755552f40,0x4c825867108270028198,0xa187a5c26816e531203d,0xcfd2f48916c300027c93,0xa55885f877da85f94847,0x4f13049319c30002a7a1],#[0x64b881f3701925c94b46,0xd62c0751682b002c3a0,0x64d8ae087499f5dd4041,0x4e82d8841542b002b2a0,0xe738e60b7659d5b12f43,0xcfe3088515427002bda6,0xa4d879f67619d5c54447,0xd22cc821683a002aa9c,0x22f7e9d3685805551c3e,0xcda2c47f12c210028897,0x2718c601729a35dd3c43,0x4dc2e09217832002caa8,0xa247ddd96bd7b5793343,0xcf53008d178250028795,0xa528a5ff749b15f14c46,0x8d42a08616c25002ad9f,0x2257f9d5681795412a40,0x4e02ec8e140280028995,0xa51885ed6f1865712c42,0x8fd3089415c26002be9e,0x69297e387f1c26395e4c,0x4cd2b8901842e002e1ac,0x601775aa609544a10239,0xd62c07e15025002618a,0x22179db75f95a4d11d3d,0xca2b49119041002778f,0x20d7a9c267173545183c,0x8c42707a13c240025b8b,0xe1a7cdd069d76529293c,0xcdc2b48115c26002618e,0xe34819da6b97e5753241,0x88432131442c0028796],#[0x8a01104043c081c37c0e,0x2c002920858241d07082,0xa061a626030645238209,0x40821420502687446084,0x420b48203202083c2b0e,0xc3860890b080207d8507,0xc2343a245d050303110,0x42d0112411010601119,0x6c002e2784a301618002,0x1a39301c1da28501e110,0x6c7890544b8525898520,0x136c82561e27484942d1,0x428a42ca663236c52c33,0xe8b3f804745464b74b8e,0x7e5001966443ee3b0032,0xd01a37a9a7aaa913221e,0x2475146b8847cf0a7941,0x23237e5074066dfd167f,0xe215927e8b37884888fe,0x70fd4091bc67d5502467,0xe1a3347df40c93221aee,0xa2357f18b1ae668cce50,0xe27900cd1c7da9914e7c,0x19832a8ec0cdac6d065,0xa8511e7362f0478f6cb7,0x313d447a973960669fd9,0x893dd3119174fb9823a0,0x943d7e091c4895af8520,0x11c3873006593b9a9124,0x4b11e6215b2416fe520a,0xc0cf1d0bf1d40cf36ffb,0xa89318c25b23307c5604],#[0x1e1f8241c38821ba170b,0x850c0b8e0330f5f82661,0xc70347c2ca564e710418,0x66904e819e9f01073131,0x8bd7157236ebcfb9823e,0x32b44e08fbc11db8420c,0x2f11a3df40c801fe12a1,0x4e34109671fcd444cbe6,0x8ac280cc87eb04598841,0xd035e9448862eb0042d7,0x4946e74041b143868ca3,0x8a62c8dc2b3a03349dfe,0x4832e1e2d7234b6820f3,0x19c3b418c0f3f045a87e,0x483a0c3c68198b586e1b,0x42498871b748503333b6,0xfd30b88022006ba73452,0x3287f124c8cd66b64278,0x91f7ffd8500470f8b47d,0xb42959b9a7241ce119fb,0x55f8b9111aa6e6d0b196,0x49099d74d1ecbdc426d6,0x1c2b42b2cfc6c08b8e10,0x5434c7cac4655ebc988b,0x67f47cb85122bb46b803,0xfbf436e48d327822a12,0xbb3119bd3284cb5dd18f,0x3416c8e7ebf54b0479cf,0x168d706b33f65d832930,0xad1931c668c2890d20cf,0xc75b718641fc3ce8247,0x53236ef359e581c9491e],#[0xc8ff2387c30d2328ff18,0xd7f2115bf08012330e80,0x81ca10670f8ac09819f0,0x92cb52af94cd7e4469f9,0x26b81c8f3f5dc713e92c,0xb8e0cf1272d7e0f623ee,0xa331439651963da318c1,0x819a7359a332426a5d33,0xc4cb3f5faa4a23d659b5,0x3ae65079a34470cd5ae3,0x2e99c09987f1bcf69a89,0xeb34451ede74e3ae8955,0xa7f3c24523443a4b9849,0x718d5789203ef3d0aca9,0x8cef1160cbac03216063,0x8469fd47964475c47da8,0xc950fe5266501a542fd9,0x489fd7b56a24490c3a60,0x3e76e81d8d9877fa3340,0x385d850b868dfefd1902,0xc246637035af1b0b8d1a,0x293665b20e7cb2297d32,0xc63fb32e08e8d53405c,0x313d004c0fb88e0ca1da,0x39323d0dd7835ffef17b,0xeaa4661f983c288ebc6a,0xcc9f8ac280ccae0824f6,0x2e157fe22811bb81cb88,0xe7f0e2034b026936a9a0,0x27a890891e0c83e881a2,0x1bf480478f9588cb3406,0xac9df89101334bc02839]]
private def groupPage6 := limbs80 #[#[0x2a7e5511979afd07d941,0xb823c265962ca14fb803,0xbd2409a2dcb0648b8fc6,0xcc909ed063cb95e31547,0x9fc90640fc0631ebcc48,0xc2330754f8032a28e507,0x4697b832db9c5071e8b0,0x2543e5819f6fc8c22849,0x23535160844fd9aba32d,0x8e0cb1ccf26466d03dea,0xd7e49930bc1364660fb8,0x8e083f6ac890927c2440,0xbe4422863e041c181a3d,0xbbd29c302467676c9072,0x2c6b32d9347a7e261992,0x57f20190bd418c63bea2,0x9723357ec31197bdd032,0x5c63da88e5d3c4642b75,0xbac06d80d0b1f66008fb,0x7804cd31089bd21665ac,0x3d0d4f511e75c88458f5,0x1e99375e7dcc11cdf104,0xa72e8019a893cfe650f6,0xa9cf9446eeb869060670,0x57c1fb30402655766832,0xcaf0a782c09a2fa11aff,0x4655ff85a228e6ae6447,0x9d30cfbfa2cd11e35f26,0x7060678f684e8ca0d1e3,0x18fc4de64839124ef4a3,0xe7de68913ebfa5808489,0x10651fc7a0623a192b42],#[0xc8cdb1b85c2da895d0fa,0x985033a71808596adeb0,0x70866553f320eb47cdaa,0x3e9d648e5f76626068e9,0xc90650f7c4c196bd1888,0x795952999cbe8d4c950f,0xe698e4ade6635b80a257,0xe8801943ee090659eb80,0x3c0109a1787da0f2577,0x40cdd9ef55331b4e4838,0x4fa491987d8e22214ba7,0xb019159a4dffb5511d34,0x83d3399b8478e69193be,0x7b16f1cc49840255b760,0x80cdbae21d78cc2a3325,0x3016666eb40832b7cac2,0x1957abf182357b531e56,0x82381fae4e251c3e1869,0x340fa2068baca086fa5d,0x4f5cf36a23e7582e946a,0x5c8c5e30964ae9c8d033,0x9789832d24db284dd0fc,0x1a03f0e92ccfc66446a,0x95f97206066cf0a7941d,0xc8f32561652b226889ec,0x7a314aeecb1e489d28ac,0x5811f7951fa011cce11d,0x9c3025cc7955c8c97f23,0xe1311c3f62635fafe2d9,0x4f8032cafab9591e67f7,0xc1066708c3f8bd232875,0x4195bf686465179c16ba],#[0x86c8b0731e55723543f2,0xb965a80cfbfde3a08048,0xd2ee53b2858fbe81933e,0xa87dfbd5688f31f0fc08,0x7f6908b5f2e5a0e01801,0xb511db2d68565b738a0c,0xc0981995f4b8c20fe07b,0x49af45e0c85f05464ec3,0x96bb250765de8743f0aa,0xcd5e5cc4c719cbc23d01,0xca1978b8e03287f1a140,0x41b024f7b1b3d333d6c9,0xee56338c66c40a3ef1cf,0x68cea7f47114ce11a453,0x8d81983978432561036b,0x79a4cd3d97912329761,0x2d786d88181234c750fe,0xe68f0d117109d5c1783,0x5ef5a0cabdf51117b91e,0x20dbf33a032ef71c508d,0x30349724e78a8679039,0xd997e87eb0468e1f8330,0xb3c813db4e707de18e46,0xcbc918fbfdb66e4067a7,0xfc115b2e4a1066f74620,0x73c89073f9e7cb047987,0x3cb9b914a163c1329833,0xdcb907260671e3f12a4a,0x1238c47e908cbd6fa88a,0xdf105d12ef58cd17f674,0x1c9f8b30324c7ad2c194,0xc7bc1235e20901c1fe46],#[0xc62f104a175d6083dce0,0x3d53bbf37ca2b13fc044,0x641399e1163b7e28123,0xce1fb131e19f808b456f,0x2c43ae18299c35dd094a,0xfe09310d7ec0cb3943c2,0x19cc33f34e4839533a18,0x12e9935f884400430542,0x8d1668d1ff3cd00a2497,0xcce3dfc0b817092df023,0x185fca19fc9273fc4895,0xf0b84c9c7f5e0659084b,0xaf6b8dd2849dcd728c40,0xff37c083854d88621659,0xd4006825cff89859c0b4,0x344e2dd61bc12bbfe4c6,0xe029aca2626d8534850,0xe6c19a03c0b79233cfe8,0xa297204e8529d897da61,0xa3b4c3cd8332ece72b4c,0x7699a303407fc2a18309,0x3018aaf3759a804acfc,0x42ca5e61b139efcc6226,0x4b2400b386712b260699,0x9232efc1a75497ad293e,0x82457b1c4a4310931871,0xd2b0e89296598fffcbae,0xc7c6b8b912a593e9e400,0xd24d0ac7e4b1ea01267c,0x14fee1429692b049cfea,0xce745e09224e59a81e92,0xe2c846ef4e78b444685d],#[0x142ba4d8e05cf400cf38,0x5065b705650927afcc02,0x4405fd876c6c198bf65,0x7f9b549342b39f9fc987,0x7c1b901217e354930094,0x1b091c88d61acc74655c,0x7cf012c7a4bc611b39e6,0x48a781df0ca17c51e6ec,0x1907fec7b04ee0efae20,0xf45471f881e480919cb4,0x2a68e75cef8212a501c2,0x52f043a5c551be783574,0xde72cc19682a4ddf17f0,0xde2872659353325db064,0xc812f711f4a12104a62f,0x30ab58f75da4a8c42f30,0x2004e0cf3fac45e93092,0xa1f93323b6052e2682cf,0x289dc1c6a6cb97ae8050,0x3b503d237fe870001349,0xc2a12a7f8deb12648138,0xf68328ff434046da033c,0xf2d99162a95309210ab6,0x2f4241a67f988786c92a,0x56a380bc110c2707c794,0xf9481a133ef18f7a88d3,0x90653c08f8a18bd0e94d,0x3035b4a5eff07d8a034c,0x256ec6813c43e12c2fc9,0xdf84ef044ac7f45c4d40,0xfd1f635188d88d10136f,0x9d10a2f9cc13161f056],#[0x9bc11e68ff9800050fa6,0x333e91dc0c26144cd9af,0x1fb7c2f9100971f2a949,0xe62665cabb2e43e419a7,0x2e6699e6b87fad689165,0x5fcd24665973f68b5ed9,0x92539e2e919ae1ae4a1,0x153ea2fb091bf5fae417,0x171160268fc74b80b449,0x463ff984c450ac64573d,0xf193caaa4dcbf789e303,0xd5e0b5ca033936ca0efc,0x5570d55a880d1388e8a8,0x45d85469d33acfcda42,0x90127718fde035a407e3,0x6973242a7a4e93e7b1fb,0x4f34c26cfbf6ee23451d,0xfb5b26a402e6a9235552,0xe580326dff0f902a0565,0xdcf715b2f5c252f59c94,0xdcd81887489fd450c047,0x4af8949d7b216d99806a,0xca18ff5a0c0cfbfb570d,0x37be51088b2b435b8420,0x66602a93d7c280850ae9,0xa99a64a427587c120ce5,0xb02bde8fe008c3ffe02,0xd0a3b0ed8d8331fe43e4,0x89c0cc1da3ec06626f6c,0x741cd9b7c2ef6123d7f5,0xe0094b4d6e790a2537c7,0x2bbeaf399214eff9ca61],#[0x5d4573690944ff9928a4,0xf70ec0cd5d4145336ff,0x855a24d55e8d169c068e,0x640f0922aacad35e09dd,0x252e2f4698478f892c66,0x695d101327cf16c1d0e,0x16a732e2ceece3ff51e,0xfb17100663ecf92f8cf3,0x83f3f0a3922477ba064c,0x12612f7fa13d01f41009,0x941192d74679c7d57187,0x4e606485033ae93c5809,0x4052466bce24db0681d5,0x34e9ff7cac28913fff6e,0x12d79d033265c1493ad0,0x5c70a5f7ffe04959a059,0x3802fc7346128dff2287,0xe9140470cab85b2b40d3,0x82e94554f9bc638c46df,0x45c2f04da60ff5c1adf6,0xea2086a4f65956328d2e,0x32cd6cfd37d099a325e7,0x1ad4dac43a4c7406f065,0x7ac28d9abf4642db3868,0xa963fcd650032872641,0x4984a72418f587af4a57,0xb1d6ca049dff890600a2,0x1e21472cf20be18928ce,0xf41250423d73242a7a4d,0x340d57b108dbfd0d5e9,0xb7604ceb2477ff0a5103,0x2de6d203ff428290289a],#[0xca17f310b32524cfe46,0x139be43024e67a781df,0x5214933f184b8bfd2231,0xc3de8fc09d770b47f0a9,0x986a6cd3ffc6c410c804,0x2a7f8196bd1544033c70,0xa21008098bc0f7e008e9,0x24248e297fbd11e47e7e,0x208bae3e24246fe67585,0xda4272f50f1b4602fd8b,0x22b4b5e0cf3faa61493c,0x5a37e55d110935fca636,0x284b0b4688efc569360,0xbdc41087f9b549342b4f,0x43e008128a308593833e,0x24a70f2f090a400d517a,0x520ee48930ff5f858899,0x294bff0c5908ea0afc0b,0xf31f3b524891fde38141,0xfaa44d1fe1400050fa64,0x26c9eb03e7a8eb0f5e92,0x1b4f11e7f5fc04204b20,0x88ac593f3ed20714933a,0xfb4a817b7470235e661f,0x1f6eb42423a7203a159f,0xd4cf21025107ca1ccabb,0xc264fa95c8c6cd2478ff,0xe6a7f8523fa5cd0b9d3b,0x848db06730fc5180ae8b,0x3e04adfe1c5744249cc7,0x2ede0ffbb515afae1a14,0xfc788b223cd70ff5ad12],#[0x332451d696152153d270,0xd665f1dc03621813333d,0xab2e357997ad2513a704,0x9254ced9210ff4be5070,0xa52c6aa6a471f64eab84,0xea208099337e2223e426,0x7ccc266ea71ad46df1fe,0xbf6b123e812144ec405,0x7c85c62e2e3f92b25011,0xd8161efafc275da161c7,0xe0957e31469487fe1848,0x5ffc70995524aeb75825,0x6ca0668da8df947d1c4a,0x48cc3ff5a210c125b8f2,0xd81607cb8248ccc1e1d2,0xb0661fe808a8d1ef8ae4,0x37c033360480500fd031,0x602e138f555b19277ae,0xfc2f80cb2109b7e6264c,0x5276f9a6070124e4473e,0x48ef09b34233efbc1003,0x17e6277a9156ff8642ed,0x71885f6ac12f716e6dc9,0x1ef08a73faaa440a17ee,0x68f400350e685f58240d,0x1562dc6505f369b5f300,0x18256fff78826882809b,0x4670ff4c0265debe24c0,0xfe29120040989fe90cc5,0x22c9327afb0a10a34a5f,0x578cd48b848dfdeb5a5d,0xa7194596134fce76050a],#[0x9ab0f5f242b594c9fcf6,0xb6360ccb97ae80548fc9,0x806adfb87e498d94a6f8,0x3a7f78a2e591fa92459c,0xe4201926a7b8c80998f3,0x8b23a6b1e3c48dfdf39a,0x8de019edca89424eb806,0xbff487000134b134bee0,0xaf070232e7d516dd1496,0x78ea857632493c8b2144,0x4984ddf1e38e1435692d,0x444a7d8831fce1a6311c,0x347e3eed6511849337d7,0x5eb481acae867a99439,0x118ce6fd691b8b34fa3e,0x27d6795454f97e9f8d5f,0x133efe6be053d040261f,0x91c7a828701223f7a0a8,0x2192e8636bca1563a843,0x4f12412e1347cf5f53a7,0x40824b903ce1f23afe0d,0x2928feb9f6028d5cfece,0x2553a1b4ec499f545d18,0x15c04d9c7815811ecc7b,0xc2c2e42ea99252d617e9,0xfd847d492b2f88450a73,0x1703497c49cb394d114f,0x841eb62d0090df9dfd23,0x8ffbd617809925cb82fe,0x97d74e5f8092dc9413b2,0x7a38933d787cd421e496,0x6dffcd529119a373bd78],#[0xe6410d52a2f88836c809,0x1cd5be3a43163526731f,0x1fe127e24acff25080d0,0x5e930999e3cc2e06794b,0xcc35e30eb29491a6715e,0x4fc09ae824b6bd7086c0,0xffc3051172eea73de0cb,0x4a6566436c3f8120ffce,0x2971647c695d2233a61d,0xb09267c7001a8f670c93,0xffef264249213067eb0c,0x837c402565374ecb325a,0x852fbf67cb154ecba7c2,0xf66aead8c5e4b85a2b64,0x659b7f8b2ec1f1a82013,0x93233f9c451092df400c,0x464d73582127515f3660,0xd875119622f498482f65,0xf041509a5ff6e290033c,0x1ff26049b02bd8fa8c42,0xe309fc0fa4c23ef78c22,0x308549a7ff3bcf2154a2,0xe0c970965327ffc71148,0x4522c2a4b8db8d8e7e2f,0x377ffac47748b24bdf1c,0xf9323cfffccc414110a9,0xbc053be011a7a012844a,0x3410674ce95b8b35be61,0x9a0834b3725ce19e3a4e,0x344c981acfba9340136d,0x79d4fd008f04fd6ee50e,0x6bcede0295fe5218c123],#[0xc027b419cf27b220e59,0xbe7999ff61445cb8bb42,0xafe4a4a6ff3164426269,0x4402690fc4701520a398,0xf36d2268563ffbf06989,0x2a699fbde35c5c8952cf,0xbfd01378a945c34d15ba,0xf191a310094878b91578,0x4248f4b83574a53bc270,0xf1547123204c5fd28514,0x96797c5a4c0da59c32cc,0xd4c8a7fe4008eb4a10a3,0xca6e6c14c1ecd5d5c608,0x75f7375ea18d5a4d1a5a,0xb89c29eb0173a4570138,0xf8c8f400482e1275f6f6,0xe179c2f492171e14d475,0x14195084feaf64832cdd,0xba675d2280933cf3e227,0x82bc24dffdfc16f30638,0x2d23c83e79609331fa8b,0x3492c9304cc0c35c3065,0xccd14fe2766c0573ffc7,0x4bca3e357c49afef047b,0x5c01027aff8b0a06984a,0x679e88154adff178000a,0xb3f5a5cd5fa45701344c,0x42d02505bd2e6c297149,0x4b0620df994f12b7ceb0,0x8fed1e26b2bb3da3adf1,0x227118d5719262ba7164,0xdc1fd6c409278e4cc265],#[0xc44337b3c46650d19340,0x63833dfcfc0b2b365781,0xa257c62dfe401298ab28,0x57e55e0676ff78645901,0xefb08a77ff9144072c09,0xc00b85d89a10fa0b9186,0x2d4308515cf0f115530b,0x8bc7ff28dc38912f4454,0xfd4f4904fcdfc043f827,0xf4e023f674584669bbc4,0x34e4e70cb4478418f663,0x4ee7fa6232604a9310e8,0x924d338bde02a7dac7b0,0xfa49098512a7dfff0748,0xbd2e15754d22979e08cb,0x44ca5c5adb569c2d19e0,0x3809a7f554d842bb0e6,0x2ba0c40d53b6351185a1,0x24dfd29d66f8aa528ee,0xe93096e7026643f33931,0xdf16c04c19d47e7083c4,0x40c851bfffc4a8a94094,0xffeb02c3000220142fe6,0x92484c18bcc9ff9824e,0x2bd8a6ae501a57ff630b,0x461b4a9bbc05c1d0ea93,0x899a3228c268cf3d2e60,0xa79da9a3f80689df6dc7,0xfa3f4ac23094bd2ad150,0x2059bff8c28c0144026c,0xcefecd060cc7fff1502f,0x330923ffa7930130fa4],#[0xf06249f70c1c997fc585,0x4b5af8416a3a0a39764c,0x8f9d2a3258f2121f09f4,0xf0c1532b3cca2332faec,0xae82325ae8ce8633858,0x55307e00e453cfc1e463,0xc5e34409280819d70f11,0x5c053259de7f45172ad8,0x4b1ea081c2481e43fbf,0x75fb40c847d338af2e76,0xae7ae9661293c1717056,0x26715acb0b73c8512c74,0xd7ae99214bca697dcf83,0x1212b7ffdb17443025c1,0xfe742969c491ffcf47a2,0x2cb698214b8502dc1997,0x98cf3d102a931e100b24,0x961f94a04ca1da221066,0x54dce0a5a1f5e90ee060,0xb639cea8421b260fe72d,0x2859352d8152e94a47d3,0x734da0932670a2b9e1e1,0x672b3301521f95e68812,0x280cb2134e7f5d831856,0xa4eca5b691a32cf3ea34,0x1f24c949310fda320607,0x97bfd9af5a65512c7df,0x4e1242b84c99e761e26c,0xc461f5fd4082f1247c60,0x490993fcdc310242f461,0xf94e602816affeea8412,0x464e3c8b1d64b86a6739],#[0xf6c9f116567b7cc8f80a,0x637c3e8932af5891f023,0xc09199ab0d2a15cc4203,0xe0294d3ec8b20168acdb,0x28f33ef53e1008f6bced,0xbd7cb82a523e975957c,0x67a80741d0680a7f7a85,0x4cd9fdec8c9bbdc31424,0xc5bed0c319b4e4e1b17c,0xf8ca44ec4057ce609922,0x58cb9f62e200cd65f47e,0xd12666c749c720cfd965,0xad9331216be223267d8b,0xbf936d29b8465a04d347,0x48cf94ffd97ea48c3dc8,0x461fc6d474048cb43c64,0x85be759b00212e7a3db8,0x8d19f62f4499a8f1ef02,0x3d6221f624aa4d8bc724,0x794465dcd692f851247f,0x9904913faacc2140959c,0xc0b03cbc24ac0681ce7f,0xfe261c580befffc20959,0xf0e04820ebc3594ff9f4,0x24ae0d7a662dc099ba3c,0xb15c29eec098a86c6fb0,0xa747a82b84915fca6350,0xe92f8c124beb82037001,0x51288050c6f2f032a1f5,0x4122980342fff8c7ca08,0x5cae7ffc61d52802527e,0xb3f4ec2c1b8b2b9d1dcc],#[0xf84b0b466bfca7b26302,0x6bd19b7fae94a57c49a,0xb497c2893d8974ccb55e,0x89d22bf9306471334ee6,0x931a5fddb1333c91358f,0x26200404e9fc3c196a0a,0x6a2a22d28d5387ff2388,0xf140343116b0c7067905,0x9e08809bba309143db18,0xc0ae76a74d6481915cf4,0xbfd4b482594c8ff89926,0x23ed78c57e30804a9f8,0xda92d4272c034efea10e,0xe749965dad7ce6410d52,0x3b892d389446fd9a1477,0xa12e7c57d6149092bfe,0xe161e2c456758c79c7a0,0xe30ea50a939e30ac2833,0xc21d283f14a93690685f,0xc05001f0451668bf8325,0x8f86ba0b21220359d337,0x20fe497bfafa8924849,0xdf3fe2a47e0563ff9785,0xe10d009bbfa18747524,0xba32af533824246eb3d0,0xe82a04cc78d6c053055e,0x4add0af309fc6a00686f,0xeb8d46850197536feff5,0x9bb2dffaf3c05093717c,0x7231856659c51a2bae84,0x87d30ff9b098aca8bfa7,0x240e8a9c8d075eb82a42]]
private def groupPage7 := limbs80 #[#[0xb398ed34e0346fa21d79,0xff12a2a502577120c919,0x61b5652687a8a70336ff,0xc30e52b65ff08a23c748,0x809f29ff900bd6927f42,0xb45623c6dea0a8cd7933,0xd2adfeab8da3b4025cf0,0x84be28069b298793c81,0x97b1d6458d1e71d1107a,0xf3b2c812b7388c65e5e0,0x75652653f33b8b015ee8,0xd0246f1fa09176303e18,0x3aa61493cd3098abe247,0xfc2830330fcfa1f00409,0x93490a679d21e3204b6f,0xfe15092200a9ad2fae7e,0x2f6404cd207f2cc4e919,0x4a55fcef9894c0b2d4f,0x29fd07643017af3f5104,0xf212371e908f18249fff,0x1adc7105f4554d543f48,0x4d50b3df3fe2a47e0563,0xb34a5cd7e9f8025761f0,0x84961eab120cc0df00bc,0x494f1a80059b6388a44b,0xa64b8f2e232689d0a53c,0x2bf350626671f5438185,0x56bbfc12a204985ad921,0xa7aa0123417f67c197b2,0xcaac08e50e2158967ef4,0x5256f7c728aa28493675,0xf30b9a15f12679087a30],#[0x6d81987d62f497c2895b,0x68d15c93d98b6a68ef7a,0xfbfb100060979f609142,0xe1eb1bbc24605b2d1977,0xfb08eb521bf442b26675,0x641cd342fbd560a6a4ac,0xccbf898110243930b2e8,0x97e02e78f092a39e7ba8,0x3e4d2c234fe797ad8478,0x592c22ad05f00f0260cf,0xa6592334dae37742466c,0x9c82999b47a82b849159,0x419f387206048ecd25e,0x390b44fba8dc23d742c4,0x6397f879100961fd52a9,0xc7a8287012149fc0b51d,0x6ba51c201337c7535511,0x8ecc3f8788aa0495fcf2,0x723ec7ca4f0922b440e,0xb99eff93c000b0b071c0,0x337d21bff4a2d4fb4912,0x3e10b259c7f99926c0ae,0x3348c7caf16124c8ae75,0xa3286c40f24f4edd72a8,0x45665fe30eb29481d2ce,0x26b7ae1aba201a5a5d5f,0xb6aca4b43ea230962079,0x6bf231ea178b092c6cc1,0x341d91252f2cf404ef09,0xbc92d7c0507e2012a71e,0xa1c00a128d356f0bf48c,0x661fd74380146e84c9c9],#[0x78aa38da1025f69879b0,0x3ebd98b1c0934c86709e,0x4bc3fca4617c7985c0d0,0x684f9434a0a64d03d4,0xb564c1ebe23217f443b2,0x288d1d7456455cc44bfb,0x8249dd3bd88b95cc7ff0,0x953f18128091b5f4bb81,0x59ea5eb461f97e20dc80,0xb8cb9b604bd1ee796648,0x46d2a1c2807ced4ddfea,0xa6db7c60a06880fffd01,0x105e0404d314b46b4833,0xce39788b947e09324657,0x9523c1ab26c868c38a33,0x8400d4b811c028e3d7bc,0xe7f9a86ec0ac3d7f4089,0x754641f943b892c92134,0x6d18fffc1e42e6a29727,0xf887c600f90da60fb4ff,0x8379785b3cf0b69c479f,0xc0cdad52184ab68b64ce,0x85a6c9e39e5c2387f28d,0x2329da10655a23933724,0x8ebc7a1b6a3ce8d70b61,0x746e97ea8acb3af76730,0xe11bb8f8d26a6b44d216,0x345acf405d612ccbe60c,0x38b2cedb8df3348ef5ae,0x57493b7aaacb4905186,0x93c9aa9950a8352ebd0b,0x40e95f885c244ec0c9d1],#[0x9f4ed6a66a2fc2780953,0x87dc3ab0661f176548f5,0x1238b1c1a16609799832,0x24f461e1a0cd3ae46e66,0xb0e188a16719efbeb68c,0x37ae8352ab8eba0e419e,0x2f5a476c10bd420ceb9a,0xead9575e85d5d242fd3c,0xf9242af054e05c25270b,0x24a1bfeefd9244eab1bb,0x715f306708ea3e46216c,0xd18d04274ccee43a5eb6,0xe032cc3cd63a39091169,0x38bec191ac5]]
def g63D8 := groupedPages #[groupPage3,groupPage4,groupPage5,groupPage6,groupPage7]
private def groupPage8 := limbs80 #[#[0x894001c011042c07,0xc020200c12000000400,0x2c0a000380400000500c,0xb80c0002008140217008,0x5000030500c20000,0x4000001800010301c0a0,0x41002800000f0009c1,0x412000481800000081,0xc824040f02034001e01,0x6804a40001000001d,0x100c010942203008a408,0x38020900808100005014,0x20000e00020080007020,0xa018001c000001c02120,0xa0f01000000200808060,0x40012024081e0400c0,0x80c08070381c00050000,0x84c00060002c100410,0x2018bc0411008600412,0x7403030000a0c0581c02,0x3c0800168000c0100054,0x10281401028080a11060,0x7000041004010e80c000,0x417020c8400003808040,0x1a00000102a15028242,0x8e400060000000010000,0x300c22040301c0a0003,0x9000140827000040004,0x81100848020001008ea,0x240c0006844120a00004,0x10020500810a82b080,0x200400110003410200],#[0x30002c1a0206004180,0x404161780436a1038080,0x8000a041d00c00081281,0x180404020000c020a04,0x7008001806008005400,0x100a0002c14000000c00,0x48800050000e0015808,0x3820080d14004021f000,0x70e17818190001400010,0xe01010bc0006030380e4,0x41a29198481207088002,0xd8000603000090880,0x1383802021e8780e0b2f,0x15008401c1000000063e,0x3a100513406060081c04,0xc0000a0082c26020700c,0x183410440606c6e15050,0x180406020093c06090,0xa011380c1e08158000c1,0x4180d0301c8605168180,0x2450030703008004185,0x402000806c3ca300,0x6e03004020c028bc1847,0xe08018003008000cc40,0x140a12071c462050403c,0x60001a13000040e010d0,0x385c08070001804020,0xf1b008000503000420,0x61a0400000010109c0,0xe030181c08290a80,0x3054280d00030041900,0x1747810e001568140405],#[0x10000000c1007098280c,0xac08030080c041609860,0xb0000a24000801808211,0x5001582a02000884a013,0x70980000132222c281,0xc1e011e0d0001d010280,0x83c025f25800aea32ea1,0x303c000000004180205,0x2f230043c0601808522e,0x2a390b0bc44560d2b84e,0x4020b338083e1000800,0xa81c0601080000035028,0xe0982800111414c00000,0x45e0d8001213408a40a2,0x808098a1a00401028380,0xd00017150040604020a,0xc87d840007124040000,0x23010080e05008282600,0x60020981c1c01018796e,0x286e1b04000000634060,0x68180004010140011030,0x304824461901930001f0,0x20d000840c0003830043,0x410018041602008501,0x1904018000344000001,0x8001e876cbde00,0xcc1c819a01e000000000,0x91751531451090bd000c,0x78a20126325321b20518,0x533beff8a8440000442,0x2200200000000480105,0x451090bf000cd41e619a],#[0x325321d2051891751531,0x6e08080c80200830a126,0x1209176fed3,0xce220019c02600200,0x518d17515514710d0bf,0x104000038126325321d2,0x900100edefe7ff020011,0x619c02c0020000000100,0x1551491110c1000ce822,0x2526325321d20518d177,0x5ebfec80000422500204,0x20000000000810001ff,0x30c1002cee24e19c0300,0x21d20518f17715714911,0x84800c0501201263255,0x20080800cbf7bf7f00,0xf627419c032002000000,0xf1771571491170c5004c,0x31008126325521d20518,0x21fd6f9fa60290000000,0x3600200000000002000,0x491190c5004d0229819c,0x325521f20518f1771591,0xf201080040427020c126,0x1200001f6d75f,0x4d062c019e03a00200,0x71911771591491190c5,0x4004278126325521f2,0x1dbe5e7ae209000,0x419e03c0040000000000,0x15b14b1190c7004d102e,0x126325521f207191177],#[0xeffdff00800200145410,0x40000000002020000ff,0x90c7006d1e30219e0400,0x21f20719117715b14b11,0xc0002862c31263255,0x10040002ffffffff04,0x2832c19e044006000000,0x517715b14b1190c7008d,0xc00326325521f20719,0x1fd47f3de0298180041,0x4600600000000000200,0x4b1190cb00ad3435219e,0x325521f20919917715b1,0x7f0000200110c0220126,0x117ff9bb,0xcd3e37419e05000600,0x919b17715b14b1190cb,0x83001004326325521f2,0x8000011dfebfde200140,0xa19e0500060000000001,0x15b14b1190cf00cd4639,0x8726325521f20919d177,0xf577a741008202202083,0x60000001000008000ff,0x90cf00ed4c3c01a20520,0x21f2091a117715b14b11,0xd900620e009009263255,0x4080401bbaeffdc40,0x563de1a2054006000000,0x117915b14b1190d3012d,0x866b26525521f2091a,0x1f23effee02c1041050],#[0x6000600000000400000,0x4d1190d3016d603fe1a2,0x52552212091a317915b1,0x9f400082453c00400526,0x800400bff559,0x18d6e41c1a206800600,0xb1a317915b14d1190d5,0x10004012652552212,0x15fbbcf7e004060,0xa1a40700060000000000,0x15b14d11b0d7018d7843,0x126525522120b1a5179,0xf3ff3e084c80c0291010,0x600000000040000c1f7,0xb0d701ad7c4661a40740,0x22120b1a517915b14d11,0x2500401850243265255,0x80210118d9fbfea00,0x8448e1a6078006000000,0x717915f14d11b0d701ed,0x8026c126525522120b1a,0x882efb46ee8000340800,0x7c00600000000000201,0x4d11d0d701ed924a81a6,0x525522520b1a917915f1,0xbc000c00000160100926,0xcfffff,0x1ed984c21a808000600,0xd1ab17915f14d11f0d9,0x40400201012652552272,0x201001f7dff316080800,0xa1a80800060000000080],#[0x15f14d11f0d9022da24e,0x4126525522720d1ab179,0xfdfffea00200000e90d1,0x60000000080000001d7,0x10d9024da850e1a80840,0x22720d1af17915f14d12,0x2800c340a0281265255,0x20000001d7ff7ff628,0xba5341a8088008000000,0xf17915f14d1210d9024d,0x42062126525522920d1a,0x17ffffffe8000220400,0x8e00800000000000420,0x4d1210db026dc455e1a8,0x525522920d1af17b15f1,0x7a05a600842128875126,0x1400005ff3fff,0x28dcc58c1a809000800,0xd1b117b15f14d1210dd,0x2c0540100126525522b2,0x40001affffff2500000,0xa1a80940080000000000,0x16114d1230df02eddc5a,0xe526525722b20d1b117b,0xffff7e80000480040825,0x8000000000000080096,0x30df030de45d61a809c0,0x22b20d1b317b16114d12,0x80800214019041265257,0x80041f77fd9fe08,0xf25f61aa09c008000000,0x517b16114d1230e1032d],#[0xc01c0126525722b20d1b,0x1ffdddffe0022240012,0xa000800000000000000,0x4d1230e3034dfa61c1aa,0x525722b20f1b717b1611,0x6e040550100806842326,0x8000040041fbfe9e,0x34e066481aa0a600800,0xf1b717b16114d1230e5,0x21c000903526525722b2,0x8000f0f47d9f0a0200,0x81aa0ae0080000000110,0x16114d1230e5036e1266,0xd26725922b20f1b917b,0xdfa7de2420420200c006,0x80000000000006001df,0x30e5036e1c6841ac0b40,0x22b20f1bb17d16114f12,0x3b5401000021267259,0x10004001ffffd6aa40,0x266a61ac0b8008000000,0xd17d16314f1230e703ae,0x84802326725922b20f1b,0x8dffff3fe00000c0010,0xc400800000000000800,0x4f1230e7040e2a6cc1ac,0x725922b20f1c117d1631,0xea000220140811025126,0x220013f9fde,0x40e366f41ac0c800800,0xf1c517d16314f1230e7,0x100414882126725922b2],#[0x8010fb5e7ed2040184,0x81ae0ca0080000000004,0x16514f1230e7040e4071,0x126725922d20f1c517d,0xff7ffe0101040022e014,0xa0000000101000601ff,0x30e7042e4673a1ae0cc0,0x22f20f1c518116514f12,0x104c0841267259,0x1000097ffef7708,0x527621ae0cc00a000000,0x918116514f1230e7044e,0x90181126725b23120f1c,0x2726cff9a1500120010,0xd000a00000000001810,0x4f1230e7044e5e7861ae,0x725b23120f1cb1811651,0xf6828001004108000126,0x288000114cdd86,0x46e627a01ae0d400c00,0xf1cf1811651511230e9,0x10008022126725d2312,0x1915f5ffa000080,0xc1ae0da00e0000000000,0x1651511250e9046e667b,0x6326725d23320f1d3181,0xdfffdcc0881022820809,0xe0000000000a90001ff,0x50e9046e6e7e01ae0dc0,0x23320f1d318116515112,0x220200222e4926725d,0x3ed63eddc08],#[0x768061b20dc00e000000,0x51811651511270eb04ae,0xa0300526725f23520f1d,0x41ffebffaf0811045160,0xdc00e00000000000404,0x511270ed04ce828221b4,0x725f23520f1d51811671,0xff804108012c14002126,0x4014801ff1fff,0x50e908441b40e000e00,0xf1d51811691511290ef,0x104000080126725f2372,0x800001f73ffddac0c102,0x81b40e200e0000000000,0x1691511290f1052e9a86,0x2126725f23b2111d7181,0xdff7bc28024002830054,0xe0000000000000001df,0x90f3058e9c8921b40e60,0x23b2111d718116b15112,0x1101200602300126725f,0x20404001d7aebd9e08,0xa88b61b40ea00e000000,0x718116b1511290f505ce,0x12408526725f23b2111d,0x81ff96ffee0061005098,0xf200e00000000002800,0x5112f0f505eeb28d81b4,0x725f23b2111d718116b1,0xee080047159000212526,0x20000409d7fffe,0x60ec08fc1b40f800e00],#[0x131d718116d1511310f5,0x606003448726725f23b2,0x101ff5efb9e80a800,0x1b60fc00e0000000000,0x16d1511330f7064eca92,0x8926725f23d2131d9181,0xdffbfa40300434610900,0x120000000008000421bf,0x30f7068ed89401b61040,0x23d2131db18116d15113,0x300609b572899326725f,0x601ffeffff600,0xe49641b8108012000000,0xd18116f1511330f706ce,0x2011126725f23f2131d,0x41fffff7fe0400182009,0x10a01200000000000000,0x511330f906cf0097e1ba,0x725f2432131dd18116f1,0x7e000440020028600926,0x104000881fb9bfb,0x72f0a9aa1ba10c01200,0x131df18116f1511330f9,0xc01045a8b26725f2432,0x810001cf7f1ef6348160,0x1ba10e0140000000002,0x16f1511370fb074f109d,0x6126725f2432131e3181,0x6daefe00825002050028,0x140000000000000101ff,0x70fb078f1e9ea1be1140,0x2452131e518117115113],#[0x40108a2419212926725f,0x10000401efbbeff00a,0x2aa101be11c014000000,0x51811711511390fb07af,0x4120526725f2452131e,0x1136ff3fbe8000e05000,0x12201400000000020000,0x5113b0fb080f3aa2a1c0,0x725f2452131e71811711,0xfe4004a0614051014326,0x61fddb7f,0x82f42a4e1c012a01400,0x131e918117115113b0fb,0x4c002100126725f2472,0x7e3bbffbe040408,0x21c012e0140000000000,0x17115113b0fd084f4ea7,0xd2672612492131e9181,0xfbff3c00400001000200,0x140000000020001001f0,0xb0fd086f56a981c01320,0x24b2131eb18117115113,0x802880d000621267261,0x1fff7ff7e00,0x5eaba1c0132014000000,0xf18117115113b0fd088f,0x4610526726124b2131e,0x1fff7fefe0012410801,0x13601400000000000009,0x5113b0ff08af68ae81c0,0x726124b2131ef1811711,0xfee01880012000000126],#[0x41b7f700,0x90f70b121c013601400,0x131f118317115113b101,0x854c00110126726124b2,0x20111fd3cbc5e130002,0x21c013c0140000000001,0x17115113b103094f72b3,0x8126726124b2131f3183,0x61a2de7a140b00445880,0x14000000004010300085,0xd103098f7cb4c1c01420,0x24d2131f518317115313,0x190140c1001267261,0x800112fefbff400,0x84b5e1c0150016000000,0x718717115313f10309af,0x81526726124d2131f,0x81fd3deefe0404024084,0x15001800000000402002,0x5313f10309ef8ab821c0,0x726124f2151f71871711,0xac02188001404c212126,0x1fdef7b,0xa2f92ba01c015001800,0x151fd18717115313f105,0x16200a0012672612512,0x1feafd6fe015009,0x21c01560180000000100,0x17115313f1070a2fa0bc,0x612672612512151fd187,0xfff8ee620007110cd904,0x1a0000000002042001bd],#[0xf1070a2fa8bec1c01600,0x2512171fd18717115313,0x4012000024e801267261,0x201f7bffffe0c,0xbcc061c216801a000000,0x118717315313f1070a4f,0x402aa526726125121720,0x1fffcbe6e0003819030,0x16c01a00000000000048,0x5313f1070a8fc8c301c2,0x72612532172011871731,0x95100cbc6aa123700926,0x4002001fbfb67,0xaafd6c521c417401a00,0x19201187173153141107,0x30304180072672612532,0x1dfefeade201015,0x81c818001a0000000020,0x1731531431070b2fe4c6,0x9267263253219201187,0xfebfec000101b0200863,0x1a0000000060000003ef,0x31070b4ff0c8e1c818a0,0x25321920118917315314,0x1888c605050101267263,0x8020ffe6613a20,0xf8cb21c818e01c000000,0x31891731531451090b8f,0x341bb726726325321b20,0xed207580052c4f7c1d0a,0xa2e558bbff31f7594802,0x3f6607b58b0981e05da3],#[0xb9ca08564481e5839754,0xc8696321de22e173aeef,0x421f2cf7a3e00d0b04a0,0x3be720837008e66be2ad,0x4a324b508ee0188a4000,0x5c04da83c88196440649,0x178600788e258415800,0xaedb7b44566af28134f8,0x1826d26a1d5cdfb37662,0xb423c0170041aa0ba695,0x225e8c01b698d288e414,0x952b8010bc05c58582c8,0xc283c1fec0024343fb44,0x601de00c4cc001c147dc,0xebe06ef0ce5313fc11e7,0x88e5ec4877a458273219,0x580e0561748e11a40509,0xce2871550d1a311e50b3,0x83ac81be80830a1608c3,0x5aea18f2170406ff6ae6,0x4b681129a75e58d12e4e,0xd1a80180901f144059fa,0xe3b0196181c4b0551c62,0x3a079a5f7ff4b86d0030,0x5981100c8200180c0235,0xcb8ac465e52c8edac4c6,0x4726ea482b4ddcfc902b,0x151aaaf197924e8db76f,0x1918ebe98f5c2a3dec66,0xb33c2258b788be0ff71b,0x71f32de20b1c79cf3eb2,0xdf3d3630147c636bb4e8],#[0x32084c18140c1610edad,0xb6253e3b8b2417230f80,0x2dcf59ea9291e933a2,0xa135406210f60d083f0e,0x42779616016d3e47f40,0x1c61188159ad802c58,0xb8262e44a500a67cf91e,0xb471a3a8fc597663f31b,0x31373b8f4c87794691d,0xc01ed37f99761d561a1b,0x60fa6cc2e1009c03057,0x2dde10cbec1f2731011a,0x44d04e0b378c20bb0a85,0x88d80b41243dec2e211f,0x943ca0cfe0056b40b004,0x571421e0000d2cb40a00,0xca11b075bdf04fe41c1,0x21b5dcd4a2500c004107,0xa90c2594cfba4d4d181e,0xf9c961c1c0400fe2223d,0xa22cd542a72a90427847,0xc610604240f5d758d0a0,0x235e60f8e8080cad96bf,0x4c7aa8aed7ec24778e80,0x60eea1c112ff1f0e94f3,0x59317ce353c5979cc2c0,0x9321ce8be63fe7e6ac15,0xd1e361e0abaf6c94f417,0xb856421acd8d3ce0b180,0x25f6dd9c720f261bdfbd,0x39090d2bc13cde200b8,0x4717ec97ea18eaa2efc1]]
private def groupPage9 := limbs80 #[#[0x856ad2715a593cabd556,0x38e66c2c850d173c1b60,0xe5c04ebe0f04c2a6df30,0x182621094c1d4a0d4228,0x56f689f4d1518be2f087,0x14d5e559fcc6891a67b6,0x484e1e4b7e09c41f9c3d,0x351892f3d2851c993db0,0xc91571f6f0ad9ede5d00,0x7437c0c81000c03168f5,0xd1395e8fd40034e607c0,0xe428f9012eaaf8d8614c,0xb6d9c1345070d3eebfb0,0xf88c5e08000014cfcde5,0xd0001866bf0563962403,0xc00c020a560e1413c057,0xe38c400332cb035e9078,0x3300c01676c364c06746,0x85f100d70123c26a3dfb,0xfcfd2453228eb082c05f,0x2c9a4352b91c04418c88,0xf1af8e8a98b15ff08c83,0x68f996cce6d708a66a8d,0x4be827c0d40b25f0b109,0xad3b4d1839038966688b,0xf08520adb851dfc227a,0x278aba97eb6d0951a777,0x6bb236b679954f9c0b8,0x86e53a0d02a095593bf4,0x7006b9866c46fa081]]
def g63H8 := groupedPages #[groupPage8,groupPage9]
private def groupPage10 := limbs80 #[#[0x104400c8310c02108010,0x4405414c521445010c42,0x88620841324c53048520,0xcc730c8720c42328c630,0xd4b51d4343d0b41d0332,0xefdfbf7efef6eebe7f53,0x6504d611826513fffbf7,0x640c46448a6228664002,0x6408d610ce61189620c6,0x620c66464e610c065406,0x639496228265802650ca,0x64091609126371163051,0x621e6103d262011602d2,0x43852626d26031262192,0x6471163222321526261b,0x630a5316d26269360450,0x639e04209160111631d1,0x605d1608116179064452,0x632a0425db401a120051,0x647d3637516031160351,0x63311618d262352646d0,0x638d2638e5313d2620d1,0x6331160690623d1633d1,0x61366313d063450644d2,0x60652646916115064751,0x63711610526449263552,0x32165611926465263951,0x624d2603536149161961,0x6455264951632e7314d0,0x60392632e731651610d2,0x601d260151639e232411,0x30612640516375262112],#[0x626506249063751600ab,0x602d2623d2600d264112,0x615116169864492605d2,0x633d1612126039b41853,0x42091607d163193633d0,0x636db42892642eb304a3,0x622d26319f30629300d1,0x64292636d06451262a12,0x60751608d16099264352,0x432506441b6449160151,0x60012644d2633906461b,0x60892608d2627d060512,0x62865311266119161811,0x4319064151609dd300d2,0x6205161312631e232718,0x62391613926021163652,0x6171161291619d264612,0x60812602526305262891,0x635926471263991601d2,0x62251638536051163611,0x61592620926309263592,0x63893637126459262291,0x64790645536345161911,0x64691606633269161552,0x60092641526011263750,0x632a1327126499263212,0x61852607d163012649d2,0x633d2625516021260691,0x61a1160a126299262792,0x63992630116161161191,0x635d26311263893604d1,0x63412648184389160251],#[0x647926475e3049064493,0x63393635526215264310,0x6371063412630d0643d1,0x60a126291163552647d0,0x61252643d264a12645d2,0x43512635d26075361411,0x535af3106f217af528af,0x424ae6372c643ee326ef,0x323ec439ef306ef527ac,0x6076e607ef4106c5386e,0x5372c3266f303ef534ee,0x324ed3042c5162f531af,0x5366c436ec306ec4366d,0x217ad3266c3196f3006f,0x5392c624ae6356e304ac,0x217ac4376c433ef5042c,0x5442c210ed6306c535ae,0x4306e6092f5186f5062c,0x6372f4042e627ac326ec,0x4062c5462f536ec430ad,0x5376c435ed326ee327ef,0x2056c5366f429ae6456f,0x624ec3172f4342f5382d,0x5306e328af439ad323ec,0x417af515ac531ac604ef,0x4362c5256f4262e6022f,0x535ec5086c4266f530af,0x623ef5172d6026f3002f,0x5186e327ae6386e647ec,0x321ee320ed6292d3142c,0x524ef404ac4302c536ee,0x627ee3072f432ac436ac],#[0x6322e6462c426ed3162d,0x5266d6106f5086d6126e,0x432ec511af537ec5172c,0x424af538ad3056e617af,0x328ac535ef5262d327ef,0x627ad6376d305ac5072d,0x606af536ad312af4296d,0x312ad631af5056f4396e,0x537ae3162c526ef2162e,0x327af505af329ae306ef,0x4056d203ed314ac5456d,0x530ed617ad6022f5106f,0x303ef405af3262c545af,0x501af5072d3196f5326e,0x606ad3072f212ac4352f,0x4356e646ac2162e3196d,0x6192e631af624ac5472f,0x506ef4256d3186c544ee,0x5466f435af4072e6286c,0x633ee2162c5106e3186c,0x3142d6162f214ac633ef,0x4372e3212f424ec4202f,0x2056f5286e657ef2196f,0x506ef324ad303ef434ef,0x6556c427af4142c527ef,0x6172d315af4366f3162e,0x212ae315af4266c5476d,0x406ef4162d6262e329ac,0x5006c546ef5256d6386f,0x654ef439ef2186c4072f,0x517af3296f403ee6586c,0x312af3042f624ee3262f],#[0x426ec5406c527ae311af,0x4006e2196d6226d3172f,0x6126f4376e3172f3062f,0x4162c520ec540ad607ee,0x524ee6162c2186d6322c,0x4342e6472d616ad6192f,0x545ee2186f5312c439ac,0x314ae322ae6172c517ac,0x433ee206ee6016f436ef,0x3256c507af5266d6076f,0x423ef412af3196f414af,0x644af206ee322ed6186f,0x5342c432ec406ef430ac,0x3262c510ec2196e6562f,0x6262f3186f435ed6256c,0x203ed3106d6286f304ae,0x547ef5362f4196c432ae,0x3296f324ef526ef3266c,0x4362f507ad300ef203ee,0x6306f4002c546ae6256c,0x547ae6186f500ec211ae,0x3286f315ae627ec434ac,0x5342e657ac4396e6376e,0x437ef400ef326ef407ac,0x3256f604ef415ac540ef,0x206ed6092f3172c324ae,0x4302f3056f437af323ec,0x305ad6356f4172c203ef,0x5362f623ee616ad324af,0x4262f2002f430ec3162c,0x527ec5212c3286e324ec,0x4356f5142f3072e6526f],#[0x317ac407ae6292c435ac,0x6016d2162e6106f5386d,0x3072c4172e3042d3286d,0x4316c4372f5162e317ac,0x5262f538ee310ec434ef,0x6226f5392e6026f5356c,0x6476c5042f520ee647ae,0x210ec324ef3202f328ae,0x321ec303ee650ec5412f,0x2186c5356c538ec3186f,0x210ef4312c644ef4212d,0x6416c323ec534ec315ae,0x3202c311af4346d620ee,0x5212d211ac5376f410ee,0x410ee640ef422ac417af,0x6406d3202f434ac328ac,0x320ee314ac404ac321ee,0x322ae620ec538ad321ed,0x6116d610ed2002d3006f,0x3042d210ec5482d217ad,0x3286e6592c4142f510ec,0x4346f4306d3212f4382f,0x321ae324ad3002e212ac,0x4212f427ee610ee3106f,0x3142f427af436ae6116c,0x415ae651af420ef4202c,0x3256d310ee3266e321ac,0x5286c5372c4296f521ec,0x521af4332c5452f533ec,0x5302c5306c530ac533ec,0x5302f531ec523ec653ef,0x531ef5316c503ec536ac],#[0x5202f503ec528af5352c,0x521ef5322c5352c543ec,0x329ac412ac4332c329ac,0x322ac5322c322ef5002d,0x322ec5402f523ec4196c,0x5416c3296c429ad322ad,0x422af5202c422ed3296c,0x321ac314af614ad3256c,0x4256c4106e6122c614ac,0x423ef511ae611ac424ec,0x306ec427ec3106c3202c,0x311ae214ac214ac420ed,0x414ad3262c403ef211ad,0x6122c312af311ad611ac,0x63052609df300e71056d,0x604e2620e6610d260893,0x6355260916650d9640d0,0x300d06406320595650d0,0x1001263852609906256a,0x640d6650632005262965,0x63055650526059264010,0x640e5610d060461620d0,0x321ae6219260612640da,0x3142c515af422ec4042d,0x521ad621af322ed206ee,0x212ad614ac5142e211af,0x5446c524ad2196d214ad,0x504ad624ac514ac504ac,0x524ae624af514ac544af,0x5346e654ac654ae614af,0x534ae644af534ac5346f,0x1ef02bd038b02d80002c],#[0xd2584421c7338c40142e,0x439e3337e66690ba394f,0xb211517a7f64afe8b710,0x4705cd8259e331645e00,0x41c3f28348fd05e6c3a7,0x4a6a81ccdd796b323d63,0x20a812002cbb5739a9f7,0x3388ce2d8a222c781804,0x70b4120015a50d284510,0x556132440f2340aa1f45,0xa0f419001fd75dbe64d7,0xd465023b8cb2c09f1f05,0x811425001cf6bd8b5953,0x55b54a480fd35cb422c6,0xb1001a002167cdd36bd9,0x456532430f233cb12506,0x11c21002247f9d86ad8,0x557533444ef354ab2146,0xf1181c0020b795c46ad8,0x851d2d43cf4364b02246,0xf0e413001ff76dbb6296,0x756946494fe35cb22285,0x20f81d001ff769b26517,0xf59941460ee32cae21c6,0x415c270020e7adc46a98,0xd5d95d4d9103b0c82b88,0x611020002217f1e06f99,0x55a546490fc35cb02306,0x81482a0022b809d96c99,0x65c14e4c50a3b0c527c7,0xd14c260022e815e56f99,0x15dd50494fe388bb28c7],#[0x6100140022c825f0721a,0x55893f460fc35cb32486,0xd12c25002197b9d16ad8,0x95c1494b10437cb82386,0xd130270022b82de07119,0xa5d54a48d01370be25c6,0x21782a0022c81dea6fd9,0x66857a559233c4d22b48,0x111c240027a9662d7d9d,0x26215d4dd153a0be24c7,0x90e412002588ae0676db,0x55351e418e62fc961bc4,0x1120240020e775bc6717,0x45f5554b90136cb422c6,0x516428002297f9df715a,0xf6456b53d2b418cc2b48,0x91042a002578ba0575db,0x25c94e4a8ff34cab2186,0x61382a0023c839e37099,0x165d6f50d1a3acc92a87,0xd1382f00240875f8759b,0x95f5554bd03350ab2106,0x21282300220815e971da,0x58139460e32f4a11fc6,0x816029002037a1c66a18,0x35e1594bd0837cba2807,0x21642700224821e070da,0x75f1634cd093acc224c7,0x9118290023d86df9745a,0x95ed4e464f8354ad22c6,0xd1182a0024a861ec735a,0x5639614dd0a38cb62486],#[0x610820002468aa02785b,0xd5ed554dd163bcb82206,0x113c2300234835e87199,0x67579519283f4ce2707,0x2168300026e92a257d5c,0x868d7452933414d02b88,0x1382b002538a20d7c1c,0x25c14b494ff348ac2587,0xf16c2b0022c81ddf6d99,0x61d66501143b4c22787,0xf124260024e881f7755b,0x65f9564b50b378b12206,0x51442b0022f831e7715a,0xa5d1534acf937cbc2547,0xe110240024986dea6f99,0xc58d47470f6358b82446,0x1098120023a849f06ed8,0x258930414de2eca41bc4,0xb14c2c0020f789c36998,0x65c5564dd103b4ca2607,0xd138240021e809d56f19,0x5cd4d4bd0939cb42487,0x8142418222a82dea719a,0xd10a3041c13020c840c0,0xac65086c4e083081010,0x86878b40470021205060,0xa1515211c2c408c4888b,0x12c7c622230745a1d302,0x81094362c56189d18905,0xeb0245b81e251f524437,0x5a7804b8710f7529137,0x2064466f4051d72446ec],#[0x49bf59111b7014a6463f,0x8f1a2453b810fc043ce0,0x5fb844005679cf020115,0xefc10022b7d7f7f0e007,0xa2ff128279da91b11e,0xcf4098e73497a293e1f2,0x3e73e2000567be10139c,0x11416e2e78054792826,0xec3b84a8a88ee64a7c3e,0xc00537ce88414d85f109,0x206297e132129406b933,0xc000a956ea206404ddbc,0xfc30832fd2d1000b2bb9,0xbe752828be750002a7ed,0x28f6dc5cf2291ce2a246,0xf8800b7eff18017b2368,0xd70c2293f7f0204153ff,0x51b1c388f6fe8190155c,0x477c8c80a6f7f080002c,0xd0151fd80127ce5e3045,0xbf20514df2a10149cd25,0xb7f90822e164f0604b2c,0x87d778c000b2fdc20082,0x143fd18028be7422045,0xd7e02677ff100197365,0x69e6685822b7eefc3403,0xaffbfe08030ebf608401,0x7eef834034caf0794025,0xfaef14000b6bf610022b,0x7a2f648a946c6388c7ff,0xc2d77fd304197b5426b,0x422fafb30002b3eff87],#[0x39e0488a4b37264287f9,0xfd284420b1fbaf79820d,0x537e0c257effc30032,0xf510273ebf2810a6ef89,0xb38f2e5800b17f34420f,0x98863fd900f777e08102,0xec223fdedc740317bdf4,0x18319e6004efc368217e,0x503e34118ecce4450ff6,0x6667904e79ef9850002d,0x667fe4100551cd990055,0xf93042cfbbe1c10dc328,0xe610151e5bd4d922b7ef,0xff0400d3ba817015df19,0xffc6102d7bff48086bfe,0xbedd845ddda0a3030051,0x154f481e5224acaaf88a,0x3808abf42c046bfe1001,0xdeff120143ff86102f79,0x51e72d4022bbdfe20114,0xcc006b7e7bc20a7f8640,0x810a0fdfc081054fddfb,0xd00a3dff0204155f3fa,0x283ce5a81057db46323f,0x2aad78cca011716cdcf8,0x1ecff3bcf0871f5f8c20,0xffc80002b7e7dbf0e407,0x47b3f9020297f98020c,0x3c8a9fbff4c00bdf8022,0xfcec0811efc184b6f419,0x273e1f020a27888808cb,0x7d204da32cd1c483afa0],#[0x1456dc580159f8508144,0x50153f6fe1801a7c3e04,0x9680a4fafc190155ddc2,0xee00149e728500959f5f,0x77814082d77fd580175b,0xb7fd7d1201a7bea02739,0xe3efa000577cee14202,0x159fbbe2000577c0a50a,0x187fe40001553ef42c4,0x432bf610082b7ffef10,0xf6c0061ef8404ef9fbe6,0x9666720142fc360297f7,0x5defb880015bf7fc9801,0x28a8f8f3049cfbda8001,0xaeffccfc285151f7de10,0xafdfe771e00d8cf98808,0xafdff060069ff6ee3841,0xbea287efff104177ba84,0x4c0240163febf0700c8a,0x702080577e481608aefe,0x791000adf7f70e2061fe,0x25f7f5600597c4098f7,0xfede2c01a11014dfbff0,0xfdfc4006bdfdc38c16fd,0x3e1e400297f78e304bdf,0x54bfd841073e05082a,0x601153f7f8c10abdfc0a,0xfe0c10c7bff87102eb7c,0xf8d3c601163fc2202dfb,0xecfc224054ffffe0082c,0x24ffc822287effc3802,0x4575ca7bec4953ffc71],#[0x402577fc20022abf84a8,0x385400ae4ee748a1f7a1,0x665800b0bcf42810597e,0x85df060458bfd80127ec,0xa5f3a11082c29e50a29b,0x50fefe5c00b5fdfd3001,0xe3fffdc58032e4cf10,0xf380187338513af7fe90,0xdccc022a9de19511d7ed,0xf85080aae9e740c2159c,0xfb801002c2ef2a041599,0x55bc1048c487fa64049d,0xebfeb70f80a6ddcb4dda,0xb6671328b3bf2da1c602,0x9ce4b6949fd6e60302b3,0xff5181660176f84b1450,0xce3c0c3feda12030e5a1,0xca030172c7401384855b,0x85e12f585e4246bfff55,0x2ef990b830249e9a5ec0,0x816fd51de560d087888b,0x902cde681128ebb79f2,0xe302c810d7311cedc43,0x28856f87d0d9f0713d21,0xaee2bbee0ca4a0ccf91f,0x32e577de4d5300acbd55,0xc72bdeab2c04a499c285,0x7c2c33cab7b945ba184d,0x2cd235f0b808a7e4aa00,0x7bc4652b285bf2224a12,0xc8a4c126f249d001593b,0x77a0851aed1023e15ce3],#[0x567e45204598ba377094,0x460c3e5b0e535e680aee,0x24a85ba5481c47585e42,0x8f7fd5728b8accf7a70,0xbe84d7b52e62533c2a55,0x614cb02b158f12c31262,0xe0c7b02937cc0ddc5377,0x92f081493fa8730b0acf,0x428670aef1fcaa64a6df,0x728ad62192fe417a4f59,0x1dcb6ff1e42871558a60,0x4cb6f4d0e600aca6940a,0x48e4298d0255ccf8ea45,0xbe79942235d57303016,0xbe2197293fd4cf042fd2,0xa5065c9c4d7e59e2a514,0x886fd910ae11693fcec0,0x23155cfb70a92058a14e,0x68547fc823322a3ecfb1,0xf43bfbaad664a8b3a98,0x90e3c3931aec330e154f,0x57a3e01b44925eb93c02,0xdf8816730917fa43e954,0x469e152a847a4d627929,0x473ec0da1c602e0b03dc,0x42bbf89744a85935206c,0xaefc653038a8f9e28793,0x4935e1f3a0cbcef15960,0xef660010b04c1ae9c120,0x8571f161814c835cc469,0x67fa2d9a02bbe69cbc8c,0x31d60074917f74644dc5],#[0xcc4709c7ecc14c48fe4a,0x6282a3ef8a2d292040b3,0xd00a61c2c1f00e891d66,0x4b3f46411979745231f3,0x2f3c150fe42409483648,0x1615dcfb5854c02d33a5,0xe547df22ce145f761e2,0x64e53bed3e90566f1983,0x5e1a0c93c0a04a3dc466,0xda9488889c9472ead84f,0x1ba64b4be2184ca8ce0b,0x9045276179c9d7b6688d,0x1e2f80ba86822cf2b11f,0x259e29503c62a31c1ff0,0xa6561815d030be141fe8,0x13acc65128f2be08a2de,0x16cc42b1911ab91cbad6,0x33a46bee2190b545d7e5,0xec8fe25dc3c032949d89,0xa6e60c7bf070f8554a11,0xc7c0f80ce1547ba3b292,0x235e2190c302c53437a8,0xc8b232b5ed932345033c,0x1e7c10c84795139453a1,0xff9b8024a85b3fda1d89,0x720596ec5c7288dd3135,0x24d3ff8042747a7e6e04,0x2d8587f400598965f764,0xcd112447e8885fdf302,0xff805de422d84858bc2e,0xa0aee523cb52323bf61d,0xa8104c4b07c0f72a23dd]]
private def groupPage11 := limbs80 #[#[0x940c56a3447a439493df,0x9602461e01528f4876f4,0x796a8a6f1cb50150f9a0,0x2f02b83fe0ac03d0185a,0x9497b2da44d45c7d9ee0,0x30b0ac752df231b84d4c,0x468ff7ec024a4b0fc287,0x628bbcc1a2302481c649,0x4928448dc2e011291383,0x19f1c7c1cab69c281f3c,0xd30a60955b39561ca9fe,0x44f02b277ba03f4a9635,0x3ac2bdd68c54c917fd46,0x6e2a52b1c88c463f8654,0x18657568a1c0b2c879fb,0x2f32918183651c639791,0xf883c0ac95332c29a4e0,0x567c6dcba02f20c03cfc,0xde4d6f4cf827b7465664,0xde5128f5f19577155f14,0xe1eb71288f3185871588,0x775a31532419dc8fb0a0,0x13615de32f412952b711,0xc12056792976145264f3,0xbaf8d395c8a42e8ff8e,0xbcce02678557b03a80cb,0x7dcda5850b0b84762446,0x2d03eae048e778db0e51,0xf0712f05967e79da1a24,0xb063dca2a1985ce521fe,0x7d32068e577faccb09cf,0x57308244fb0a2908927e],#[0xeacc93cfc85c14024aea,0x7c0b2fb9a5b044a8617e,0x1e2789541b8443ce1751,0xe2c293c9ff889c0567d2,0x1bb84ebc2e6ac890776d,0x63ded81cd0573d09d128,0x4a0ce60530e15e9e4184,0x1d6155f1c6ee4f1bd89e,0x877c4c099491fa487c42,0xba4c1948acfe49523585,0x4575bac38ab7fc8b6847,0xe5701e2124cd7cb3a09,0x94a0da1101dcb0ec2b4c,0x1f1bf6442b80181e17cb,0x8c5187092af332133615,0x114cd911cef5dea8a678,0xb3fb32824c574de78585,0x4fb1101862507d611d82,0xae67e8a08c775758715,0x7285a0bb6ba393b75e24,0x96163f1667af43037c5c,0x47fa7238474587e18601,0xa0e48fe11457c905325,0xa60d8917b3025bff88e4,0x287165bfdb6d014b17c6,0xd934aa0ce51847bd665c,0x6f0959b6021971650cd9,0xb42bb8a4370c3939d611,0xfa579b8e507d6e06728b,0xc4a81816d7f30c8060a2,0xfa073a0c83e530b0aafa,0x4df320b2c2abcd0e5277],#[0xc1c4b2353c9809cd949,0x849c30ecb61ca978f409,0x1e741867894f614dbb3b,0x871a59bdf4038c0927b6,0x63b3c07a92a0b8fdecb6,0x617c28267ecd828af11,0x18c8f60aa93b7bc462ba,0xd14092bc46b73c27a052,0x3e12a38ccb9c8a77bb13,0x1f1229507f15139a5f94,0x152971f910c032c2dbfc,0x38aa9e70f227bb99e769,0xd8467d6e16a8acef5bac,0x970c38b09b94932aca1d,0x84b4e4efe80ae12e2778,0xf31d8b949fd6a0728364,0x1e11545cbfe04518120c,0x5cf5f059c1996145f34e,0x81595cd8727af774930e,0x1afe47c4042d3fe9e20d,0x7503c62a39f3c07f7115,0x17451be115715d972120,0x898718228f7bf3d4112a,0x11a7730998249fc13322,0xe1552847153e88a37895,0x2a8d9d131b0ef380523,0x5a88c4d4e04e7f9f8039,0xdc8213491fe9f3c0a9ca,0xcdd8497f5900024cb675,0xcf7ec082682e5667af02,0x3def827f0513e52aca35,0x88169d981e7851593659],#[0xe0a4da82e1d2bb9a5e2c,0xb5782349157311ef0713,0x1bb0916]]
def g63D9 := groupedPages #[groupPage10,groupPage11]
private def groupPage12 := limbs80 #[#[0xf0603030000002c0a01,0xa0104040601010212,0x5011200000200040300,0x12091501050301000001,0x405020002010c030013,0x4040108000207,0xe071f020b00030902,0x2041a05010200060100,0x2012302060001020016,0x6111506050200020503,0x1909030f0105000e00,0xf0901000002000b0000,0x4000000010206080403,0xf0800031603000d0600,0x10000000000a01000600,0x1050004090100000902,0x8040803010203001312,0x1010101020109000601,0x5150502000904010600,0x202030a000205090100,0x3060100000209060106,0x60000000205000b01,0x1f0108140e0101020102,0x1a04020000170517,0x10202000202030002,0x2050605050b14000501,0x17000101000105010204,0x104040102010b0c0c00,0xb0a0029031c00060200,0xb05120e060000020c02,0x1400310120001160500,0x1f07060c000000000a0b],#[0x3301050a000000030400,0xb0d04060528010411,0x570509010002000c0300,0x8030b000f0110000500,0x1100200041501490408,0xc020003060202040000,0x1060702060002000200,0x7050004000808000002,0x40a0109010007000b01,0x1041004070001200205,0x2f030103000300012201,0x50f041f010000000102,0x3010002051a03000b04,0x500032d00000b02000a,0x111b0c04000b0f1e0300,0xb000702080003020103,0x310d0101230303000002,0x4000301001045030002,0x1002603090103000100,0x201090203040202090b,0x13020600000000080400,0x20301090003010a1317,0x3141902010205080502,0x70b010f00000c170a00,0xf0a0a0d0001050401,0x1b06021e0901010301,0x80320080b00000003,0x180711040e0d230002,0x1e011b15061616160106,0x17040700021000150000,0xc0018002c4900040503,0xb041e2e1b050a0a000d],#[0x2e150204020500070832,0x70036040b02050d0101,0x3040d001103020a0802,0x70b0005050910001f03,0x808000302221001181b,0x1020000120531000300,0x30017041e0111200403,0x15200405000d00001402,0x204000006001d0003,0x8000007170309320616,0x80000100410000f2100,0x6220702010103670f,0x8420205020600450000,0x12905010b0300031601,0xa17000800080a090000,0x20204040d01071c0100,0x23f0006000300090b00,0x4031306070101040a0a,0x10c240601211e1b,0x1902081700021008002e,0x1030e2b000e03080e01,0x50107001634002b0c07,0x70f0809001305020103,0x8370005200503031d,0x25030406000e04060501,0x1407110b010e2e0408,0x1120e24000600090113,0x60a030100003e020001,0x1525000400020d2a2808,0x60200071c000a0000,0x806180900020b2c1d,0x50a021f00050e0a06],#[0xe0622180b0202450304,0x4040722000013001603,0x41eb42b000b050f1504,0x5180608060405013e,0x2050800243a0f081000,0x1c160a01001504140201,0xa1d1a05041b05110114,0x91b040003010f350001,0x73e0481070a280f0207,0x380301070b340f050600,0x1607120d0003131000,0x41b074f020f18220d04,0x272501002a0601000024,0x808010220124f0b0204,0xe95d913c06282c000210,0x73db69b6bdb89f3f26,0x1000000200040634e20,0xf28ed87e63e5335021a8,0xdbbbb4ca3e94e94c9438,0xd99ade370cc3c96c92c3,0x86647e80d77d7d5e60,0x1ac01500008100000042,0x438f28ee882643536502,0x2c3ebbdb4da4095194c9,0xc9feb397cd90cc4c96c9,0x119320045b93246eeb1c,0x5021b401600000280200,0x4c9438f28ee884648539,0x7c93c3ebbdb4fa439539,0xdb7d8ae9dafeccdcc4c9,0x2001260000732685467f,0x53a5021bd01600001000],#[0x5494c9438f28ee88564e,0x4c98c93c40bbfb50a479,0x83ed8fdefe7c229079cc,0x40310082b0000492b80c,0x65153d5021c801800101,0x4895694c9438f28ee886,0x3cc5c98c93c41bc2b51a,0x9aedb71bfb538e8cf19e,0x1000050000e5122d39f3,0x88665653f5021d201c00,0x53a4995894c9448f28ee,0x5a16cc6c99c93c44bc2b,0xa9d1903c32ec4fe39bf9,0xc0010002008081c0900c,0x8ee88765c5415021d901,0xc3b56a4e95b94c9448f3,0x48aa10dcc7c99c93c45b,0x98154600f8c50ea8e6a4,0x10210010200001000002,0x8f38ee88765e5455021e,0x46bc5b56a5295d94c944,0xb601894532cc7c9ac93c,0x400500b5d62584901f60,0x21e50240010000484025,0x9448f58ee88966354750,0x93c48bc5b57a5395e94c,0xb4ebea0096234cc7c9ac,0x8101100281a3180a208,0x85021ea0240010000809,0x94c9448f58ee88966b54,0x9ac93c4abc5b57a56961,0xb1acadaebea74008cc8c],#[0x8882702808e23efa7,0xf5485031f00250020080,0x96394c9448f58ee88966,0xc9c9bc93c4bbc6b58a57,0x541eddeff061e93f253c,0x20000412450011334d6,0x967754b5041f20270020,0xa5a96494d9448f58ee88,0xcbccbc9bc93c4bbc8b59,0x1d32442c7f1c9f286ae4,0x2002000002010d24024,0xe88b67c54c5041fb02a0,0xb5ba5e96494d9448f68e,0x450bbccbc9cc93c4cbc8,0x90a007099e1043867e31,0x2c002000008020810208,0x88ee88c68054d5042030,0xbc9b5da5f96594d9448f,0x87141592cccc9cc93c4c,0x11021c289342913c87ba,0x902e002000000081e00,0x48f98ee88d6805505042,0xc4cbcab5ea6196694d94,0xb2ed1068b46ccdc9dc93,0x43004804c3824e099fea,0x521002f002210000000,0xd9448fa8ee88d6845505,0xc93c4cbccb5fa6396794,0xa32d77d6810d07ccdc9e,0x808a004006da22600646,0x5250521a032002000002,0xa94d9448fa8ee88d6885],#[0xc9ec93c4dbccb61a6396,0xd0a8f79cf549fa109cce,0x241084017c004cc,0x8b553505221035002800,0x496c94d9448fa8ee88e6,0xccec9ec93c4fbcfb61a6,0x80c49eae394f12a96883,0x1000c250c000ca53,0x8f691555505228038002,0x1a6596e94d9448fc8ee8,0xc10ccec9ec93c50bd0b6,0xa40fb596dd124fe0190d,0x20000008002005b015,0xee88f69555750523003c,0x1b62a6597294d9448fd8,0xed8beeccec9fc93c50bd,0x84b540c9a158ad60436f,0x4200200000000a7408b,0xfd8ee89069b558506234,0xbd1b62a6897694d9448,0x38e1927abcceca0c93c5,0x8d188bd1ad29ab2633c7,0x23d043003000000000d0,0x449008ee89069e559506,0x3c50bd1b62a7097794d9,0xbfc6a12cbf68cceca0c9,0x88058082ce058b8d35f,0x50624304700302000000,0x4d9449018ee8926a255b,0xc93c50bd1b63a7597a9,0xb3f9ffc46d6abe8cceca,0xd4104003d5f1761b4],#[0x55e50824d04e00300000,0x7d94d9449018ee8926a4,0xeca1c93c50bd3b63a769,0xa952c8e269a9d91340cc,0xd53058037d2bc,0x6aa56150825605100300,0x7798294d9449018ee894,0xccceca1c93c50bd5b63a,0xfa99ab002f297f015fb0,0x400000000005d2900d05,0x8956b156350925905300,0x63a7998694d9449048ee,0x1188cceca1c93c50bd6b,0x42881178c0f502f782dd,0x40040004080002880108,0x8ee8986b556550925e05,0xd7b63a7e98894d944904,0x4664e22cceca1c93c50b,0x240d147a041e63bfc23f,0x305900408000800d1420,0x9048ee8986b956650926,0x51bd8b63a8298894d944,0x99080bece3ccfca1c93c,0xe142048ce5536e8c8ebd,0x926a05d0040000008018,0x9449058ee8986bd56750,0x93c52bdbb63a8498a94d,0xfbed67b1f48f9cd0ca1c,0xc1805089e5a0f2a3de7,0xa50927105e0040000000,0x94d9449058ef8986c356,0xa1c93c52bdcb64a8698e],#[0xfdd65f5c9ea76ec7cd1c,0x8000030c00a0636d32a8,0x956c50927c0610048000,0x98f94d9449068ef8986c,0xd1ca1c93c52bdeb66a89,0xa74f4f7ddf101cc978c,0x4002001024900048b5b,0x96ce56f5092860640060,0xa8b99194d9449068ef89,0x6cd2ca1c93c53bdfb67,0xa21a21a851eea68db377,0x6000000080582030105,0xf8996d657150a28d0690,0xb68a8c99294d9449078e,0x8209ecd2ca2c93c54be0,0x47c802c9684cc0c28f0d,0x6d006000001003010088,0x88ef8996d857350a2960,0xbe1b68a9099394d94490,0x7dab71c7cd2ca2c93c55,0xd269634ade8ebc7d679,0x9a06f006000000000438,0x49098ef89a6da57750b2,0xc56be1b69a9499394d94,0xc81b024fb61cd2ca2c93,0xc482100de4b774bec34,0xb2a4072006200000000,0xd94490c8ef89b6df57a5,0xc93c56be1b6ba9799594,0x5edebdb000de23cd2ca2,0xa02904e0a1820,0x8050d2a9076006000010],#[0x694d94490c8ef89b6e25,0xca2c93c56be1b6da9a99,0x3f0afd1a240e44180cd3,0x21181001315b904,0xe858250d2af079006000,0xa99694d94490d8ef89b6,0xcd4ca2c93c56be3b6da9,0xbda8e4fffef88db14190,0x1008401008001a082142,0x9b6ed58350e2b607b006,0xa9a99994d94490d8ef8,0x8e8cd4ca2c93c56be3b7,0x37000c58cc1dfc101f1,0x600000000003400044,0xef89c6f458550e2bc07e,0x3b73a9a99994d94590e8,0x2ea217cd6ca3c93c57be,0x4fcd384216e6fa555a,0x8400600000000090d30,0xe8ef89d6f558750e2c3,0x7be4b74a9b99a94d9459,0x4a4636801cd6ca3c93c5,0x10411e4130f314671633,0x2cb08500600000000241,0x4590e8ef89e6fa58950e,0x3c57be6b75a9d99c94d9,0x265e72804628cd6ca3c9,0x941c5020bc1d50304be5,0x50e2cf08700601000000,0x4d94590e8ef89e6fe58c,0x3c93c57be8b77a9f99d9,0x7bb91f96a6ad004cd6ca],#[0x2004044c8304ed4892cf,0x58d50e2d508d00620010,0xa294d94590e8ef89e701,0x6ca4c93c57be8b78aa29,0x66bfebd75dfd072fa1cd,0x104000480122400825be,0x70658f50e2d909300600,0xa39a494d94690f8ef89f,0x2cd7ca5c93c58beab79a,0xcb4cef45acf7d0309196,0x7002000100a8d2082bd9,0x8a070a59250f2e109900,0x7aaa49a494d9469108ef,0xe082cd7ca6c93c59bedb,0x10b91739a1bbef7f500a,0xf00701000000400800b0,0x8ef8a171359450f2e409,0xeeb7aaa59a994d946912,0x1128548cd7ca7c93c5ab,0x8cb3160accb91c2c14c2,0x90a40070010000020200,0x9148ef8a171c5955102e,0x5abefb7caa59a994d946,0xe721a1a60fcd7ca8c93c,0x1208002997f84db8e5,0x12eb0a80070002000020,0x9469148ef8a371e59651,0x94c5abf1b7caa69ae94d,0xef5d0e87d45bacd7ca8c,0xc001882ed611ec0e3ff,0x75122f10ad0070000000,0x94d9469158ef8a672359],#[0xa8c94c5bbf1b7caa89af,0x7c839577b0c12e2ccd7c,0x4684228ec4afe6a,0x75975122fa0b20071200,0x9b194d9469168ef8a972,0xd7ca8c94c5bbf1b7daad,0x380beb1625aa7eb21d2c,0x4000188600180993a4,0xb72e59a5122fd0b50070,0xab09b394d9469168f08a,0x95cd8ca8c94c5cbf2b7e,0xf121b33d818f6eb650ae,0x7080a00008230009182,0x8ab73259d5123060b60,0xb7fab29b394d9469178f,0x9630dcd8ca8c94c5ebf4,0xb00841204971261d687,0xb9007000000488000400,0x78f08ab73759f51230e0,0xbf4b7fab89b494d94691,0x5d8af388cd8ca9c94c60,0x60802261c8167ddf1b1f,0x180bc007041200000220,0x69178f08ab7375a25143,0xc61bf4b7fab99b594d94,0xfc726820fb9cd9ca9c94,0x2020930862e995ebea8b,0x143220be007000000000,0xd9469198f08ab73e5a35,0xc94c61bf4b7faba9b794,0xe99d201e788020cdbcaa,0x82181c1400391d1520b7],#[0xa45153280c1007004200,0x794d94691a8f08ac7465,0xcaac94c61bf7b7fabc9b,0xade5d5aa90044b908cdb,0x20000a88100dcbc612,0x4a5a451532c0c4007000,0xe9b894d94691a8f08ad7,0xcdccaac94c64bf9b81ab,0x4223f1315228fcb1902b,0x400100868080008e00,0xaf7525a551632f0c8007,0x2abf9ba94d94691b8f08,0xedecdccabc94c64bf9b8,0x2c2316000c8fe910002,0x700000000002002121,0xf08b07545a85163370c9,0xab82ac09bb94d94691d8,0xb46101cdccabc94c66bf,0x80d271a290cfcfb7114a,0xcc00700020000127060,0x1d8f08b07575ab51633c,0x6bfbb82ac29bc94d9469,0x514519c10cdccabc94c6,0x300002c0341416398c1,0x3410d100780000000008,0x4691e8f08b175c5ab516,0x4c66bfdb83ac49be94d9,0xfb11a60159d0cdccacc9,0xc0830480d58347403b60,0x5163470d400700000000,0x4d94691e8f08b375e5ac,0xcc94c67bfdb83ac59c09],#[0x6050439648405b1cdcca,0x20000504208805be6,0x5ae51634c0da00700000,0xc494d94691f8f08b5761,0xccacc94c67bfdb83ac79,0xf5f65dc65ad6e2949bcd,0x802400235255cb777,0x7625b05183500dc00701,0xc89c594d94691f8f08b7,0x8cdccacc94c67bffb83a,0x21d6711687edc117876e,0x70004000008221723083,0x8ba7685b35193550de00,0x83acb9c994d94691f8f0,0x8a94cddcacc94c69c01b,0xa33185187a104f0cda10,0xf0070000000403318090,0x8f08bb76a5b451935d0d,0x4b83acc9ce94e94691f,0xec8498fcddcacc94c6ac,0x1c09a170d406d67c40ff,0x20e00070100002088980,0x9208f08bb76e5b551936,0x6ac06b83ace9d194e946,0xa589a17fc0cdecacc94c,0x20001488b0d45561512f,0x936b0e20070000002a08,0x9469238f08bb7725b851,0x94c6bc07b83ad09d394e,0x88f2c7398002fcdecadc,0xa0a28091a0e2a99bfff,0xd51a3720e50070000040],#[0x94e9469238f08bc7745b,0xaec94c6dc07b84ad29d4,0x29d8cf570f00dd4acdec,0x5000073000042778023c,0x75be51b37a0e80070000,0x9d794e9469238f08bd77,0xdecafc94c6dc09b87ad3,0xf21fbc17f25da371d24c,0x801011760da011e36,0xd77c5bf51c3810ea0070,0xad59d894e9469238f08b,0x42cdfcafc95c6dc0ab89,0x22a087f25dd8dd60bf78,0x70840000005022000b5,0x18be7815bf51c3870eb0,0xb8bad79d894e9469258f,0x57d6ccdfcafc95c6fc0f,0x82861448a5597bdf679a,0xee008820883002840440,0x58f18bf7875c151c3900,0xc0fb8bad99da94e94692,0x3aa2bcc6cdfcb0c95c70,0xaa879c90da8e77efb56,0x9b0f2008000010002849,0x69258f18c07895c251c3,0xc74c10b8badd9db94e94,0xf0f76e043f1ce0cb1c95,0x20040a0824668f8dce63,0x1c3a30f8008080000002,0xe9479258f18c078c5c55,0xc95c74c12b8dadf9de94,0x485fd55e0a1035ce1cb1],#[0x1a02a0248002e7a404,0xc751c3ab0fc008200000,0xe94e9479268f18c17925,0xcb2c95c74c12b8dae39d,0xdfce07bd92a9828c4ce1,0x10400020a0364061a436,0x975c751d3b00ff009008,0x59e094e9479298f18c17,0xce1cb2c95c75c13b8dae,0x870ced4cfa2fd3c87d0,0x2000322e00102b2e,0xc179b5c851d3b5106009,0xfae89e294e9479298f18,0x8f3ce2cb2c95c77c14b8,0x3354f8d6b45f3eec0583,0x900080000902404997,0xf18c279d5ca51d3be10a,0x5b90aec9e394e94792a8,0x268006ce2cb2c95c78c1,0x9a2db10eafebb56b15,0x10c00940900001002580,0x2c8f18c37a55cc51d3c4,0x8c16b92aed9e694e9479,0xb814b5bdfce2cb2c96c7,0x10942d412df48c2a667,0x3c711100900000000204,0x4792c8f18c47ad5ce51d,0x6c7ac18b93aee9e694e9,0x16ff4090414fce2cb4c9,0x80221004c166320079c,0x51d3cf11200900000000,0x4e94792d8f18c57b25d2]]
private def groupPage13 := limbs80 #[#[0x4c96c7ac19b93af19e79,0x97beb9fd499ccb9ce2cb,0x20001420a58075367,0x5d451d3d511900902040,0xea94e94792d8f18c67b6,0x2cb4c96c7ac19b93af29,0x9ee7d27f7d4d959363ce,0x1001892880028f2dee,0x7bb5d751d3df11e00910,0xf49eb94e94792d8f18c8,0xace2cb4c96c7cc19b94a,0xd946c33c62fc7700fe95,0x9002200804405900c46c,0x8ca7c35d951e3e512100,0x95af79ed94e94792d8f1,0xac21ce4cb4c96c7dc1ab,0x6b47d28bdeba7ffd85fe,0x400b0000000001470001,0x8f18cb7c75da51f3eb12,0x1bb96afb9ef94e94792d,0x75ae2a8ce5cb5c96c7ec,0x5e6c4038521cee128c,0x512900b0800000004d00,0x92d8f18cb7cf5db5213f,0x7ec1db96afe9f094e947,0xbaa4471718ce5cb5c96c,0x6f148104ef36644799,0x13fd12900b4000000001,0x94792e8f18cb7d25e052,0x96c7fc1eb97aff9f294e,0x5eb97af0e2bb0ce5cb5c,0x4080800222a3290638d9],#[0x152140412a00b0000000,0x94e94792e8f18cc7d55e,0xb6c96c7fc20b98b019f6,0xbbdd2ae58c6c7c03ce5c,0x9420344106233d6a6,0x85e452440e12d00b0000,0x9f694e94792f8f18cc7d,0xe5cb7c96c7fc21b99b02,0x3100687eff3abb0b122c,0x2b380100ab6f5,0xc7de5e752541513100c0,0xb049f894e94792f8f28c,0x4ce6cb7c96c80c21b9b,0x944714ec7bf9db8dab00,0xc000100400114020029,0x28cc7e45e952641a1370,0xb9bb089f994e9479308f,0xbd1ffce6cb7c96c80c23,0x14f8c10b3fbd2616cb25,0x4100c00100000020580a,0x8f28cd7e85eb52741f1,0xc23b9cb099fb94e94793,0xeeb85224ce7cb8c96c80,0x2024d2422f463dd9dfdf,0x2914200c000000098022,0x79328f28cd7ec5ef5284,0xc80c25b9cb0b9fc94e94,0xbf9ee914799ce8cb8c96,0x100404bd86046402876,0x2843114700c00000010f,0xe9479348f28ce7f35f15,0xc96c80c26b9cb0c9fe94],#[0x9f7eff6bfb013cce8cba,0x44060200e66617c0e9,0xf352943914900c000000,0x94e9479368f28cf7f75,0xcbac96c80c26b9cb0fa0,0x17ca441ae2d68a04fce9,0x12000001524ce16,0xfc5f752944314e00c800,0xfa0194e9479368f28d07,0xce9cbac96c80c28b9eb0,0xc206bdfa7e9992df981c,0x2000000002058002c425,0xd08015fc52944a15000d,0xfb10a0294e9479368f28,0xdccce9cbac96c81c28b9,0x489b86ebe5fe6f258c21,0xd0040400100080810c,0xf28d18055fd52a454156,0x8b9fb13a0394e9479378,0x7e4167ce9cbbc96c81c2,0x4c8591085f636f6932e2,0x15b00e000a0000049000,0x378f28d280c60252a459,0x2c28ba0b14a0394e9489,0x807c521e3ceacbcc96c8,0x208827ca21cb5b1f042,0x46215c00e00000004208,0x489378f28d381060452a,0x6c82c28ba0b17a0694e9,0xb0de0ff520e2ceccbcc9,0x1c610740386f976a239a,0x52a46516100e00100080],#[0x4e9489378f28d581260a,0xcc96c83c28ba1b1aa079,0xaf12111f3b42442ceccb,0x20852000008d6504537,0x60c52a46916300e00000,0xb94e9489388f28d6818,0xecbcc96c83c29ba1b1ea,0xc190635a20900158ce,0x800000500290165,0x81d61052a47016400e00,0x20a0c94e9489388f28d6,0x4ceecbcc96c84c2aba1b,0x492b3abf63437cb92028,0xe0000000000009000689,0x8d682061152c47416800,0xa1b20a0d94e9489388f2,0x1487cefcbcc96c84c2bb,0x100707a2316b1b353164,0xc00e0020800000050402,0x8f28d982661452c47916,0x2bba2b20a0e94e948938,0xab7c240cefcbcc96c84c,0x1076045a10e9b7bc408,0xf16f00e0030000836004,0x9388f28da82a61552c47,0x85c2bba3b23a0e94e948,0xefefb7c220cf0cbcc96c,0x12011a2c92995ff7bf5b,0xc48617200e004000000c,0x9489388f28db82d61652,0x96c86c2bba4b25a1194e,0xb8596309902cf2cbcc],#[0x4082202bc88b005aab,0x752c49017500e0000004,0x94e9489388f28dd83261,0xbcc96c87c2eba7b26a12,0x9c1f59db8a0a1badcf2c,0x42627301c26b7,0x761a52c49517600e0001,0xa1494e9499398f28de83,0xf2cbcc96c88c2eba7b27,0x581fb9f852a0f2180a0c,0x404000142bc8,0x83a61a52d49c17900f0,0xb2aa1694e9499398f28e,0x54cf2cbdc96c88c2fba9,0x6974b8bb9e964439abf8,0xf0000024246685ca057,0x28e284061c52d4a017f0,0xbaab2aa1794e94993a8f,0x34402cf2cbdc96c88c2f,0x525dd9322429d81376,0x8200f408002000404081,0xb8f28e484061f52e4a61,0xc31bacb2ca1c94e94993,0x44a58898cf3cbec96c89,0xa40ddcc1e40193d9498,0xaa18201000008000c504,0x993b8f28e584562452e4,0xc8cc31badb2da1e94e94,0x9e3799e67b5cf3cbec96,0x10829c2420c6de7dafa,0x2f4af183010080000002,0xe94993b8f28e584a6255],#[0xc96c8cc32baeb30a2194,0x8ae6d8e499f3b8cf4cbe,0x40353d2054356c60b0,0x2752f4ba185010000000,0x294e94993c8f28e584e6,0xcbec96c8cc34bafb33a2,0x926cc67c6230344bdcf5,0xc910000ac95f007,0x5062852f4c3186010000,0x7a2594e94993e8f28e68,0xcf5cbec96c8cc35bb0b3,0x84e2e7a91edeace4961a,0x80000000301600227957,0xe685462d52f4c918b010,0xb39a2994e94a93e8f28,0xe5cf5cbec96c8cc35bb,0x206c539fe9fffedfdb05,0x10001028020120c4300,0xf28e785963052f4d018f,0x7bb0b3aa2d94e94a93e8,0xa4f12cf6cbec96c8cc3,0x24239a41245cb20c171d,0x19201000000000230a43,0x408f28e885e63052f4db,0xdc39bb2b3aa2e94e94a9,0xcba4a4903cf7cc0c96c8,0x80d1737bf5e3c8a33ef,0x4e219501000000004134,0x4a9418f28e886063052f,0x6c8dc3abb3b3ea3194e9,0x851b35d085c3cf7cc0c9,0xc858007b4a58c85e12],#[0x5304e519801000000001,0x4e94b9418f28e9867635,0x1c96c8dc3abb5b42a339,0x850c1d748400164cf7cc,0x440160004c1b55,0x6395304eb19901004000,0x3794e94b9428f28ea86c,0x8cc1c96c8dc3abb5b43a,0xe06e63c3d519032024cf,0x1218001084a420758ce5,0x86f63a5304ef19b01000,0x43a3894e94c9428f28eb,0x4cf8cc1c96c8ec3bbb7b,0xd1c8d6fdac35bade6629,0x90143400da3,0x8eb87663b5314f21a101,0xb8b46a3b94e94c9428f2,0xc6cacf9cc1c96c91c3bb,0xa65c6c0179fbfe018f,0x50100050000100864c28,0x8f28ec87b63e5334fb1a,0x3bbb9b48a3e94e94c943,0x8a45accf9cc1c96c91c,0xa7dda8bf222d9e10b80d,0x82ace1e3cc209008f1c9,0xfc24af9040d715f12605,0xc7f7a97d0bb80f89b421,0x6e7d3627e8c19d431793,0xe2f2c255cfeaf8662b1d,0xa385225376598f7a8a5a,0xa8181fb00d24268bbfb,0xc60620e183b82f3cea8],#[0xbd8108bc18000680c704,0xf8a6020c258a040c7604,0xf4088cda10005420a1bf,0x3b828bdda080cc6a855,0x78ff9bb601f443d33143,0x116298c3bf005c39f3c,0x10008b6001f533c00024,0x617f2a64101e0c0d006,0x3288548e064020364c0e,0x12c5546c5ca0018e3077,0x7d084200381d8857e57,0x8a049282eab84f40457b,0x14e2dc00578035ab6579,0x2f03d8c5f8c0c48a020e,0xfe405180f9fdeb00003a,0xa0ae8f0cf2c8e0692001,0x2a1181b9c1f5401ce19e,0x2f339650161fea8cbb82,0x81459ea8601b4196aade,0xdbcc3958605fc20466de,0x540460f3b526f486e193,0x11bcf4000140382dd083,0x800186a3ac4004c0f412,0x6191026b1ed1013002fd,0x59c17f322b30697f136,0x42508fb9050c04500de8,0x8ca0fb0a06f50ba947a1,0xd6812e0eb829c2956890,0x876816e920f157fdb6ac,0x76980024b7616820c090,0x740030145821ef800858,0xedf94aae7ed9c1c00e43],#[0x58fb081e9e16ea10c6b2,0xfb5203239d280abe2357,0x3c000181598485d6003c,0x633112f6c3003e4802e2,0xadbe7194746c8000bb00,0x3f40129a40d1bcc0b49,0x18204214760084f37a0,0x184106ac2bf08765e360,0xb815010803a028a32014,0x922c70700f0b8087b88d,0x72508103f91634687c6b,0x41136ce7ebb202f93c54,0x8c84e0841766e864ebbb,0xf0c6e6216a4a1b34d7d0,0xe7003003401d5e0a4f24,0x37380282f0bc61c0f5a3,0xe290bb1b782cb99c1f00,0x62d007ab428058ac7636,0x21f67c60e0d23b04657d,0xa14185c50c08e3b431a2,0x2811519ac220f803e143,0xd28e82421886f364e2c2,0xe020f80840ed806e3d11,0xadc3ec056a008da04171,0xe929a4c1f97662364950,0x2042c788600ad0406b0,0x2454d0ef45d4032c5430,0x58c378fe034006144,0x47c0017008e1048199,0x8a1c26aa62e99d48d4d,0x6c05007001000000cc0a,0x143f03cfec5a10d2cb17],#[0x6198718c06439dc0004,0x36e802500627b9c7002a,0xc2000085831395848ef,0xb072f8543a41a80d0e00,0x465b447e41b8a3878820,0xa40001c02056d3813eba,0x94e340120019c02d7e01,0x305122b680b408e867ee,0xb41492e7579d06aa,0x20c8fe0dc541b020445b,0x91a30250c0efe1bb628a,0x1c00088b93c0a00b820e,0x3ec39c431911bacce22c,0xde3c438fc6800c84a055,0x587f3f03c85f68856702,0x174b6a3f040da33d7c5c,0x8c715fac14a3eedc758f,0x465e9b00c581e805f0a,0x71830140c00fcb262d31,0x896c82b0879cdf17081b,0x1187a89273f20284059c,0x269725a8a857382dde18,0x316873c60e016077647e,0x56bafc9de678d9041018,0x38d420e8810123565008,0xfc06b6012903f1a4f4e2,0x913facde2c2708310062,0xddc6165b1786dce2346a,0xe070de8fd747f197331,0xa4f1481e70e0c8b8bfb3,0x6b8a15ea86476181a01f,0xbc068e89a000e628a029],#[0x936dfbaec0fbe819825,0x97a2aead030ee0144040,0x808fb4ea30bc02313604,0x2f8f3de90fb153fac6d,0x18517284fbc6f51094c0,0x20d5d18ffa4b06479d5c,0x2fd38d007a9eb15ff0d8,0x833dfe8c7da5e7685687,0x71cfb469be71afec40fa,0x5bbd5f757c011d61189c,0x283a1de20bc0edbbe917,0xcf80cc0630006be0c760,0xd5fc3feb8806c2f56362,0xb04a5cc28326ca01fdac,0x4068dfacd2510d40e197,0x871ea011ab5f106150a0,0x49fe1f0318f018147da0,0xffc50434120a4c20bc81,0x1c50280c40b600300427,0xd814f1c6218510902dab,0x88060850704018040030,0x1afa88426a2616843f0b,0x210050984fbe06de861e,0xca041f28d8f60104c000,0xdfee42c3c151af21f419,0x240894002bf84ea8a83,0xb1336ac837650626e006,0x429431a48002ad1127a4,0x99596200337a00002e20,0x9235c91338e804bf538c,0xee442c3ba00028200b4,0x18487464000fc065000],#[0x40cbe0cf81303da5e42c,0x800066b4383ced9ba8b0,0x281800339fa6cadbc9c9,0xda0340b1380886575224,0x41dc02540d025807d861,0x994afa36accb8f8b39e2,0xd03b09173834ec35be70,0x5081b711ca0443810055,0xe680af4261837d2356ae,0xf7432000c0f0244320b8,0x140140007bd018c0bea9,0x90c34801083144100041,0xf086ad512a4766cc72a9,0x5444bd1af12510f9d81f,0xc6d98b188b0912b]]
def g63H9 := groupedPages #[groupPage12,groupPage13]
def g63D10 := limbs80 #[#[0x221a42188a628220207f,0x5a96651086098440106a,0x5a868190e842146398c6,0x2a64020e21a0ea7980a,0x61086490461080a29902,0xc442100043c8680098e8,0x6aed589c449e0cc55218,0x6218d04212003e9d8da6,0x4df6830d5a9f469e0d45,0x8ba4a1e0b0360d00405e,0x50c000c18010182431c,0x80338018a01858712304,0x19a80670033800ee8032,0xa001280198019a803b40,0x7003bd0064015c007002,0xcb401d402b9806400c,0x74015e0067e803200af5,0x300af80194028015ea80,0x660063003a00a0052007,0x19ea019f400e7401c00,0x38]]
def g63H10 := limbs80 #[#[0x84800030082c0c0c,0x402018080a000180c22,0x8040204020040700024,0x6824220100018020a010,0x488c02020001800070,0x1000160105060060,0x50e010000c000080,0x80468000880828020381,0x1780c0001058080c0f04,0x12800061b078102200,0xc010288c4408010000c,0x20080d000180a000a014,0x480c0201000100200000,0x3028b8460b0403834050,0x110e000025d0080c040,0x680209030040e0388c3,0x34d018010b806101802,0x1054364405000020102,0x9000980606058140000,0x261e000040c360292c03,0x780405020200a0301010,0x40180c00010140a1a158,0x40100042080191c08510,0x4000c9460000000020,0x634060081604000040,0x8c41a050708804430500,0x1c0202068c404000f,0xa048141e0000800dc06,0x2000c440001507806,0x420070280c003e06818,0xb00c080d000083619050,0x904c580701021e6090],#[0xfa8eddd1404d03058120,0x80111201648eadfe7,0xe3f81da7401fc0900004,0xbf7ed70a5ee21d869ba0,0x4000400000810081a047,0xfa76859060d6a5088503,0x91441d2d6ca7e9cc0422,0x3a2a120020c000100202,0x53945f6a1a1641845ab4,0x33899080467fff7f8e,0x136ad1a8f85a00880000,0xfffec54a34c7a9687906,0x115214000eede,0xa1e49855ab492541b802,0x877f6cd77aff6deb86a7,0x8800800002800808380,0xd31a9e8792e176b52c9b,0x7018008fbff7ff6ca0a3,0x34c28a26002000000008,0x5a8df615eaba1e4d85db,0x4002450c2417a8bf917,0x461b6cd36a80b2008024,0x8bb5ff85c621f9aae879,0x40040080021940049d6,0xafa2657875b54fab62e8,0x85f4e7fc4dd6c3680e,0xb20ce010020001204018,0x2fe51ac68b9761d6e542,0x1020300903f05ffcd3d0,0x5b9522e2370048000000,0xfeb53d637eeb3a3e5f87,0x801944067fd23],#[0x197e236fd48bf0e40100,0x6cb8dfbc7c5a9fb3ace9,0xb80800000000804b0013,0x8eb3a466388dbf5431c3,0x844055ddeb558c91e2d4,0x54cd8fa0280000800000,0x86bc9fface9199e23715,0x4000040d200993a19fe9,0x88dc556b4c4200a20010,0xe15bf5c0c23beb5a466b,0x80000200008020b07d40,0xe959ae2572d5cda90c02,0x816f7fff7fc4d75df1ad,0x24480a00000000100000,0xa276b9a566d89dcf57b8,0x20470131dfbefcc375b8,0x4560e892a03800000004,0xf2ed82cebae6959b6277,0x120c191f6df7e7,0x6d8add75a3ba4e812000,0xbff697d72bffb7eb9a56,0x5004008200800014875,0xae6959b62f76570f614c,0x82097edf7df76dd962b7,0xc0055016000000008330,0x8c7f7ebda5e6d8bddb5d,0x4a040027f5fbdfd9b1,0x177d7f08164058000020,0xfecbd26d699af6979be3,0x8013ffff7,0x5e6f8cde360c405e0160,0xe143e7f21162f1236bfa],#[0x94058200000004261235,0xffafe979be3379d85179,0x60c197d7867e6f0df2f,0x6346c680180080000002,0x3cdad226bfa66738dded,0xc2102103addfdb32,0x6377dd8f221ac0700000,0xdd786275bee43b06999d,0xe000000405022a80926d,0x1a66778edf7654a26e01,0x7f5d38cf7355f8846c,0xe1c608000000000002e1,0x9027b0e999e63b7f59d2,0x49000009f4fb9e3661b9,0x1684d27502000000000,0xc45a9793f6c3a667b8ee,0x110000024648a6ffecaf,0x9f63b80da53a1e808000,0x2e00000027b0e99,0x82400000010000000000,0x6c7a66838fe0769cfa7e,0x6dad23f51205cfafc6c2,0x14941a5573b9ca0263f7,0x3444a830d8d13d896f06,0x258db8050c91150ff44b,0x47495c6364487a3a61e,0x90a11634eac6d461b195,0x588b8b4024ba4ae11b2a,0x686df7d7620e731eb18a,0x1723f470047a896e1ece,0x807db391d38b2195616e,0x338232bd00fb03c01839],#[0x3172904213f5af7a7a50,0x1b10001992fe1cba82d0,0xfe1d668410f1ae60a207,0xd1c78cee0cc9160ee343,0x440d2070617d80ca963,0x5e1fe05f1e5038433d96,0xa3640313163d5c69da3,0x3d000012800957ed04d,0x22541780ac158136de5,0xf91bee987d0c5c48bb62,0xf897d64a7370f0b40cf0,0x8f6b15f47f774018ff9e,0x4d6c095a71aa8d89d4a1,0x6d77b95fb17c3d824524,0x3912b9dcd978b6a0895f,0x6c50ad4004bbb36c0e0c,0x8c7f86e137dc12696043,0x383e1007dc6005c6cf84,0x9a285d7135dc0b89584,0x3b8d81056612518dc020,0x72b6b8c85dcc80f3056d,0x4081bc0129411f50f57,0xb6802db1b4c6b85145f3,0xf49464cb842c7da3e805,0xe8158e02c93cdb8c4960,0x3684]]
def g63D11 := limbs80 #[#[0x8103f]]
def g63H11 := limbs80 #[#[0x40d0e9102044040600,0x700079f42c0ff73ff7f0,0x91e301796dea609b782,0xe60176b4300062398cd]]
def g63L : Nat → Packing
  | 5 => (6,6,6,327686,51,6,8192,g63D5)
  | 6 => (155,5,6,4522106,119,29131,8207,g63D6)
  | 7 => (2355,4,6,6161519,123,934543,8352,g63D7)
  | 8 => (3321,3,6,2359984,106,5452433,8316,g63D8)
  | 9 => (867,2,6,786473,70,2622095,8255,g63D9)
  | 10 => (41,1,6,65537,0,168522,8206,g63D10)
  | 11 => (1,0,6,65537,0,4096,8194,g63D11)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => groupLookup 2 7 3 1 3 1 g63H6
  | 7 => groupLookup 52 173 6 3 8 7 g63H7
  | 8 => groupLookup 785 2591 9 5 12 16 g63H8
  | 9 => groupLookup 1107 4057 8 5 12 19 g63H9
  | 10 => groupLookup 289 967 9 4 10 9 g63H10
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
def cubWitness : Array Nat := #[37699309116,15217471879,8104363836,11929408589,52970245692,28104597041,11929603644,14077486878,22768176444,22667372058,11929412238,15253772451,14077470234,14077420302,37699217446,9782085798,8104412988,27857732721,12046590151,37732772646,12399363900,22766732377,63145792009,64851352881,8104329638,28154811477,15285620745,37766416700,15151403529,37766417724,42128253575,15219627797,32152700017,28104480533,8104396604,64935180387,12399285353,55202035875,7701561417,37699217574,49336631637,37766401340,9781928590,64918461745,37934190140,40921217187,55202036387,28343146659,64918403235,22768034970,63145783947,15150354953,53037354300,14077420046,15471284565,7701541511,37699284150,15151403785,64935192870,28104596529,7869923994,40921275697,48982418190,63196127886,22667505210,15219627285,15151411851,28104479765,63145775625,15151536681,15150895885,15150879241,12250221372,37766326950,22701067580,14077603386,64918461489,8155514684,53309908122,22768033946,14312350362,8104321446,22768168122,15219569031,28070925717,14077569123,28104595505,28154973756,53209245210,23375349564,65207838234,14381289813,15186547079,27200348814,23460467110,22768043097,40921275441,44619293454,29432222217,28104480021,65191040277,52970154150,41532535175,58850816391,15151553325,37732863292,49621899427,14077403918,11929412110,32599716491,42262403185,14077569318,44619343386,27200540220,22700926106,57827942727,37766471753,22768034842,14077419790,37699308604,58884903303,15219560839,14077158158,15219635607,41038761276,15151420173,28154811413,7735656718,11929411726,15671707452,28104596657,32706154887,28104613173,46817370766,15151470105,15251558791,11929502805,32152633766]
def cubTag (k i : Nat) : Nat :=
  match k with
  | 5 => cubWitness[((#[0,0,0,1,0,2] : Array Nat)[i-0]?.getD 0)]?.getD 0
  | 6 => cubWitness[((#[3,4,5,0,6,0,7,8,9,10,11,9,12,13,0,0,14,15,16,13,0,9,17,18,13,12,9,19,20,0,21,22,0,0,0,6,23,24,0,0,0,25,0,0,12,26,27,9,6,0,28,0,0,29,0,0,30,31,20,0,32,20,24,33,0,29,34,0,0,0,10,9,0,0,0,4,12,11,9,35,13,23,36,28,0,6,37,9,38,10,14,35,0,6,39,32,0,0,10,40,39,0,0,34,13,24,27,25,28,0,0,0,0,0,41,0,12,42,43,24,9,0,0,17,26,41,16,12,44,0,44,9] : Array Nat)[i-7]?.getD 0)]?.getD 0
  | 7 => cubWitness[((#[13,45,0,46,47,39,39,10,39,10,0,42,0,25,12,9,48,10,0,12,10,39,11,49,29,0,10,29,29,0,29,8,1,9,9,50,39,51,9,29,35,52,0,53,39,39,8,9,54,9,0,13,25,9,29,0,0,4,0,0,10,55,29,53,0,56,9,4,39,6,0,39,0,35,9,9,57,0,0,29,12,58,12,10,9,59,60,61,9,9,29,9,62,6,4,49,29,13,63,11,6,0,11,10,64,0,48,65,34,9,29,11,10,66,67,68,0,9,49,9,58,49,39,35,7,12,9,69,25,70,29,71,13,9,60,12,12,0,39,43,72,6,9,10,73,39,0,10,11,9,74,39,0,75,9,0,76,10,39,12,11,0,39,77,49,0,0,0,9,0,78,39,13,10,79,49,39,11,9,48,80,0,9,10,12,39,0,81,39,9,35,12,28,0,82,16,9,83,10,29,14,43,29,49,35,0,14,84,39,9,39,10,78,4,39,0,29,13,28,11,85,29,0,10,10,6,10,4,0,9,9,86,56,11,0,11,9,87,0,9,39,0,10,88,11,39,0,12,75,6,39,0,5,0,29,89,9,9,4,11,9,9,29,39,0,8,10,0,0,59,49,9,52,90,47,13,13,49,91,90,39,7,0,13,28,0,10,49,29,39,16,29,13,9,88,39,39,29,25,9,39,39,92,0,0,81,93,9,12,8,11,0,9,8,4,49,77,0,10,39,49,94,95,89,59,39,13,83,39,83,10,68,9,0,39,0,12,0,71,96,29,10,78,0,39,45,10,0,49,49,13,11,29,29,16,88,0,29,39,10,4,9,9,57,12,45,0,0,10,0,12,10,61,90,97,39,10,81,39,98,28,10,0,35,0,29,12,88,49,60,7,0,99,6,4,0,39,16,45,39,100,39,13,49,48,5,0,101,11,25,29,12,10,25,100,13,10,0,49,9,87,49,23,0,47,29,65,0,100,39,0,0,0,49,0,10,9,11,13,97,0,9,0,0,9,12,0,0,29,29,39,29,4,16,0,10,9,39,49,0,9,39,49,39,79,39,39,49,0,9,6,65,59,9,10,29,13,100,10,0,11,9,0,102,0,10,0,13,39,39,11,31,0,60,0,78,39,6,4,25,10,103,0,19,49,104,74,35,9,48,13,0,0,29,9,23,48,0,13,10,48,10,29,11,4,29,9,0,29,65,4,35,49,0,68,4,48,10,10,12,5,82,29,39,39,0,0,13,48,96,96,0,39,55,9,0,13,9,9,9,93,25,29,0,12,0,29,39,9,39,0,39,35,59,39,10,0,13,9,105,9,9,0,89,25,13,39,10,8,11,10,0,59,13,35,29,13,48,0,49,10,78,0,9,39,7,0,106,75,9,49,39,49,29,93,49,10,10,45,9,39,107,10,0,16,0,0,10,29,88,0,0,0,9,29,28,39,13,63,16,0,49,11,6,0,11,43,0,30,10,99,28,12,49,29,9,108,48,13,0,64,92,11,56,48,14,13,12,49,49,58,39,12,81,48,39,0,99,87,9,90,9,109,25,9,88,33,49,29,110,9,10,45,0,111,39,4,12,0,25,49,11,29,13,56,11,12,112,9,25,4,45,39,25,9,9,11,28,0,11,4,12,79,12,39,28,12,4,49,39,9,93,48,39,0,76,12,29,10,59,9,49,39,29,25,11,39,4,12,113,0,10,0,10,10,0,39,76,59,39,25,114,10,39,115,29,78,10,10,49,39,6,13,17,9,39,49,39,50,0,9,11,99,11,39,4,0,61,39,39,39,14,116,117,83,29,9,8,0,9,29,96,4,39,99,89,4,12,6,9,64,28,4,5,4,39,6,39,48,47,8,13,33,0,4,39,118,10,10,39,9,0,0,39,59,88,49,89,29,29,9,39,76,12,45,13,9,10,12,4,11,0,12,13,10,39,0,35,16,88,9,48,0,16,0,119,113,12,29,0,49,39,101,39,0,39,0,11,9,6,25,49,9,87,0,0,93,9,101,120,25,0,0,4,29,0,9,9,29,9,7,9,100,97,9,0,10,9,58,39,0,11,121,0,12,0,49,56,4,9,25,11,29,59,88,29,10,122,9,39,10,9,0,6,9,9,64,39,11,39,0,13,29,10,83,29,39,88,123,9,13,25,11,39,52,48,76,12,19,9,9,13,11,11,10,68,10,124,4,31,9,10,25,9,76,48,0,49,29,39,39,13,78,35,35,48,0,0,66,9,57,48,9,0,4,29,49,9,9,39,29,9,39,54,11,11,29,119,57,4,60,0,35,4,9,39,29,39,125,9,0,11,11,39,47,19,43,10,0,9,83,9,48,0,0,122,0,59,10,0,13,10,126,39,25,9,9,31,127,48,92,39,6,13,57,9,0,39,10,0,0,128,0,39,77,9,0,6,59,28,99,39,106,80,122,39,35,8,11,0,29,9,0,59,43,88,39,64,49,0,82,6,0,129,130,6,49,0,39,6,49,0,25,6,4,99,10,29,59,0,9,9,39,52,43,0,39,131,35,63,0,57,124,85,6,14,9,9,0,10,0,89,39,68,6,39,9,13,9,0,0,42,4,0,9,11,39,0,29,0,0,9,9,49,49,0,28,99,4,11,10,10,0,25,25,48,132,11,29,96,11,12,0,10,0,9,10,9,39,10,9,9,12,0,10,59,49,0,0,39,39,9,76,0,39,10,9,49,9,49,13,119,132,124,39,59,39,39,51,49,9,0,113,124,0,0,11,49,9,4,0,9,10,49,10,66,13,4,29,29,9,9,0,29,72,6,9,39,96,35,8,9,39,9,49,11,78,75,49,9,29,6,25,39,0,4,0,33,11,49,9,0,11,13,0,9,6,59,39,0,9,83,0,97,9,133,124,39,78,76,39,65,49,4,10,25,0,0,19,10,10,88,8,12,0,0,6,28,0,134,76,4,9,9,9,28,9,117,66,9,4,0,39,16,9,0,0,6,49,88,81,39,49,103,9,9,0,39,10,0,29,39,11,9,39,11,25,135,39,35,0,11,0,35,84,6,29,8,0,0,0,10,0,4,29,13,13,6,23,39,0,39,0,97,89,6,13,78,39,12,0,39,29,0,13,8,60,136,25,48,25,39,11,0,11,9,9,29,0,113,83,9,29,39,46,35,35,0,4,137,11,11,28,60,10,39,76,0,9,0] : Array Nat)[i-228]?.getD 0)]?.getD 0
  | 8 => cubWitness[((#[49,4,49,88,9,4,88,25,63,39,49,50,88,120,4,9,10,25,50,9,49,88,9,9,4,9,59,9,120,13,50,4,35,25,35,25,4,39,88,39,25,9,39,88,49,35,52,39,25,4,39,39,8,29,76,39,9,88,0,88,25,39,88,9,9,87,39,29,9,76,88,39,88,39,25,52,52,39,52,39,9,29,39,39,29,29,4,10,87,59,59,8,58,4,9,124,9,78,78,25,88,59,120,120,39,13,4,25,4,4,9,63,9,45,35,52,58,0,88,88,49,0,4,49,88,59,4,39,45,52,50,49,4,52,39,88,88,49,25,88,25,39,49,39,49,88,39,10,4,35,39,4,10,39,25,59,120,25,124,35,25,87,13,13,50,39,9,120,58,87,49,10,87,49,52,88,0,4,76,25,39,9,88,25,9,4,25,35,25,39,76,25,25,39,39,9,50,88,39,35,88,9,9,88,9,50,63,100,25,9,88,59,8,4,8,39,25,35,88,4,39,90,35,52,88,76,9,49,29,9,88,9,63,9,4,9,9,10,88,9,25,4,39,100,4,35,25,39,100,0,35,59,88,49,49,9,39,0,9,50,25,59,120,50,9,9,9] : Array Nat)[i-1331]?.getD 0)]?.getD 0
  | _ => 0
def cubRows (word : Nat) : SixRows := ⟨Fin.ofNat 512 ((word >>> 0) % 64),Fin.ofNat 512 ((word >>> 6) % 64),Fin.ofNat 512 ((word >>> 12) % 64),Fin.ofNat 512 ((word >>> 18) % 64),Fin.ofNat 512 ((word >>> 24) % 64),Fin.ofNat 512 ((word >>> 30) % 64)⟩

def crossOK (g : Forest) (k i : Nat) : Bool :=
  let S := (stateSet g k i).toFinset
  let r := cubRows (cubTag k i)
  decide (S.card = k+1) && decide ((∑ s ∈ S, sixCost (readSix r s)) < sixCost (readSix r (targetOf g)))

def spanOK (g : Forest) (k start n : Nat) : Prop :=
  ∀ i, start ≤ i → i < start+n →
    nodeVerified g k i = true ∨ Impossible g.mode (targetOf g) k (stateSet g k i).toFinset

theorem spanOld {g k a n} (h : block g k a n = true) : spanOK g k a n :=
  fun i lo hi => Or.inl (block_at h i lo hi)

theorem spanSix {g k a n} (h : ((List.range n).all (fun j => crossOK g k (a+j))) = true) : spanOK g k a n := by
  intro i lo hi
  have v := List.all_eq_true.mp h (i-a) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le lo] at v
  simp only [crossOK,Bool.and_eq_true,decide_eq_true_eq] at v
  exact Or.inr (six_cut (cubRows (cubTag k i)) v.1 v.2)

namespace Nat92GE
structure TeachingShape where
  roots : List Probe32
  out : Probe32
  price : Nat
  select : Fin 92 → Fin 32

def TeachingShape.good (s : TeachingShape) : Prop := FacePrice (s.roots.map (lift92 s.select)) s.price ∧ lift92 s.select s.out=goal
def hintShape0 : TeachingShape := ⟨[0xffffff97,0x16,0x2a,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape0V : hintShape0.good := by
  constructor
  · have eq : hintShape0.roots.map (lift92 hintShape0.select) = facet0 := by decide +kernel
    rw [eq]
    exact facetPrice0
  · decide +kernel
def hintShape1 : TeachingShape := ⟨[0xffffffcb,0xffffffc9,0xffffffd5,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape1V : hintShape1.good := by
  constructor
  · have eq : hintShape1.roots.map (lift92 hintShape1.select) = facet1 := by decide +kernel
    rw [eq]
    exact facetPrice1
  · decide +kernel
def hintShape2 : TeachingShape := ⟨[0x2a,0x16,0xffffffab,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape2V : hintShape2.good := by
  constructor
  · have eq : hintShape2.roots.map (lift92 hintShape2.select) = facet2 := by decide +kernel
    rw [eq]
    exact facetPrice2
  · decide +kernel
def hintShape3 : TeachingShape := ⟨[0x3a,0x16,0xffffffab,0x4c],0x70,5,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6,6,6,4,4,4,4,5,5,5,5,6,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape3V : hintShape3.good := by
  constructor
  · have eq : hintShape3.roots.map (lift92 hintShape3.select) = facet3 := by decide +kernel
    rw [eq]
    exact facetPrice3
  · decide +kernel
def hintShape4 : TeachingShape := ⟨[0xffffff33,0xffffff55,0xffffff69,0x8e],0xf0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape4V : hintShape4.good := by
  constructor
  · have eq : hintShape4.roots.map (lift92 hintShape4.select) = facet4 := by decide +kernel
    rw [eq]
    exact facetPrice4
  · decide +kernel
def hintShape5 : TeachingShape := ⟨[0x12,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape5V : hintShape5.good := by
  constructor
  · have eq : hintShape5.roots.map (lift92 hintShape5.select) = facet5 := by decide +kernel
    rw [eq]
    exact facetPrice5
  · decide +kernel
def hintShape6 : TeachingShape := ⟨[0xffffffd3,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape6V : hintShape6.good := by
  constructor
  · have eq : hintShape6.roots.map (lift92 hintShape6.select) = facet6 := by decide +kernel
    rw [eq]
    exact facetPrice6
  · decide +kernel
def hintShape7 : TeachingShape := ⟨[0xffffffdb,0xffffffcd,0xffffffd1,0x26],0x38,4,fun i => Fin.ofNat 32 ((#[0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,1,2,0,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3,3,3,4,4,4,5,5,5,3] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape7V : hintShape7.good := by
  constructor
  · have eq : hintShape7.roots.map (lift92 hintShape7.select) = facet7 := by decide +kernel
    rw [eq]
    exact facetPrice7
  · decide +kernel
def hintShape8 : TeachingShape := ⟨[0xfffffe23,0x22,0x4e,0x94,0x118],0x1e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape8V : hintShape8.good := by
  constructor
  · have eq : hintShape8.roots.map (lift92 hintShape8.select) = teaching0 := by decide +kernel
    rw [eq]
    exact teachingPrice0
  · decide +kernel
def hintShape9 : TeachingShape := ⟨[0xffffff33,0xffffff31,0xffffff55,0xffffff69,0x8e],0xf0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,4,4,4,4,5,5,5,5,6,6,6,6,7,7] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape9V : hintShape9.good := by
  constructor
  · have eq : hintShape9.roots.map (lift92 hintShape9.select) = teaching1 := by decide +kernel
    rw [eq]
    exact teachingPrice1
  · decide +kernel
def hintShape10 : TeachingShape := ⟨[0xfffffd47,0x146,0xfffffc6b,0x192,0x21c],0x3e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape10V : hintShape10.good := by
  constructor
  · have eq : hintShape10.roots.map (lift92 hintShape10.select) = teaching2 := by decide +kernel
    rw [eq]
    exact teachingPrice2
  · decide +kernel
def hintShape11 : TeachingShape := ⟨[0x7c,0xfffffea9,0xfffffe3d,0xce,0x110],0x1e0,6,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,5,5,5,5,5,6] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape11V : hintShape11.good := by
  constructor
  · have eq : hintShape11.roots.map (lift92 hintShape11.select) = teaching3 := by decide +kernel
    rw [eq]
    exact teachingPrice3
  · decide +kernel
def hintShape12 : TeachingShape := ⟨[0xfffffac7,0x18e,0xfffff913,0x224,0x438],0x7c0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,3,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8,8,8,9,9,9,9,9,9,10,10,10,10,10,10,6,6,6,6,6,6,7,7,7,7,7,7,8,8,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape12V : hintShape12.good := by
  constructor
  · have eq : hintShape12.roots.map (lift92 hintShape12.select) = teaching4 := by decide +kernel
    rw [eq]
    exact teachingPrice4
  · decide +kernel
def hintShape13 : TeachingShape := ⟨[0xffff255b,0xffff49a3,0xffff0e0d,0x700e,0x8030],0xffc0,8,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,5,0,1,2,3,4,5,0,1,2,0,3,0,2,3,1,4,5,1,3,0,4,5,0,2,2,1,3,2,4,5,2,5,2,4,3,4,5,1,1,3,6,7,8,9,10,11,12,13,14,15,6,7,8,8,9,10,10,11,12,13,14,15,15,6,6,7,8,8,9,10,11,12,12,13,13,14,6,6,7,7,8,9,9,10,11,11] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape13V : hintShape13.good := by
  constructor
  · have eq : hintShape13.roots.map (lift92 hintShape13.select) = teaching5 := by decide +kernel
    rw [eq]
    exact teachingPrice5
  · decide +kernel
def hintShape14 : TeachingShape := ⟨[0xfffffd67,0xfffffcab,0xfffffcc1,0x112,0x21c],0x3e0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,1,2,3,4,0,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9,9,9,9,9,5,5,5,5,5,6,6,6,6,6,7,7,7,7,7,8,8,8,8,8,9] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape14V : hintShape14.good := by
  constructor
  · have eq : hintShape14.roots.map (lift92 hintShape14.select) = teaching6 := by decide +kernel
    rw [eq]
    exact teachingPrice6
  · decide +kernel
def hintShape15 : TeachingShape := ⟨[0x2e6,0xfffffc35,0x14a,0xfffff983,0x60c],0x7f0,7,fun i => Fin.ofNat 32 ((#[0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,2,3,0,1,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8,8,8,9,9,9,9,10,10,10,10,4,4,4,4,5,5,5,5,6,6,6,6,7,7,7,7,8,8] : Array Nat)[i.val]?.getD 0)⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hintShape15V : hintShape15.good := by
  constructor
  · have eq : hintShape15.roots.map (lift92 hintShape15.select) = teaching7 := by decide +kernel
    rw [eq]
    exact teachingPrice7
  · decide +kernel
def selectTeaching : Nat → {s : TeachingShape // s.good}
  | 1 => ⟨hintShape1,hintShape1V⟩
  | 2 => ⟨hintShape2,hintShape2V⟩
  | 3 => ⟨hintShape3,hintShape3V⟩
  | 4 => ⟨hintShape4,hintShape4V⟩
  | 5 => ⟨hintShape5,hintShape5V⟩
  | 6 => ⟨hintShape6,hintShape6V⟩
  | 7 => ⟨hintShape7,hintShape7V⟩
  | 8 => ⟨hintShape8,hintShape8V⟩
  | 9 => ⟨hintShape9,hintShape9V⟩
  | 10 => ⟨hintShape10,hintShape10V⟩
  | 11 => ⟨hintShape11,hintShape11V⟩
  | 12 => ⟨hintShape12,hintShape12V⟩
  | 13 => ⟨hintShape13,hintShape13V⟩
  | 14 => ⟨hintShape14,hintShape14V⟩
  | 15 => ⟨hintShape15,hintShape15V⟩
  | _ => ⟨hintShape0,hintShape0V⟩
def chartTeaching : Array (Nat × Nat × Nat) := #[(0,7,0x38aa1eb18e9),(0,7,0x2ae21ea3c69),(0,7,0x1a39529015c),(0,7,0x3486ac7aae6),(1,6,0x8f1da18b4),(1,6,0xf2d56c705),(1,6,0x843623a5a),(1,6,0x1e6b4616c),(1,6,0xb1c17cb55),(1,6,0xb1c17ca55),(1,6,0x2c7383286),(1,6,0x347385306),(5,6,0xdb15d6d13),(9,8,0x29c44568e2d5),(9,8,0x15260a54735a),(0,7,0x23c5a84a613),(0,7,0x34cb8dbceb1),(0,7,0x15c76456cb4),(0,7,0x1a255296151),(0,7,0x23c7a86ae32),(0,7,0x755a14a613),(0,7,0x755a14a616),(0,7,0x32aa1eb1a63),(0,7,0x298fa878caa),(0,7,0x1a3bc2b8b1c),(0,7,0x38711f31559),(0,7,0x221839a31cb),(0,7,0x34711f31655),(0,7,0x1957c478d1c),(0,7,0x315764725b4),(0,7,0x1ce11f15c59),(0,7,0x29c7c86cd38),(0,7,0x78e60c68a5),(0,7,0xd55a14a49c),(0,7,0x26f3ab2ae32),(0,7,0x19255214151),(0,7,0x318fa878ab2),(0,7,0xe69528545c),(0,7,0x164ca5ce2da),(0,7,0x2aca1ea9c63),(0,7,0x3459cdbc79d),(0,7,0x3496cd7cb6e),(0,7,0x16d1cd9df15),(0,7,0x34cb8dbcef1),(0,7,0x1567c474e1c),(0,7,0x38713f335da),(0,7,0x38aacebcba9),(0,7,0x34cb8dbceb9),(0,7,0x78e60c68b4),(0,7,0xe6bc2ace1c),(0,7,0x23a7a862e2a),(0,7,0x388a1eb18e9),(0,7,0x38ca1ea98f1),(0,7,0xe9bc19cd2c),(0,7,0x19c7c45cd38),(0,7,0x2a0c68e61ce),(0,7,0x15c664468a5),(0,7,0x3496cd7cb66),(0,7,0xe255296445),(0,7,0x1848578d1d5),(0,7,0xd57c16cd1c),(0,7,0x32d21da39f1),(0,7,0x31a7c874930),(0,7,0x9387305183),(0,7,0x1af36716d32),(0,7,0x734e14630a),(0,7,0x298fa878c2a),(0,7,0x23a7a872e2a),(0,7,0x28903b8b1e3),(0,7,0x25d2cd6df26),(0,7,0x1c58578d1d5),(0,7,0x724e0c628c),(0,7,0x15c7c45cc34),(0,7,0x15c7c45ce34),(0,7,0x29c7a86acb8),(0,7,0xb695285511),(0,7,0x3459cdbc7d5),(0,7,0x2dd7c96cd38),(0,7,0x9395291585),(0,7,0x15c7c454e34),(0,7,0x1358a5cb39a),(0,7,0x38d11f19571),(0,7,0x3459cdbc795),(0,7,0x263bc1b472c),(0,7,0x29d7c96cd38),(0,7,0x221839a31da),(0,7,0x31a7c874b38),(0,7,0x38711f315d9),(0,7,0x78e60c68a4),(0,7,0x2519c9bc795),(0,7,0x31a7c874938),(0,7,0x308a1eb18e9),(0,7,0x38713f335db),(0,7,0x3167c474738),(0,7,0xb6b12a1c11),(0,7,0x38713f335d9),(0,7,0x1114a55a389),(0,7,0x724e14630a),(0,7,0x23c5a842613),(0,7,0xc18538d1d5),(0,7,0xd255214445),(1,6,0x8e6562874),(1,6,0x8e9ba18ac),(1,6,0x843323a4e),(1,6,0xc59f11c1c),(1,6,0x8c7983886),(1,6,0x1cd38518c),(1,6,0x711599797),(1,6,0xbbceacab8),(1,6,0xb2286eb63),(1,6,0xd9ef16d1c),(1,6,0x14630734e),(1,6,0x30614e347),(1,6,0xe2a87ac63),(1,6,0xf2dd6cd25),(1,6,0x8e9ea18b8),(1,6,0x1ce34614c),(1,6,0x5f6cd64f2),(1,6,0x4d6c97cf6),(1,6,0x9f5da58b4),(1,6,0xb3497cb75),(1,6,0x5b47367bc),(1,6,0x3872c6283),(1,6,0x18a0ce1cb),(1,6,0xc63ea1c2a),(1,6,0xbbaf2ab38),(1,6,0x38d1cc185),(1,6,0xab887a8f1),(1,6,0xcd7d93c96),(1,6,0xca18b1ce),(1,6,0x2da5ca0d2),(1,6,0xb38abcbba),(1,6,0xd97cd6c93),(1,6,0xdbaf32d38),(1,6,0x673e93632),(1,6,0x73847c771),(1,6,0x4f25b35f6),(3,7,0x2a878a7ac63),(3,7,0x38cb4cfcdba),(3,7,0x91ce0cc185),(3,7,0x614c54e347),(3,7,0x32b21f33b6e),(3,7,0x34e32e76ebc),(3,7,0x1c5b45fcd9e),(3,7,0x15db3591cb4),(3,7,0x31f15d11738),(3,7,0x1c4f45fccdb),(3,7,0x13d1cc5bf36),(3,7,0xd1ce0cc185),(3,7,0x91ce0c0185),(3,7,0x62836872ce),(3,7,0x26ebcca4e2a),(3,7,0x162836872ce),(3,7,0x26ebcaa4e32),(3,7,0x29f35b21d38),(3,7,0xdc7c44cc21),(3,7,0x328668738b),(3,7,0x1adbc598d32),(3,7,0x1c46457cc59),(3,7,0x9c7c44cd21),(3,7,0x2a1833a31e6),(4,8,0x878caac698fa),(4,8,0x29444568e2d5),(4,8,0xf15c59d1cc11),(4,8,0x15858a5491da),(4,8,0x15848a54d1da),(4,8,0x15c48a54d1de),(4,8,0xea3a71ab2e21),(4,8,0xea9c63e2ac21),(4,8,0xea3a71aa2e21),(4,8,0x15c48a54d1da),(5,6,0xba3b6caa5),(5,6,0x3891c6303),(7,6,0x456d31576),(7,6,0x47871567c),(7,6,0xf3165ce11),(7,6,0x86acb18fa),(7,6,0xba3a6caa1),(7,6,0x878aa3a7a),(7,6,0x4f2e1bc7a),(7,6,0xf3365ce13),(7,6,0x9a3a648a1),(7,6,0x14c28724e),(8,9,0x78e6b431a2b25),(8,9,0x231e6a43886b25),(8,9,0x221832a68c72da),(8,9,0x221836268c765a),(8,9,0x78e6d431a2d25),(8,9,0x34b211bcc691e6),(8,9,0x78e6b431a2b24),(8,9,0x78e6b431a2925),(8,9,0x231e6a43886a21),(9,8,0xea98f1ab8ca1),(9,8,0xea3a71ab2e21),(9,8,0x878caac698fa),(9,8,0x474e1cc5567c),(9,8,0xeb18e9cb8aa1),(9,8,0x872e2ac63a7a),(9,8,0x465e1cc5567c),(9,8,0xf15671734e11),(9,8,0x29c15139a2d5),(9,8,0x86ae32a63c7a),(9,8,0x15360a54735a),(9,8,0xf31559d38711),(9,8,0xea98f1ab88a1),(9,8,0x478d1cc5957c),(9,8,0xf19571738911),(9,8,0xf19571738d11),(10,10,0xf077a3e9ce250e2),(10,10,0x29148519a389547),(10,10,0x3992d51ca19c445),(10,10,0xf885c1631daf0d),(10,10,0x55a64e35115628c),(10,10,0x3a93631cc1a2843),(11,9,0x298f1eb8cb086a),(11,9,0x34e1c45565df31),(11,9,0x19571f38d3045c),(11,9,0x2acb8869c79ea3),(11,9,0x29c63eaaca2878),(11,9,0x34738471679f15),(11,9,0xd1d569849014a),(11,9,0x32e2a863a6beb1),(11,9,0x318e9eb8aa8862),(12,11,0x2ae25b28eabbbcb69),(12,11,0x2ae05b28eabbbc369),(12,11,0x64eac921ce9b3e9a),(12,11,0x261f18e71a4883865),(12,11,0x31aa8821cb8e6e9a),(15,11,0x1a2d534739e4ca15c),(0,7,0x3157c478734),(0,7,0x96b12a1c91),(0,7,0x72ce0c628c),(0,7,0x182856951c9),(0,7,0x32593db35da),(0,7,0x755a14a612),(0,7,0xd387305183),(1,6,0x30518d387),(1,6,0xe1c47ce55),(1,6,0xb2a86eb63),(1,6,0xd6df25d2c),(1,6,0x1e6d46174),(1,6,0x39a5ca193),(4,8,0x872ab88f1a7a),(4,8,0x478d1cc5957c),(4,8,0x47473857167c),(4,8,0xea3c69caac21),(4,8,0x4f8d1ccdb5fc),(4,8,0xf19c55e1cc11),(4,8,0x47891cc5957c),(5,6,0x8b48639b1),(5,6,0x19c147395),(5,6,0x8ac8639a9),(8,9,0x2cab886ef3ac69),(8,9,0x34cb8876f3aa71),(8,9,0x38b2a87ceae8e9),(8,9,0x325912b6c552da),(8,9,0x3471617cd9e1d5),(8,9,0x34b251bcd6d1e6),(8,9,0x1c5b445ef36c55),(8,9,0x3459c476f1e655),(8,9,0x3abbcdaae2cd32),(8,9,0x38d3287ceb68f1),(8,9,0x3459c176f1e355),(8,9,0x32593636cd765a),(8,9,0x1673445edbcc55),(8,9,0x34cb8476f3a671),(8,9,0x2ce2a87cbba8e9),(8,9,0x324d62b3d9739a),(8,9,0x68832a61e32ce),(8,9,0x34b258bcd6d8e6),(8,9,0x2ab3886eebcc69),(8,9,0x325932b6cd72da),(8,9,0x32e344fadbc5f1),(8,9,0x16c937365f375e),(8,9,0x3892287cea68e9),(8,9,0x3845c2b1f1539a),(8,9,0x3892a87ceae8e9),(8,9,0x16d1c4f67bc6d5),(8,9,0x2cab896ef3ad69),(8,9,0x38cb447af36571),(8,9,0x38b2a83ceae8e9),(8,9,0x38b2287ceae8e9),(8,9,0x3ceaed78b2a974),(8,9,0x3496c1b5f2d3a6),(8,9,0x38862a31e638b),(8,9,0x2470617c99e1d5),(8,9,0x34b251bcd691e6),(8,9,0x32e344fadbc5f3),(8,9,0x2cd25abcb75ae6),(8,9,0x2ce2a97cbba9e9),(8,9,0x16d1c4f67bc6d7),(9,8,0x15858a5491da),(9,8,0x6891d5298485),(9,8,0xf19c55e1cd11),(9,8,0x45ce34655c7c),(10,10,0x3a93631cc1aa843),(10,10,0x878c2a8b18e9ea6),(10,10,0x15850a1951c968e),(10,10,0x54e35a645446298),(10,10,0x9951f18c68b4461),(10,10,0x1d935a38519360a),(10,10,0x54e35a645456298),(10,10,0x6a32f164a632851),(10,10,0x3992d51ca19c405),(10,10,0x8728b8a23a71ebc),(10,10,0x9b18d51e21b4445),(10,10,0xf0da55c6cd1c151),(10,10,0x478c1c531559f1e),(10,10,0x1d935a38519160a),(10,10,0x86a8b8c23c69ebc),(10,10,0x86aa32c29c63eb6),(10,10,0x54e35a645456290),(10,10,0x8de3fcb4387272c),(10,10,0x45c538c15c59f3a),(10,10,0x4f8c9c5b35d9f1e),(10,10,0x7035a1d1ef098f1),(11,9,0x31655f34714478),(11,9,0x318e9eb8aa8872),(11,9,0x31a63eb2aa2878),(11,9,0x38caa8698ebeb1),(11,9,0x1cd38459c79f15),(11,9,0x19c55f1cd14478),(11,9,0x15671f34e3045c),(11,9,0x1ce34455c75f19),(11,9,0x31559f38718474),(12,11,0x3c99a3aed387062aa),(12,11,0x135b8c925dbcf6e9a),(12,11,0x13c9c592cd95f679a),(12,11,0x2ae25b28ea3bbcb69),(12,11,0x21d2ab24d63a7cba6),(12,11,0x11c9c592c5957679a),(12,11,0x3c569c7572ce11865),(12,11,0x34713594f31d9e5d5),(12,11,0x21b32d24a63c7cda6),(12,11,0x261e98e71a4883865),(12,11,0x22e25d30ea39bcd71),(12,11,0x35aac921cb8f6e9a),(12,11,0x3cc49575e2c711165),(12,11,0x3c6a639ee34b0a196),(12,11,0x135b8c925d9cf6e9a),(12,11,0x361f18e75b4c83865),(12,11,0x1cd13594f197b65d5),(12,11,0x115b8c925d9c76e9a),(12,11,0x3cc4d575e2c711165),(12,11,0x13c9c592cdb5f679a),(12,11,0x22e25b28ea39bcb69),(13,16,((0x974b24ca <<< 64) + 0xa8b8c28d6dba6f3a)),(13,16,((0x478718c9 <<< 64) + 0x64b4c14c5579af36)),(13,16,((0x874b24ca <<< 64) + 0xa8b8c28c69ba6f3a)),(13,16,((0x472592e1 <<< 64) + 0xc634c14c5579adbc)),(14,10,0x1a5734b073a6b7c),(14,10,0x29687044e2da5f1),(14,10,0xf0dc5956cd1c151),(14,10,0x156b347073557bc),(14,10,0x15818c2951c968e),(14,10,0x2940c615a2ce547),(14,10,0x1a847084e1e6a71),(14,10,0x29118315a389547),(14,10,0x156b347072557bc),(14,10,0x29118315a38b547),(14,10,0xf0ecd76ace1c293),(15,11,0x21d0a6164419b1689),(15,11,0x151da38b35d4c529c),(15,11,0x1a25534739e44a15c),(10,10,0x6872d564a616151),(12,11,0x21d2ab24c63a7cba6),(12,11,0x115b8c92559c76e9a),(12,11,0x5b16d2434757cda6),(13,16,((0x4f2592e1 <<< 64) + 0xc634c14cd779adbc)),(13,16,((0x45ce185b <<< 64) + 0x24b4530571e9af36)),(13,16,((0x2a1ca215 <<< 64) + 0x619105225ada6c55))]
def pickTeaching (k i : Nat) : Nat :=
  match k with
  | 6 => ((#[0,0,1,2,3,4,5,6,7,8,9,10,11,12,13,14] : Array Nat)[i-139]?).getD 0
  | 7 => ((#[15,16,0,17,18,19,0,16,20,21,22,23,24,19,25,20,0,0,26,27,28,19,17,29,30,19,31,32,0,33,34,0,35,36,37,38,39,0,0,25,25,36,17,25,19,17,40,0,41,42,15,19,40,19,0,25,43,44,25,25,25,27,45,46,30,38,19,37,31,22,0,41,27,25,47,48,19,25,0,0,25,0,25,15,19,0,0,49,50,0,19,51,0,52,40,22,53,52,17,31,54,30,22,25,55,56,57,49,25,26,23,19,30,49,0,22,25,27,19,25,56,25,37,25,25,0,58,59,0,54,37,25,25,52,15,0,31,39,23,60,25,25,0,52,39,25,39,61,62,25,56,40,0,63,25,45,64,1,25,65,52,38,25,20,49,66,25,49,52,0,37,31,28,17,37,67,19,49,68,0,69,70,71,22,72,22,22,22,25,73,19,71,49,74,75,76,16,49,25,0,49,77,0,73,0,25,53,70,43,16,15,78,73,32,23,31,73,17,39,25,22,25,17,17,79,25,80,31,81,16,15,17,73,25,26,52,25,17,25,73,82,0,26,49,0,57,30,67,25,83,25,31,70,52,15,23,49,25,15,25,84,17,0,85,0,25,86,0,40,17,39,87,44,17,36,88,17,25,74,25,22,70,73,89,45,20,22,25,0,22,54,0,72,90,20,91,74,25,29,92,73,25,36,26,3,0,93,0,25,22,17,31,17,71,94,22,22,25,22,37,19,30,15,54,17,23,45,25,25,65,65,49,19,29,52,18,0,73,25,0,29,95,52,53,25,17,63,19,49,25,0,96,73,25,51,73,97,27,0,0,49,25,66,25,58,98,53,49,0,45,70,49,25,29,74,74,25,36,54,65,54,27,25,25,45,31,0,52,1,25,25,0,29,0,25,20,17,70,25,0,99,56,17,16,39,100,37,15,37,15,101,102,103,104,10,105,5,8,106,10,107,105,108,8,105,109,8,110,106,111,10,5,10,112,11,10,11,11,103,8,113,11,114,115,105,116,4,102,11,7,8,117,11,118,119,8,120,8,8,121,4,8,5,108,122,123,124,125,105,7,5,126,127,10,4,5,10,128,129,116,4,130,131,105,10,106,105,132,122,4,102,8,133,4,134,10,10,11,135,8,106,136,5,4,137,138,139,140,138,141,141,142,143,144,145,146,143,147,148,149,137,149,150,151,152,153,142,154,139,137,145,150,155,137,156,157,158,137,159,137,160,147,161,162,161,163,164,165,162,166,161,164,161,164,164,167,161,161,161,164,162,168,162,161,162,162,169,170,161,165,161,162,171,12,171,172,172,172,172,173,174,175,176,175,177,178,179,180,177,181,182,175,174,174,182,181,183,184,185,183,186,187,188,189,190,191,192,193,194,195,13,13,196,13,194,194,192,197,192,198,192,199,192,200,13,199,13,197,201,192,192,192,196,202,203,194,197,194,192,192,195,196,194,192,196,195,197,204,205,203,194,194,13,194,194,195,206,194,199,193,13,207,207,192,194,13,205,192,208,209,210,210,211,212,209,210,208,213,210,214,214,215,216,217,217,214,215,214,215,218,214,219,214,215,214,219,219,214,220,221,214,214,214,217,222,219,214,223,223,224,225,226,227,227,225,228,228] : Array Nat)[i-1638]?).getD 0
  | 8 => ((#[36,19,73,0,25,27,0,25,57,52,229,0,25,30,25,81,49,0,53,27,0,0,53,73,52,25,53,54,71,22,70,25,53,71,96,25,49,49,19,19,53,70,0,81,52,25,53,81,31,0,17,53,77,30,25,41,97,0,17,53,94,22,37,25,0,54,25,54,49,49,0,0,45,49,39,63,0,0,49,22,0,25,63,25,230,0,0,25,37,0,19,17,0,0,22,0,70,19,22,60,22,25,19,74,22,0,19,0,57,19,49,52,0,49,25,22,0,22,22,54,17,0,25,22,231,74,0,22,65,22,49,22,22,0,96,63,27,31,26,0,31,25,25,74,22,22,27,49,0,0,67,37,70,84,0,25,73,0,0,49,25,25,22,73,53,27,44,17,40,60,0,22,0,17,53,25,17,25,22,25,22,19,54,17,49,31,0,0,49,232,53,0,49,19,22,25,63,56,25,49,233,52,27,73,0,25,25,25,57,0,0,0,25,17,0,23,0,15,17,0,17,22,44,22,54,71,73,17,233,0,53,67,67,25,1,0,0,15,22,25,25,0,31,49,19,39,52,38,54,73,54,54,0,0,0,25,0,97,52,71,49,71,17,37,67,26,53,49,73,53,22,67,53,19,25,0,73,22,44,27,15,25,49,0,22,31,25,0,25,70,27,60,53,25,0,54,25,0,49,81,22,67,78,53,73,17,0,22,30,36,82,31,53,82,49,53,54,25,22,0,20,49,0,0,0,84,22,17,26,38,49,54,31,73,27,0,65,25,54,22,22,53,60,60,52,53,25,54,63,96,49,0,25,0,0,22,25,53,0,22,25,0,37,22,49,31,67,19,40,229,25,17,67,17,40,0,0,70,31,17,25,25,67,25,0,0,49,17,52,54,53,49,25,54,53,25,25,0,49,0,234,19,49,0,25,22,25,49,15,97,73,0,67,0,19,54,17,49,31,0,22,19,67,25,49,0,0,233,88,19,17,40,23,22,54,81,40,19,25,0,19,63,53,25,54,25,25,22,49,19,73,60,0,19,22,231,53,27,22,53,22,22,25,25,25,25,0,0,25,22,31,53,0,49,54,25,25,57,19,0,25,52,49,81,0,53,25,22,25,53,0,0,19,19,53,0,60,19,232,0,63,0,0,49,0,22,25,71,49,25,95,32,19,15,0,26,0,70,54,49,19,22,19,53,0,73,25,67,49,22,37,52,25,26,53,22,52,19,22,0,0,54,19,65,1,232,15,0,73,19,25,0,70,49,71,0,31,25,53,25,25,44,81,0,0,0,17,235,22,25,63,25,52,25,25,25,236,8,106,110,105,10,106,8,237,105,106,8,110,110,112,106,125,8,8,10,8,105,110,8,106,110,112,10,125,112,8,125,10,11,8,106,110,237,125,105,116,106,116,10,10,11,125,106,106,112,112,8,106,105,120,238,106,125,105,8,8,131,8,110,10,8,120,112,105,238,8,10,239,125,112,8,10,8,11,106,112,108,240,125,105,106,112,106,131,106,112,105,238,106,116,10,123,10,116,8,10,238,8,240,125,241,8,10,112,8,110,159,159,155,155,159,242,243,161,161,242,243,244,243,242,244,245,163,244,243,246,244,244,244,243,243,161,243,242,242,243,161,161,161,161,161,247,161,165,248,161,243,163,243,244,243,162,244,165,161,242,161,243,243,169,161,245,244,242,243,242,243,162,244,169,161,243,161,164,242,243,161,169,168,244,244,161,244,243,242,243,161,161,244,161,242,243,249,249,172,250,172,172,251,172,249,177,174,252,253,252,254,255,183,187,256,257,256,183,258,184,252,258,257,258,256,259,254,260,254,261,187,256,187,252,187,254,257,262,183,187,261,256,257,258,261,256,184,252,254,183,263,254,264,254,265,258,190,258,183,254,264,254,266,259,188,187,258,267,259,254,187,252,255,257,256,262,252,268,183,183,257,269,254,257,187,270,271,256,263,263,266,257,272,187,264,187,254,254,266,261,256,252,259,183,271,261,254,190,259,259,254,263,273,274,275,254,256,276,187,258,257,183,256,261,267,187,256,269,258,263,256,277,253,258,183,252,187,252,278,254,263,256,279,278,183,183,280,263,256,281,261,266,183,252,189,263,252,279,252,254,259,183,261,254,259,271,267,282,254,261,188,187,252,283,256,183,184,269,256,267,267,187,252,284,262,187,261,271,285,258,257,183,286,183,256,263,183,183,259,252,283,257,287,262,269,288,267,258,269,254,279,263,256,183,254,289,263,290,187,263,279,267,259,258,187,256,263,265,183,258,261,283,254,184,254,183,266,258,256,279,269,252,258,263,263,279,187,201,195,194,197,194,205,192,197,193,205,194,207,197,207,194,192,202,192,192,192,194,192,207,194,195,192,192,194,201,194,202,195,207,192,194,194,197,192,291,13,201,197,207,201,207,205,203,205,13,197,207,192,192,207,13,194,201,195,197,192,194,205,205,201,194,197,292,194,193,192,207,192,195,199,13,201,195,197,194,195,194,197,196,194,197,201,205,207,205,194,195,197,192,195,195,205,193,197,13,194,207,201,205,201,199,193,207,201,194,199,195,194,192,207,192,199,192,197,201,195,197,192,197,197,207,197,193,197,193,293,294,201,197,201,207,13,192,195,194,192,202,197,197,194,199,13,192,197,13,194,192,193,194,194,194,205,192,194,192,205,207,207,194,192,192,205,195,197,195,192,194,197,202,201,207,197,192,197,195,197,207,201,207,197,205,195,203,195,194,201,193,207,192,195,194,201,207,197,194,195,202,194,193,192,201,201,192,194,193,196,197,197,294,194,195,192,192,192,207,192,192,195,194,203,207,197,192,194,194,201,194,197,13,197,194,192,192,197,194,207,195,194,207,201,197,205,192,197,192,199,205,207,192,14,199,14,194,197,193,192,197,294,197,193,207,196,193,194,294,195,210,295,296,208,209,297,298,297,209,209,209,295,295,210,299,300,209,301,209,210,211,209,213,209,302,301,303,210,301,304,210,301,304,305,209,213,210,210,210,302,301,304,297,298,299,209,210,299,209,306,295,307,209,300,308,302,209,305,297,210,210,301,301,309,302,295,310,297,209,309,310,210,209,210,209,301,295,295,300,297,311,210,312,297,313,297,210,209,209,314,302,297,210,295,209,209,302,209,211,311,301,209,209,295,297,315,295,297,314,301,209,316,214,221,214,214,317,318,214,215,319,214,214,215,216,221,214,214,214,217,216,317,214,221,318,317,317,317,214,318,214,317,214,320,318,214,215,318,217,215,221,214,214,221,214,318,318,221,214,317,319,214,316,214,214,215,214,221,317,214,321,317,214,214,215,214,318,318,322,216,318,323,221,317,317,214,216,324,214,214,214,215,215,221,214,215,214,318,318,214,317,317,317,214,217,214,214,220,214,221,318,214,214,320,214,215,216,318,214,221,221,221,316,215,317,318,214,324,317,317,316,214,215,321,317,318,319,216,215,318,318,325,326,327,328,325,226,329,330,325,331,225,331,332,331,226,325,325,333,334,331,331,335,325,336,223,336,337,336,338,334,339,331,331,340,327,331,325,331,331,325,331,338,226,325,332,325,341,337,342,343,331,331,325,341,331,325,331,331,334,344,325,325,345,344,340,331,331,327,325,331,340,331,331,331,336,226,339,331,331,331,337,331,331,223,331,346,347,348,349,350,351,352,350,352,353,354,352,352,355,352,356,352,350,350,352,352,353,357,350,353,352,352,352,350,358,352,352,352,352,352,352,359,352,350,357,352,353,350,350,352,350,360,353,350,228,228,228,361,228,228,228,228,228,228,362,228,228,228,362,228,228,362,228,228,228,228,228,228,228,228,228,228,228,363,228,362,228,362,228,362,228,228,228,228,228,228,228,362,228,228,228,362,228,362,228,362,228,362] : Array Nat)[i-1598]?).getD 0
  | 9 => ((#[256,259,263,183,258,263,267,183,261,267,269,183,187,271,183,269,263,183,258,257,263,271,263,256,183,183,252,267,263,183,257,187,256,258,187,271,254,262,265,187,254,252,256,257,271,256,256,254,259,267,271,187,183,187,258,267,257,254,183,183,257,254,183,259,252,254,183,252,267,187,183,271,254,187,257,262,187,254,257,254,252,267,271,210,300,302,295,209,297,295,295,209,302,302,301,209,209,210,301,302,209,364,210,297,295,209,301,209,297,300,210,364,295,210,297,301,364,300,364,210,209,301,297,297,300,364,364,297,300,301,300,325,331,331,336,331,225,365,225,225,336,336,225,366,333,225,331,225,331,331,336,336,336,325,331,336,336,367,225,368,347,348,348,347,349,369,347,347,347,347,347,347,346,348,347,348,348,347,370,348,348,348,348,347,348,348,348,369,348,349,347,347,347,350,350,350,353,353,352,352,353,350,350,350,353,228,228,228,228,228,228,228,228,228,228,228,228,228,228,228,228,228,228,228,228,228,228] : Array Nat)[i-640]?).getD 0
  | _ => 0
def selectedTeaching (k i : Nat) := (chartTeaching[pickTeaching k i]?).getD (0,0,0)
def tileRows (w : Nat × Nat × Nat) (r : Fin 32) : Row :=
  Fin.ofNat 512 ((w.2.2 >>> (6*(if r.val<w.2.1 then r.val else 0))) % 64)
def teachingTest (g : Forest) (k i : Nat) : Bool :=
  let w := selectedTeaching k i
  let s := (selectTeaching w.1).1
  facetOK32 (tileRows w) s.roots s.out (targetOf g) (stateSet g k i) k s.price
theorem teachingTest_cut {g k i} (yes : teachingTest g k i=true) :
    Impossible true (targetOf g) k (stateSet g k i).toFinset := by
  let ss := selectTeaching (selectedTeaching k i).1
  exact facetOK32_sound (sel:=ss.1.select) ss.2.1 ss.2.2 yes
end Nat92GE

theorem spanTeaching {g k a n} (h : ((List.range n).all (fun j => Nat92GE.teachingTest g k (a+j)))=true) (mode : g.mode=true := by decide) : spanOK g k a n := by
  intro i lo hi
  right
  rw [mode]
  have v := List.all_eq_true.mp h (i-a) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le lo] at v
  exact Nat92GE.teachingTest_cut v

theorem spanMerge {g k a n m} (h : spanOK g k a n) (h' : spanOK g k (a+n) m) :
    spanOK g k a (n+m) := by
  intro i hi hj
  by_cases lt : i<a+n
  · exact h i hi lt
  · exact h' i (by omega) (by omega)

theorem forest_span (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : ∀ k ≤ top, spanOK g k 0 (g.levels k).1) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with ok|done
    case inr => exact done
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact ok
  | succ k ih =>
    intro hk i hi
    rcases rows (k+1) hk i (by omega) (by omega) with ok|done
    case inr => exact done
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact ok

theorem root_span {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : ∀ k ≤ top, spanOK g k 0 (g.levels k).1) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_span g top prior low geom blocks _ le i idx.1

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP5_0 : spanOK g63 5 0 6 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB5 : spanOK g63 5 0 6 := crossP5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_0 : spanOK g63 6 0 6 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_6 : spanOK g63 6 6 1 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_7 : spanOK g63 6 7 132 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_139 : spanOK g63 6 139 5 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_144 : spanOK g63 6 144 9 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_153 : spanOK g63 6 153 2 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB6 : spanOK g63 6 0 155 := (spanMerge (spanMerge crossP6_0 (spanMerge crossP6_6 crossP6_7)) (spanMerge crossP6_139 (spanMerge crossP6_144 crossP6_153)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_0 : spanOK g63 7 0 15 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_15 : spanOK g63 7 15 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_111 : spanOK g63 7 111 94 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_205 : spanOK g63 7 205 23 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_228 : spanOK g63 7 228 256 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_484 : spanOK g63 7 484 256 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_740 : spanOK g63 7 740 256 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_996 : spanOK g63 7 996 256 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1252 : spanOK g63 7 1252 256 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1508 : spanOK g63 7 1508 130 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1638 : spanOK g63 7 1638 256 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_1894 : spanOK g63 7 1894 154 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2048 : spanOK g63 7 2048 94 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2142 : spanOK g63 7 2142 68 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2210 : spanOK g63 7 2210 24 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2234 : spanOK g63 7 2234 10 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2244 : spanOK g63 7 2244 62 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2306 : spanOK g63 7 2306 11 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2317 : spanOK g63 7 2317 31 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2348 : spanOK g63 7 2348 2 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2350 : spanOK g63 7 2350 2 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2352 : spanOK g63 7 2352 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2353 : spanOK g63 7 2353 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_2354 : spanOK g63 7 2354 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB7 : spanOK g63 7 0 2355 := (spanMerge (spanMerge (spanMerge (spanMerge crossP7_0 (spanMerge crossP7_15 crossP7_111)) (spanMerge crossP7_205 (spanMerge crossP7_228 crossP7_484))) (spanMerge (spanMerge crossP7_740 (spanMerge crossP7_996 crossP7_1252)) (spanMerge crossP7_1508 (spanMerge crossP7_1638 crossP7_1894)))) (spanMerge (spanMerge (spanMerge crossP7_2048 (spanMerge crossP7_2142 crossP7_2210)) (spanMerge crossP7_2234 (spanMerge crossP7_2244 crossP7_2306))) (spanMerge (spanMerge crossP7_2317 (spanMerge crossP7_2348 crossP7_2350)) (spanMerge crossP7_2352 (spanMerge crossP7_2353 crossP7_2354)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_0 : spanOK g63 8 0 16 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_16 : spanOK g63 8 16 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_112 : spanOK g63 8 112 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_208 : spanOK g63 8 208 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_304 : spanOK g63 8 304 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_400 : spanOK g63 8 400 24 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_424 : spanOK g63 8 424 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_520 : spanOK g63 8 520 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_616 : spanOK g63 8 616 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_712 : spanOK g63 8 712 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_808 : spanOK g63 8 808 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_904 : spanOK g63 8 904 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1000 : spanOK g63 8 1000 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1096 : spanOK g63 8 1096 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1192 : spanOK g63 8 1192 90 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1282 : spanOK g63 8 1282 49 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1331 : spanOK g63 8 1331 256 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1587 : spanOK g63 8 1587 11 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1598 : spanOK g63 8 1598 256 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1854 : spanOK g63 8 1854 256 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2110 : spanOK g63 8 2110 64 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2174 : spanOK g63 8 2174 111 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2285 : spanOK g63 8 2285 5 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2290 : spanOK g63 8 2290 2 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2292 : spanOK g63 8 2292 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2293 : spanOK g63 8 2293 23 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2316 : spanOK g63 8 2316 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2317 : spanOK g63 8 2317 5 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2322 : spanOK g63 8 2322 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2323 : spanOK g63 8 2323 7 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2330 : spanOK g63 8 2330 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2331 : spanOK g63 8 2331 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2332 : spanOK g63 8 2332 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2333 : spanOK g63 8 2333 13 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2346 : spanOK g63 8 2346 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2347 : spanOK g63 8 2347 5 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2352 : spanOK g63 8 2352 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2353 : spanOK g63 8 2353 7 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2360 : spanOK g63 8 2360 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2361 : spanOK g63 8 2361 10 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2371 : spanOK g63 8 2371 11 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2382 : spanOK g63 8 2382 240 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2622 : spanOK g63 8 2622 256 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2878 : spanOK g63 8 2878 14 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_2892 : spanOK g63 8 2892 111 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3003 : spanOK g63 8 3003 130 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3133 : spanOK g63 8 3133 18 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3151 : spanOK g63 8 3151 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3152 : spanOK g63 8 3152 11 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3163 : spanOK g63 8 3163 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3164 : spanOK g63 8 3164 52 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3216 : spanOK g63 8 3216 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3217 : spanOK g63 8 3217 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3218 : spanOK g63 8 3218 4 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3222 : spanOK g63 8 3222 64 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3286 : spanOK g63 8 3286 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3287 : spanOK g63 8 3287 5 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3292 : spanOK g63 8 3292 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3293 : spanOK g63 8 3293 6 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3299 : spanOK g63 8 3299 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3300 : spanOK g63 8 3300 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3301 : spanOK g63 8 3301 1 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_3302 : spanOK g63 8 3302 19 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB8 : spanOK g63 8 0 3321 := (spanMerge (spanMerge (spanMerge (spanMerge (spanMerge crossP8_0 (spanMerge crossP8_16 crossP8_112)) (spanMerge (spanMerge crossP8_208 crossP8_304) (spanMerge crossP8_400 crossP8_424))) (spanMerge (spanMerge (spanMerge crossP8_520 crossP8_616) (spanMerge crossP8_712 crossP8_808)) (spanMerge (spanMerge crossP8_904 crossP8_1000) (spanMerge crossP8_1096 crossP8_1192)))) (spanMerge (spanMerge (spanMerge (spanMerge crossP8_1282 crossP8_1331) (spanMerge crossP8_1587 crossP8_1598)) (spanMerge (spanMerge crossP8_1854 crossP8_2110) (spanMerge crossP8_2174 crossP8_2285))) (spanMerge (spanMerge (spanMerge crossP8_2290 crossP8_2292) (spanMerge crossP8_2293 crossP8_2316)) (spanMerge (spanMerge crossP8_2317 crossP8_2322) (spanMerge crossP8_2323 crossP8_2330))))) (spanMerge (spanMerge (spanMerge (spanMerge (spanMerge crossP8_2331 crossP8_2332) (spanMerge crossP8_2333 crossP8_2346)) (spanMerge (spanMerge crossP8_2347 crossP8_2352) (spanMerge crossP8_2353 crossP8_2360))) (spanMerge (spanMerge (spanMerge crossP8_2361 crossP8_2371) (spanMerge crossP8_2382 crossP8_2622)) (spanMerge (spanMerge crossP8_2878 crossP8_2892) (spanMerge crossP8_3003 crossP8_3133)))) (spanMerge (spanMerge (spanMerge (spanMerge crossP8_3151 crossP8_3152) (spanMerge crossP8_3163 crossP8_3164)) (spanMerge (spanMerge crossP8_3216 crossP8_3217) (spanMerge crossP8_3218 crossP8_3222))) (spanMerge (spanMerge (spanMerge crossP8_3286 crossP8_3287) (spanMerge crossP8_3292 crossP8_3293)) (spanMerge (spanMerge crossP8_3299 crossP8_3300) (spanMerge crossP8_3301 crossP8_3302))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_0 : spanOK g63 9 0 18 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_18 : spanOK g63 9 18 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_114 : spanOK g63 9 114 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_210 : spanOK g63 9 210 44 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_254 : spanOK g63 9 254 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_350 : spanOK g63 9 350 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_446 : spanOK g63 9 446 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_542 : spanOK g63 9 542 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_638 : spanOK g63 9 638 2 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_640 : spanOK g63 9 640 159 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_799 : spanOK g63 9 799 34 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_833 : spanOK g63 9 833 34 := by
  apply spanTeaching (mode:=rfl)
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB9 : spanOK g63 9 0 867 := (spanMerge (spanMerge (spanMerge crossP9_0 (spanMerge crossP9_18 crossP9_114)) (spanMerge crossP9_210 (spanMerge crossP9_254 crossP9_350))) (spanMerge (spanMerge crossP9_446 (spanMerge crossP9_542 crossP9_638)) (spanMerge crossP9_640 (spanMerge crossP9_799 crossP9_833))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP10_0 : spanOK g63 10 0 41 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB10 : spanOK g63 10 0 41 := crossP10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP11_0 : spanOK g63 11 0 1 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB11 : spanOK g63 11 0 1 := crossP11_0
theorem crossT : ∀ k ≤ 11, spanOK g63 k 0 (g63.levels k).1 := by
  intro k hk
  interval_cases k
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · exact crossB5
  · exact crossB6
  · exact crossB7
  · exact crossB8
  · exact crossB9
  · exact crossB10
  · exact crossB11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K2109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullLower : Impossible true graph 11 instanceInputs.toFinset := by
  rw [show graph = targetOf g63 by decide +kernel]
  exact root_span (g:=g63) (top:=11) (i:=0) (before_sound K2109 V2109) g63G crossT (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_43236

open PEqualNP.Outside.L_meta_43236 in
theorem PEqualNP.Outside.L_meta_43236 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808392 * 2 ^ 32 + 4003523200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808392 * 2 ^ 32 + 4003523200) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s ⟨⟨gates,o⟩,fit,sz,correct⟩
  have legal : ∀ g ∈ gates, (g.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op=PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length≤2 := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  obtain ⟨gs,out,mono,small,ok⟩ := replaceShort fullLower gates o legal correct
  refine ⟨⟨gs,out⟩,?_,small.trans sz,ok⟩
  intro g hg
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg
