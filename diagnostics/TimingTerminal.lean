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

def g63Y : Array (Bits × Bits) := #[((bitLimbs [0xde2fffecdfefb7fe24,0xfd0134df79125f96f973]),(bitLimbs [0xa06242024e9910024,0x6100748d00121f84f140])),((bitLimbs [0xf5503c3b283fcee9db,0xc7fedeaad4fda56597ab]),(bitLimbs [0x7018380b000fc7495a,0x8426d28ad4f42520162b])),((bitLimbs [0x2ff76a2be05e6c1477,0x90d689a536f5605be5de]),(bitLimbs [0xf72ca28e016780415,0xf09028243665405be1d6])),((bitLimbs [0x9ba2cff09f04f9c7d8,0x2fffdf7e8f8ddb39423c]),(bitLimbs [0x81a0c1d14a1028c140,0x65d03720b89c011023c])),((bitLimbs [0x31cfad16d8cbe79bed,0x96abe3c1f34fc3ea3e44]),(bitLimbs [0x50dd8c46d808459a8a,0x929bc1c1f34dc3ea1c00])),((bitLimbs [0xe3dc53df34f95ef91f,0xde42373243e2b4ee5dd5]),(bitLimbs [0xe9280351325016b003,0x4c4f27324182b06e4dd5])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,16,2095,0,9),(0,32,2079,0,9),(0,4,2107,0,8),(2,0,61,0,8),(32,0,31,0,8),(0,2,2109,0,7),(1,0,62,0,7),(4,0,59,0,7),(8,0,55,0,7),(16,0,47,0,7),(0,8,2103,0,6),(2,16,45,0,6),(4,32,27,0,6),(0,18,4141,0,5),(0,20,4139,0,5),(0,36,4123,0,5),(0,40,2071,0,5),(0,48,6159,0,5),(1,4,58,0,5),(1,8,54,0,5),(1,16,46,0,5),(1,32,30,0,5),(2,4,57,0,5),(2,32,29,0,5),(8,16,2087,0,5),(16,2,2093,0,5),(16,4,2091,0,5),(24,0,39,0,5),(32,2,2077,0,5),(32,4,2075,0,5),(48,0,15,0,5),(1,2,60,0,4),(1,20,42,0,4),(1,40,22,0,4),(1,48,14,0,4),(2,36,25,0,4),(4,2,2105,0,4),(4,16,43,0,4),(8,2,37,0,4),(8,4,51,0,4),(8,18,37,0,4),(8,32,23,0,4),(16,32,2063,0,4),(24,2,37,0,4),(32,16,4111,0,4),(48,2,13,0,4),(48,4,11,0,4)]
def g63A : List (List Nat) := [[]]
def g63D5 := limbs80 #[#[0xd0c43087766003148020,0x8591d0c43580215d981,0x1c8214c030e61731cd60,0x58031dda84085300c074,0x65c4358421103985c872,0x1c961100435857008440,0x4808418d304811064043,0x600414c120209315c031,0x853065c64188214c072,0x990625c0214c08318970,0x190614c3831897008530,0x4c064188218c13024981,0x20971103206446418630,0xa8e98e8b65a64b62b443,0x9f06f05ee86e16cb2caa,0xfc8b86b6874e30b70af0,0xdbd4348d410d523d052c,0xc7d00594ba9e4b2d4528,0x5cc3898520cad4483d01,0x243242432386d4220d1c,0x2232b0ed0219d20c4d4d,0x55d28d652992514e2528,0x1d4259d49]]
private def groupPage0 := limbs80 #[#[0xdd832440106003244010,0x58c7244010dd84344010,0xa147344010a087344010,0x1c93044010a087544010,0x20f76440101cd3044010,0xa0f76440102177644010,0x5d9650c420a177644010,0x596640c420989650c420,0x61f630c420596740c420,0x99563104205956310420,0x59673104209cd6310420,0x99673104206027310420,0x61831480206003148020,0xdd83148020a143148020,0x600414802058c4148020,0xdd85148020a0c4148020,0xc74048020ddb3148020,0x58f4148020cc74048020,0x2077648020a0f4148020,0xe0776480202177648020,0x604744c020600414c020,0x59473584205944358420,0xa1431c802061831c8020,0xa0c41c802058c41c8020,0x58f41c802010f41c8020,0xe1d63cc420a0f41c8020,0x59443d042059674cc420,0x59673d0420d8c43d0420,0x61a73d042060273d0420,0x9d17010c212097010c21,0x6017610c21e197010c21,0xe017610c21a117610c21],#[0x6074310c215db4310c21,0x61a731502160e7015021,0x61c43580216004358021,0xd0c4358021a004358021,0x6005358021dcc4358021,0x6005458021a005358021,0xa0c5458021a005458021,0x60473580215cc7358021,0x9cc73580216087358021,0xdcc7358021a087358021,0xdcd73580219cd7358021,0x6027358021e017358021,0x6074358021dce7358021,0xa03535802161f5358021,0xe0176d0c216004398021,0xe0176d4c2161a70d0c21,0x589611443061a74d4c21,0x59162144309c96114430,0x1d0214c0301c8214c030,0x618214c030600214c030,0xdc4214c030a10214c030,0xdd8214c030dc8214c030,0xa08514c030600514c030,0xa08714c030600524c030,0xa08744c0301d0724c030,0x1ca214c030209614c030,0x1c7214c030dda214c030,0xddb414c030ddb214c030,0xa0b714c030a0b514c030,0x213764c030207764c030,0x5885258430e07764c030,0x60072584305905258430],#[0x1d56258430a087558430,0x1d564584302156258430,0xddb524c4316002198030,0x217764c43120b764c431,0xe0b764c431e03764c431,0x60054580316004258031,0x5c87258031a085458031,0xdcc72580315cc7258031,0x5c931580311c93158031,0x5ce7258031a023258031,0xa035358031dca7258031,0x207764c832a0b5358031,0x5c47158032a07764c832,0xa035358032e016158032,0x5d8430844058c4308440,0x61c43084406004308440,0x10d700844010d6108440,0x9c9610c4405857008440,0xa097010c402097010c40,0x10c72584406004358440,0xa1072584406007258440,0x2097098c41e01768c841,0x98e70d4841a097098c41,0xa0871580435c47158043,0x99072580435c87258043,0xe0161580439c87258043,0xdc97158043e016258043,0x99271580436066458043,0x9927258043a0a7158043,0x1c96258443dca7258043,0x9cd62104509cd6308450,0x9cd62d04509ce6210450],#[0xe1d320c8519ce62d0450,0xe0163108519cd6310851,0x600325805161a7310851,0xa00325805161c3258051,0xa0c4258051dc83258051,0x5cc73580515c87258051,0x20973580519cc7358051,0x6027358051a023258051,0x1cb3258051dce7358051,0x6003298051a0f4258051,0x61a73d0851e1d63d0851,0x61c63081101d37358052,0x18d200811010d2008110,0x2097010d10205700c910,0x61c43189106027210d10,0xa0843481106004348110,0x18c624811010c6248110,0x18d30481101893048110,0x20930481102053048110,0x18a31481102113048110,0x18f434811018b3048110,0x188714c110a0b5348110,0x1d0724c11018c724c110,0x9d8438811018f724c110,0x18c62c8110a08658c510,0x18a31c811018d30c8110,0x5c4510c12060272d4d10,0x195300c120600510c120,0x5c5300c120209300c120,0x219710c120215710c120,0xe1d310c520195310c520,0x4c5700c520209700c520],#[0x60031101205c43110120,0x602731052020d7110120,0x61c63145209cb3114120,0x8c970145202097014520,0x1c8314c120194314c120,0xa08314c1201d0314c120,0x194414c120a14314c120,0x600414c1201c8414c120,0x18c514c120a08434c120,0xa0c514c120600514c120,0x1c8714c120dc4514c120,0x10c724c1201d0714c120,0xdd0724c1201d0724c120,0x1cb314c1201cb304c120,0xa0b314c1201d3314c120,0x1cb714c1201cb414c120,0xdd3714c120a1b714c120,0xa08544c520a08434c520,0x600318c120194318c120,0xa0b318c120a14318c120,0x604548c920604438c920,0x9c931d0120606748c920,0x9cf63d052060273d0520,0x60c54085306044208530,0x1906208530a0c5408530,0xd9062085309906208530,0x61c64085306006408530,0x18970085301517008530,0x20d70085301917008530,0xa0d70085309917008530,0xd857008530d0d7008530,0xe0d7008530d897008530],#[0x1927308530a126408530,0x1967408530d927308530,0xa1a74085309967408530,0x6074308530e0e7608530,0xa0353085306035308530,0xd8b61085301936108530,0x1936208530d936108530,0x1976408530d936208530,0x9db64085309976408530,0xd90620c530190620c530,0x193620c530602720c530,0xd93620c5309cb620c530,0x20971101306002110130,0x18970105305886210530,0x60041141305c84114130,0xa0c42145305cc4214530,0x9cb61145309cc6214530,0x19062149309cf6214530,0xa0c5418530a0c4218530,0x60064185306046218530,0xe1d61185306046418530,0x9cb62185309927218530,0x2046418930a0c5418930,0x60864189306046418930,0xe046418930a086418930,0x9d162189302056218930,0x5897118930e1d6218930,0xa126518930a126418930,0x5c5701913058a7118930,0x5c971191302097119130,0x99764485305cb7119130,0x99062885301906288530],#[0xd9062885309946288530,0x99764885301897088530,0x190218c130188218c130,0xa10218c130600218c130,0xa08318c130d84218c130,0x600418c130190418c130,0xa08618c130190618c130,0x204648c130190628c130,0x604648c130208648c130,0x193218c130187218c130,0xa0b318c130087308c130,0xa0b618c130193418c130,0x6086498530a0c4298530,0x1927298530a086498530,0xa0b619853060b6198530,0x60464989302046498930,0xe046498930a046498930,0x18570c853099461c8530,0x60272cc53099764c8530,0x9cf41d01309cc61d0130,0x5cc21d413058862d0530,0x5cd21d41309cc21d4130,0xd9272d85309c861d4530,0x21570189316006218131,0x219711513260062d8131,0x60032c421060454d8132,0x6027310620e19700c620,0x60031c8220a0c4198220,0xa0c41c8220a1431c8220,0x21130c822060043c8220,0xa0f41c822060331c8220,0x9d163086306004358221],#[0x20d7008630e1d6308630,0x60d700863058d7008630,0xe197008630d0d7008630,0x215620c6306035308630,0xa097610e302097610e30,0x2096358a30618724c630,0x60051cc23058e7298630,0xa0a61cc23021562cc230,0x60272cc6309c962cc630,0x60970cc63161843d0630,0x6004398232a0970cc631,0xe1d320cb10989300c310,0x10e62103109897110310,0x20930483106044348310,0x98d30483109893048310,0x10e6248310e053048310,0x1d0724c3106074348310,0x600744c31098c724c310,0x608744c310604744c310,0x9d2624c3101d2624c310,0x98b714c3101d2634c310,0x600424c7101d3724c310,0xd0c4398b10dd8724c710,0x9d5320c720e1d310c720,0x8c970107202097110320,0x98c514c3202097010f20,0x1d0724c32098c714c320,0x1d2634c320604744c320,0x191700873058c43d0720,0x60221d43305cc21d4330,0x5cc72583315c87258331,0xdca72583315ce7258331],#[0x2097010f41d0d7008740,0x10d708cb41a097010f41,0x10e708cb419d1708cb41,0x61c43983419d2708cb41,0xa097098f412097098f41,0x9cd630875060273d0b41,0x770de17c1f1cd6348750,0x1fa3ec7b8ef1be1fc3d8,0x65dcb996f2be56c9f937,0xed1b9f53e67b4e797d2f,0x3ba734de97d2da5747e8,0xad759eaf55da7d4f69e5,0xf636be57aaf35dab756d,0xbad6dabb5369eced9bb1,0xf1dcdb8f6f2dd5b9b6d6,0xe27c3f87b0ee1bbd379a,0xcc778eb1be36c5f8b715,0xdd9b735e67cb78fb1ee3,0x9f33d679cf19db3ae73c,0xf556a7d3da6f4d697d1f,0xd6b9d6dad759eaed5baa,0xf8de9bcb756e6dc7af35,0xe4fc7b8df1ae2fc3f85e,0xdcd79a733e5dcb795f2a,0x8fad756e79ceb9cf38e6,0xbc774ee5db3b5769ecdd,0xec028dd2812fa5f47e2f,0xc36200eae58e32e5020e,0x130812c97212ece7246e,0xc8f924570e32ea53a320,0x2230e4e2250ca0ab9047,0xc6c89b8273057388ca8c],#[0x7306586b305399924b43,0x2ea68173027400c49e81,0x469092c7f8db2e988db,0x7b88124b42250efb81f3,0xe32ea63eeec042170e,0xa070e073a0ca8d266ec0,0x88ca8c8cd2a04a32ec20,0xaecdda29249a9712ab43,0xec3405b2c16a0f0e7e30,0xea70f9225800b2ea0226,0x99bc0c89ba06ec0d0db2,0xc2e8ca7c2250ef40db2e,0x81f305801f30fe256ec0,0x27304c8c12a468073015,0x86ec0892c9481f30650,0x205e9ab2053b210c733d,0xa81a490cd5b690872903,0xaec4086f832d0617218c,0x52f8ca87b010871acae4,0x13b2ea6bacc40a8892c9,0xf0ca93a48c67a320e822,0x12435a3d285514928e1a,0xc8b626b0ece0ed28f3c1,0x89908b2cdcbdd28e2b00,0x288b124b441324e29a52,0x683b30d511524059bb20,0xa4b302c3fee62bbad0a4,0x8104720a33032a3b0eaa,0x330d2107204689720b33,0x30d4037204fc16c69b87,0xce7a772e2e416ec1088f,0x4c8a52cc3aab0ec4272e],#[0x489330d1101266511720,0x23d081fa38c8aa0ef2c1,0x653083bb8c8b04352438,0x4e8b923ec6a2c10c89b9,0x206531ce82cbb8c89cb4,0xec0a4f0e241292ae19cf,0x27272e6420f52efa3cb0,0xd23908e4acce4aea4f30,0xa98c8d2a1d0a473152cb,0x7330a8238e8579152404,0x304f23ab24d7b4f24248,0x20e9bcec89bb3f2c3329,0xec33a8ca848ed289d16f,0x4524ae6db3acc4082b72,0x13030c329ab2054b3f26,0x903205dbcf0e3195d248,0x4f2425955309c9072eba,0x324bb0f33068238e85c3,0xcf7c5ae66ca6f2222b1,0x1019432ea625922ba27f,0x9ea4aecaf9b320b694b2,0x89d92ac892d2ae0c0ec4,0x2d2e2ac3050ccb1d7204,0xb320cf288e88598d2a48,0xe24d16b22e2390ca8b1,0xe62b953269b3c8c8ab35,0xecba3b289026f24b4b3e,0x4bb49242229ce8e303b2,0x740d24f631b04b410320,0xb2d06188912ca3b1304b,0xa8ea7431320bd3e12435,0x908e426cec783b8c89fb],#[0xc66f8f52e71a3b0ecca3,0x92408c49e8d12a2732e,0x9baf92ad843d289c8633,0xbb1304b894d289cc150c,0x1a32c181072ebc1ab225,0x392e533bee87639f2a27,0x6e289103204c26eec032,0x2e4da3f209abd5287dad,0xc89c50c89ea1b0c0a89d,0x7f412c4adad50a6d07d2,0x92850ca13b928272cd08,0xa773035c3ec89cb94eaa,0xbeec32a8508d482b3056,0xcc41a2c5047ab2d0611b,0xc8c5a1d2a088ef209aba,0x8ff87320bd23d0ca1b60,0x5625d0c821812ad43cb0,0xda1aece39e12ab425f04,0x360c8c302b2e6489d2e2,0x1b0c0b8f5300a24ec66e,0x72427370e4330f73065a,0x303a11320b0903205fbe,0x8e609d2e4a8f32105a77,0x6d3df28e13d086510e92,0x99152405461069ead10a,0x23d0c85258e866a772e6,0xa528cba3b269a8a52e34,0xd0c8b23b30f3320c8c30,0xe6eca3b0cf0911245723,0xeb1a38c8d2a1d2a6bbba,0xc90e928fe9812ababcb2,0x7143221dbd2c831480c8],#[0x40f2e3082f20623bf282,0x5f0eb9b00c8c6b192e53,0x8ca7f0f53105a89249aa,0x202707730fc09d2e673a,0xd013992a270ef20203ff,0x61af20b40532ea4a3f0,0x9bf1223b24f303b0f321,0x103304a02b206a3450c7,0x1f22e12392822be2c6e8,0xd2cb2c152c7f390ca90c,0xe8f4aa30ec223d281f87,0x46c3ec89fb572267bd0,0x49a924b404d2eef1073,0x502f203024d082c23909,0x25ce866b57222bb28c67,0x5b0e68a690e3931d0854,0xac650b3ec68782b2e692,0x2021ac704ea40b24f63b,0x6bd2cb046d89b204602f,0x5d3cb2e988f7202735b2,0xeb06ec341ab305390330,0x82b2e26b450c73bd0c89,0xc1245713b2ea7274ec92,0xf20bdbf0e60193b2e999,0x22131812abc03f30d48e,0x4bb09f3035c78c8c23ab,0xba348e45a26f3000b152,0x2a3b0cfb39d0a2725d22,0xa1f0e09324c833277202,0x2b2edb448c89f2b7069c,0xf206ec48c89b83330508,0xcac94b210226eec0202],#[0xa8726b24b4a5d28ba269,0xb0ac5048024f303bba8c,0x72690c811f320c7bd6c8,0x9a320b80712e5b117205,0x372e4f0332ea03c8c8b5,0xb0cf2a3b0ed0218ca960,0xecd21cca1c23b0ea7a3,0xec33a8ca8c474c41aa3b,0xb7ba8ca8da58ec918572,0xdb052833a9ec8d29a72e,0xb1d245331520bd3bd243,0xdb209c21cca0b21d0a29,0xb0ecf07b30f9b1922533,0x2645a39209aa1f0e09a3,0xc122f2ecdc3bec8b133f,0x13276ec36a3f0c52a5ee,0xcbd102bca5f2c60bad22,0x9b5205ca4f30358bb20d,0x4aecdb89b204b349242b,0xd2c8c14b2102a1d0a273,0xcf50ed2ebea4eec3cbc,0xc1a8f52cd30f3302c23b,0x13af10ab9af52a162db0,0xc3d0c8d61bb206610526,0x3a8ca8b8e928ff07d2cc,0x652c8625f300f9632e6c,0x52a78a1d0e153f2e6278,0x305e3d508512d2e28098,0x40633f2c36360e8330f5,0x441052612a3d0cbe1152,0x29c52e410f5243e11524,0x8492ef5b28c672a5f242],#[0x67069eb132cbd21f2a22,0xd0cae280e837c16ec39c,0x83fbbb08271052eefa5,0x8882f206aa3d0ca231d,0x190292ed9113205187b3,0xbb250822459069f08b2c,0x21d0a47acd0683321282,0xf52a0cc16ec1123908a3,0x330beba92a0d90730582,0xc89eb1108ee23f0d0087,0x4e2a4ce661c59069bc56,0x5ab9b0a272830ec2c152,0x41852a70a3d28e2a5904,0xb050cc99132044a39090,0xe2e6283330c349812a46,0x302f182f307782b20d8b,0xe629394eaaba78ea72a9,0xe07b9d2a19b4f2cdbbe2,0xe288e88e87f30358d72,0x131d0e3f23d081eb2d06,0x2c906833fee667c1724e,0x6f2cf7338e62225b22ba,0x924b4bbeec38c1124e12,0x2ebf31b02b38ab20caa6,0xb403b2eafa3b209abcb,0x25a8508fd31d22530972,0xeb94eaa9c11243a09f26,0x2772eea82f202d2f0ca8,0x69047fa3d282f24d0caf,0xb0e6440b0ea58ed30dfc,0x8ff873301b2850cd3a5,0x42221d0e86ae52a19bcd],#[0x9c4252a9ca39281e34f2,0xf94d28e091d243d23b30,0x29ce8a4bcb24f310330f,0xc8e4879cb2c108f33024,0xb0ebf276ec37bd0c8d1a,0xc3234b0c351a528bfbc,0x23590320603e1242734b,0x9b88b2c1234f242bbf72,0x50f52ef10892c943c8c8,0xa3f30a891b2c9b1432ea,0xc8c8c111524439152cac,0xeec3682f2cda903205f3,0x2cf745f069f45f069ba4,0xc9709b262612d2a9ca69,0x22c30e8323c8c89f0b12,0xeb01087923f28e025924,0x3c8e8592770ce1a3b304,0x3d282fa3b00d6c0ae448,0x6ec348492eed0f52e74a,0x229e0492ef023b0ea83f,0x45324ee62b9352cd396b,0xa41e924c891b20fcb192,0xa1b52058a3f0c5229ce8,0x42d2a7f37ec2c32c5048,0x3f0c1dbd6e8f4b3ee622,0xb2050398ea7187330c1a,0x308426b0ecea3f269a9a,0xa8f08b2cde89d2e25063,0x2703f30fd21d2a1cba8c,0xb9ab22f69a528c019128,0xad2e27b15d247d25f2ce,0x4b21032190a2a3d0e875]]
private def groupPage1 := limbs80 #[#[0x92ad708f30ad1bf20659,0x872b56c2c30e92849af,0x4cd8a730c2c192c7cb6f,0x1023b0e23af0ca883cb2,0xcc7d24c71112e01ba92a,0x23b30cdb50e2599552c9,0xfd2c9cafcca333b8e876,0x6ec3243b289ca9d28e2b,0x8711ad2441a770eeb41,0x8470f5266b1152c81311,0xf08b307039aca0a0e92,0xea5b0455a1b2a1ca5eec,0x48322c60a330c2a692c7,0x63229cc38c89ca3d2890,0x6c89e87330c2c16ec354,0xca09ab2223ba8ea713d,0xab7143230002b206ea85,0x3589d2e232e32a199792,0x8b4aecde23d0c76c1724,0xf52eeeb3eec331892a4,0x192ae52b2e6fd9072065,0xd26131cf2046a4eec37a,0xe6679f924b43572cd9ba,0x43d44ec89b9bf202733e,0x9d2fcca141212ae98f52,0x1352c23339cca0a14d28,0xc5b249cc232a9c913203,0x4ec89f3b8e8773db28e2,0x8eaedc5d249cbbd08274,0x2e63a3d0829a58ec9127,0xe3eb3f2c371332ec809d,0x2a91320432b6e66f3450],#[0xf2392503a3aec4f30108,0xbf6ec3a82f20828ed201,0x9d2e262590c959792acf,0xd24b49532eca46ec49e8,0xca8fba8ca8ab27282ba6,0x6e0a3b282fa4b0e243a8,0x323acc41bbb92835ab30,0x534ee462b3f2ce6b2b0c,0x2f2c2108b2c17a3f2d0,0x6f300107d2cb20f73027,0xb2082a3f2ee927d0a84a,0x30408f320611a720b782,0x82703b2e98414c89b9c5,0xda3cb2cfaa5928ba23d0,0xec38c89fc68c49ebb52a,0xa3b0ecfa6f3042b98eae,0x4924df23b2c4fa3d2503,0xcec979a524c1b1324bbb,0x22e2a5f22ba13b2e98a4,0xf8b57222234ac60ec1b,0x1d24eec3c0f320968453,0x833f062b23b0ed0a8908,0x23d282e8572ce89c1225,0x812aad09d2e492772063,0xb2c0f460e603b4f2cdd1,0xe8f10652c932192a2288,0x8b53e6ec3225f300dbb8,0x72955269da5f30100ed2,0xdb00c8c4a3b0e9a3490c,0x26eec403050cc52b7069,0x333102a8908f937ee233,0x9087f3f72227370c4c30],#[0x3006a1d2ada23d0c8e2c,0x1c60a9c38e0e200021d,0xf81735d4e433a281a120,0xb332a0f00dad2c3b0a28,0x9c1b1a6938b7f6356433,0x604c3d2c1d150d00d8c,0x20e00d8d0bcb49c8d7f7,0xc9d958d85755c4d3f372,0xd5e4031221a00ddcfc0a,0xc0d02b827705098217c6,0x302848eb05c101fa8608,0x12393c0fc001b38960b0,0x9860650d1c1183a20804,0x5870e460568626d04287,0x31a101318f12221fc1c8,0x64e4805c70c44f02424c,0x80288050103303e1141a,0x204f127a082d91301603,0x88810043362ad84006f4,0x532b15b034c089f4865c,0x84c88000272106762d60,0xb41edac4000001027ea8,0x102e61040128204fd689,0xcb0d5861c0806c21,0xe21029c14b8198a14e42,0x476d31eb810d871c0e,0x1058cd041b0800043641,0x426f0e31c9a12d84001c,0xcd0fb54151a1000000d1,0x43a6840003bf63004d86,0xfb43e6840bf1564db]]
def g63D6 := groupedPages #[groupPage0,groupPage1]
def g63H6 := limbs80 #[#[0x26ff982a1a330840335,0x90a003c0340038004600,0xf023d97eb0048000001,0xc]]
private def groupPage2 := limbs80 #[#[0xc8105c032040740c810,0x417610c105c04304176,0x10d1004032440109c843,0x440101c9100405244010,0x4075440101d11004073,0xdd91004163440104c110,0x4801098d200416348010,0x40744c0101c93004264,0x1d1630407258c1098930,0xc80109d232042728c810,0x4163cc8101d33004073,0x9cf4204163d081099332,0xd4c109cf5204163d4810,0x81630c4201503108274,0x5d831081700c42059431,0xc42099031082620c420,0x82740c4209cc3108265,0x58c41083630c4209d431,0x104205c0410816510420,0x82651042098c4108262,0x5c0430816510c209cc41,0x10c205d8430817110c20,0x827610c209c44308265,0x5d8510816314420d8c43,0x480200c5200827314420,0x80514802010d2008041,0xd01200833148020cc120,0x48020d45200834148020,0x80744c0201053008376,0x10d61083414c02098930,0x584201d1610807358420,0x807458c201c56308163],#[0x9d231082628c420dc563,0x9842058e610804398420,0x8031c80209d26108273,0xcc72008043c802010720,0xcc0201073008341c8020,0x8054cc420d073008074,0x5973108163cc4201d331,0xcc4205db3108170cc420,0x8265cc4209933108263,0xd8f3108275cc4209d331,0xd0020cc74008031d0020,0x8163d042010f4108341,0x98b4108170d042059741,0xd04209934108263d0420,0x8171d0c209cf4108265,0x5c75308273d442058f51,0x10c215c04308674d4c20,0x874310c219c04308576,0x5c0540867014c215c053,0x580219cc540867015021,0x84545802114d6008443,0x1d56008474580211cd60,0x580219cd600857358021,0x8743580219d56008674,0x151630877358021d4d60,0xd0c215c2630844398021,0x8570d4c219c34308576,0x9d35308670d4c215db53,0x8430584210c06408430,0xc16508430590210c162,0x988210c176084305c021,0x8430994210c26408430],#[0xc05210430d4c210c274,0x590510c1621443058451,0x144305d8510c17014430,0xc27214430990510c262,0x5c0520c1641483058852,0x4c030990520c26214830,0xc0514c030105300c021,0x1c9300c0714c03014930,0x4c030585300c0744c030,0xc2614c030885300c162,0xd01300c3214c03098930,0x4c030d45300c3414c030,0xc3724c030dc5300c352,0x1c9310c3764c030dd130,0x584301c9610c05258430,0xc162584304c9610c075,0x985610c2325843059161,0x58830d4d610c26258430,0xc164588301d5620c071,0x146300c0218c030d4e21,0x8c43058a310c1618c430,0xc021980309d2310c262,0x14a610c3519803014660,0x98830d4e610c26298430,0xc26498830592620c071,0x87300c170c84305c664,0xd40305c3410c051cc030,0xc170d4430c87500c021,0x9c0420c570108319cb51,0x150315c0540c57614831,0xc4524c4319c8540c670,0xdc9310c7524c4311c931],#[0x4c8311c1320c7764c431,0xc45258031109600c770,0x1d1600c4725803115160,0x580314c5600c47558031,0xc632580315c9600c532,0x9d5600c674580319c960,0x58031d49600c74258031,0xc5768c8315c2320c753,0x5c3420c570988319c232,0xd4c319c3520c670d0831,0xc970150329cb530c576,0xdd9320c970190329c054,0x580321c5600c85458032,0xca71580325c5600c961,0x9c6600c96198032d4d60,0x844010c2110176d4c32,0x10176084405c02110161,0x9c831101700c44058431,0x144405c0431016310c40,0x100724c4405c05210170,0x1496110043584400c961,0x584401cd611007258440,0x10232584405896110132,0xcc961102625844098561,0xcc440cca611003298440,0x10021d00409cb3110170,0x98c5210563d004058740,0x580418c9601053258041,0x105768c841d4d6010752,0x5cf5210570d48415c263,0x14c429c35210663d4841,0x108715804214d6010970],#[0xd4d6010875580421cd60,0x580431c56010f7358042,0x10d62580435856010c72,0x9856010d72580435c560,0x580439916010e6258043,0x10e72580439c56010e65,0x1c96110f7158043d4d60,0x98043dc16110d6258443,0x10e65980439866010d61,0x5c02114163084509c660,0xc4509cc211417608450,0x141760c8505d83114170,0x5c041141631045058841,0x10c509cc411426210450,0x14163484501cd2114170,0x8c961141325845098921,0x58c501c5631404358850,0x142628845058e2114371,0x98a31141628c4509ce21,0x988505c6621404398850,0x14163c84509d26214271,0x58f3114273c84505c321,0xd045058f3214170cc450,0x14170d045058f4114162,0x58f4214273d045098b41,0xc8519cf4214262d0850,0x145760c8515c03214532,0x5c04214563108519c032,0x10c519cc421467010851,0x144704c8519c04314570,0x109601443258051dc132,0x580511c9601444358051],#[0x14532580511d16014473,0x8c96014573580515c960,0x580519cd601467258051,0x1474258051cc96014674,0xdcd601477258051d0d60,0x8c8515da32145708c851,0x14443980510ca6014670,0x5c33214563cc8515c263,0xd085158f4214670cc851,0x14673d08519c34214570,0x5c0431496310c529c343,0x580521d1601484358052,0x14b7058452dcd6014b43,0x1c56014d709905210e60,0x580541c5601537158053,0x4437258054dc56015072,0x19020440630811010c20,0x81105cc204412008110,0x44272081109902044263,0x5c032440620c11014830,0x10d105c043442720c910,0x44063141100c85044272,0x5c05244272141105c850,0x1891010c624417314910,0x44363189101946244063,0x14d20440434811019463,0x48110189204405448110,0x44130481101952044063,0x8c52044230481104c520,0x4811098d204423248110,0x4435348110d0d2044330,0x149304437348110d8d20],#[0x4c11018d30440624c110,0x440744c1101c93044071,0xd8930443524c11098930,0x4c110dc530443634c110,0x440764c9101953244372,0x19220440638811010e20,0x881104c2204406588110,0x440528c1109da2044263,0x98a30440658c11018a30,0x8c5109da30442648c110,0x440638c9101963144062,0x99232441708c91019632,0xc811010f204417098d10,0x44130c811018f2044062,0x5cf2044163c81104cb20,0xc81108cb2044231c8110,0x44353c8110d0f2044263,0x14b3044373c8110d8b20,0xd09105c33244062cc910,0x44173d41100cb5044170,0x5c35244063d4910ccb50,0xd4d105c35344173d4910,0x48065d8d1018f6244272,0x5c430481300c12014430,0xc1209c830482710c120,0x483510c1209d03048273,0x5c031481310c52019431,0xc5209c831482320c520,0x483430c5209d43148273,0x5c4404803110120d8c31,0x101209c4404817310120,0x4817010520cc44048273],#[0x9cc4148232105205cc41,0x10d205c4434817010d20,0x482721412018c5048272,0x5c0514806314520cc450,0x145208c8514817314520,0x4817114d20d8c5148273,0xc53048273151205c454,0x4c12010d30480414c120,0x480634c1201513048051,0x1d130480724c1201c530,0x4c120cc130480764c120,0x483514c120d053048331,0xdc530483634c120d8530,0x4c52010d31483744c120,0x480764c5201d13148054,0xc630483704c520cc531,0x8c1205ce30480518c120,0x483518c120cc63048330,0x5c231480638c52010e31,0x8c5209d231481738c520,0x480438c920d8e3148331,0x9d232482718c92015232,0xcc12010730482768c920,0x48341cc1205c73048051,0x5c33148054cc520d4730,0xcc5209cb3148270cc520,0x48276cc5209d73148274,0xc74048353cc520d0f31,0xd01208c74048131d0120,0x48170d0520cc74048272,0x9cf4148232d05205cf41,0xd0d205c34348363d0520],#[0x48173d41205c75048171,0x5c75348331d41209cf50,0xd8d209c76348054d8d20,0x4857014d215c04348674,0x5c06348443181215c054,0xd812114f6048443d8121,0x48753d81211d76048473,0x10c214c04208530dcf60,0x8530150214c05308530,0x4c06508530190214c062,0x994214c264085305c021,0x85309cc214c27208530,0x4c342085309d8214c274,0xd84214c35308530d0c21,0xc530d90214c36208530,0x4c0640c530188314c052,0xd48314c2760c5309c831,0xc930d90314c3620c530,0x4c021101305c4324c064,0x148414c271101305c440,0x10530190414c06210530,0x4c162105304c8414c065,0x988414c232105305c041,0x105309c8414c26510530,0x4c36210530d4c414c352,0x5c0424c0651093019042,0x10930994424c17110930,0x4c06410d30d4c424c273,0x84504c27210d305c443,0x141305c8504c04114130,0x4c34114130c84504c272,0x10c514c042145300c851],#[0x14530190514c06214530,0x4c272145305cc514c170,0xcc8514c276145309cc51,0x14530d84514c34214530,0x4c04314930d90514c362,0x5c0524c0641493018852,0x149309d0524c17114930,0x4c06415130d90524c362,0x9cc544c272151305c454,0x18530108614c03218530,0x4c05418530148614c043,0x584614c0641853018861,0x18530990614c26218530,0x4c332185309c8614c265,0xd80614c35218530d0861,0x18930d8c614c36218530,0x4c06418930150624c043,0x5c4624c1701893058862,0x18930994624c26418930,0x4c072191301c4644c271,0x5c4644c170191301d464,0x19130994644c17219130,0x4c370191309d4644c272,0x191214c37219130dc464,0x485301d9214c06548530,0x4c36448530d4d214c265,0x1c1314c0624c530dc121,0x58530dc1314c0724c530,0x4c07258530191614c062,0xdc9614c36458530d8961,0x589301c5624c06458930,0x4c04388530dc5624c364],#[0x18a214c0548853014e21,0x88530196214c06488530,0x4c26588530992214c170,0xd4e214c343885309da21,0x8c130086304c36488530,0x4c0418c1300ca304c031,0x18a304c0618c13014630,0x8c1309ca304c0648c130,0x4c3318c130cc2304c321,0xd86304c3518c130d0630,0x8c930192314c0628c530,0x4c3328c9305c6324c064,0x192614c0629853010a61,0x98530d0a614c27298530,0x4c36498930192624c361,0x193214c061c85309d265,0xc85301d3214c065c8530,0x4c353c8530997214c170,0x147304c021cc130d9321,0xcc530887304c061cc130,0x4c064cc53018b314c052,0xd4b314c276cc5309cb31,0xcc930d93314c362cc530,0x4c276cc9305c7324c064,0x147404c021d0130d9332,0xd0130187404c052d0130,0x4c272d01305c7404c062,0x10f414c341d01309cf40,0xd0530193414c062d0530,0x4c162d05304cb414c065,0x98b414c232d05305c341,0xd05309cb414c265d0530],#[0x4c353d0530d0b414c276,0x197424c064d0930d8b41,0xd09305c7424c170d0930,0x4c353d09309db424c265,0x107504c021d41305c743,0xd41305cf504c121d4130,0x4c321d41309cf504c221,0x18b514c061d4530d0b50,0xd45305c3514c064d4530,0x4c362d4530d87514c272,0x193524c062d4930d9351,0xd49305c7524c170d4930,0x4c052d85305c7534c364,0x58b614c132d853018b61,0xd85309cb614c262d8530,0x4c043d8930d8b614c352,0x997644c064d893015362,0x10d315c0424c5700c931,0x4c570149319c8434c570,0xc8604c672151315c054,0x18131188604c44318131,0x4c5701893110c624c672,0xcb604c570cc9315c331,0xd813110f604c442d8131,0x4c472d813118b604c454,0xd0b604c732d81311d360,0x10d32dcb604c762d8131,0x4c970151325c4434c970,0x5c7434c843181325c454,0xd813210f604c971d4d32,0x841700ca101c7604c854,0x4c1208417014a105c043],#[0x4c21098d208416348210,0x8416398a104c96184262,0x58f2084043c42100cb10,0xc6205c031881630c620,0x88273106205c04188273,0x58c518817110e205c043,0x4c2209cc518817014620,0x88031982201d16388041,0xc720883419822010660,0xc822010f2088041c8220,0x88331c82204c32088051,0xd472088341c8220d0320,0xcc6205db3188054cc620,0x88031d02209d73188274,0x9cf4188170d0620cc740,0x10e215c75388171d0e20,0x88570152215c05388570,0x14d6088443582219cc54,0x582215cd608845458221,0x88753582219d56088673,0x10c218c17098e2110e60,0x8630150218c05308630,0x8c1700863058c218c064,0x9d0218c265086305d821,0xc630d4c218c34308630,0x8c1700c630588318c052,0x9c8318c2620c6308c831,0x10630148418c3530c630,0x8c353106308c8418c170,0xc8518c17610e30d4c42,0x1463010c518c04214630,0x8c1701463058c518c162],#[0x9c8518c262146305d851,0x14a30d08518c33214630,0x8c17114a305c0528c043,0xd4d218c163486309d052,0x58630989318c0724c630,0x8c132586301c9618c052,0x1c5638c16358a3058961,0x8863014e218c07458e30,0x8c0328c630d4e218c163,0x5c6328c2628c63010e31,0x98230086608c2748ca30,0x8c043986300ca618c051,0x1d3218c2729863058e61,0xcc230d4f218c265c8630,0x8c162cc230147308c021,0xd47308c262cc23098730,0xcc63058b318c052cc630,0x8c272cc63098b318c170,0x5c3418c163d063010f41,0xd06308cb418c176d0630,0x8c342d06309cb418c262,0xd4f428c163d0a30d4f41,0xd4230087508c171d0e30,0x8c262d463058b518c321,0x9d3538c171d4e309cb51,0x10e315c0428c5700ca31,0x8c57614a319c8438c576,0x5c3318c7328ca319c854,0xd4a31993328c570cca31,0x8c97110e325c0438c970,0x10d608c971152325c054,0x58232585608c85458232],#[0x8ca6458232985608c971,0x10e608ca74582329c560,0x98232986608c96198232,0x8ca64986325c2618ca64,0x5c6648c97099232cca61,0x83105db328c970cca32,0xc4263083105cc20c4043,0x5c430c41300c3109c820,0xcb101d032c42620c310,0xc41760cb105c032c4132,0x10c40c43530cb109c832,0x10b1098840c417110310,0xc427310b105c042c4163,0x5c843c417110f105c043,0x10f109c843c417610f10,0xc4172143100c850c4343,0x9c850c4263143105d850,0x4831010d20c427315310,0xc4131483104c120c4073,0x98920c42324831058d20,0x48310cc120c426348310,0xc40424c3100c930c4343,0x1c930c40524c31010d30,0x4c31098930c40744c310,0xc43304c3109d130c4263,0xd4930c43424c310cc930,0x4c310dc930c43714c310,0xc40434c71010931c4374,0xcc931c40724c71015131,0x4cb10dd931c43424c710,0xc407258f1015163c4043,0x10e20c437258f101d163],#[0x8c31010e30c426388310,0xc40438cb10cc230c4262,0x5c232c40748cb1015232,0x8cb109ca32c41768cb10,0xc434398b1010e62c4274,0x4cb20c4130c831010f20,0xc83109cf20c4232c8310,0xc4373c8310d4f20c4343,0x98b30c4074cc31014b30,0xd031058f32c4272cc310,0xc4262d03108cb40c4131,0xd0f40c4273d03109cb40,0xd0b105c342c4163d0b10,0xc4032d43109cb43c4273,0x5cf52c4170d4b109cf50,0xd4f105db53c4273d4b10,0xc80510c3209d353c4272,0x15031c81710c3204c030,0xc7204c831c81310c720,0xc82320c7205c031c8163,0xd4c31c83430c72099031,0x103200c440c83630c720,0xc8331103205c440c8043,0x58c43c8273107205c041,0x10f205c443c817010f20,0xc834310f209c443c8264,0x4c851c8331143200c450,0x147205c051c816314720,0xc80314c3209cc51c8263,0x1c530c80514c32010530,0x4c3201d130c80724c320,0xc83314c32098d30c8161]]
private def groupPage3 := limbs80 #[#[0x10d31c83724c320dc530,0x4c7201d131c80544c720,0xc80544cb2010d32c8263,0xc630c805458f20dcd61,0x8c72010e31c80518c320,0xc8054cc72098e31c8054,0x58f31c8132cc7201d331,0xcc7208cb31c8170cc720,0xc8274cc7209cb31c8270,0xd8f31c8353cc7209d731,0xd0320d0740c8131d0320,0xc8170d072010f41c8343,0x9cf41c8264d07208cb41,0xd47204cb51c8171d0f20,0xc8274d47209cf51c8163,0x5c043c8674d4f205c753,0x193215c054c857014f21,0xc84535832110d60c8570,0x10e60c87535832115160,0x873019021cc17098f21,0xcc02114330d4c21cc170,0xd0450cc3211433010450,0x14b309c851cc17014730,0xcc265887305c064cc170,0x5c341cc052d0330d4e21,0xd433008750cc272d0730,0xcc321d433088750cc121,0x5c042cc672d4730d0b50,0x14b315c052cc67010b31,0xcc570153319c052cc573,0x5c064cc672153319c054,0x5833114960cc44258331],#[0xcc474583311c960cc454,0x58960cc532583311d560,0x583318c960cc57258331,0xcc6655833198960cc660,0x9d560cc674583319c960,0x58331d4960cc74258331,0xcc6708cb315c232cc753,0x99660cc662983315ca60,0x98b315c262cc67298331,0xcc672997319c262cc665,0x9c352cc670d0b315c342,0x583325c054cca72d4f31,0xd017008740d4d60cca71,0x5c031d03430874098c21,0x4c74098c51d02720c740,0xd023258740dc131d0072,0x5cf41d0272cc7405c331,0x10f415c032d0632d0740,0xd057014b415c043d0563,0x9c052d066314b415cc52,0x583410c960d057014f41,0xd05325834114d60d0452,0xd4960d0732583418c960,0x8cb4110e32d075358341,0xd06748cb419c232d0570,0x10e60d0432983419da32,0xd0b415c342d057098f41,0xd0573d4b415c352d0673,0x5c053d0a70d4b4198f52,0x583429c560d085358342,0xd0b53583429d560d0a73,0xdc161d0c72587435c263],#[0x87505c021d416308750,0xd42730875099021d4263,0x1cd21d416310f509cc41,0x58f50dc121d416348750,0xd416388750dc563d4071,0x9ce21d4263887505c221,0xc87505c321d4163c8750,0xd4163ccb5058f31d4273,0x9cf42d4163d0b509cf41,0x10f515c042d45700cb51,0xd4442583510c960d4570,0x5c232d46325835110d60,0x983510ca60d45768cb51,0xd4570ccb515c263d4443,0x10e60d497010f525c342,0x583535c560d4d7098f52,0xd4f70587539d160d4d72,0x97e3f8f63b8be1f5c264,0xa6e8f9fe7e9f67b9de6f,0xae6b7abeaeab6aba7e9d,0xb76dbb5ecfafebeaf6bb,0xbbeeebb6ebbaae7b7ede,0xbfafdbf2fbbeaf9bdef6,0xcbb2dcaf27c7f1dc6f0f,0xd3f3fcfb3dcef3acdf2f,0xdbf6edb76bd9f5fd775b,0xdf77cdef7ade777ddb73,0xe8f9fe7b9de6f97e3f7e,0xedfb6ed7b3ebfadeafa7,0xf9fcfefbbdef3bbeebb9,0xfe7f6fd7f4fcfeefb7eb,0x35e32a6e20410edff3fa],#[0x6a3234969b235302c3ac,0xd3ab9264323b96939945,0x41337aa32374613a92d5,0x249e5d3aca165c20ce20,0xc05c3ab4b66322faab3,0xce5d328c0673a18765bb,0x10343b4e5d328e36bc20,0x6bbb0c071bb047254016,0xc3a8125c3ab5003c3131,0xc284a64420ce07c3b1f5,0x2a4065c39301d4293f5f,0x3372a40b2d67b234f603,0xd75e32a4122c013621c1,0xa683a0c16a420ce03c35,0x5e32a5a00c302d5d328a,0xc42b1f693a0e05c32a43,0x32a99643a26c5c32a6f1,0xa2865c32a89643a2085e,0xe1663234c663a0c2653,0x5000c3a4502c3bd7673a,0xe02c38a86a323470343b,0x3c3dda5f3aa305c3ab4,0x3420d165bb0cd6832353,0x4294103c393021c10ed2,0x23bb6432305693a0a11d,0xa4f18428ed5e32aa2643,0x465c3ab526bbb0cd6032,0x666322f90343b5265399,0x14324b02c3b39643a27,0x832351653a28b673a186,0xc3def1842b372a4131f6,0x2a3f643a201643230302],#[0x41b1a42b2d5d3aad4603,0x4f05c3b2d5e4284a4242,0x1683a0c467b234c66323,0x5d3284c5d3a81d02c3b7,0x32a515e3a9f1663a0c5,0x429395d32857673a0e26,0x23c673bb04608433dd1d,0xb2909c342b09c3c53ae3,0x222cc01806fb1a582ec0,0x73bb04262b285a30401,0x2cc305ca3328da27420a,0x5bb0fc30c30ba6cc3551,0xc03fb30c01a730c010c7,0xabe62b28556d320d130,0x80ab1320e7724091f50c,0xc6ae3a8eb3c42c7c3b42,0xa08c31439eb287927422,0x9c383e633286882b9d3,0x9c39976fbb0bbaeb20ea,0x4212109432572cc34170,0x38d733117282322f227,0x2e5943927109c34a614c,0x5a2cc341f084393a8832,0x50ec3b6109c39c663328,0x623a81008c342d094396,0xe42db009439c80943912,0xb285408c318576bb47e1,0x2900ae3235708c39a662,0xb86f3983e2742331744,0xb394312c515c3cbeaf32,0x508c3a0e99b0ac530c05,0x274232108c3083733162],#[0xcc305e31401c830c0112,0xc35c673315c508c34d82,0x3616e3981009c381e08,0x4b16232a546d3b3134cc,0x1f2dc3b2d75bb0ff30c0,0x5723913b4cc00ba73409,0x6eb19a208432ab6d320a,0xcbb0a3633283531c015b,0xb08b06cbb12908c317b6,0x162475390ad0943de574,0x2c530c01cd2943d53733,0x8f6dbb4e8bc438d46c32,0x272319e508c308609c39,0x6c323786cc3b726fb99f,0x2b285b9eb28a8b63980e,0xbb0b875bb00c6dbb5516,0x14f076bb47d2d432be72,0x3956d324a03140105753,0xe9084394809c3c0f6d3b,0xa09c319475bb4f608c39,0x6c323c80943ab82e4393,0xc3a4ea1343cf72fc095e,0xc39cd6cbb07209c3d20a,0x10d9633aa4d08c39bc08,0x98a08433d911c3d312f4,0xae30c03ee6eb99e42d41,0x7bc3913b30c03f031c05,0x6fb99b152c0419b9bb0c,0xc30de843a556adba201,0x31a5c09c062008c31c43,0x35a273399982f410d272,0x4840943e1b6dc35db09c],#[0x6a6d324a26d3b2e114c0,0xd7b3aad96d3b2d4a0b28,0x3942c177d3ad31afb230,0xcc20a66fb988a6f319a5,0x4012526c013631401656,0x33fc09c319f13c3d3031,0x31508c31ba31c012277c,0x3c734291f08431e80843,0x66d3200109c3c3b77c34,0x84397c0f4331709c3e1,0xd3208509c3c08723934d,0xc096109431e010413376,0x3c7208c340c6d4355126,0x3abbd310a16242be408c,0x146fbb0ba74b092e2743,0x36cc3b7708c30651f42c,0x9c346f6f3982008c3ac,0x943895b0b20d06e31a03,0xc3485264240408c3dd10,0x286a6d3b3c709c340b26,0x2b56d420a672b10b0a13,0x7bc390d808c382e0843,0xe63bb03609c3d4856c00,0x73bb04310c3a616d320e,0x6c000630c016c27413d7,0xb1a3a08c317908c35185,0x322731c00906e410ce6f,0x85f084326030c05b1084,0xd1863a4f06c32382b4b1,0x909c00f808c31a063328,0xb0c20d111c3d796cbb0b,0xd3b3a16d3b37f094324a],#[0x32876afb22d009c39be6,0x323fb1320a130c010563,0x9e2733119073310f1744,0x8a633aad36fbb0be6fb1,0x76c3a01509432ad09438,0x10c3a48b1320d162bb06,0x4319f8094394b30c03eb,0xc3d3209c39ac6eb99d6b,0x916408c3b2208c389509,0x2f26d3201330c05ba73b,0x952c41466a3310670f43,0x515c343c30c05cb30c00,0xaeb20b57d3aa486232aa,0x8c31a108c3460bcb10ad,0xc3983a33103009432770,0x184a6332837524123e09,0xde9bc408d46d3b30b724,0x1a45c13370cc3dce0cc3,0x708c3cbc623ace0753b2,0x31401af30c010363328f,0xc428d46232aa7633a824,0xbb06c08c391075bb00bb,0x38c130c043508c31c062,0xba823239d08c3d89744,0x1909c340909c313377bb,0xe85ba550633a82808c30,0x75b0b0208432afb0323b,0x539309623a81130c062b,0xc10ce73399782cc34197,0x232348c033331c043177,0xb7754200f744180f6c3,0xa563328a508c3dfc09c3],#[0xe09c014c62bb02509c34,0x943dba314008c6d3a1d,0x8c3ab60cc392931401a8,0x3234c2e4324630c01530,0x10ceaf320a208c30226c,0x92327c033709c307c764,0xc89e32a6f27425b51e42,0x99898a4708c39b430c01,0x6c3a20008c38a073bb04,0xd3b3c008c35a029c3866,0x42b626f39c0f98409e16,0x3d006c3b26fbc3a8d437,0x43b74390c4bdb12cf08c,0xaf09c319086c0ce86d3a,0x277bb0beac3a26c30405,0xbc428e80943de840c1d4,0x3237e08439ac08c3427,0xbb0c908c3db809c317ab,0x3bf609c3bce30c03f96f,0x11062bb02a30c05bf08c,0x346c0d1f09439b33140,0xd304015c08c307e08c3e,0x94397f6dc3131c3bb00,0x5bb0fe264210b6d32498,0xc00982d431f86fbb0c07,0x2de6633a82e633a9d630,0x5a162bb0362f411391f4,0x9d08433dc6fbb0c609c3,0x675b8924af320b20f433,0x633290209439b40943d8,0xd3b2da08c340a6232a47,0x43b4d08c3e2730c03e96],#[0x347774b092b623ac0109,0x95e08c302131c01ae08c,0xe708c352b08c3dcd2e40,0x708c39a831c062930c03,0x6cbb08427425ca823231,0x8c34c508c30406eb99ea,0xbb53a264212309c396e0,0x38d363328ee6d320bf6c,0x89408432b339428412e4,0x4f08c3d380843e082ec0,0x82b9d7309c30f974432,0x924124f08c309b274233,0xe4290b09c3e007339984,0x39e0830c043262bb03a1,0x9d4a28c30f095b12c56e,0xa18ae3a8ec31c04b06eb,0x7eaf320ea72b117708c3,0x4a5328a109c35f708439,0x8c35287b3ab95084323,0x5bb00709c342c72bb0a7,0xc31340943abc30c02ba7,0x28d16e31a1e733119408,0xe46d3a370723135aa53,0x47b1b23096232a422742,0x508c3e21b0322cf94412,0x15c3a3e2ec0cb42ec340,0xd3b2d1ae322c209c340e,0xc3d876db23d108432646,0x301f30c008c08c319d08,0x14530c04a730c016208c,0xf63329138621d3bb041,0xabe319d882b9cc72dc35],#[0xaeb20a7274208d0d432c,0x9c009d63328f1b0b20ad,0xbb0a80d4251408c39120,0xb38c31c015c08c38e56c,0x82474c3b7a74bb12a6d3,0x4d52c028e08c309f09c3,0x96fc08ce2ec09106c3a0,0xa0b286608c39e40fc18f,0x3bb0756e31a3972bb0ae,0x4289009c049cb1420d16,0xc7530c016530c04ac1e,0x3c6623a9fd0f433052fc,0x96f3996e7239168afb2,0x26232a526cb933708c35,0x9432a708433f70843d5,0xcc018883b22c92943cea,0x3997da3328a211c3d472,0x23126eb9a360843c0372,0x9de2dc115d6d3a056afb,0xb46dc22b709c3085633a,0x66e420ce6eb9a0e31405,0x6fbb0bd31c062aac3236,0xcc3044bd310d00cc05f2,0xc01256d320b709c311c2,0xb5ce6d3b3146dc209930,0xbd08c318ea1328666cb,0x3d634282788322c54cc0,0xcb03a8d56c3230f74391,0x314010c08c3a1228c30b,0x9c011430c01100843cdd,0x4381072b95ab09c390a0,0x115d6232a8108c3a5e08],#[0x95e09c019c09c01b92c4,0xa56c3a163b431a291e42,0x210c3d340943bef74b08,0x2941897304010a08c3e2,0xeb20aeaeb20da6d3a4c0,0xc35a372390d42ec3007a,0x3409084339b6fc381c08,0x95d314012030c01a877c,0x3430c01a6633ad191e42,0x4633ac086c3a4e97d3ad,0x8c3caf953923eb0b094,0x2c28276fbb0cb56c0405,0x3a8dc08c306209439af6,0x2a97afb23578232305ae,0x2b09c307f09c009a623,0x63a4b28a172319e608c3,0xe724084a094395775b89,0x6d3b2f430c0091823a0b,0xac302d46c0dce6fbb0bf,0x4325975bb0fd73b910d0,0x2a466d3b2d9a4b28d108,0x4172b91066e408cea43,0xc76dbb4f231c012673bb,0xd6e31a3a2c411ae08c35,0x2cc34debf319d86ec3a4,0x3bb0da30c008b6f3999e,0x31cd408c350608c30007,0x280f08c3a636d3b35873,0xb1e08c3ac663328bf744,0xa873399927231232b0c0,0xe2ec30d073bb0db6f39a,0xaec132ca3310366d3a16],#[0xc3b33f2ec0135843a26e,0xbb0d209c049a77bb0bd6,0xa4eaa3328ea2ec300675,0x31f28c3a1c08433b5adb,0x2cd43980d08c3e0e2e41,0xd8fc1ac52fc08596d421,0x6eb9cd662b285177c33f,0xcb8b368e41ac508c3525,0xc31a208c3d4a0cc3ad16,0x35736d3209e623ab4a09,0x19b0943db808c34e726c,0xf77e3a9f7094393c09c3,0x230c012072312313b42c,0x26421ae08c311d09c008,0x8432386f39993724284a,0x4331130c05fa4cc047b0,0x301a2d432296d3b3ca09,0x10073b95b598b8cbe08c,0x3e08c389862bb0a975c1,0x526c314409c39c1bc391,0x6232a571f42bee6c322d,0x8c3b200d423d126c033b,0xc3c14414247a63328310,0x4ab09c349608c351e08,0x28e73c011f951925f30c,0x912439f508c350a733b,0xf76408ce6d3208675bb0,0x9439a677bb0bf6cbb0a,0x3310f427c033808c3035,0x3b30e394285c09432627,0x383c30c042e3442b376d,0x1a72641336acb192908c],#[0xf474312dd08c31a43140,0x708c34da924153b08433,0x4cc036408c34c16fb1a4,0xf328a373c084a08c3c71,0x3ac66744110072b11729,0x398f09c381c87ba4f062,0x1a975bb0086fb9a236fc,0x8528c347b73310b072b9,0xa2f410e930405ae6d3b3,0x31405b12f4393c11c399,0xc05be63328f60943bf9,0xb91b06d320f44cc00c93,0xb39226424070bc382573,0x37a6d42082633acc06d3,0x4627422bd633ad387539,0xb6c323c175b0ac5633ac,0x6e3985275bb00608433c,0x8c30890843c6476b1c3c,0x32aa408c383d6d3a3e10,0x8a6eb9cbcac3a20162,0xa109c34906f39874314,0xf015c3d2d08c3c2ebcb1,0x727423206cb20d108432,0x754280f1243cdcb0b20e,0xc323026cc3b7b2e4380e,0xc30466eb99aa6d320b06,0x9b9e414236152c00422c,0xd408432ac52411f4833,0xb530c03e14cc00bcbc39,0x408c3088ae3230d2cc34,0x41420ba08433f509c30f,0xfc18f62943a0174b8959],#[0xbb04408c31717b3aad40,0x1b16db234c09439a873,0xa08432656cc34e830c,0x58863a202633a81c75bb,0x96f39d4831c010b6232a,0xaf4132caeb20b809c3d1,0xec3b65633291862bb0a4,0xb99d862bb0756f398240,0x390cae322d030c05b494,0xbc75b0a47bd310ad08c,0x9972b10f19e32a786fbb,0xc09c30b02ec01376c420,0x6d3b3ae6d3b3c509c345,0x9c3c6a6fb19e16eb9a3b,0xb19df6c3a0c56c3b2780,0xb030ac3236326420906f,0x11a62b28502ec0b1e62b,0x976c4244e2dc11ae09c0,0x56f39e002cc304108c34,0x73bb0480843c5e723946,0xeb9a5badba26c743b27d,0xbb0c808c38e409c342a6,0x3e142d4143462bb07a6f,0x3226c3a34a6f3999709c,0xfa75314c86c4214d2742,0xb8621cc831c01ad08c30,0xa331025ac32367753b21,0xd3a0e228c19ed52c0044,0xc39db633acbc6c422cb6,0x20a730c00e408c345d08,0xc1623acdd08c30f7af3,0xa308c35a52ec0d0c7439],#[0xc46c0cd263328509eb28,0x733117709c3e0c09c343,0x33287b2cc341c3140112,0x32a71bc428d808c35226,0x1af0943e1d09439f2a6,0x51f09c30a508c351130c,0xb3bc408d809c342826c3,0x108c31a3823a0bf31405,0x62bb034bc3a8d808c341,0xcbb0b6723915c08c3118,0x3a9f22cc3510754180f6,0xb301ac3236272b119062,0x9210943de60943ce06d3,0x432cc341a08c31c374b8,0xe0943bee08c31992cc30,0x9c359f833a46c6fc39b,0x9432666eb988d6232aa9,0x320cf6d3937c08c3a1f0,0x23480943e1e52c04176d,0xa036c3235a30c03df6c3,0x9c3e0672b915a6fb1,0x1843a55026422260943a,0x6c3236926c35d81f42ab,0xc03e009c30876c3238d,0xc3c3a0d424eb08c39bb3,0x39da753912d084329308,0x410944125f74bb0a108c,0xfa432a8a09c399109c3,0xc0943381951924774420,0x28c30ef6c3a15908c34c,0x84328877c34106fc3866,0xbb0bc31c05afb1b22cf0]]
private def groupPage4 := limbs80 #[#[0x3cd609439256d3a46e77,0x2c91f42cfe733997508c,0x8074432dd6d3a3760f43,0x830c03f6afb22c208c30,0x77bb0ca08c39afb14213,0x943dd4af320da3140103,0x4291f08c31c530c04af0,0xa6006d3209c26c307372,0x11909c303863bb0676d3,0xd30943d832ec014008c3,0xd2642475633282673393,0x6d3b2ed09c35a40d4255,0xd3b39113c3a466eb19bf,0x32a6e31c016a6c425fd6,0x1a608c31960cc3ac3a2,0x93808c39d62ec00d0314,0x7663329176c422b7b021,0x56332901b0b20d16f399,0x8c3a4d26424316232a5,0x9c30f6623ac00a632a82,0xc34701f4288d98409df0,0x3cc2264133709c3d3f08,0x91530c04b208c3c3411c,0x100dc3ac31343cf86332,0xe2d4123bb0b20a108433,0x304015b0843de409c33f,0x5314bf76bb47c0943910,0x4198b72bb0a208c309e7,0x3a172c4322526c348c2d,0x94909c345b30c008a08c,0xf5ac3a5536232a500943,0x66eb9d006c425f06eb9d],#[0x633ad3277bb0c3b4b184,0x8c3dee08433f809c3081,0xb8cb108c3e0252413ff0,0x100f2ec0b1d31c04a974,0x20408432aa89b22c5754,0xde52c041c6fb98916c3b,0xc72bb0b27e3acdc74312,0x8432b428c30ba77bb0c,0xdc22cb09c3e1308c3018,0xc3c8e8d39d4731401626,0x10a08c3c3509c012809,0x8a70943de108c307b31c,0x7b3ab92bebb41ba332,0x874b09321f429ea75c01,0x8c39b36f398592d412b,0x8b8a3e31405ba7331cd7,0xc388a6232a7e744100f9,0x28536c423b3314009508,0x4021f42bf11143d5b1f4,0x412cc305f08c301b6c3a,0xf83b23051f4290652c00,0x30c01bc74390d7274339,0x9431fe30c01bb2ec09b5,0xbb0b309c35c928c347a0,0x23452f438d66c323d16c,0x337a331075aeb20a26c3,0x952c41989b02192a4441,0xc09c342972b119473399,0x2ec34066cc3ac32d432c,0x3328cfbcb10d06d3b2c3,0x32a3eaeb20b29f328a86,0x982f72395af1f42cada6],#[0x360bc312cf72c011f6f3,0x7309c3527314008b6d3b,0x3bd310e76232a8708433,0x6c3b34485ba26e6f3998,0x6c088482322c909c3454,0xc0d5c783b34096b95414,0xa26d16c39d578312e554,0x50e16c18887931e0d8a3,0x4358c0ce29a412dd4a42,0xf8b4084c97192545ac03,0x78b18319dc11e1c1a1cd,0x8b284f78bb44332c0147,0xc114d5ac020da832a91a,0x3c5f16c003596b958f79,0xa8d913982f1743b42174,0x518a21d3bb3a1d1c54c0,0x679bb04b8a3a5548b40d,0x4ac0d44ba313625ac19f,0xb283516c0179a832a68,0xc3bb416c053e96b92fc8,0x28355ac03b75ac026816,0x31d32432a016c3a0d813,0x4e78bb02f7931cbdb232,0xb783b203bb31cdb79319,0x32c194a8a3a54f5ac059,0x8c0d1278b1c0b8a3a4f1,0x3a517971953d784294d5,0x382f9c292e54ac0d4279,0x58d8a3a2673341c3317c,0x965ac004b32c015096b9,0x2d1c21f45ac01ee5ac05,0x59414f59c312e578b19c],#[0xda0845ba31a2b90b9afe,0xb287816c3cff9a41a4fd,0x3de9c2944a5541285a8,0xc18783a5175ac02f816c,0x555ac054d96b92f85541,0x53341c15c6431f497b95,0xb221cc9cd195719c32ae,0xb18609b3951a5ac059d,0x3954316c3a53dc411f4c,0x98325ac01d5b23232897,0x27f32c01e94a421f4793,0x238a3a5558ac084c5ac0,0x916c040c4f4144878bb0,0x784114d3341112554127,0xda92e58a3a54c5ac0221,0x41d3b16c05a64f4146d9,0x1c1e4ac0d728ac0d519a,0x8339db12e5dc20845c0b,0xdf32433b832c304fa8b2,0xd79319514ac05e9c021c,0x16c3035783a1cbc0b185,0xa3a203793b2d84ec1ac1,0xc050b90b9b084a424db8,0xb4f1a832a9458c0d0532,0x36616c3d3cbab1c8179b,0xf44a422243341105ba31,0x68a3a2729c411e1ba319,0x783b27a973a53490b9d4,0x2322d879bb04e9bb94f0,0x21c895ac04123341c30b,0xb38ba832a7378b1c26ca,0x605554185d16c0257793],#[0xb8d0421f4c13251016c0,0xd54c0a8fcc21d7590b9b,0xa8b285878b1977973925,0x743b438a3a4e7c0b1c18,0x4339c79c10b1783b3421,0x197033415aab3c0b2c17,0xdfd783a4617942869794,0x11743316793a46e7942,0x4803ace1793a88d78bb0,0x793a37654c0a8c784291,0x342b1e55412691743c12,0x4331532c0ab09da9c3cb,0x9d9c33433555ac347a16,0x8968b3b2e1784250890b,0x55b3b22d378b99a9793a,0x6793a53879c30818bba5,0x32c008b79411bd4f41b5,0x9b99a979c19ccc0c108d,0x3a890793b2bf5ac01ef7,0x28d432c3078c4b10ad79,0x82fa932858793b216c04,0x46b2c131e783b20ba8b2,0xac031389793b328793a4,0x4f41362c0391043f42d5,0x8bb0385a403a35ac02ce,0x3932879c3c3b783aaba7,0x188f79c311c793b3a797,0x3a6b343551554128032c,0x59bbbb0ba4f41bd55b40,0x9554127432c350532c34,0x16c05914b433ab793116,0x93b2fc78bb456793b38f],#[0x3a56b784009d78b18387,0x1090c131124de3900d97,0x23d8b3b3abba31a03c04,0xd03343920b23238b5541,0x7842ab732c3db9cdb22,0x91c1ac579b99d2c14229,0x640cb932c011179c33fd,0x41387793b3a497392919,0x3bc7793b06d16c3d615b,0xac516c05d6bbb988a8ac,0xb6a93282f32c39119041,0xeba3988a32c345a7840c,0x78bb49232c3894c7314b,0x8323e217c03b15541272,0x313269b390ad783258a7,0x32728a323824f4147bc0,0x2e0554124e32c0120334,0x334329f79c35d9b232,0x178c362679b99d4c1b92,0x7940bb35ac039616c195,0x343895a9328ba32419ad,0x410f08b3b3a18b3b37f3,0x19b033419c917c02aa4f,0x20216c307b334322c334,0x3179324b316c04279a39,0x99c413fd783a0528a409,0x9739297334323332c346,0x83a1aebab99ec813aad3,0x428e816c3b5f794243d7,0xb7b334320ac4c0138c0,0x38679c11bdcc21860b2c,0xd47842213793b297ddb1],#[0xd334320378c138ec43a8,0x7842acb97392a3c4c0b1,0x340b2cb3c209078bb070,0xb1d7458c0d357841970b,0x362616c060416c3bd479,0x3c4783a1b716c060779c,0xb67931ddf78b98e4b3b2,0x8a2192b78399a933415,0x9641258b2c208d32c392,0xbc0b68c1b91b078bb06d,0xbb12179c01b9bbb1a94c,0x915a5b438c3784145579,0x88e803acdb55413d6c13,0x3b79c35f732c1893c4c0,0x68bb23c27840e2d4b413,0x78c13069d422c57842c3,0xf41b19793b253a8c288d,0x4388a334388a16c05164,0x3e390b9bbcdd98c1d79,0x169b3320b2783916332c,0x28794245533439a67841,0x2334337578bb58fdbb12,0x1643cdb334327759410d,0x93b39079433d88b32c3f,0x42b8e7842a19c031a227,0x2c3334322fc021b5778,0x5f4793192b32c0bf9b2c,0x719039cdbc04146a17c0,0x81743cfa78411bdbab18,0x33415ad32c389532c3da,0xbb8a6aba31a247840082,0xc03f3334110f78b1cd19],#[0x12e079325148bb238d17,0x584784162c32c0cacc0b,0x4b3c032c8a323a532c0,0xc16c05659d4243c16c03,0x7842cc479c01149dc343,0x3b1d73b221c8a16c3b6a,0xc05b8793a3cdc4c14f9b,0x20953f42d4cc0b91a932,0x95797390ae5ac0441334,0xba7840d93793b2c63343,0xd16433b19b3930917438,0x3343356c6c009116c3a3,0x2c05be97a1a4916c3b8a,0xc097455412848a323233,0x13a73343965c7bb0ba78,0x50a79c361a4b41d76c1b,0xc5c4b9109813ad3216c0,0x29c41ac516c009f9dc1a,0x78415299ab8adc32c391,0x33215978c15f059438d0,0x3b2c3793b2fd79c31c7b,0x208bca3236416c3b9079,0x2444b4133d4bc0337334,0x8c78bb5bd79428275541,0x558c0b2678c319b33418,0x5b4147b5ac029233433d,0x541c1e9c415d3c5c0890,0x413653343abc79318a55,0x15db32c39b532c34ee4f,0x45f54411f49bc08818a4,0xba319fbc0312e35ac0,0xc33432969641533b23a2],#[0x793b2c0b2c031e4f410b,0xac3485ce3237e784229c,0xc399778b1c3c55412834,0x9109334328379b1bd179,0x89132c1de24f4147fc5b,0x8a793a03ea832a72793a,0xddbb12cf33433b6b3a18,0x793b1d616c049b8b4137,0x5c35319dc02cb78433f4,0x42306793b30078b1ccb5,0x116978bb56897393ad78,0x2853341c16334110879c,0x1e79c15f0334320d3343,0x179325c07942c4e78409,0xc4c313816c05d0334336,0x9c345b79c397633c3894,0x3a20a79bb12478c12207,0x3c6b79315d591b99ee8a,0xe2833432ae33424ab16c,0x89793b3b2b23231b7840,0x8793b3b4bab99aa5ac03,0x784162d78b199fcb40b6,0x841be4793b294bbb1a73,0xc0ce858c0ceec0323c67,0x39f24f41bb69c42ac5ce,0xca732c01b179c3085174,0xfbc6c009897c108132c0,0x4793b2c1ba31a0716c00,0xa8bb03633439a85ac038,0xb42599b3422bd79410b1,0x39b0ac4c137a793a38b4,0xb0c69139bba32c352f91],#[0x5b932c3db8b2c3b2cbbb,0x258a3233a334188f32c0,0x7794294db23139e32c39,0x33c390a3343905c4290d,0x9415f016c3abfb3b2300,0xb23d2c0b1848b2c13777,0x927333431ff16c3d46b3,0x33578bb083793a066963,0xb432c05e39cc11e14b41,0x932c05b479c3e0c5ac03,0x16c0617334332678bb46,0x9c1455ba319fc79432b3,0x3a3ec3343398783a4fc7,0xb06b9ab8d2c793b3af78,0x449b2420909c429df78b,0xcb8bba20358c0acd78bb,0x7793a096b34131e79422,0xc4c18d19b394cec13235,0xf4236f78bb07416c0457,0xc30b01743a004b4235c4,0x13c333c0168784282779,0x9f2793b296dc329d8c5b,0x7b23232a16c060f3f42,0x5b3b232f9cbb47a793b3,0xc0bb41c78b1169324147,0x34233116c00b4793a090,0xc1c3d793b283c1b910d3,0x1be433c010b16c3cba78,0x3c316c3c8016c0089782,0x8e3f42d5f78bb4d19b39,0x755411f39c42c3cb33a0,0x793b23d32c3db1b2323a],#[0xc41c3c16c3adc5ac026a,0xb282c78bb0ae33c01ad9,0x910678bb446793211580,0xdab32c351332c3da9c0b,0x4e334209378bb02978b9,0x17842a0c1743a671743d,0xc03235732c014979325c,0x9c35e05ac048f5b410bc,0xc3b0eb2b187279315977,0x1c3c4f4136e78408398a,0x465794144e32c01f99cc,0x5d4f4236c16433c9c039,0xa16c3d364ac3de97942b,0x794019c783237832c0bf,0x6b9568793932778322c5,0x409f478b99b078410b19,0x3a4e4f410c94ac0129de,0x9f1334330732c020516c,0xc578b1c0e32c19ebc032,0x7b341336a832a8379322,0x32c1c30793a532793987,0xb4133c4b42361963135a,0x42d2e17c1c2c17432c84,0x3d20784397c58c0c409a,0x2478bb23d179b99b079c,0x5359414f433415bf9c42,0x64f4136c78c11bd33420,0x33c01c1b3b23d379c3c8,0xa425cc33432dc17439ee,0x322cf97c1087324115d8,0xa3209bc149f78399d2ce,0xa75b2b20ae78bb494793],#[0xd633439a77931d493343,0x7ddb90ba9d41a5f16c39,0xca3236116c01e216c345,0x8bb0a933414fb4f41b75,0xb08ba793a06f32c014b7,0x3b18cc322c279c1acbc4,0x8f68b3b2d178bb45116c,0xb479c3e10ba31a0691c1,0x478319e6ca3a0ba16c30,0x8a323a9964125f79b995,0xbc118f79c359f33413e9,0xc35629d41ac55ac0479b,0x220333c014cc4410c132,0xc37b341368c4c1938783,0xfb16c049d334321416c3,0xa1743a6816c052833431,0x55412535ac051b58c0cf,0xda0c1b32c30dd8ab9337,0x3b2f116c3c8f793b2f3d,0xa06632c3033794008279,0x4e38a3a2773243d52bb3,0xb432c30d0c6c03e132c3,0x3793a10ddd988478ab20,0x5443225793112e5a402e,0x93a57a79321b833431e3,0x431dd32c05897931ddc7,0x2b2c3343253793b20e33,0x35d794114db3328a3b34,0xe658c04f316c3b0c7942,0x78c361816c03db5b402,0x78414d59139b9979c341,0x3433b779b99b632c3451],#[0xc34fa793b2f8c1b91643,0x2b417931e01334330832,0x17132c0ca83343279794,0x2b33439c878b1c8716c0,0xe783a88d793b3c796414,0x8ac3b01793a106793b2e,0x4313098b3a0815b403ac,0x323bfb3b22d85b43386c,0x988d17c0578a932863b2,0x1117841306b3c243b79b,0xaf3341467783a896c039,0x97392d85ac028033c05,0x78b99b679c399378399b,0x313d278bb424783a890,0xc39afb34326f78bb53cc,0x116a973956817c02f532,0x23d793b2cd3341893324,0xeb554129f9a40d7f5ac0,0x64ac03ab5b410df8a21d,0x7942899c8b2873793102,0x590c678a322e99b4149f,0xc03e8a94288d91a1c47c,0x2906a832a6dc031a2d32,0x1d9b332b604b423b6a8c,0x3916c3b0778b9a157832,0x5c44100f554184832c34,0x79c398316c3d37334323,0x1b13cc59c0cdb32c3356,0xc00d158c0ce878bb2fec,0x2df0ba31a0a783b26dc4,0x59a832a6933419b1794,0x574b4133332c18923242],#[0xb9a30b82b232390cdb23,0x79c027c5ac026b54414d,0x2c195678bb42032c0cae,0x432c0334336a7842dfd3,0xb45979b99a7ba31a6d33,0x2a7164339b79b1baa78b,0x978323e433c3dae16c0,0x979325bb7942069c5391,0xb232b6017431fe784121,0x7c02afba3989416c3b24,0x409df16c0311b240b2c1,0x1a9978b988d79bb5599a,0x1d879c317abbb989497a,0x91174384f16c01a1dc32,0x132c30234f41ac1bbb1a,0x783adb5793b29d79c358,0x2c008a32c3462d631a02,0x3a5eac1b02c232c05ed3,0x8d4e55415959d411e18b,0xad891b9cd978bb5059bb,0xfc33432f74b42491813a,0x391c1c9916c061517439,0x96c3b57973aa99b2b1d7,0x8bb58d78c12d63343be8,0x420f216c3a80c4391097,0x33a9783a05333433974b,0x80578b1d21793b29b174,0x1e5ac022f793b2d278b1,0xfb3413779d41c3c33413,0x334146878bb4d317c014,0x3419ab964154079c3087,0x3232b8bb22c516c3d2c3],#[0xb2c733c0082bb32066b2,0x1f1b23a4e9d9b19f4793,0xf29739443334208fc032,0x178c35d9c0c0a9078433,0x78b9dca793b56a8b4113,0xb3b35833433185ac0233,0x42c81bab1ce478b196f8,0xa01617c02db78b1d1d3e,0x88c9ab94ce4f41af7783,0x567942306dc313893343,0xe4ac05d8cec0b1e4ec1b,0xccc132c784019c793b2c,0x1b12e74f41b1c16c3c5a,0x3960a8a3b33f3f429d6c,0x33614f4136f4ac033e78,0x2c4334325da93284e4f4,0x8e96392727842455793b,0xb78bb0058bba4e716c3d,0x78bb4cf78bb0814f410c,0x2c35244b4258c16c3aff,0xc306d783a92178415ff3,0x34387940b94bb31ce616,0x8bac5b892478415f032c,0x688ab8b369a398094f43,0xc79c138e32c39b396392,0x79c35a49132ac97842a9,0x2c390378b1e0d58c0b25,0x3232317c025979323233,0xadab9c422c58a322d578,0x9ea79b918279c382f793,0xfa7931df6ca3236abab9,0x733413ea33432fec0311],#[0x32c015732c390c32c34e,0x3419a716c3b0e7842d08,0x32a01793b2d333413203,0x1202813ac437841a13ba,0x3869032ac932c34f1c43,0x5816c349532c35585ac0,0x9794097478bb46b16c3c,0x79bb4e778c31a2973a56,0x8c389878432b333431ee,0x432581743311bb31d4e7,0xb2f7793b29e79c357f79,0x43e32c04343343953793,0x43b2c032c79b1b2378bb,0xe5b431f6324389478bb5,0x78391d17932601c5b1b7,0xa40b68a8b286b793b2df,0xc0c3b16c3a0ebbb1a68c,0x1c767942d88793b291c5,0x32e79c011a5ac01ff78b,0x1133415b7b3c0b7bb232,0xf9c42bfcc04143bd831a,0xbbb19eec1c1090554135,0x3415b233424adc1a1b57,0xc039379c396e79c00823,0x8cdb1743ced78bb56d17,0x4ed5bc059a7939cc09bb,0x5417c05dd79b915d32c3,0x1b23232632c009479c34,0xb332164783915916c04d,0xa31a2c7942ab79d32ae5,0x415e179321d9174384bb,0x123c7841173783a89133]]
private def groupPage5 := limbs80 #[#[0xcd99132af278b1c8b334,0x9e79b1d3dbb31ce71743,0x1793b30a33c305816c05,0x78bb0f24bc033833432c,0x3b238b79b989132c0583,0x423e433433d216c011bb,0x2b57c139106c1b19f179,0xa235bc03a34a41336c13,0x5ca9328787831a373f42,0x232c359517c04a455413,0x793b543c0b1842793114,0x2c30ba32c061c793196f,0xb99219b413e579c381e3,0x989091b99f217c03f578,0x27c90b9d9b4b4339e793,0xb164322797395407842,0xadc219d89032af278c3d,0x783a92432c01a7b3b230,0x6c3ad8793b2e07839181,0xb2382783221e58c3b7e1,0x198dbbc38667940c4e8b,0xd4c973958f79c097478b,0x76bbb1a9f32424a91743,0x578c019cc032b5778c3b,0x55411fc33419b68b3b38,0x2c022a7942a7c7841cd5,0xbb56e554159416c3afb3,0x2a6f554135b32c05de78,0xd39793b284c5310ada83,0xe59739452334326d16c3,0x99c4243c793b56c58c0c,0xc0219f1b23233279399a],#[0x2c34735b438ba16c038d,0x39cc9bbb1b1a8ac05513,0x22e77942c3d78bb58c79,0x4e2c0c150b783a958b23,0xf416c3c51334338932c3,0x48a322e54ac033adc311,0xb2323cda94290655413d,0x8bb0ddc0311f43341107,0xc09f44b4235b79c35c97,0x15ac32c347a9bb0ac5df,0xc8179c361916c057c334,0x8a793b2159c21ac517c3,0x359431f7334331cc7400,0x9139bb68b3a2ce79c313,0xb32aca793937b32c34e5,0xc188c78c10b116c3d458,0xb42378bb064c43892232,0xb9458c04f896312c578b,0xb34b422f7bb31d0e7842,0x47840dfd7942b8e32c05,0x1743ceeb33207479b1aa,0xac047a594100a3343267,0xc057ec4c0894b340b7b5,0x32f079c387479c30b716,0x5e1c0391b38ac137d164,0x9616c3b0879315d332c0,0xa78bb07132c39a633433,0x784280216c3d01c4c09a,0x6c007b97393c49d32c3c,0x394f0dc311f655411ee1,0x230433418929c41c109a,0x2f8783a346793a2d38a3],#[0xc379c08398a32aca3343,0x33c015bc5b0b6178bb4,0x324115b793b2149041d9,0x34322b32c05a916c05fe,0x3a5b5c0b95be78bb44d3,0x2143343295334209679,0xac217c04b74ac033d5ac,0x9078433dd78b9d02c1b1,0xfc43a8d8793b3a0a9c28,0x793b2fe554146b32c03e,0x8c0ac7c44098c554205f,0xc03c279c30f6b2c34e85,0x22c2b2322d378b192b16,0x90578b99244b422c7c13,0x4eb340b3678433d832c3,0x5c1310ae78425c178414,0x5ac03a6334137732c351,0x93b2e832c39a778b1994,0xc02d58bb232397393907,0x10dd334115978c114d16,0x37ac0b1332793a370554,0x5d7942421c6c05b5c541,0x3cd4132c79bb16390b9a,0xdc20c1b78b1e0955412a,0x322c2cc322d05ac01dd,0x4208d8b4212b3343894c,0xa3d032c02bcc09912133,0xa7278c197033432a3793,0x4cb4136879c34a31743,0xf9d429df78b99ad79410,0x324390a784111a78bb44,0x8c0b2890b9bba334331a],#[0xba20079c340d32c1df95,0xa90964142a594121bb3,0xb944f43364bbb1a00c14,0xe297392fc793b3547840,0xb793a1aec032229793b2,0xb3a1d0b793a48391c1ac,0x9c398c58c0ced16c39e3,0xb237e16c01c4ba32a1c7,0x10c0793a059c4b1809cf,0x15d79c3c6a78423e4cb4,0x1e79c192cc6c01b178b9,0xe8142827dc390c358c0b,0x16c016732c34748b3b3a,0x8c0d0ac1432a63343910,0x3a02478bb437963926d5,0x30f21743d4d784138e79,0x9679b99d17843c5e32c,0xffc5b8963d2319f8783a,0xb9621a6e813ac4679c15,0x79b99ad793a56f793b2f,0xd413fd5ac03ac7942bb3,0xc0d0ebbbb0c816c3b619,0x99b158c0cd94f41afe59,0x2eb16c019616c0484bbb,0x619dc15d3973929f5b40,0x4da311f79739493a9328,0x78c1d82ba323668042be,0xab8a4e78313a517c1887,0x3b24e16c05c4783a0909,0x3b585b41388c4313be79,0xa779c21c3cb2c0b2c8ac,0x1d5541860554129ba832],#[0x916c0577783a10ddc18c,0x90b99d679c340b16c3c5,0x2c34d95ac01e37942c21,0xc0122c53120255c35663,0xb825ac036179c33fc33,0x27fc5b1309794227c9bb,0x8332c305833431d53343,0x8793221e9c322c5793b3,0x9d322c59739481793b3a,0xb3a441ca4136833424b1,0xc03c94f4236232c35618,0x99638a322f6793916317,0x38e78bb0f379c343c79b,0x9279324e75ac00ba7941,0xd9d42409793a1b733432,0x8a422cb5bc02a017c057,0x343ce9783a9559041b02,0xb91665541842783a1063,0x3d608b320b479c31a279,0x7d334327478bb45816c,0xb8c1314e179b9921793a,0x64f4336a78432b49740c,0x5ac03b6784289932c34e,0x2c30ab793b3bfb33a094,0xc30d14f4336d97192a43,0x1d71bbb989033415b4c4,0x3a2bab988dc032222b3b,0x27793b380b221ba0793b,0x44f438c67842a7c79420,0x9bb920916c04c132c356,0xac048933405c2ba42066,0x29ac579318b432c05fc5],#[0x6d793a4e9783a4e99c,0x907842027c7c009016c,0x9b1743304973929833c0,0x2a8b285117432e979c31,0x793b29878b187616c061,0x6c04955ac035fb3b231d,0x323c24f41a6a79c30a51,0x145579b992432c1abb8a,0x12416c0447793b03b794,0x5a794324758c0d04c099,0xe79412d678bb4c68a323,0x8a322ef8a3238d793a02,0x8bb58e16c00f53343a00,0xc108578c361a79433e67,0x14d0bb399aa32c010597,0xa67793b30c78b1d41784,0xc816c02627842c3da832,0x416c02e9b242b2c4f438,0x8ab933d4ac048532c350,0x6c3b54793b2d779b91d0,0xc0ce37831a5f783b2791,0x1dccc03916016c023a58,0x5db79324bb5ac04248ba,0x9116c0598a93284b8b41,0x832c345078bb06333420,0x17433819c2a2c5cac0b6,0x34110dc1b02d032c32c1,0xc054178bb06eb332ad13,0xb0b297c38ae78bb53717,0x1d7793b210793b35878b,0x2c33c39ac9cb8a3e793b,0x75ac024e7841623c0c13],#[0x5ac048d16c038178bb03,0x93b35bb2b187378b1e01,0xc149f334394a78bb0ac7,0x19ce5ac01fc79c36189a,0x2a133419b4964125479c,0x368b4093133420559739,0x133c303879c3152b2413,0x32c0095793b21d334322,0x34188ec532b7e4f41b2b,0x40a704ac0334cdb22c23,0x14f997393d378b1c8878,0xafd33439b516c0523c54,0xa679c029c7942b9416c3,0xa3e42ba4b232ad178428,0xc438a7532c342533433b,0x6c3ace78bb30816c02f6,0xc145558c0ac6bb31cef1,0x2b443343324b23a08a78,0x36632c01b479c342bb33,0x69793144478bb4814f41,0x832c05e232c010333432,0x793b355c6c03ec55431f,0x942802bbb1a218b3b2ed,0x410be78bb45a7931cd77,0xb38a79b99b478410044f,0x209334326a78bb541793,0x7e79bb0ba78433d9c431,0x3d630b6aa8b2874c432b,0xc0b10d0cfb22cf4ac033,0x2c042f32c34913341017,0x433dac1314db963a26e3,0x88c632c015332c351b78],#[0x45f9ab8ccdc1b1a22d63,0xc35b402ce78bb43879bb,0xaba2a0668bba2779bc0c,0x3f42cedb232b44554127,0x8c342a334388db232300,0x414d978432b5ca21b6d7,0x8ac1310e779b91d355,0xbcf78c388a5ac0491c6c,0xaac03131b16c056c33c3,0xf7940dfd7842b4132424,0x793b27f78b1c579cc1a5,0x7433c2b2b20b2b23239a,0x4133779c39c1d8319f41,0x358a784243d78bb03b4a,0x11316c1ddf32c01b378c,0x3c32c1c3332c01c87932,0x416c0143a9328339c29c,0xdc3138679399b0973929,0xb425ea7940d93793b356,0x328749a409e19dc1a5f8,0x32845bc02e332c3437a9,0x4e83343244b2323a0334,0x6bc0bb417c1b91a68ac1,0xfc43895b32c39b4d810b,0x58c0b1a334390cb3b23b,0x8c357f5ac046b784183f,0x413214ac05ecc7bb0c37,0x3e08973a29979433f233,0x16d58c0b1d783222e784,0x5279c02cb32c342078bb,0x6bab1cee78bb4cdba398,0x32c3557c1c143b8a3231],#[0x93b29ab3321635ac02dc,0xc02f3793b30e16c3a857,0x1a4779c3e00973958d5a,0x87378bb1277940e289da,0x2f32c388a7941623b3b1,0x979c162c78b9db5b2323,0x78bb43916c03a9c4b895,0x34391232c3daa32c3512,0x4117316c1df69031a1e3,0x39ac78c192cb3320e779,0xcd3a832a7f5943228324,0x74bb31cf1794083916c3,0xf334324e32c0d5eb2420,0x793a921b3b23909a4149,0x3439b37940a7078c31c7,0x3a9fa3343bef8bc22cb3,0x1b1879c3c8e78b916680,0x89133431fc3341322bbb,0x1d78bb425b3ba4e9bbb9,0x879412203341891793a3,0x9ac3acf78319dc793a54,0x3425b533415ba9c2a43c,0x43325793b2ea554129eb,0x39039d42ac578c027c33,0xabd32c1dfb7943302334,0x458a423b332c05f5783a,0xf4b4339f793261f913a4,0x5541267164331079c319,0x6c05d29139874bb3988d,0xc3c4f793b2ec32c05861,0xb2449d42bfcdc319d816,0x3d1793117278c31bf793],#[0xc5b410be33439b48a32,0x38b3b2c316c3c4159410,0x79b960bbbb1a07b2323d,0x842d888bb8b3678b990d,0x4391178c00828a323457,0x25bc33411ed16c012f33,0x3ebc0b13a090390be793,0xa317c031079bb4fac6c0,0x732c05e580b286dc0313,0x334332b793916bdc1884,0xac3ac379a1dc132c0c13,0x432cc793b1d5b240b7b8,0x39a89c41a5f32c0ab255,0x5227942a0cb2c35d832c,0xca8b3a563783b27b16c0,0x432c358b334328079c3c,0xc0319f1334323d32c306,0x6c3b84a8b2850c0b132f,0x3b3608b3a5eb55412921,0x1e1179c34a55ac02e68b,0x88b97c154916c3d8c78b,0x2a783a90d58c0b243343,0xc33410e5c1a19f179c34,0x90b9d99793b2ff793b24,0x932dc178b99061743d54,0x411635b4147dd7b0b617,0x1c955ac01f0794091e33,0x3448a41131c7314ec78b,0x3f32c388b79c399e8a3b,0x732c008cd23136179418,0x3341472793b20f793250,0x8319e732c05aa3f42a67],#[0x3257732c0854b33a32c7,0xb56c33411669ac13e58b,0xab8b41014b332b8578b,0xa678bb5395bc057078bb,0xeca3236db34216417c04,0xda312cfd2390ba90b9a0,0x139b0090b9d9a9da1ac5,0x3a567783a9065ac044d9,0x92a09d312e54ac007379,0x42d963954f8a21dea973,0x59793a924334132916c0,0x8c03230d7942ad616c05,0x3f42d63b3320bada3122,0x2c05e89cb12e58bb22d5,0xb88ba97392f8c14132c3,0x12c533413ed783a5b5d7,0x50cb2c3551c03915c97b,0x52b232b8558c0d0d32c0,0x54b422c6c14325678bb4,0x793b3adb34208d79b9db,0xb287b96392775ac02f7,0x41247803a9f49ab8d398,0x1a599041d9232c02b996,0x9dba4118f8a3239c79b,0x9e78bb49116c052a79c0,0xb78bb48378bb48f33c01,0xc4b892179a19165ac02e,0x3b23cc793148297c1533,0xc016233419b279c0306b,0x1954bbbb0bb32c1de732,0x36654c0d5b32c307132c,0x59c1395be79c35804f42],#[0xe33c388a32c350d783b5,0x79bb1595b43389b3b232,0xb4038432420908ac04e8,0x43874cd413d617c3c435,0x1a6a16c3ad28a323b078,0x306793b1dd9da9ac5ba3,0x2cc0b915a79c13067941,0x784159379c14d096414,0xcc32357554127fa84289,0xd32ac5bb3a86632c05a8,0xbb4227842df033432fd9,0x287bc13a32d16c018e78,0xd09d42c3c793b35e813,0x4a78391cf16c057bb2b2,0x19ab8cc39719574783a3,0x16c054b32c05c29d3b21,0x9432c579b990d16c3a5d,0x4331933433bdb240b367,0x388ab33215a79415a733,0xf9c14108d7931d26324,0x784f41d4e16c3c7979c3,0xe334327a554126a78bb0,0x973956a79c19703f42a0,0x7c1ddc90b9bb678bb440,0xc305e9bc0ccd16c3b1a1,0x33869ab8a3d8ac1df1c0,0x8a633439259c32ac5334,0x8c78422cb79b1a547942,0x7793b280793258a32c38,0xc5314f055411f216c3af,0x9315cf32c04b479bb074,0x42247bb31d4f334110e7],#[0xb0037931df38b414e89d,0x52bbabb47a78b1c6378b,0x6e55412953e42c4316c0,0xd5ac044b58c0b18c5c09,0x79c019c964108133414f,0x4c088d793b30879b9906,0xc342c96392677842c4ec,0x3ab9b3b23cd33410e679,0x5c89da1c3cc4c0d0c334,0x7079325ab7842a1316c0,0x14ac05738a322c532c30,0x32c011032c061dc13112,0xa31a00dc390ba32c061b,0x315033f42a7f9041d8ab,0x233291c1d8a1743a6ac7,0x585783915f33433ccb3b,0x9f793a5ab9b393be32c0,0x855432be793b3018b3b3,0x554205c32c3dba78bb47,0x2c05f832c39105541296,0x409749c42409793b2e73,0x1b0f964153d79325c378,0x4099d41c103343379904,0x5cc1b1a2d32424b079c3,0x978bb061793b35f793b3,0x32c01a6b2c25b578b9cc,0x2c01a8793a90d793b2e4,0x40c4eb232361793adb53,0x308132c342433419a978,0x9ff783b34378c083978c,0x427942acb32c188eba31,0x178bb441963a55016c3c],#[0x5ac029f78bb45032c009,0x8b2829793a90616c3a4c,0x31190793b20d33439afa,0x2a3f7942c3633439ca79,0x735ac044cb3b23289a4,0x5979b99598bb23044ac3,0x9c1393d333c0c66793b3,0x3e42ae43f42b24793915,0x80f7403e8000091c18f9,0x6e582f0c13ca080b0307,0x720b9405360255e10040,0x622dd105c079c0377a19,0x5e0e2c9214d309d4c4a4,0xafc7096364319e98c5e4,0x99118884363f871ea80e,0x27f793658965048bd233,0xc462cde15e1ca9d0525b,0x9e65f731be98574be185,0xce3b66f62367a1aa2cd0,0xf6d0f68479273b519d0c,0xa821c090978826b3ff39,0x14922241791c228bb644,0x9e3e4df3265b12df0948,0x3fca7b852c3a8cd541b2,0x896742b13d575e2b1d15,0xb00317b28bb515c60ad8,0x622b278d8ee2c4e8614b,0x2869b5346a99f9ace5d6,0x6dba86d11361c5ad30d5,0x4d0fc2785a0037ccdbad,0xb32a89ba3c7f1d069164,0x3a8c22503a003bcdf328],#[0xbca969aa32809bc5d13a,0x400b41d0260038cda32c,0xc62d2a1a628f9f06d970,0x3389e1903400424f135c,0xbc2be9ca2a741a05f124,0x3a88e1a83a003c0df322,0xb6a8a96a2a7d99a5893c,0x3189a1a03c0037ed2b18,0xb0a928e20e739884e0fa,0x3f0b01f84200380d2afa,0xc02c0a1a48811a85b93e,0x3c8a61c038003e0e7b52,0xd52dca0a40771a45b13c,0x508e22804a00438fd390,0xff3a0d1302b0a647c9a0,0x420c226846004f124446,0xcf2fcb42a4909e86514c,0x378b21b042003e8e8b74,0xddb14aca6e841bc5d92a,0x4a8ee2c85a00453013ba,0xdf334b9a94952126b962,0x460d61e8460045707bc2,0xdeb3cb52748d1e063944,0x5b1282f07a00452fdbc6,0xabb6db330b02728f1d8,0x420ce1f8440052333c6d,0xde318b8a9c902126c96a,0x428b8228420044102bce,0xcbaf2ad266869e065138,0x4e8f82e05a0040ef237c,0xc8afcaaa5c90a1c7c184,0x528ec240520041eeeb5a],#[0xdd326bb2a897a1a6f16a,0x508e8258500040ef839e,0xe2b50c029c931ea7097e,0x6411a3386c0047f07bbe,0x12bf8e5336bba80929d8,0x408da1f83a0055f474a5,0xe8b52bcaac979f66b962,0x551162f85c0049514c0c,0xeb37ad12eca8a5e7c180,0x3f8c8288400049111402,0xdeb2ab4a788f1e469146,0x4d0f8238540045b05bc0,0xf4b90ceaf0ae2587b188,0x400d22304c004a11241c,0xc62cca5a628a9d66b158,0x3589e1682a003dce1336,0xe2336bca9c8f1f05f926,0x488ec1f04200475083cc,0xff3a8d0adea325078192,0x470e021830004e11fc2a,0xdab0ab9a8a8b9f06c966,0x480ea258420042ef43a2,0xeeb72c62b297a1474172,0x448c02584e004df1cc1a,0xd7af4a72487d9be61152,0x410cc2484a00438fcba0,0xb8a909921e7a9a45e956,0x4d10a31066003c8e1336,0xdbb34ba29a909f66b964,0x428b22183e0044d00bbc,0xd932cb528c8d1c662142,0x4e8d62304a0048f0fbd6]]
private def groupPage6 := limbs80 #[#[0xf1b9ad6b18aaa527e1a4,0x568f82d0480049d13c24,0xe6b64cdafca2a207519a,0x400ba20038004730cc00,0xe132eb7280851a45712a,0x5c90634862004690c3f0,0x9bc6d8b0ca8a5a841b4,0x498c42403a004d926c6f,0xdbf4e932eb02507e192,0x480ba1e026004fd2d477,0xda32ebf2a8909f06b968,0x5c10e3306e0043f00baa,0xf2b82caaf4aba6c851ae,0x540f82b854004d320c28,0x12bf0e0324b1a5e7c9a6,0x3c8be1f82a0054b38c99,0xe131cb6a78901c863140,0x368a61f8480048108bc8,0xca2f0a5a4e831ca5b906,0x5610e2c03a003fcedb86,0xfbbb8d530eae25c7c9b2,0x4e0ec25042004d123c3c,0xe8344bfabc9aa0670176,0x3f0ae220340046100bc4,0xc9af4a8a6a859b86494c,0x4b8c01983800434f9b88,0xea360c32949520a6e96e,0x448d8258500049f0fbcc,0xefb8ecaacc9821271176,0x53900290460047f0d40c,0xf5ba0d42e2a2a3a77988,0x5a1142d068004a91dc22],#[0xeab7ccc2feaaa587d194,0x4a0ce240440047906bee,0xe9342b827e911ee67960,0x490ec220340047d0b3e2,0xf7386d1af8a8a4c7697a,0x458e22485a004e12142c,0xc4abea527a889f673964,0x4f8fe3005c003e4ef362,0xec374c9ad4a52387e9b4,0x4d0c4218340049313412,0xceb10b0a728e1dc5f94e,0x528e22305200412f4b90,0xf8390cdb08a72487d990,0x450be1e036004a71b440,0xe6b24afa90952046c16e,0x550f42403600459043d8,0xdfb40bfabc9c2347a98a,0x5410c2b8500042af93b2,0xdab06b7a869622a7999a,0x3b0c01b03000444ffbac,0xdeb4cbba96891cc64922,0x480e02004c00463043b4,0xe033ab8a908f1f86b96a,0x501022905400451063c6,0xe4b5cc22cea12447c1ae,0x3f8b81601a00440ff3d0,0xc22b497a1c7a99c5993a,0x460de26850003a0dab40,0xd8b2ebe2b29c2106e96e,0x410dc1d84a0042cf9ba2,0xe3330b4282922066a146,0x528f02383e004930bbd6],#[0xe1322b5aa699220731a0,0x500ee2d07200493103e0,0xee34abf2caa22126e976,0x4e8e82b0440049d16c00,0xde33ac02ae9fa4c78990,0x6212c300580045f033c4,0xfbb94d8b0ead2688f9dc,0x5d90c32070004cd23c4e,0xf5382cf302a9242841b8,0x440b01e03c004890c400,0xe0336b82a6921f467966,0x348a21982a00459023c2,0xc7ad0a8a587d1c05d11a,0x4c8de278640042aefb72,0xe9b5eccad2982087017e,0x5710c2884e00457053d2,0xf1b7cd2adea4242811b6,0x368a81c02600493153f2,0xe0334b628a891b25a126,0x478e02384000438fb39e,0xd7b22b4a728b1e86495c,0x518f22483e004a30e3cc,0xf236cc2ac0a0a267d9ac,0x4f0f0298540046b09400,0xf638ad22daa2250811a4,0x3f8d21f828004c117c24,0xeeb58bcaa48e2086b956,0x550e01e036004f720420,0x1386cd2c8a1a527e9bc,0x430ca22054004d324c51,0xd3b28b8a808f1ee6c16a,0x3c8a81985600428f9394],#[0xe7326b1a8c8b1ea6492c,0x528ec2584a0049909bec,0xf6b90d0af4a5a387d1ac,0x470ca21050004cf2642e,0xd22fcae25a8b9fa6c152,0x3f8b61c8380044afaba8,0xe4b44bc29a8d1d05c126,0x4a8d629066004b113be4,0xefb60c9ad69aa026c952,0x5b91028056004a510c02,0xf93a0d6b0aa824a821b6,0x518cc248520048513c2a,0xc8afcb329694a307a97e,0x2f08c17030003f6e835a,0x889de6c9965a946470f2,0x380b02003a002c2a1a58,0xbcaac982287e9a652110,0x3e8be2083c00380d3b2c,0xa426e8d9e86d98854126,0x3689e1d83a00326b7ab0,0x99244899dc731b25a92c,0x2b882188200033cc02be,0x95228801ba5c138440ca,0x388b02182c002b0a8264,0xc0ac49fa20791925011e,0x3c8d02003000360ccb12,0xa1a6a8ea2a799985510e,0x3187c1682e0032abc2b6,0x96248839de6294a478dc,0x478c81f02a002d0ad286,0xaca7e94228779c863144,0x430dc1d03a0035ec9b06],#[0xb02888b9f66f9945b142,0x40120382600336c2afa,0xde8001d800100005008,0xa0f02a182410c8602802,0x1003e0d0320328960f83,0x81c8ea11112105722306,0x820cc103d0418861309,0x84090143804350724700,0x22c27e049362383a1c0c,0x24986a3b8961c8141689,0x904f44c14a0a8aa485a,0xa05c62e0bc150022f07,0x20708a0180230480e50e,0x612900b18e60e046484c,0x4240420b8702e8423913,0x2110383016c0b0b84609,0x4449904886e1482c3e0e,0x46204110948281e1181b,0x602b25a968910a43b00,0xc3108631303d0c41019,0x839006419942a9845436,0x1283b802154612523106,0x45a124dd021481c16602,0x8210881c390f42026097,0x4830c8d8550a2270002e,0xa8a4c5c090182245b18,0x8670a87a170d1382de13,0xc42fbc309c46c3288391,0xe540859e8ea436a444aa,0x3089f60c706b7d465e89,0xc7089d9b19bc1052f862,0xb15997f28cb0e0c68bba],#[0xb09c528bf5518a330cde,0x41a5f0869f45e0c9048e,0xcec66fc2700208687fcf,0xa307cd57408517e82aa,0xe28410907a13514906a4,0x2f8432c6e3648d706357,0x958d706417e8ab14661a,0x1b43b4148deb1522f3d0,0x1bdd94231a2bcb3fad82,0x165051887786a98216a2,0x216c277e61b0650654bb,0x7ac59eb177516db066c4,0x4c2a70cb482f11a4b428,0x1fc4661908e1d4ec8b6a,0x3eed4194c8f160e6821b,0xa7635a3e79e839032e0d,0xe86e78b885790c9f60c6,0x193ec18cbd6227b95545,0x2c8f7d005213dd0c8082,0x9860cb0e0c76eb4762c,0x3cf5e065c648b8c82c34,0x703b1c1a9028faf4b28c,0xc2c3cc4b7c2d0cdeb13,0x352261b27ad82178b4cc,0xe6153879070f023c70b4,0x27b885859c2e488e148d,0x935f422527c18c1d3ca4,0x359e10f4ea40a38e360c,0xc88f9e419bc10458706,0x7506527b85945854f806,0x869be51563da832f768,0xf177065ea0c6ce63669a],#[0x64e458b069c2318becd8,0xc9dbb2431797a11362f0,0x65ed15b9c19b54c1074,0x1a0d481479d9ac75109f,0x115b37608487c34baa06,0x15b2597a6247470b735a,0xe9aba042d82736002953,0x48d147aa9111560ed08a,0x8915e1089f9f31e0c0c,0xe58444f3e3c4b2ec0e1e,0xf1268013e68394de0839,0x81b3f37a8c195bf44146,0x4fb40cc3490890f3c8e2,0x1b55cd22a1dcc2c0a3e7,0x32abddfa0c3c69636526,0x4267fa610c2660febf00,0x674f0fe2249667464ab0,0x6fedc010b337d12201f2,0x6332d16ec2ca4af78289,0x2e2b84c7a533842b760f,0x78ad33f794a312c2cece,0x60491d3947e00cac1fe4,0x3463d42998d043cfe0,0x6916ff03121013e88dfa,0x6b81723abb416e8ba3af,0x65e3496247f0bff02125,0x63db4c58d9d1e2536168,0xb453a294b815820043c,0x30e6ad64c6686084b53e,0x2d9222250b7d9c2657d6,0xced829fc1a0230bb6aa1,0x29cd9ad4f82d3f72548e],#[0xc09899437f7e522888ea,0xb4270343b69b68030cdf,0xb7ac26811f6c111e3f27,0x995987da001090f9f426,0x7410acfe761e85ce565e,0x58db47734fae266066f1,0xca34a279f89067a872b3,0x8ab6a8a3f78b0a126ea5,0x6807c057521d7be20944,0xcc0f2c7308779185287,0x1081df5e489983f2eb42,0x586861f9bc548d0e5fb8,0xd8aa1967a5c115da01f2,0x8d233fb66328dab86cb5,0x8145108639659e31ce21,0x60a134aa5b6ac4d042d5,0xe2cdd342779603e1acd9,0x1a48234f3d7c2bb8043,0x62f5611f5e06242261e3,0x71e1881a02876e36635c,0xca3102100489ec3e82d9,0x3146f59a44ac3d509cfe,0x66f1a217ae30646ef968,0xd04fe90151a8787d1a69,0xa880efef800cc6fa020,0x614bda376447fa08282a,0xeda78090301355bc9168,0xc8fedc3021cfbb082511,0x27f560cad1e50d60338a,0x5a155e2fd074f83a0425,0x21d8c3c1b4a68c9e4fe4,0x8b68b7cc19085a60a79],#[0x5e54833e0eac24c2bc95,0xeeb4b44bba541548df44,0x2d3010b3d07ff880ba33,0x742d79e864af85919013,0x9aa28cec90832ba1ffc0,0xaff6b20433657d63bfcc,0xb0bd87f22cc1b3b95ba2,0x9a51472e148321b87cb3,0xff400c90908784198718,0xcb015b782d987cd40458,0x28a06d90b05224247fe0,0xa20d16e857d88186bf11,0x54e84c7254e840b07952,0xd91ec1a03ff9580ca8f9,0x7ac245d89df6828ffe05,0xaa05fb460cccfe1c87a1,0x7e020050d047668a8dd8,0x5b340aca8bf02410f0f4,0x37af985259abf8901fe4,0x727e71215921a4fe0023,0x8a6b3a9d0b70ffd00446,0x3287ff90354467a48e9,0xc53596bba629acc14f08,0xe74665cd0b901fd648e3,0xa9f818e1b884acb769a2,0x6a3d932d99a6f2086514,0x9e8be01b64cddf986c19,0x1097dcd5139253db66c1,0x4801001347b14153f100,0xad8206837e68942858ff,0xc0a0ed6f9997a1a3fce0,0xc3a0128810ee7918403f],#[0xd1decc4afb25220250f4,0x120ca0b477fc7e428808,0x100a243fa222066af97,0x8d3cff37a9098d58fe04,0xd10dd820d3d7f9608844,0xe34946478fa02fff2374,0x26a1c3efe1eb8802495,0xe1a1bc52012ce4f3aa,0x833c409105ac493e3d79,0x2aab5c0689e6f5183283,0xca95c1948fdca4de27d9,0x9224ad0f3ff06020867a,0x6d66a15ea147fffc8020,0x7f92d0180287664a8eb6,0xf2decd832d3fe1842850,0x7e90819225e83656a4a1,0x7204237e34f8a982da16,0x74a4ae43564b865979f2,0x844879ffb5ac159235f,0xc9dcb41ce1ace0f935a,0xacbb6049a6e5225efaf6,0x89d38b6305c11a7bb70,0x5067e6e00d5b35b6d5bb,0x4a37b1c346683ce63f52,0x65fb4c92387ffa222066,0x4efeb2833599baf35106,0x79fe1f40e2467b7d4c28,0x81f11c0521bf4083be04,0xadaa4aa123ff28509d33,0x86bee6a89edf68a225a1,0x1e7c10aacce0fcd21004,0x733d4261482f1bf0330b],#[0x915e9d05b2b7c7a22026,0xc7b6c61021960ff31936,0x906bd4320011185eba64,0x1f36fd085967dd680d17,0xaf96c2269c62e1c0889a,0x528e3f44af0c019d13f1,0x58f05b39bf6624217a8b,0xf5d69a23ee7a0891ea1a,0xd9619becd0021a16f821,0xac284b6dd297615bb44a,0x19c33831cc7ed2a46d78,0x7cffb500099831e50b40,0xca013cbfea01890af280,0xb44850fa20c84932c1db,0x66a7e8a4810b390a46fd,0xf210d7df244ae93f1b2f,0x94f07cf5692c20dcf222,0x4088290d9019084ece2c,0x91f1effa800008911afa,0x61ffff20082485c71d8a,0xccb1138223fbd52d2408,0x86564f0021183edde00,0x69a843520859ddca904a,0xbb22ca12bff45a0d610d,0x44f16506548872c77518,0xf911d4539b49b7728306,0x442f19a32f7aa4124375,0x1662665fa129163ff6f2,0x4b4574b503be30d05fa6,0x55ac3dfed1d3ff31a2b6,0x10edff83204330df0a2,0x8319bef9049e1f1a0f20],#[0x819a19f19a6f45f43143,0x930c60ccb93bc22b7fe5,0x32fc69445c3ebb24923a,0x68a804e7c559a1775582,0x10248cf58abb2164fda,0x3f74a63ab91ea35fffad,0x115ebd2a123f11d4539b,0xd0ddff00a093343f0742,0x82a59f5ec941f2d6c19a,0x4a133ff10516a33817ec,0x82049258ad3b066578b5,0x9215fcc4b8ca343af5ae,0x340bfc469422d4735be7,0xbc5b00414314bdf68a00,0xa184cae47e508e269c46,0x46f4cca1ff7b148a4bfd,0x22d5bfd21819bdf3059f,0xa17b80a30ed831a8f5e9,0x5a1b3cace536ce3da808,0x8887e2210c086e5ad833,0x91eb467094c20d72d02b,0x9ca1c370b2d3f8d090a1,0x979f2208d0a1df596089,0x772930c57768d3fb4841,0xb01a3a6217f684954296,0x565251c60e5f68cf42ad,0xb0d2ff68e8f3413529f4,0xef109448affd1cdc1996,0xcd054c770c9c250d32e5,0x37a10cee8043ea90a1f1,0x9fb21af98c004747bbb7,0x981486f4aa6085e79e83],#[0xe35da428fdcb24900698,0x31216ffbc832942d618,0xff32560511c3b96467ab,0x587d0c48428fb820147b,0x30a3acff90452fc43e06,0x2f7dba00cf163510fd88,0x6443f62048f0fb81065,0x183f0bff281133467917,0x1aa3d3ad9955fd750312,0xa203988d910ef66c802,0xe200b90345bbbf440860,0x60c842e3f8b90b42d07f,0x6b3f2084e6e1056b323e,0x1b508f3021ede960010b,0xeeccedebd4661f186804,0x67c04feb2d6b3f37a02,0xe7db20040269087ed810,0x4357c0c4840e95183297,0x8b4550c625140da2778,0xcc87ae2c8c7fdec108a6,0x7fe00968af2d1519848e,0x4c214c16d03faa48234,0x8239ce9709bbfe10191b,0x6dc684558a3310b5df9c,0xf2931307fc80b012c81a,0x506061c717a22d74563b,0xed9958a24fa2888f4d52,0x2c91f2e2028f1c9b0a10,0x129b0b4286305d9047ac,0x7fc0c4842fa931c5168a,0x404694f5fe990a224691,0xe4c2f5385a1dbff806a0],#[0x6ed315890ccedf99a085,0xaafa103ca8818d706696,0x10504a01a214dda68cd9,0x123497ddffb51119d1fc,0x8110f7d403c7ff2c4321,0x860fb26b144898b874e4,0x2d7953ec1945fa5b99a0,0x7e452839204457c7f123,0x9004224385b4fc00366e,0xa0cadfa6045086ce8fea,0x13c4d374215c144d8ff0,0x5e00670b075b203e6172,0x94a314ed1ae114187ca8,0x4876fff5d808109a131d,0x7b071886b3f3f88cc98d,0xca3445be9dd9c0482440,0xe992844052265feca328,0xef266ca6fd550010bcf3,0xc8e1f48cd920e59d11f3,0xc8dd89b81256cbb0318a,0x43efcacc1183dff2808c,0x2038ec41991aaefaa411,0x2155fc0b9086fdc4b61,0x9d0276cf2143b2cffc1,0xc107607e83934e15f9d2,0xbb08624347c286997df8,0x60255a9f05671205193f,0xfff341419214e6ffbea5,0xe31cc46b1271342f4cab,0xd35864869a35e062422a,0x3e10450dfe848800ce9f,0xb66de4a28a8ff104212f],#[0xa6eff820065ef8f800e,0x8e7a32ed833c5d04f4d0,0xcd0f0fc084a8c9224767,0x103d0bf904325021f960,0xca3668e230c6fd289685,0x5978e03859103a1f7691,0x1002870f88740da819a5,0x3fbfe0300008687f0590,0xa8c803a110d5087e1803,0x4ae177c7d70204902fd9,0x9ac1a2bba5354cced1a0,0x9403b3f956e11b24e9d2,0xdc6eb46105fdb040a857,0x6b42f2177e308586b5e0,0x9030134ddad8146cf568,0x845b407d093267ffe542,0x424d101c470656b75e4a,0x24319c32f949ddbe6d5a,0xc7d619257a6707e69004,0x6bc05838f64e30657e01,0xb3475e3452845c1f7b31,0xe7a780e933b61ff12c05,0xb323cbc5a10ef0ca2505,0x6457f328422436262b64,0x6b1cfff584062482ce50,0xe64f00212315a46b3676,0x1f57010a0291214deea3,0xfd482305304fc00367e5,0xfab4ca0fa39430086de3,0x60d9e33ceb4d1a88d385,0x94d4017f51667ec3f916,0x367e8c06785a1c3b7610],#[0xe5a19bc0a188337b8a68,0x95784286136dc23b9520,0x16776a26b93c2f3704f5,0x89c9db6b3e85cec18ca8,0xd58211a38e7accd7f255,0xa6b383a3766e42d0f2f4,0xf4810808bf46848aca98,0x56f58a7d78d08024917f,0x1623040c17cb4062b596,0x73086164fa0cdd5edf02,0x189e1528919f5899e42c,0x22fd7490460ef937e266,0x448cdbf5fea9001220b9,0x1f54a243be94c197f4f4,0xf2015a5390f695d83587,0xc2c04cdd87cb264c99c1,0x8e1c3b60f7fb802466f9,0xd9a4adfd9d3b4ce41dd,0xb0a3ee08c8ddf2d06301,0xdc2d7f09500335b6e94b,0xcc04894fa0c265a401ed,0xb7459ad7b48c7641494c,0x11566a0f58844e37bd1,0x69ffda0c000ced2cbda0,0x4042507fc2213333b250,0xca56b51c43d6391992fe,0x5869cd991d996ab0a187,0xa332e685661e6d8d0b01,0xe30cf8ecb3c670954473,0xddfd2d54a80876f86a07,0x9e0c4b9e2010523bc018,0xf2f9609221a1f431210a]]
private def groupPage7 := limbs80 #[#[0xd1fc41a24937f8189088,0xc1f2cdde528c4b0b38f,0x14f0afce9185eba64aed,0xc58001999fe440802868,0xc4002203fe8880019cbf,0x306affe40290a2b03f92,0x650021947ee59248365c,0x79bfee44ca0f9e83772a,0x2832059a3084496982da,0x1a7c854630034f84878f,0xf64ecde0684b76881e4e,0x8242177f9e05606249c8,0xbf2c7552d3010b3a3f26,0xb2bcd7a2e3b8335a15b,0xf9639b0b3cfa4875e10c,0x6697aa6fa1363e41169b,0x8fb0dc1f6c191b80f355,0x59dc9964fc028c40c12e,0xff08c94906e0f8a8d0ad,0xfff20cc84cf6fdca26d5,0xd102c38adef4490361db,0x3b0f42d3c0c484b669a2,0x300887937a5ea74767f,0xff615486178160f993e6,0xcd5640b70d7c0625a100,0xb075b3e8fb8ae4a480f,0x6a8f43bff0c8134a788f,0x977cc245437be9452408,0xdae8a83095d9ef8c19b,0x68fddec8166f714dea33,0xfdc8a40167f7e8210008,0x3237e2c5c2059c5fa09b],#[0xe40419787a5003316678,0xcb0096468e7e9f6810ba,0x6b133c5f9442fd04997f,0xf59490bce43cb0a43e4f,0xc014357ca85083321a1b,0xdd46ae18559b4377e980,0x48b013443f17956230c8,0xe55e06533b9b44e1fe10,0x794263563f8100402898,0xeb1b0c917e60449e5e84,0xfbc2303319df2113cffa,0xeda074b22b06a570856f,0x3652b5a8d0ee9e9ec030,0x4183fc86232157fa5092,0x875211dca9053d0dccdf,0xfac21ffe54d4c8c8d3ae,0x690bfeb97014925bc358,0x8248c23f041cf18e710c,0x74c127f599b066d5f754,0xa79242c233c90ae8086f,0x161972b7c0869f190046,0x9686a32fb51a3fb28a3a,0x381f54d008dc38bc5470,0xf396e109ada270afe9a3,0xcba58819b1e02f2ed0a1,0x75a880bf9676a400698f,0xbe11099b9f6e210810c5,0xab02897ffeb40409203e,0xda597b9c360d097d25a3,0xe68210ef290c504b3820,0x3a42866fcc923a0cf4d9,0x580859f8ce2fd084faf8],#[0xf809278edf74e0662ea0,0x2f5cb7084f4d0ad941cc,0x7814227ca889cb09226a,0x923efc17594d9ace0fd3,0x1892163c72201f3a652,0xd18fd92895a543ef5fe1,0x4689bfd48815cb708c2e,0x4e575b480a44fe22d020,0x9a24fcead52042d7bb74,0xcfe5a513817f30194efc,0xa702e0cb27d144672420,0x5f9708e8fa3252090872,0x2a1684edcb5df60ce271,0x5288e2edeb04244294f9,0x8ab065149e6826172ff9,0x2e8686eb2b445776883f,0x431cc46349a608287c95,0x88feb183323f04ba100f,0x202752b0437b5265e854,0x2f9c8f7c25a13c43931f,0x44a27d3d07cddc16ff52,0xc16c53a39e38fe258cc,0x5dfd85cc6d20d30f4cd1,0xb4d9a1b04e3c3699ebe0,0xff6ac0a36237455005d9,0xd3fac16b357a6c3f590c,0x87150b2ea45a58a05884,0xff5a020491247ba22be8,0x33e3da00cb59c406cabf,0xa8c3ffd2144607f410a1,0xc490dd6a9ed8334ff2c9,0xa135e0c1908e1a2ff080],#[0x82266afe7c00cb4fc735,0x484084d1df424c9d5ff0,0x219b7fa3141348ee1fe,0xc855efdb4241a23fc68,0x2a7f4d6188296692ff3d,0x2120f190a2aa52b42393,0xeef51b3f9d87a171ca68,0x84f0720fbc565c3066d1,0x700f82138dea294bd0d0,0x6fd93682ee2477650863,0x401096c315440c10f050,0xe83d7fa08bda376437f3,0x657f58ea9f412833319f,0x3dff7dd812293ec98294,0xc3058fc2d07dfa60a513,0xf010b35bc1050f2020e5,0xecc1e84bfe9c21141638,0x79d4807904319e1589e5,0x537cbe88f6667881e1a1,0x1716a9423bddfb3a2343,0x5b60edf5041c27ee8365,0x1b34fae2652717a68464,0xa85c80cd636cebfd5241,0x820ac343a556c6cc1cda,0x33928f0021014e091f36,0xf9752f2086af6f9b56d9,0xcd8ddba64f7002ac243,0x687a2df201487aff4444,0x5b766242141abc1434b8,0x96dcb633473c14501843,0xf1f4247e7e06cc6cf5f8,0xb60409277e3204092290],#[0x99865c639c431a46ffeb,0x904c810d2f0417bc3123,0xb5dc847097f3b8093dbf,0x1aa6857551882166d6e8,0x4070fdf17b4cf1f9fa32,0x771a1084327ddab6c093,0x1800044488737e3a489,0xec7946d914bd6587f055,0x96d27f41f7e9802899e4,0x69ed53cc53a674fb8789,0xe4d183287ff6db0a2004,0x188c7a598410a1db0636,0xe334a323b22f0478100,0xcde8a9065df1fc280a24,0x40bfd79509cb2d478010,0xd5fba4b237fc3cc32323,0x683b30f2a193cb5d240c,0x13fa5902215e3e694b0a,0xb0664c25633cd812e2a7,0xb1b6e110c2d54696c6dc,0x33cdaff427bfda4810b8,0x609cd800a54e6edf1833,0x4ecdc64d15ff55691acf,0x24b7ffaec80044d01b78,0x8bf7598850abfeb97099,0x6ccb6c06cf2a240de6b4,0xa5c72028f8343465b14e,0x248431e6c0948e2e210a,0x84d7909425bc8707eae2,0x49123417eb8127c60da0,0x7378a931a02888ffe580,0xc2ffc0840ef8075a567a],#[0x79599397e7eb585aa1a3,0x26c4b83aca4c16ed6727,0xfe409899e7ffac489049,0xbff2a511a78f648adc3,0xf09632782087fa501049,0x84887263ee5a0e70d672,0x5f8f444bee6a89f16f7e,0xff810066ee5260e70d68,0xbcf8df19b34f4b822e07,0x5aacbb067cf25420859d,0x19fcac0b86c23f041e7e,0xa2f2e568444ce658331,0x2485f7884824897df0bd,0x717a2b2341168a77c4c2,0x71817238ef42224809f4,0x368a085effa21110338c,0xfff08242249af3c18d5b,0x3a17216b180715b259a7,0x5b34b8e2a3910c6ffc61,0xe3bb090503411011dd30,0xb997fe9820233abec041,0x482a1996e40e10476f08,0xe2961359b4f0085e7c8d,0x3a8062434fe04a023a31,0xa686f4977e4b9cab4c3e,0x97ca1050f82cebb21cfd,0xa50afc72184864e0a5e3,0xc991890a5e68d903ec9a,0x819021a52810fcb066f7,0x96b387fa911033147f5d,0x9b25e7fcba228ef51c60,0x810891cf477072143e91],#[0xe0c3fa78864044695def,0x265e0822c569d8331a1a,0x9ebf89313af7ff3c2049,0xb002151bb115bdf674ad,0xa85bbd4136d6b5a2134c,0xc48428be8c9a13df1060,0x935e33cc3e8d4469b6ec,0xeb9b18248dffc0fdd304,0xe12d7e8c18faf80c4b3a,0xa290b8fcbc1021772109,0x3d32effeb8059243b372,0x3e89616bda21c3336456,0x989bb7a129e062420999,0x44237cc10dab675fad48,0x222268af2f784ca6ff8e,0x1064b5be665e86cfb724,0x4d18d58f040100a223fa,0xc2b2ed93457808f4fc3a,0xd8261fffe8281248ee14,0xd0449009fd227833579f,0x34278f89074cc3fff58,0x14b63343614bd605f2a0,0x66c93ffef0259247e96e,0xb1160d1bc62d78460fa4,0xca308a9698085a0929ed,0x2cf26050469236622bf7,0xa7d7e8592482f44f2a04,0x5772e96f4297e9868899,0xb74fcccd021c5f808448,0x42f199aac09f8138da2d,0xdfca686b660e00b646f8,0x56c965679f5238826310],#[0xf52220664f82c05acc1c,0x79b6c388cc396317d903,0x4edacc8e3047f2306288,0x7b01d7ffc41a2478fad3,0x7df0b067e65fc61aa862,0x130185cffae100486a90,0xdecec2f3ea4704426311,0x892af4709a455a1c515,0xfe3906c235a27fe32762,0x4004d4cd9fc3698cd1d,0x68399afa1247cfe594a8,0xe014e0695b9ec323f3a2,0x7adcd727fd0f669c8fc5,0x1f48cd90bf96a800811a,0x42211e506efe4aeba10c,0x9bffd7a00202688787e0,0x4a31080244f37e9e0899,0x53965ae1cf9099b5ff16,0x7f694350aaf23410815a,0x849f5211159bbb03b859,0x7c619c3a5460ca6f15c0,0xf90453bc890252df0158,0x608e2e11bfba430332f8,0xf9b81096fe08a00c487b,0x7419f3e36b132df02377,0xc22480c6656598b1997,0x1002bfe38348336fff1d,0xa1645be10ca5213c9602,0xe0672edd61d0aacd0dee,0x608939ec2a365c8edf74,0x80019efdba24d3ff6b96,0xe3249eb4ab12243fa7c1],#[0x21ad4934751ec996ccc2,0x98862430bfcd00044122,0x7d44e854ff9f3032b3f2,0x10410d1bfe68084920d0,0x108efc5252014876f8ca,0xfd833d67a766ca2ff878,0xb47ce613052993b7c4a,0x32c36bbd0685568c16c1,0xa233fed040266cf0ff00,0x19758aac18adef7604e0,0x2e0cb19977419d3fb0d0,0xc36b31335ff948327903,0x3e3c01967b3cb839830f,0xdf052455c1fbe0e41a16,0x9f602107ebef840924c2,0xc90bc99c42a78a08535,0x1ab265438f0fe6d14a5f,0x3fc221749fa822b3dbad,0x197df2706849a26f51c5,0xd6b06c922582093f8489,0x2250543972ea942ab346,0x86cec0a0bfcf6d1ecdf4,0xb22271bdda4539451221,0x1cf17ca5485a7e8a4810,0xcf62061e3a15787e2a0d,0x9876edf805521345ba19,0x20d7c7c822a3d7e8c814,0x9e0c49cd13eb0b3132c,0xc57f068edd54214c16d,0x522d114fe46444e410fb,0xb2081d0f07a3f2cfaa32,0xb32c7c78032cf678b447],#[0x9c360d09eb024cbdd2c9,0x980859e5364aa11a597b,0xab191a4bfdb444cad842,0xd3ff5f90051203ffc821,0x130f71990690c598af2c,0x222bb314f1833b3c0006,0xf9e4401247b80110b4d4,0x84b78c1c6118315acb32,0x8477f05061c310bd1ac1,0x34ca99f2fbe06697b54a,0x4888989a56f9c1479eb6,0x45404421b28d1d7fb7f9,0x93c1dbd264d48ecd6fbb,0xfd28b7967a22bd3ac509,0x2e205488df54c98d2082,0xae7a0b2126f6e84a86db,0x7093ec98f6d0a2c73c83,0x3560bed54505d928e149,0x6173454c0c19d45bf217,0x9d2a2853c10716189952,0x9725f8a35703642c6d1c,0xc7b635bdba2379850f0,0x787c18637d42838525c2,0x8f45270e098b52b84c7,0x210bf2fbe0650baaea3e,0x31ce909340cec8a97f10,0x259e64d47b7606a30f6d,0x6a084b06a5e8e5fb1714,0x8df54c9cd78247aa0b1f,0x91da850a5ef8631bc144,0xd45eb82f3c1ebec2a3d7,0x61691a68ef8752a65a38],#[0x82688f3a8f1fac1075ed,0x3d07ea42198d2f6a3f49,0x5860e1542a916f686d18,0x75d09381e12e36552006,0x92f041084c725a6c5043,0x27ae0ba0473c2253ca0c,0xed87ec2a291c177df6d4,0x9f5051b36c17d9116ea4,0x15da3986a4594c4e3525,0x58352f46008fe416a1c,0xab6d1d0d246d131e8510,0x29084ac33b1d3860a99b,0x2852e9d7a98334e908de,0xca9b3e1e201470e5f032,0x109476fc7582131bb765,0xab142f523a2dba100cbe,0xc7ba761668fa26346afd,0x24303fbc12c6f2e3066a,0x6785276ab0613cdcf795,0x8144012fede0420acb6d,0x3a7e8841e7a831cb0387,0x3cdc9840fcc5078fc688,0x217bd4882522af0577e4,0x38213acea2564f40425,0x3a525c22e1f094c1999b,0xf5cea283c3440047ec2a,0x82a5955c1618953475b0,0xe3432bac64c10b74af5b,0x99c8e34cd8d20a9e0839,0x4143c2129290fde24147,0x485e74720dae2511b4c1,0xa6ad8a8c6e871f12bf4],#[0x87d7e61419897868f1aa,0x883ebeea22793587d142,0x7cea82d1b82303c143f4,0xfaf050c89b6707f646d4,0x576d059123c69939887,0x28e5cf8fad030ccf5410,0x3eea4]]
def g63D7 := groupedPages #[groupPage2,groupPage3,groupPage4,groupPage5,groupPage6,groupPage7]
def g63H7 := limbs80 #[#[0x1010ac0800048080000,0x409000a4400f058083c,0x201000000c0a07810,0x10141a10000480419008,0x106000030080c04020,0x4003e800000501808020,0x1c07008301a01000040,0x8000c130080c02000180,0x20100c140080826001a,0x28108411000440000,0x804008d83e770180800,0x28c6011600044031300c,0xf41e02030280800000,0xd0400800040303006020,0x1800814000b9ac162,0xc0407000180a0f018041,0x301c060a00034000405,0xc28031101c764703,0x7048101293030383204,0x16142100c00110003000,0xb02015298000214010c0,0xe004901b090182616260,0x1330000c1500000280b0,0xc9509010002502804820,0x844080b828640e020302,0x81010001883404000308,0x10141e04040001c142e,0x3306840080001004202f,0xac0300014101a01b6006,0x4e001690e14232f008,0x204802000ab709802070,0xfde77d3e230402c248f0],#[0xffff8901c801fde76d3f,0xe3007200fffdb9ffffff,0x1c80b7fff66fffffff6f,0x42dfaffaf2cfaffaf0f8,0xffd12bffefd12e4b8720,0x7ff7dbfb7f95c1d011df,0xe73beb6620760577dbf2,0xfff9ba1d818fa77bab6f,0x79078075ff7bf7f7ffeb,0xe825ff9ffbffffbffefe,0x3ffdbbbff7fdfbbfa181,0x66752dff6e75a9407c0a,0xefffffffea841f82ddff,0xfffffeab8800c7fffeff,0xffaea20033fbfdfeffff,0x90800e7fffffffffff7f,0x839dffffffffffffffec,0xefffdffffffffff36220,0xffdffffffff6e80820ef,0xffffffffbda2103fffff,0xfffff05886105ffff7ff,0xfc5221845fafffffffbf,0x88611d7bf7bfed7bf7ff,0x4be9deef7fe9feff7723,0xafdb7effafdbfecc2218,0xfcfeffff7df3c88813ff,0x5fdbfffd2622051e7ef7,0xfeff5608a1671fdbff7f,0xd8c2285dfffffaf9ffff,0x8a18efe8ffffeffcff7f,0x6effffb7eefffeb7f710,0xbfcefeffff5efdf82306],#[0xfffffef4f8b88e19eff,0xe622406beffded,0x203a48901c8000000080,0x449f183202c86b620c04,0xab7e6d28a6f02420525e,0xdbc88f41c292f860fabd,0xd5a3a30dcb0056cc19b1,0xa32e38ec56fe030d6,0xb054d80d47267c22b040,0x80b1f82613fbe81b161e,0x807bc5938d8f21088369,0xcf03716610c6e8e378e4,0xcf542eb7dc3251ee2c5f,0x80b74cc1926d5f8a1df5,0x285bb94e8b11c5f77006,0xa15cacb64423fe03f831,0x173723818399c77170ac,0xd4ebe80640ca6e0e10b1,0xa8996bfd9f0c8b9f48b0,0xe1aadbeb5dfaf55941c3,0x59046def556b26789e21,0xaf60a5d0518d94ca8f37,0x83ab5f925d07e502f8a9,0x9a2af0517889c58aeb69,0xa23bca8658d03950d027,0xaf10024ca3189df6035e,0x752030d441bb26161a3e,0xf6001ca52a8204abec4d,0x228c15c4423e17a2e829,0x8252e2aa6051151a72ec,0xcb50705b6662ee156b57,0x16abc2a6082305f4382],#[0x2db6c3e4f9ef0bf10eac,0x8e525b6c087cad12733,0x38a207e9d3f89406c29a,0x355cb0075d08fe63501d,0x9a14d410006e8baf3e28,0xeb8032efbf2bf5]]
private def groupPage8 := limbs80 #[#[0x1481010c10108100c810,0x48010440101501014c10,0x8c81058c104c8104c010,0xcc010c80109881098010,0xd0c10d0810d0010cc810,0xc420d4c10d4810d4010,0x14c201442010c2010420,0x480201902018c2015020,0x58c20584204c4204c020,0x98820984208c42059420,0xcc020c80209902098c20,0xd0c20d0420d0020cc420,0x10821d4c20d4420d4020,0x580211502114c2110c21,0x98c21988219802158c21,0x1043008430d4c21d0c21,0x15030148301443010830,0x4c4304c0304843019030,0x5903058830584304c830,0x8c8308c4308c03088430,0x99030988309843098030,0xd0430d0030cc030c8430,0xd4430d4030d0c30d0830,0x1483110831d4c30d4830,0x580314c8314c43115031,0xd083198831980318c831,0x15032d4c31d4831d0c31,0x58432580324c83219032,0xd4c32d0c329903298032,0x10c400c8400c44008440,0x4844014c401484014440,0x58840584404c8404c440],#[0x984408c8408c44088440,0xcc840cc440c844098840,0xd4840d4440d4040d0040,0x14c41148410c841d4c40,0x8c84158c41580414c841,0xcc84198c419884198041,0x5804214c42d4c41d4841,0x98c429804258c4258442,0x588435844358043d4c42,0x99443988439844398043,0xc45008450d4c43d0c43,0x10c5010850104500c850,0x584504c8504c45048450,0x8c4508845058c5058850,0xc845099050988508c850,0xd0850d0450cc850cc450,0x10c51108510c851d0c50,0x8c85158c51580514c851,0xcc85198c519885198051,0x5805210c52d0c51d0851,0x98c529805258c5258452,0x5845358053d0c5299052,0x58454580549905398853,0x98c54988549805458c54,0x101100c9100c11008110,0x149101411010d1010910,0x18d10189101511014d10,0x4c110481101951019110,0x8411058d104c9104c510,0x8c9108c5108c11088110,0xc81109911098d1098910,0xd0910d0110cc910cc110],#[0xd4d10d4910d4110d0d10,0xc5200c120d8d10d8910,0x1412010d201052010120,0x191201512014d2014520,0x8c5208c1204c5204c120,0xd0120cc520cc1208c920,0xd4520d4120d0d20d0520,0x10d21d8d20d8520d4d20,0x18d21181211512114d21,0xd8121d4d21d0d2119121,0xc9300c53008530d8d21,0x10d30109301053010130,0x14d30149301453014130,0x19130189301853015130,0x585304c9304c53048530,0x8c5308c1308853058930,0x9913098930985308c930,0xcc530cc130c853099530,0xd0930d0530d0130cc930,0xd4930d4530d4130d0d30,0xd9130d8930d8530d4d30,0x1493110d31109310c931,0x18931181311513114d31,0x991318c9314c93119131,0xd4931d0931cc931cc531,0x10d32d8931d8131d4d31,0xd0d32191321813215132,0xca10d8532d8132d4d32,0x14e1014a1010e1010a10,0x1921018e1018a1015210,0x586104ca104c21048210,0x98a108ca1058e1058a10],#[0xcc210c8210c421099210,0xd4210d0e10d0a10cca10,0x106200c620d4e10d4a10,0x1522014e201462010e20,0x58e20586204c6204c220,0xc822099220982208c620,0xd0620d0220cc620cc220,0x10a21d4e20d4620d0e20,0x582211522114e2110e21,0xd0e2198e219822158e21,0xca300c63008630d4e21,0x1463010e3010a3010630,0x192301523014e3014a30,0x586304ca304c63048630,0x8c6308863058e3058a30,0x98a3098630982308ca30,0xcca30cc630cc230c8630,0xd0e30d0a30d0630d0230,0xd4e30d4a30d4630d4230,0x14a3110e3110a310ca31,0x582314ca311523114e31,0xcc63198a31982318ca31,0xd4a31d0e31d0a31cca31,0x1523214e3210e32d4e31,0x98232586325823219232,0xd0e32cca329923298632,0xcb100c31008310d4e32,0x1431010f1010b1010310,0x483101531014f1014b10,0x58f104cb104c7104c310,0x98b108cb108c31088310,0xd0310ccb10cc310c8310],#[0xd4b10d4310d0f10d0b10,0x103200c7200c320d4f10,0x147201432010f2010720,0x4c320193201532014f20,0x58f20587204cb204c720,0x987208cb208c7208c320,0xcc720cc3209932098f20,0xd4320d0f20d0720d0320,0x10f21d8f20d4f20d4720,0x1932118f211532114f21,0x98f219832158f2158321,0xd8f21d4f21d0f2199321,0x10b30107301033008730,0x1533014b301473014330,0x587304c7304873019330,0x99730987308c73088730,0xd0b30d0730d0330c8730,0xd4b30d4730d4330d0f30,0x1533114b3110b31d4f30,0x58b31583314cb3119331,0x9933198b31983318cb31,0xd4f31d4b31d0b3199731,0x99332587325833215332,0xc74008740d4f32d0f32,0x14b4014740143400cb40,0x4cb404c7404874014f40,0x8c7408874058b4058740,0x9974098f4098b408cb40,0xd0740ccb40cc740c8740,0xd4f40d4b40d4740d0f40,0x14f4114b4110f410cb41,0x8cb4158f41583414cb41],#[0xccb4198f4198b4198341,0x14f42d4f41d4b41d0b41,0x9834258f425874258342,0x5874314f43d4f4298f42,0x875098b439834358b43,0x10b50107500cb500c750,0x4cb504c7504875010f50,0x8c7508875058f5058750,0xc87509935098b508cb50,0xd0b50d0750ccb50cc750,0x10f5110b510cb51d0f50,0x8cb5158f51583514cb51,0x9935198f5198b5198351,0x10f52d0f51d0b51ccb51,0x9835258f525875258352,0x58353d0f529935298f52,0xe6f2f9935398b5358753,0xdeef377b7d7e7f3e9ece,0xd5e9f3f9dcde3eff7ebe,0xdfdfefb7bbbdcedf5fad,0xf9fbfd7dfedf3f7fbbcf,0xa0863f003a2fbffff7f7,0x7bb0c27aca29013a2ec,0x20eec23013a03a1ae222,0x4a4b18ee14e4bb2f310a,0x861eec031f328a4bcc42,0xe92b88661ae2d9813a2,0x89482ca28803a1e414e4,0x20eaeb10a29cc8291eb2,0x20a484ca28a0b28921ae,0xe422013a444bac424a6b,0x328920ce60f1f3104814],#[0x8ec781f3289472ca29a1,0xcb28969cc82529320a21,0x1ae20f1d328a692c73c9,0x28b20a2a2c2442932092,0x49ac82502b983c04e8ad,0xb813a08826ec2304391e,0x96a2c82485bb0da1ae2b,0x4faa3226c16ec0f9d328,0x3a83ce7420b3b2682ae0,0x67c0ab841c64e09fc199,0x12c48cca2732b089c2ae,0xa63f0d3a9c03ce8f5303,0x32a6e2ae0918b3b290c8,0x2c665ab323b82ae6baab,0x33282ec2c4230abb358b,0x2aed108abb4d860e09d2,0xab9d025ce28316b8bd8,0x2cac6418abb03688ca85,0x48abb45c2aecbf33b909,0xe2aae09bab328962aed0,0x2f32b096e2ae06f8abb3,0x39254e48ab1320a42aec,0x2c698b831a2ae0f28abb,0x92142ae6fd8ab83c0cac,0xe91f0abb31454e4f7953,0xb19f82eecfb3bb227c3c,0x2c6fa0b3b26238e8bead,0xb10b62ae0362a32260b,0x2ae15e3299092c0865a3,0x23328902aed020bb81a2,0x8aae69bb2b0882acc825,0x12a3228a5ae2ee2b323a],#[0x402ae61d0d3a9fa2ae69,0x978abb10c8cca230e3a0,0x122cec928abb4022cec,0xc95233284cb2c6438bbb,0xb3602cec99313156a2ce,0xc428ab32016cac2230ab,0x992802ceca3a33285cc4,0xaeca5b229106aec6a9c1,0xbbb4cc2ae70c8abb2e42,0xccc2448b3b2c2cac6c08,0xab992a62e0d4953921a,0xca8e8be8abb0d62aec4d,0x30abb1022cecac8bb818,0xcb2c6668abb26834ea8,0x28d3ab86a8c8a096b8a,0x26444e6a6adb1a2a5ce3,0x89e22b28522aec96aa32,0xa16e2aec478f3a28838e,0xea29b13b228a8c8a68f3,0xbb52a2aec0833308acac,0xaec673db228c62e0a60a,0xabb09e2ae14116b8ba82,0x34eb370abb0b062e0a80,0x8abb4c68cca310bb9966,0x664e0738a3b1e234eb41,0xf0abb0063ce8128abb08,0xac2aec3b16b88ceccca3,0x3233bb00c2eec5830b10,0x992b6c68999b836a2aed,0xd088abb198b6c6778ab9,0x8014c4c42d0b3b20e56e,0xec8e0abb4942aed2f0ab],#[0xba08c2aecd0a33285e2c,0xaec022b3207a2aec403d,0x6b8bfa2cec8b0d3aa542,0x2aec0931310922aec3c1,0xbb8138acc827233287c,0x430ea9e2ab1cf2aac825,0xf16b8c62cac2dd8ab99f,0x9eaae4298abb3dacac21,0x8816b8be4e8c89f2b323,0x1de2aec6a8b3b1c028ec,0xa838bb99b42aed468e3a,0x20062aed2aab3202834e,0xec758abb06caae229ab3,0xbb3fc34eb028ab981a2c,0x4c4bd0bb9d382eed560a,0xf3a53e3ae33a30b108ec,0xc8e82496b8c0a2cec8a8,0x8abb5402ee13f0abb0be,0x42aecc68ab85022aed5a,0xc0abb3442aed3899b816,0x2ec264370d3a90e2aec5,0x3f10b9c8254e48fc6983,0x172a8c8950a3b222cee4,0x22b15394682aed4b313a,0xb31e2aed068ab9908cac,0xe053339910634eb158ab,0x3a9dc8ccb2e313115a2a,0xae60f2232a0ecea6288c,0x1b12842ae1590ab80e22,0x2aece6adb1a2034eaf4b,0x8ab81f2a8c89f23328ac,0xa54e48b32b09022aecc2],#[0x42b320822aec3cabba2f,0x5a8aca2995391c2acc82,0xdc0bbb00e2cec8f8abb4,0x4722aec16b21910630ea,0x12d2c31a32c4c45b8bbb,0xb1408cca110abb18e2ee,0xe03e0abb3502aec460ab,0x392762ee7092a3229066,0x4e6abac31a00a8c89594,0x7b8be82aecdd14b91cc4,0x2aec0b479803eb4c6669,0x8bbb0f864e096b1388a4,0xc6a6250abb1142cec90,0x20bb9d5ac2c4558ab81f,0x608aca142232a2434eac,0x230ab9c588cca238abb4,0xf4d6ec230abb196acc8,0x8a30ab81b0ca643f0abb,0x9b2c8cca2632b08f0f0c,0xe693a33288a2aed230ab,0x3b1e862e0dd99b85362a,0xaecca32b08982ae7150b,0x3a10a2aec8a10b3b29c2,0x2aece70abb3bc8aca28b,0x8abb5308aca118ab9b4a,0xc5ae2960f3a20c2aec1e,0x60ab99742ee01c439827,0xc2aecef8abb01c2aecc,0x1a0abb3d62aed248d3ac,0x164acc82da232a302aec,0xa2496b8bda2ae06f3131,0xb55234eb2f8ab9d66c8e],#[0xe8232cb1d302ee63f0ab,0xbb1563ce8ddb1310aef0,0xcec738b3b21c2aecce8a,0xd31c1e34eaff33311062,0x2aecc3b2b084acea624a,0x33320a25ae30010b9a92,0xb4c63eab323b0ccc23f,0x8f3a154cc6428953926,0xc2aec398abb3122aed3,0xe60abb33c5ae2844ba80,0xacc8080abb38cacc8,0x44197b8ba42aec3a2b32,0x9c6a34ea75b0b117ccea,0xec9e8d3ab142eecbd10b,0x38a6eb2c70d0abb51c2a,0x4c82519381c42aec5e2b,0xabb4682cec8696b8bdcc,0x1e80cb8abb0e42aec010,0xbb9d72cac43f1539217,0xac0c4770abb10444e69a,0xc0ab9a86c8a6418abb35,0x9e2cecaa8abb3a08cca2,0xab8abb17a88ca842a322,0x2d054e48d0c3aa762cec,0x4248bb83482aed3b8b3b,0xb4c02ae0d331328a4ce8,0xe0ada232a328aca248ab,0x31568b4c6fa0e3a2f22a,0x8c899adb1a062aec49b1,0x9b836c2aec12abb2276a,0x2aec210b3b1d22aed521,0xabb4aec686290b3b28a],#[0x2ae6878b3b1fe3ce8ad,0xa0bb85143ae254233283,0xe82aec0bb0b10a2cac23,0xfe0c3aaf046e6da0e3a3,0x89e3ce9028abb4e05ae2,0xd058f3a5268cca29a332,0x207c8cca1590b9c6e2ae,0xece08b3b24c2aec612b3,0x32092c6865a22b284cb2,0x2e0710abb2e02aeca2b3,0xabb056cc642497b89886,0x2ae159bbba08c2ae1138,0xabb15e5ae303a33284a,0x42aec2a0abb50e2aece2,0x20b3b1c42ae6750bb984,0xc0aec0a9b3b98fc2eec6,0x920b3b1ca30eaf98abb0,0x2962ae0a18bbb0402ae0,0x204c3a188c42e7198b3b,0x8bfec8e43f0b3b2105ee,0xed390bbb08e2aecb896b,0xbb35eacc80a8ab9c1c2a,0x4eb0c1139a9254e4f50a,0xabb30ca8c8a12bb22a23,0xcec29fb3308b42aecd90,0xabb26264e0838abb0b4,0x42cec8923328ce62e0d6,0xc8b3b27a2aec3230b88a,0x5c2aed5b0bbb0102aec2,0x480abb440b2c7079139a,0x4b8acc8262b323a02eec,0x42890b9a628cca288abb],#[0x1910acc8228abb35cc8a,0xc22495394c234ea4baab,0x3136cacc8020ab812acc,0x2e4f78abb058cec283b1,0xbb32ec2c42d0abb4d65,0xc4e65c98385365ae2f8b,0x8bb99382aed350abb31c,0x85ae2ff0abb53e2ae613,0xc16b8c02b6c67b98b837,0x728cca2a0abb0ac34eae,0xa80abb0d4b2c63e8bb85,0x3b6cac2402db19ca64e0,0x424a332840ccc428ab32,0x9972acc82e8bb8144c2c,0xeceeb1314aa2ae61c8ab,0xb19788cca322c31a262a,0x4e0860abb10ab2c658ac,0xbb9d70c0c49d2b3208e6,0x2cec800abb5271e800f8,0xf3a352b2c6620ab99a8,0x8ccca418ab84562ee734,0x48abb1582ee06b8abb07,0x742ae14610b9a682aec5,0x46b1311782ee1570bb85,0x1922aec340abb2de2aec,0x4588bbb5322aed190ab8,0x9d102ae713b131160c4c,0xc298b131094c2c49b0bb,0x3116c2ee66833a98fcce,0x4c4c2b2b0a6aaec89e31,0xbba3722eecda2dbb08cc,0x62e094953921c2ae11c2],#[0x983827254e48b9139a52,0x2ae0ae14b91c2c8a424,0x41738c622ae069acb182,0x9242e6972ab8a6e2aece,0x882db1a142aec3aa3328,0x5e64e0a60d3aa9050e4,0x4288b3b2062aed578abb,0xa08cb4c6620abb466c88,0xed4d0bbb0422eec233a3,0x310dc2cec970abb4182e,0xc68822b2844a8c8a331,0xb3b1ea2aec568abb436b,0x2ae6d98bb999e2aec088,0x8d3a82044e6988abb332,0x2ee1148abb12eb0c677,0xcb3310922aec990b3b26,0xa62ae6f00b3b1c82aece,0x550abb0268cca292b390,0x82eacea9bb02a0a42aed,0x89f8abb46a2eed338d3a,0x22a22ae75119b8272a8c,0xc89d8a3b27042e7182a3,0x3a9c2cac22d0abb410a8,0xee04933318fc2ae06c8d,0x938252c4c45f8e3a08c2,0x2ee06e30311fe88ca849,0xa232a2a2aecf818b82de,0xe2aed51ab3209e2cec89,0xa8ab82502cec9596b83a,0x7e2ae15eaa32aa6ceecf,0x2530b10ae2ae11631310,0x10652ecf32232a2642e7],#[0x43f10b9aae2cec84b299,0x94682ae745b3b0a52cc6,0xe4b60b3b2402aed3a94b,0xbb00a3ce91eb13109c54,0xcc8288abb4782ae75e8a,0xabb000c2c456b1313e6a,0x8cca169738a588cca200,0x8abb15c2aed5a2232a0c,0x82ee16032210922cec8d,0x7aa322745ee2f98ab849,0xc2aac63b96b892eacc80,0x288abb49654e48633bb0,0x972acc81a8ab9d60ccca,0xce03021972b2c75430b9,0xb050c2c45baa322622ae,0xc89e0bbb322acc82a0ab,0xb8bd660e1330abb06aa8,0xcec8c8abb17e2aed2196,0xf3a09c5ce2840abb4802,0xcac63f16b8bb4c4ca250,0x8abb46cc8ea3f2a9826e,0xecea428a332842ace49b,0x623328aece86288b3b1e,0x902aed4a0ab9a488cca1,0x8e313108262e073b1310,0xa525cec7b0d3ace454e4,0x8040abb180c6862510b9,0xb2582ae12db13a0a438e,0xe0e38abb3382aecd38b3,0xb844cc2eccf8e3a22062,0x2e0e5b0312baca62318a,0xabb448cac4418ab83ac6],#[0xc4c4232a3229c62e09f8,0xabb3f4acc82d2b32084,0xe38e89d8abb10e5ae301,0xf8bb986e8aca250ab9af,0x6a2ae6692b323a4c2c60,0x728ab9d76c4e25caa322,0x122ae64f0bb9d1264e0,0xa03b03127aacc824ab32,0xb2b02aec608abb0ce30e,0xec9719b84cc2aec618b3,0xb856234ead51039b682a,0xaec0d0f3a27e2cec730a,0x53920cccca24adb19c42,0xc8a43f0abb33452e0f31,0xabb488cac244aa32a6e,0x2ee648ab3201052e4f5,0x8abb3522aece88ab9d0,0xb62ee04e96b899a34eab,0x118ab99bab6c683b1310,0x194aac2442232a202aed,0xcc22b320a42ae0b70ab8,0x80ccce86248ab82be2ae,0xc661b0b1b2eb4c6048ab,0xbb4142ae64a0ab99bcb2,0xaed4f0b3b2662aed038a,0xabb4902eec310f3a2822,0x46e622ad318422ee6c90,0xabb22a42ae1608bb9936,0x2a8c89498b81ca2ae750,0xcab388a63ce889b3a909,0x608cca2f2d31d508cca2,0x708bbb2702aed5394b92]]
private def groupPage9 := limbs80 #[#[0x3c42eed4d8abb3623ce8,0x6162b3200e2aecba0bb8,0xb19a2ae758acb1842b2c,0xed5432390922ae0b50ab,0x38a7862e083b2b10a22a,0x686f319382802aecf716,0xab812c5ce3038e3a41f0,0x8cca148abb0622aed4b8,0x8abb4b02eed080d3abd4,0x42cecb38b3b2142ae6bb,0x50abb0162eec3d8ab858,0x542ae06a2c31a065ae2f,0x5d8b3b2a82aecf630b18,0x3deb4c6588abb43c2aec,0x61499b82742aec260abb,0xb01e62ece0b3b0a122ae,0xea3aa3328322cec740ab,0xbb0602ee037b2b08ea34,0xaed2fabb226cc8e63f0a,0xf3a46038e8c815392362,0x2cec94a232a2e2cec708,0xbbb1622aed1b8abb030,0x6c4c42b0bb998a8cca34,0x495393502aec190abb55,0x2a2cec832b31ce6aac82,0xbbb1642ee1448abb4,0x9722eec3eaa322722aed,0x8288abb07c2aec2730b8,0xb3e4b6c6800b3b25ac8a,0xc89eb331906a8c89c0ab,0xbb11c56e49d8f3a07ca8,0xaec0e0f3a42ace643f0a],#[0x4b94c2c4c43e96b82c02,0xacc807313115642e7229,0x8ab84a4aac82915391cc,0xaa8c8a3ca9800ccea641,0x58bb81e462e0b90bbb4c,0xd02aec5bc6901c054e4b,0x94b02a0942ae68eadb19,0x3405ee29e2ab926e2aec,0x736b2190fc88ca8b0abb,0x99e688ca888abb39e2ae,0xe13cb2b109262e09696b,0xb99d850e4c8ab32aa63a,0x6c68c8ab84a68cca250a,0xabb0325ae21e313117ab,0xb0c67baa322a02aec0a0,0xb131098c4c423c3a008c,0x62e0860abb31634ea4f,0x90bbb0902aec44aa21d0,0x18c0c47eb131012a8c8a,0x298b3b1fa62e0a00b3b2,0x40cc4c45f0f39910acca,0xd310ab98182ee0680abb,0x11622ee147b13108a2ae,0xe0c50bb9cfac2c45e30b,0xbb54ac2c41f8abb2e662,0xeec22acb18122ae6c00a,0x8b82e23ce0542a218fc2,0x2aeca70abb0822aec2e9,0x31313a42ae1178abb080,0x3ce8ca0abb132acc82e,0x431a98a42ee6d1b13112,0xb6c2c427322a0928cca1],#[0x140abb4623ae03b8abb0,0xbfa3ae1420f3a2522ee7,0x66d8f3a284ccc43f2cb1,0x90a2cec2a08abb07e2ee,0xecb10ab80762aed12b29,0xb180c2ae6640abb1542c,0x4e483ab321428cca11b2,0xb3202ccc644190b9a9a5,0x8cca1f8bb81b62aec00a,0x32b087ecac2ca33a90fc,0x4c2c420b1310b0ccc223,0xb2a32280c6865c8ab852,0xf86ce6090eb9ce62aec5,0x9837b0a7c68eca54c98b,0xa0c6ae72536b1bda6ae2,0x70db7319c0dcea1b9ab8,0xa926ce6c5c83a894dac,0xe4a2373114a6ce51fbfa,0xa1bdd32e2f71a39d326c,0x8e127cc98bfe68ec78bf,0xab9c546ae2b61b3a04c6,0xdac657b6bb0046ae30f9,0xbf3926edac6189ab844a,0xc6ce4b8c428a7cda64bd,0xbb6390c66ae706b6b1bf,0xead8ea3736b0bc6dcc87,0x2dc410b826ce13f9ab99,0x13268e49cb7313fe6ce4,0x677b62949c6ae1521b38,0x93a726a20f9ab9c0f16c,0xa73e9ab85466ce4feb7a,0xb8a88dac60ab7323c6de],#[0xcea319ab8aa0d8e8fb9a,0x998b2e6ae0c61a3a000d,0xf8e8881ab8a16d8a81bc,0xb6b1bd66ae1019b393dc,0x6ce4a89ab8b8cdcc477,0x74c30a9cdee756b6288a,0xc46ae2179b39a16f8c8a,0x9ec91922e68e6071ab81,0x4f8daec49b621d6120c4,0x13c36b0af06ee0519bb8,0x9936fec8a3b63a19e6ce,0xe0ab36b1b34d8ca75b62,0x2a3466ae0741b3b1c06a,0xce8f236bb436f8c89ab6,0xab83406ae146b7b918a6,0x6ae1184c39092fec89e9,0x1b3982adac6d69ab8b5c,0xdac6df1ab8a3916a29f,0xc3732c9cdea6939b3a29,0x8adee54e9ab823efec89,0x3a9ab8440dcc2f1b6211,0x9d46ae0d79b3a3526ae0,0x12a9b39462de8631b631,0xa7cd8c87a9ab80c86ce,0xa4eab7322f268e037c43,0x3a436f8e49b9ab83dad8,0xcc742b73a57e68e8fe9a,0xab84eadcc6f79ab8358d,0xdac6404c1900d38a2a31,0x9ab847924c41f4da91ec,0x66ce7059ab9b44d8c67d,0x8b61918ade6462b6b197],#[0xc8dcc62e362a2ca6ce4f,0x19a3a2726ae0d5b7320,0x1826ce02f1b3929c6ce9,0x70b9ab99da6ae7014899,0x90c66ce45238b282e6ae,0xc440b7323f26ae054b7a,0xb8c0adea650c9993c8dc,0xce60bb731bd2dac6e29a,0x621b7edaecccb6b19986,0xdcc8701b3a380fac8213,0x491922c6ce03036b8d7e,0xfcc90e9b392546ae01f,0x483a8a46ce8d79b3a28,0x34f8c894b6b1b326ae2a,0x309b390166ce4e11ab81,0x2a4daec321ab993136e4,0x8de1abb07cdac616bfb2,0x8942dea2284d98a26dcc,0xe6189a3a3e6dcc65537b,0x2888cdae2f0b6b1d0a6c,0xa430b73101edec69ace,0xb39b1a6ae13c4e293833,0xd886679bb99dd10429f1,0xb7194fad8a8d21ab81d2,0x26ae7001ab82c46ce65d,0x337b1a0e6ce4731b380d,0x6cd8c68236b1c0710e82,0x271b3a016fe830e3621a,0x86e6ce4b21ab80c0d885,0x60c1ab84f66aeceeb63a,0xa41ee4ca0c1ab8c14dec,0x64dbb6319e8dcc455be3],#[0x31b106ae12ab731c3eda,0xce89eb6b199c6ae0e037,0xe32292dac661b6b0bc26,0xdac704b732a6c68e424b,0x49194386ae13fb731be0,0x26ce7051b3a3846ce8f4,0x11b391c06ce0359b3920,0xd46ce52bbfa12946ae0e,0x14f98220e2ca171b39b,0x10cdac731cda13eadcc7,0x54a1abb02e6cec7a1b39,0x94cc6ee0511ab854adcc,0xc8279ab81ef38a4269a3,0x3819a6ae310b621a4edc,0xae29f37312a2dcc8f09b,0xab825338c2a336990fc6,0xd8ed081b3a02edce8319,0x37b1c10dcc40bb6b1858,0xcdac45137a9d106ae117,0xbb73ac9c6ae03c3fb226,0x58de872936108a12086c,0x833730142f842441b392,0x252dcc63cc8991f73a60,0x313e3aa6f26620f9b3b,0x11eadcea509ab8a5868e,0x650337a198a6aece2b63,0x39a4e6ae12c1ab8a2522,0xae05f37b998afe872f36,0xc390c2dee431c9993f46,0x6ce9011ab827adcc2f0c,0x9bb83ecdcc4239ab80d6,0x26ae03b3e21a94dae32c],#[0xac9194366ce751b63a92,0xfe6ae0eebe3228f36630,0x234c21bea6ae2f2b7a1a,0x298dac6e51b3850b38e2,0x89eb7b1a306cec969b39,0x14646ce4e2be32270f8c,0xc4419ab8b866ae2e3b73,0xb999e6ae0171ab848edc,0xaec1637a18dd2464f5b7,0x7a91233842a31b384466,0x6ae673373196c6ae2843,0x48311dcd886fd9b39c04,0x6dce7441b3925afe870e,0x7482125268e90836b195,0x1068e89c362a0146aec1,0x111b3812ed8e2c9b7310,0x4486ce8f79ab81aa68e6,0x29f36388dc6ae2cf1b38,0x1a046ae07ec599273166,0x86d51a391446ce81937b,0x3939c6ae72f37390c716,0xce01eb6b1b70dcc4171b,0xab83b66ae6fc9ab810c6,0x3cc2e0b6bb3d66ce6569,0xb6b10fcd886cab63207d,0x66ce52fb6b949d3e6107,0xbb63a3726ae1199b3902,0x56dcc6039abb082fae49,0x4c1b398306ae0b79ab84,0x3f8d8e85ac9b12646ae0,0x6c64e1088cd8e8689a3a,0x927e68e13e3e322a4dac],#[0x87271bb8222dac6571b3,0x31282d8a53ec821a28de,0xee2119bb8c266ae15336,0xab83d66ae057b7a1c506,0xdcc87ab732320dce9271,0x4db0a8b22650e9ab810a,0xa6ce067363a942dea527,0xb62a0c710a22a9ab839,0x7ad88756b71955b22c42,0x4b1ab83e26ae111b6b19,0x352dac6bfbfb228adac7,0x6dd9a3a0106ce8df3632,0x840a6ae00cb6b1959108,0xe684b6bb4fed8e81bce9,0xb149c6ae0fd3731cc66a,0xae30a1a3a3c4d8c471b6,0x6b197c6ce4df1ab99d46,0x6ce01e45a1b56e2ca1f3,0x36b08406ee14c9b38196,0xd26621536b1af0dce28f,0x536b8d10dce8f0b73191,0x466ae081cdb93eade867,0x4bb7b8d3a68e89db7320,0x88cdcc6073e322966ce7,0x81c1bb8a74d8c89ac420,0x9c506ae03545b888cd8e,0x65581ab85066ce47ab62,0x3b058dcc4d54f10a8cd8,0xce74b37190926ae12f37,0xb384af20c49937a184e6,0xdac6be1a390fcdac60c9,0xb63894320849eb6389ac],#[0x320e2293e3226c6ce497,0x1b6b957f20c47db73b41,0xfcd8a8fbb73126adae6d,0x511b390c06ae0a79b391,0x1120860f9b391d2dcc4,0x49a9ab81ce6ae303b732,0x88471642e0be21c3a6ce,0xe0671b39954fec89937b,0xb914310c49f1b3a3546a,0xc607737314be6ce89fb7,0xf194e668e4779ab8ad13,0x6ce049b7191666ae0613,0x4cb08826ae14c1a3936e,0xed8c4953e3225e6cec9a,0xb9b390046aec3a1ab99c,0xe520870b4f1088cdcec7,0x84c293ea6ae0f21ab83,0x8f2dce450c5b19eedeed,0xcd79b3a26ad8a8b6b6b1,0x825cd8c6859bb9be66ae,0xc7031b393ded8a44a1ab,0x3137cd886adb632252da,0x8c6731b3a3f86ae73b37,0xb385686ae018cfb128cd,0x6ae12e9b3b2906ae29a1,0x1b3b294d8e8d24421a7c,0x66ce4711ab99f66ae050,0xb73237c6ce5011ab80e,0xee68e8161bb84206ce8a,0x629abb35c6ce0469a3b1,0x97e6ce4f49bb84ccdae4,0x4e0be218e868e8079b39],#[0x81206ae0e2cd98a233ea,0xe0d837310f8dcc4431bb,0xb8bd06ce60d1ab8a6e6a,0x8e907c9b11f6d8c6701a,0x429382fae09b9b39d266,0x2062cbb73138ad8c49f4,0x9ab8226d8a8dc9ab9c11,0x8dec2891ab850cd8ea93,0x63fa186936a4309b3a3e,0x82dee714442888c6ae66,0x3eb6bb3f4d8e2b6b7318,0x5546ae28737310a2de65,0x603b7a1cb2dcc7019ab8,0x13833ee4234db89dedac,0xec98b6b1984dac6c14eb,0x3a3ecd8653e9b3a3966c,0xae0729b3a29efee8779a,0x8993f930e4fab63999e6,0x22c41f1a3a28a6ae2d5c,0xb7b91ac6ae68d1ab9cd5,0xd8ec77b6b19dd10422a,0x93e21c0f32c23a362199,0x6edac665bfb22546ae12,0x1a36b1982dcc64237a98,0x53adcea37362a0dcdac6,0xfcb73998a6ae72b3639,0x854efe8704b631a353e6,0xe4a0b6992a2fee49b9ab,0xb846adcc8bf36bb1ee6c,0xac6d61b3a29d30c2a29a,0x631a02dccadfc821854d,0x38c4a336b1c3a6cec9ab],#[0x3628b7adaed283731307,0x2dcc8133e3228ad8c4a5,0x7b632220d8c673b6b12a,0xf46ce6fe36322bc6cec9,0x639b380cefe82169ab9c,0x4f66ae28ab63a9366ce0,0x6d1c590a7cd8e4489b38,0xb2546ce68c37b1858dea,0xe13d1ab9bfedcc4db9b3,0x319166ce8d59b3b2646a,0x6a2234d189dc6ce89937,0xab8b946ce53c1b39d4f1,0x6ce4ad1ab8b612464771,0x1bb8188d8a8f09b39a0c,0xa6ae0ff44319ded88691,0xac99918f24c4214c213e,0x5ce4ca161ab820e6cec7,0xa9ab80826ae67a1ab83,0x4826ae046b6324606ce9,0x2881b381832682cbb731,0x857d38e4231b381526ee,0xa92736393eedee2371ab,0xb8864dee693b7b8c26d8,0x8a914373a0dc6ae2971a,0xab812730e43f36b1b14d,0x6ae0e6443888cdcc4fc9,0x491920e6ce6f637b1c36,0xcde86dfccb087ce4ca1f,0x94c3a3eadec09ab6bb3d,0x206ce8f89ab81fef8c89,0xd4d993ea6ce1254d98c,0x11e68e90d3618b2a6ae3],#[0x4319ab80f33064fa9ab8,0x1afefec8a41ab814eda6,0xe033b7908a06ae10ab73,0x31258dac7499ab9a306a,0xcc424b8b28306ce6f936,0x42927c6ce4351b3935ed,0xde86679b39286dac6f9c,0x1ab8a96dac60737300dc,0xe6ce481b6b1822d8e405,0x1b3814ed886ad1ab8ac,0x3cdc64dbb6b88dc6ae12,0x57b738cb2de869b362a2,0x18ad8e9569ab8c1a6ce1,0x67d9ab8402dcc6bc3699,0x9c3f30ca7b1bb83c4dac,0xa432b7314a2dea53e9ab,0x3928edac6d7bfb2256d8,0x8861b9ab9bde6ce8981b,0x738bc26ce1549bb8558d,0xda64489a3a0431042233,0x1ab82c66ceca3ccb8c02,0xa6ae10249a13526ae670,0xe1ab82e4d88556b7a12c,0xf26ae11bb73b032dec70,0x523fb8a6e6ae2979b393,0x1ec6ae098b6b182edcc2,0x431b7a0b2adee26d4c31,0x21de6ae0e4b7190fcdae,0xe51a1ab80a868e051363,0x311f8d8e71437a1a4e6c,0xce49b9ab825ad8e462b6,0x93a228d886d19b39a346],#[0xd8c907c8b8a28dac6cdc,0x453185930a4ebb629cfa,0x330e8031b381306ce4ab,0xe9b3a3f26ce1171ab818,0xf66ae12b481883e6ce70,0x639b393e468e4bccd189,0x23068e8db9b393966ae0,0x4bcb61955adcc64c4919,0xa1de6ce4ffb6290a0dcc,0xa908be21cff1064ddbe3,0xa0b8312c61637b1a1320,0xae0aa9ab849268e70945,0xb391da6ae10336b11426,0x30e2779ab84bed886d29,0xc91940c6cec7b9b3a253,0x8dccabf9b3a28adcc45b,0x89b3a284dcc40c37323e,0x6cd8e25a9b39484dcca2,0xa11a3927668e4fa1b399,0x29e6ce0611bb8c1e6ae2,0x898b6218726ae2854831,0x1b92dac75bb73918a6ce,0xe6fe1ab9cded886b2b6b,0xb8218dcc415b6311c26a,0xce8f4b63998ad886069a,0x938a28dcc4f6373187c6,0xdac752363a0dcd8a693c,0x1ab8000d8ec884418a7c,0x6ce6ff9ab81546ae689,0xb363986e6ce528b7308e,0x206ae0e89ab8212d8c89,0x103fb229ed8e2dc9a381],#[0xc3a6ce90236b1d3c6ce9,0x6421b39b36da65271ab9,0x916adec60c9ab9c32dac,0xe4f5cda93ea6ce8f5363,0x32832dcc527373104a6c,0xce470b7a1bf6dcc250b9,0x6bb0006ce8feb6b0c1e6,0xdcc1271b38456fcc820b,0x37325266ae154cc3a892,0xb22650436b1bf8dec677,0xcb632280fe82e21b39bd,0x6edaec0c9ab821adac74,0x973610b7adeecfa1ab85,0x2e26ce42bce2928cf8c8,0xc97373b4d86ee1279ab8,0xa4b2dae450b63a1ac68e,0xe2c836b19166ae0a2b62,0x324a26aece037324a46e,0xae0c536b1b40dced3fb7,0xa3936adec68636b184c6,0xdac6ffb7a9936dcc6c11,0x37b1c126ae0b44db11ec,0x6ae2a4bf3205cdce88f,0xfccb8bd66ae157be3229,0x8a6ce8a3be3225726820,0xfcdb8be8dee448b73a1,0xd266ce8f5b6b195a6ce9,0x6174e2908cd8e8633731,0xa80cd8a54048b9436dac,0xc8553731898fee8fa4c3,0xb85206ae0f737310aedc,0xec49db731af8f886171b],#[0xb39d3cd8e52736219a4d,0xd8a4ad1ab8b96dcc47a9,0x3e322946ae09a441927c,0x26ae08b491943a6ae045,0xfbe32254d8e64db6b1b5,0x30dcc61349191f66ce70,0xad9bb8b706ce4981abb0,0x12ede8756b6311ded8c8,0x2151b3b29d30e4031ab8,0x8ad66ce1281ab9bd9206,0xe6fc37b8ada6ce1551ab,0x284346ae6f937b91b46c,0xcc23736321d4dac6094e,0xab993d16829f373241ed,0xdce250beb2082dea6319,0xb7319dc68e0621ab83b0,0x2dcc4523731040d8ca82,0xac49928e6ce5389ab8c1,0x9120e2251ab8526d8ca9,0xb29b381ab226505b6191,0x1f6fcc81f37b99b4dec4,0x8ea3621d70d8e8b2b632,0x853c6ae1059ab821cdcc,0xe1041b39294dcc6019ab,0xb8a906ee1269a394766a,0xce03536b1d4e6aecd49a,0xb393126ae01a9abb0326,0xd8c68137320166ae6fc1,0x9ab84c4dec68d9a3a040,0x868e8dab73249cdec4a8,0x4b7b19d4d8a7441ab8a9,0x752464f9b7328a46ce4e],#[0xfe36b1b8868e8119a3a2,0x2766ce4d53638936dcc8,0x5271ab8b78dec0a93631,0x84186ae13037b19f6dee,0xc4ad1abb08538a2e09ab,0xb8a1a68eca2b6b1804d8,0x2e5049ab8b18de82281a,0xab8400fce29bb731c172,0x6ce01b1bb99366ae6f69,0x9b3a4166ce8de1ab8a32,0xadcc4e0b6b1cc4dcc450,0x19ab8132dae250b6292c,0xf86ae0c69ab8bbede843,0xd63731d3d1086de1a390,0x85468e6f9b7a18a4dcc4,0x2269ab81966ce70bc9a0,0xb4d86ae132373acb338a,0xa909cfa8434d8e46d36b,0x39408d8c8a09b3946ed8,0x8e1561b394826ce6f49b,0x7321ded8e4b29bbb05c6,0x6ce471cc989dcdac74c3,0x443908d2265101ab8316,0x46ae11b1a3a27868e8fd,0xa9ab8484dcc4ddb6b1b7,0x506ae10d9b380e6dcc89,0xa21ab84d86ce52a1bb9c,0x9d4dcc43ab6b191c6ce8,0xc8b4f98224dcc63c3632,0xa24edeed07b732b7cdce,0xc4a34c98a0edac6da362,0xa138a6ae6f4be3229ed8]]
private def groupPage10 := limbs80 #[#[0xac6b94c21b02d8c496bf,0xb393a330a4289b3a436d,0xd8c4a89b384a4dec6821,0x9ab82a8d8e8119b39c00,0xcdee61bbf3238adcc535,0x29ab84e26ee7091ab806,0xcadac7001a3949d3ea10,0x436bb4126ae1381ab83,0x500dc64319ab9c40dac7,0x6811b39a0ed8e4633619,0xb3806ce0479b3b28a6ae,0xe0211b393d4dee26b1bb,0x312ca6ae29b363127e6a,0xae6899ab83426ae066b6,0x9193f86ae634b6192b46,0xd8e862b6b18446ae106c,0x1bb847268e8f59ab8332,0xad8c8ad37192a268e423,0xcc8b108510a42a9b3a04,0xea68e8159b39bde6eec0,0x37b7b1a2e6ae0d4cc2a3,0xab668e6fe373986e6ee0,0x894b7323c86ce8f1b7a1,0x2858dcc67dbe3a3e8dcc,0x82cbb731be6dee4dcb8b,0x311fcdea648beb207d20,0xae3063e21b8a6ce68436,0xab8240d8ec889b3938e6,0x6ce8954da93ae6ce1431,0x3732948dcc67a1b38492,0xe6eec161ab9a1710c89f,0xb1ab856910c67bb93282],#[0xdcdea63736b1d4724e48,0x771ab80ae6ae30f36b1b,0xea6ceca59ab84a13a60,0x4759b384966ce9079b39,0x8a786ce701b7b182e6ce,0xc8a89b3927c68e8111bb,0x994fb3842e0b6b08e0fe,0xae0b3373255ede863336,0x7b1c0cd884b2b6b10926,0x6ae055c8213526ee67db,0x37318ff20a88a363a8c6,0xa6ce4d61b3997c6ce687,0x99b3b27ad886b6b6b998,0xf66ce89f459088cd8a8c,0xf19ab839c6ae08ccc989,0xb54dcca509b3984cd886,0x68b1ab852edac601c5a9,0x13fa6ce4a4b7a118adec,0xc6e336b19546ce49a373,0xb82b26ce12b36293a6da,0x263033f3a4ff3ea4a31a,0xf984286ce0619ab84973,0xdac72f37992cadac705c,0xb731cc46ce8ff1ab8c30,0x46ae08e1ab802edcc458,0x937a9c9cdec2881ab829,0x926ae7429ab8c326ae09,0x9b363ac9cd8e9144c290,0x9486ae2ce36322cada60,0x6171ab834468e547b6b0,0x8242dcc55237a9c506ce,0xe51ab6192cb24e5049ab],#[0x39984dce35fb7320e06c,0xce818c919212d882ca9b,0xe1089adceb441b393766,0x6ee2103731bf86ce4fd4,0x1b3911a6ae1439b3a2a0,0x8dcc45e4828b2ed8c89f,0x5b7321f66ae705373105,0x826ae2f1b732040dac6c,0x959b3a2a4dcc4f54420b,0xbbb3086031b391f86ae2,0x85c1ab8204dcc63a1ab8,0x1bfe6ae03a373208cdcc,0xe08c373949c68e4043fa,0xb185c6ce4729ab8a866a,0xae7309b3a06adc6462b7,0xb3a3f53ea423393285c6,0x30a4c09ab80d2d886629,0xb73104336c298b6321ef,0x32264f59b39c406ae121,0xb9b3986c6ce524371912,0x9cdee24d9b39d4cfee09,0x61b731cf522650db63a4,0x412d8a431bfb22626ae0,0x80b1a3849ad8a811bf32,0x1afe6ae14a442908c6ce,0xe703b7b1c3ade861bb62,0x310fd30a47b37318846c,0xce155cf983e86eece2b7,0x7a149cdac71037b8b266,0x6ae0b39b3a41924e50db,0x1b390826ce6c53731bf0,0xe6ee2db1b384f46ce066],#[0xc9ab81c8d8c49abe38a6,0x6ed8caad9ab9a186ae0e,0xd19ab8a9edcead1b6b13,0xc1adcc60ab6b0942de86,0x70cb7323f53c42e09b39,0x9a12dcc6c69ab8a646ce,0xc63c4cb88786ce4ee1b3,0xb82706ce895b63a014da,0xce4d7373218e6ae01e1b,0xab807ad886f0b7388dc6,0xdac2374e983d46ae02f1,0x1ab80b71464d51b390ba,0xd8a61bb73957edac65e,0xb1ab843cf8c89a36b183,0x6d20e48838b2832dac65,0x3d1b3a000dcc8373632a,0x3e8d8a4deb6b1960dac7,0x90336b1d292464863731,0x8b2e6ae680b6b1be06ce,0xe66136b1b1a6ce8ddc9a,0x38d3afcea9bce981e86a,0xcec9749b125310a2e0b6,0x7a181a6ae1109ab80046,0x36c2a73fba2206ae12a3,0x1ab82c320820fb732353,0x46ae6821ab815adee463,0x19ab82b66ce4f61ab821,0xe4d887141b38506d8a6d,0x1fb7a92ca6ae155b731a,0x2526ae20c9ab8a34dcc4,0x8969a391432465041b39,0x24a0dc65271abb358f8c],#[0xecd59ab850a6ce89b373,0x3926268e51d1b380686a,0xae0561b384a8dc65341b,0xa3b270dcc5211ab81986,0x26e507b6321c0dac6081,0x9b3856adcc64037b896b,0xcdac6001ab8030fae29b,0x89ab9a1c6ce500b73109,0x106ee734be322a26ce54,0x6b1ab843b10829f36b9d,0x6adee4051b3b29ed8e4,0x13bb621d76dcc72f1b38,0xa07b16c29f3fb226a6ae,0xc8a737b916b3262f99b3,0xb1a14d8c6861ab8034fe,0xae61b9b39b446ce47437,0x7a9cb26ae68436b1d2ed,0xdac64c3732461268494b,0xb638c266ae1319a39960,0xa6ee147b73207cdcc8f4,0xb6389b46ae0efb732a6,0x6e6ae0a71ab8296dac60,0xe0b7318353a60bc373a0,0x292dac7529b392a13cc4,0x6c41ab9c066ae705b631,0x8a3cdac74a9b3a442dac,0xe3441b3b2566ae11236b,0x219d46aece4c919236dc,0x8a81c4c2900cdcc89b36,0xc3980cdac2c8373b436d,0xd8e2119b380c8da6424c,0x9b39998dac60d1ab834e],#[0xedac63fb7b9936dee4fb,0xe9b3a39268e8e0362184,0x5b24c420b6b1d4cdac6c,0x31b6b1b606ae12bb639d,0x686ae73145a8b826ae7,0x5e36210c6d8871536bb,0x136a6ce80d48312526ae,0x64c09ab81766ae0cdb73,0x3844adcc4e11ab8bcf30,0xce53036b197ed8a5289b,0x6b088d36c2949b3902c6,0xd8e831bfb22526ae01a3,0x9ab824c68e4239ab848c,0xf20a20f9bb81e2d8a448,0x49ab852c6ce9081a3980,0x6a6ae14a9b392b2d886b,0xb2b6208a06ae0161ab85,0x1666aecd81ab8354dee4,0x5079ab8aa4dccb293699,0x1c22dcc5389ab835120e,0xc898b7314cc6ce525c82,0x391426ee0313f32084f8,0xae1251b3a3f0f886f636,0x7b19cf2082151b3a4346,0xdaec161a3a3e86ee6fe3,0x3732ca2d8c6771b3a360,0x6de875c3632284dac63a,0x51ab82aed8e8c99a3814,0x6c6ce6863fba41e6aecd,0xa39b3948c6aece11ab98,0x412d8c49cb739b46d8c4,0x2231b3a0586ce8a89ab8],#[0x9c10dcc42336399b5168,0xe307d1a94854086fe1b3,0x193ff40c8995020c6940,0x8215d0312a340c496d1,0x1a19dd40630a513822d4,0x4086fc5198a21446496d,0xd0219c140a5195020c8b,0x740ca9ed032a71468498,0xb51a929540a41fd0b812,0x3746c49ad020a6142e08,0x7dd198c1f40821051384,0xa27468703502184d4686,0x2a6d032a974086d85021,0x135540c49ad02925b408,0x870ad0b843742628bd13,0x3883346a69ed1a9b8b40,0x6a69c51a1be746c4a3d1,0x198c3942e304d1981dd4,0x42c4e1513185d46628bd,0xd029b7542c6175021bd3,0xf40861150294834464e2,0xad1a9a9746a519503128,0x634686fe50b8a6d46828,0x22d1981f740a90350212,0xa2342630e5110c8b4243,0x28850981dd44ca9c5021,0x19dd4264a5502a353406,0x6285d02929346a496d1b,0xa0a2146830d502938b46,0x870850311df468522d1,0x110a9b4242a6d0981f74,0x46628d51a0b31406307d],#[0xd1b11df40caa551b19f7,0xb468307d1a9b5942e528,0x9d1983f942e20cd1a129,0x2146e477d138a6d4660f,0x9550983e744c60c51a0b,0xa654663055198c3f46c4,0x4d65138c3d4662895021,0xa22340a80bd0b1831446,0xc49551a135f42c4d5503,0x391df46a6a55020a2b40,0x260fe51384ff46c4a550,0x1a0c69466284509925b4,0x468215d0219dd46630a5,0x511929540a69ed031295,0xb40830d502a3f540a4d6,0xf51b8a21408288502a42,0x31468322d02948542e30,0x94d032a5b42e13fd020b,0xaf40867dd198c0f40a8,0x6da51b93e94682985029,0x84146a6dd51a1c3746a,0xc4e150219e940c67751a,0x20c1f40e4fa51b8c1f44,0xa4a551a0a9b44e528d0,0x1a9b8d4082c8502a27b4,0x40a888d021be740e2885,0xd018a254084d7d0319f7,0x344e304d1b125b46a696,0xad13914344e049d1b12a,0x6d40ca7ad1a8c1f44c90,0x8502a43740ca94d02a2,0x3e940c47ad030a9340a9],#[0x2525118c3946a6e05029,0x8a1146c498d1a91df44e,0xa495502a33340a4e1501,0x10a93468683d131c2b46,0x4c894d132a5b46a71850,0x1383d742c4d7d13202f4,0x40c498d0299dd46a61f5,0xd13a22d42e07550213e9,0x944cad4d0388dd408698,0x750193e94664fa51a83f,0xa3406303d1a93fb46c4a,0x1e50b826d42c4e4d13aa,0x26b42e0f5d1a9a5346a7,0x4a551a1b5344c89ed1a1,0x92a346a6265021a2144c,0xa6d6d0299f744e0f7502,0x21bf540c4a75021a6b46,0xa6d4d010c6940c67050,0x132c6144c420d13a4374,0x42e0f75190b9140ec77d,0xd13243740a87751a93e9,0x140c4a4d03229f408694,0xd13a33346a4e1513242,0x2d44e4a8d132a5344e25,0x115021b7d408707d1a9a,0xc8b42ec0cd03a3e940e6,0x4a8d03936f42e0a2d010,0x8b540caa2d020a7d42e,0x42985198b35406473501,0x2a05944c7085132c7940,0x869ed13949d40a49ad0,0x1b83c544ca9ed02a1f74],#[0x46a6f5d0291eb40a4d55,0x51992634042a6d019203,0x94042e0d021aa540c877,0x8d1a9c3740a2895029bf,0x9540ca78d19920340649,0xa8d02a3e944cae050b12,0xa9740849ad0329df46a4,0x6a2d13aa6f44e0a2d132,0x1bf342c70dd0b800146a,0x649ad1a8a2544eca2d02,0x32a5d40ca77501926b46,0x869b502937d40a4a3d0,0x321f744c496d0bb28b4,0x40a30a502936f44e8fd5,0x50321e940429f5190c69,0x94064f7d018a2f44ca1f,0xd01937d44ea8b513a05,0xf94684a0d03226342c42,0x16d0329f742e4f7502a3,0x3f344caa2d1380694662,0x15190c8b44e49bd029,0x926b44e89b51a8c2942e,0xa428d01940540429651a,0x329e940e450d13240d40,0x6a67751a1a5340e88850,0x1a935546429851908b54,0x42e01a5018c3940c89ad,0xd13ac3740a88ad1a9a5d,0x544c4d7d0b841340a694,0x6d13ab3340c894d018b3,0xe944e4f750290934642a,0x9ed03a41f4086d7d1a03],#[0x28f44c4e4d0291f94686,0xadbd1a99f746a70351a9,0x99d540a90d50193f340e,0xa88851a1a2d42c496d0b,0x291c344e2385132a5d40,0x8522d13205940a28ad0,0x1a9b5340e90850b82b74,0x40c87050b949d40ca7bd,0x503227b44caa55028a0d,0xf46a28ad190a7d44e237,0x950b82a342e49bd0291d,0xd40a495502a26b40c8a,0xa35021b5340a907d0b1c,0x1dd46a2835028c354042,0xa705028a214684fa51a8,0x12834086a7d02129b40c,0xc89b5021bed40e811502,0x21be94042235018c1540,0x6a28851a8c3540a302d0,0x1a9bf9406216d0293fb4,0x42e00cd118a2f44ea165,0xd138cd946a302d1a81f7,0x94442a35028c1f40630f,0x95028a9340a4f551a91f,0x5f40a88b519935f40a8a,0x7a50389434042e450193,0x146829f513900540c6,0x118e03498087a011480,0xe2022fa07af01a860571,0xdff833f40c0282c1609,0xda128a045e0105203c80,0x5fd016d38570814ac04e],#[0x68707a1b0b067e818f60,0x16a881b81f6a078f01d3,0xa25b9892a8237908a002,0xbce29f00a39e27cd89ab,0x8bd7e2e4e0b4c42c048a,0xd38cf1632a40c5fa306a,0x38f78dfc836d60d75634,0xae3d260f0b83b1d0e7f0,0xa54416b101503f3f8f8,0x491d524626113ca43ce9,0xcd012f1e4aa6125dc486,0x5158140f04f2b937fa4,0xd78560095288538d9498,0x9744a5ba5168da58d795,0x918a64614217f885e76,0x69d91a1b666f79960664,0x526fd61b9326ccf1ad4c,0xda8875379cf7472911c5,0xc1f0987ab89e55c780d1,0x30a2068480469fb667d6,0x6889121c6485c4a11b68,0xdf88e03232b68b37a277,0xa5434939ea48d690cda3,0xba6a9e994625fe29671,0xa18b2807e9ec3275d09c,0xf2a76ba97a6a48a28c24,0xb9b6ace02aea0aa392a2,0xbad0e4b2dfac5d2afeba,0xb632e77eb8772dc46b59,0x6c0ec2fe42be1f2f2fcb,0xfc4c66f31482c3c53097,0x335decc1fb2ad2c96831],#[0x79b4c22d1a0b40daced0,0xd9d9361eed7203577ad4,0xe2dfdcb796adce0b6d60,0x9aece56438fd4e299384,0xc3b144ead93a61ce82fb,0x3383c776f07abbcb4eda,0xaf8e13dd9af5e93d274f,0xef6fe8f3f4ccfbaebe90,0xc13230375c08dd00ed3f,0x11c2757089bc1d77062f,0x2509002f85a00430e70b,0x4cbaeca6a5e861de6916,0x8418c41f03a00408efb8,0x2cc2ecaaa4c821cc6294,0x24f0f227058003ecebb7,0xe2b30b8aa6942047098,0x63d8ac188420046d0abd,0x8dc30cac25c7c9b85891,0xe400aa1d83e00422f83a,0x2c6acea7254889b65b13,0x64c8f82a04e00400eab6,0xee3b3ebcaa094a0a7097,0x83389418834004710bbd,0xec8ad8a3a46819c26411,0x3f8ca1d01e003eaedb6,0x8cbace9f2367d9b45c93,0x4498d62385e00406ee37,0xddb40baa9a92a006715,0x2428b61c82e00438fbbc,0xcd9b1ab7aa0982026c17,0xe348a01b03a00450feb9,0xb7a8a902006b9704d90],#[0xc370bc1f846003badb33,0xab8abaa225a881c85f92,0xe390b01f048003a0dcb2,0x6bc2ac96a387b9cc5d91,0x6530f226832003cce0b2,0xcd7b1eb92aa92a087398,0x4539082a06600446feba,0x2dcb30b62849822a7798,0x2488ec25852004810fbd,0xada2f0aca76909f06b16,0xa468e42484a0044f01ba,0x2d1af8ac27a8c9f86915,0x64d0f02384400406efb9,0xebb62c2ac29f2347b19,0x6428ba200440047909bf,0x6b528c8e1ec751aa5994,0x8470e82604600392d130,0x8cf300a9a5a881f26a15,0x2450c0240460040ef537,0xad9316b6a98962026c97,0x44d0e2238420040ef63a,0x6d4314b529c931f47217,0xe400c42384400428fbba,0xbc2bc9e238801cc6013,0xc408de2504a003c0de34,0x8d0b08afa6a881c66194,0xc410c620042003e0ea36,0xcbae8a523c789be6193,0xc490e82704800402f1b7,0xed32feafa728e1fe6c14,0x511022c05e00434f838,0xed6b10b4a98919fc7018],#[0x438e22405800412ed38,0x8c1ab6a223c7c1aa6295,0x85592e2d050003e8e2b3,0xce2352c1aa69b21c7b1a,0x84d8e828060004770f3d,0xbb2bca223c7f9e67197,0xe400aa1601e003c8de34,0x2c22daa826a889ca6114,0x2480e623858003b6de35,0x4d2b08b427c891ec6916,0x8350ae1b82e00420fcb9,0x8b1a88921f8739845791,0xa520d42505200398d7b0,0xee3b30b8a9c9d2307c18,0x440e02082e0048d0bbe,0xcc52daad24a881d86516,0xe3d0a815818003f4e9b4,0x6beac89f230779aa5e13,0x4488ea2704800396d934,0x2d7318b5a62859dc6e18,0x24b0f22c85000424f93b,0xcd2b1ab0a96919fc6c96,0x64e1022b0560041ef9ba,0x2c9ad4a3a64891f06f18,0xa3f0d02285a003dee635,0x6c72d09ca3c829c25e13,0x8438ce29040003dcea36,0xed431cafa688b9de6695,0x64e0ee2986a00410f138,0x6e6b40beac89a22a7499,0x63d0b21f8440045707bd,0x4bfaba9a2327c9c06014],#[0xc488f02705200414ed36,0xd0302aea72871fa6b95,0x6428cc238540040ef3b9,0x8c82d6a7248889d06315,0x4448d422844003d6e033,0xecb2deae2648c9d46615,0xc490f824850003f6ecb6,0x6da304b0a8290a126d96,0x2418bc1883c00443023b,0xcd2b08ac27a8a1e66495,0x6480ec2c05000432ffba,0x6c6adea8a808f9e66194,0xc410ce2384e00402ec37,0x2c5ad2a1a68891da6694,0xe3a88e1682a003cae536,0x2c5ad4a223a871ce5e14,0x44c8e220058003c6e0b4,0xadab2ab8a9c8e1de6797,0xa460da2484c00428f339,0xaceb04a6a5a881fa6b15,0x468ec2d056003bce8b6,0x8c62d8a02287d9ba6396,0xa458ce2003c003d0e335,0xcd1b1ab6a9a8d1e06615,0x4418c0200340043cf638,0x6d1b06aca7c849d66394,0x83f0bc2685000414f4b8,0x2c0abaa12367b9905b93,0x330a418042003aed9b4,0xabe2ba9aa1a761a45911,0x6458e424850003cce335,0x6d4300b02888ea006f96]]
private def groupPage11 := limbs80 #[#[0xc3b0b21e83400420f7ba,0x6d3300a8a70879c26012,0xa3a0ba248320042af839,0xcccaf0a8a507f9d25f12,0x8518de1e85000416edb6,0xae5b5ac22d2a0a2e7c99,0x6508fa2904a00459043d,0x8efb76c92daa02327719,0xe440e0258380047b10c0,0x8cbaeea9266829ca5f92,0x84e8e82d06000448f839,0x8e8b60c9ac69da3a7e1b,0xc448ca2084e0048f0fc0,0x6db31ab7292879dc6414,0x8438ba1e834004710f3c,0x6c1ae8aba748d9e46c16,0x84b10829852003d6e034,0xad3b16b3a668c9ea6a97,0x4438c21e02a00410efb8,0x2db32cbdab29c2207717,0x2478e2248540048b093c,0x2e9b56bbabca22427116,0x5190a328720045d09bf,0x4ccafeaa28093a16751a,0xa591182b03a003d4edb9,0x2de354c32c2a2a487d1a,0x5290c2f860004790b3c,0xcf6b7ad22e2ac276889b,0x4408c01d04c004831641,0xac0aba9aa347b1ae5793,0x5310a2d8520040aeab4,0xcce2f0b12728c9fa771a],#[0x438c8268520041af8b9,0x6c52caa1a40831b66394,0x570ec2202e003e4e5b4,0x4dbb34bbaba9ca287899,0x8458d02103a0045b033d,0xaccaeaaa272881de6b14,0x6480e424840003feed37,0x504bbcd2ae49fa0a6f16,0x65c9262f8680050f29c6,0x90f3ccdcb42b928c831b,0x25f11c328480052734c8,0x90d3d0de326b4a94969f,0x2568fe26848005633fc9,0x3053b6d7b22b428c869d,0x65f12230874005413147,0x512bfeeab70bda82891d,0x4569163407000561434a,0x4f9ba8d4b0ab5a6a819b,0xa5c910288440053f2d44,0xb09bf2e6352bca8c8e9c,0x85e93e31858005533748,0xb1641cec336b426e809c,0x25b9183486e0055540ca,0xb0b3cae1b26b0a768e1e,0x619203005e005192f47,0x2f5b8ad42d8aea768a9c,0x266942360620050930c3,0xd21c28f1396c8ac49ea0,0x5d0f8240480057f454b,0xd1c408e5322b52828a1d,0x65e11e3185e0057344cb,0xf19402e9b5eb7a948c9d],#[0xa5590a2a05e005734ccc,0x11e406e5b1ab524c8499,0xc490ea280440058b52ce,0x5003aed52e0a02407c97,0xe50106260540055737c7,0xb17bf0e5b2ab42708399,0x45c9022984e0057f444b,0x323440f8374c3aa4939e,0x66d12e3506c0058f504e,0xd20c08ebb56c02c69ba0,0x659383086e005af524e,0xd23c38f1350c2aa6941f,0x5d1002b85e005c7584e,0xb0b3aed3302b126e7e1c,0xa4c0da1d03e0059746c9,0xcee368c8ab4952167298,0x4510fe298580049f1840,0xafebaad5ae6ab2427718,0xe581062b84a004db25c3,0x2fa3a4d5ad6a924a7618,0xc520e42184e0050b2944,0xd143ece8b46b7a707d1a,0xe468ce2204c005413aca,0x3093aad1ae6a0a207117,0xa54902318680054b3aca,0xcf8376c42b69b21a7419,0xe4e8d22684e004c919c1,0xf033a6cfaeaa7a2a7398,0xc5e10c2783c005473ac7,0xb26c28fa388ccac68f1c,0x4b0f02605a0059750ce,0xae2360c12a0969e46516],#[0x4d8ea27046004a9103e,0x50d3cad6304a3a2c7099,0xe559062a05800557454a,0xb1f436f6370c4aa48e1b,0x671443386e0057d48cd,0x1073c0e3b40b727a869d,0x6601242c8520051927c5,0x512bfceab5ac5ac4941f,0x26091a2c0500055f3cc9,0x3013b6ce2d0a82547c1a,0x453102288580051b33c6,0xd02bd6e1348c1288821b,0xa5a1242f0540050f3246,0x8ffba8da316aea748b1c,0xa6612c32080004f128c4,0x916c00eb35cbb2aa969f,0xa591203304e005994c4c,0xaf839ad3b08ae256831c,0xa4a0c22183c004e11fc1,0x4f73a2d5ada9f23e7d98,0x8639242f858004f924c2,0xd16c1af1356c6ac6919e,0xe66140340740056f3fca,0x6ff3b8dab00b2a78909e,0x550f829048004ff2d45,0x921c0aeb33ab927a839a,0x8579042e8600059953cf,0xb0c3d8e4350bcaa0891b,0xc4b0e02a848005052ec6,0x3103ced8306a7a568018,0xe480c0248480053332c9,0x506bc6d62d49a9f46b96],#[0xe518ea23038005493547,0x10fbdedfb22b02647a18,0x65c10e3405c005553bc9,0xd10beee9b3cb7a7e8a9d,0xa5c11c3386e0052d3649,0x324c60f6378c82b8951e,0xa500e828052005bd5950,0x7043bedfb18a922e791a,0x24d0fc2b85e005032cc6,0x3093b6d22fca9a58871a,0xe4f8fc3186e0052531c7,0xd023c2d6300a42307d19,0xc62132338740051726c5,0x2fe39ed12f4a4a5e8b1c,0xe4c0ec210400053f3246,0x2fcb8ed1b10b1a547597,0x8611142984a004e52643,0xf3384cfb02aea56851b,0x85790a2e0620050529c3,0x5143e6e1b3eb8a7a8e1c,0xc5d11637070005413e4b,0x91c400e9b48c32ac949d,0x2530f2280560058549cc,0xf21c16ecb4cba26a861c,0xa500f82d066005bf5fce,0xfeb90d5314afa5e8699,0x86111029058005072f46,0xf25c42f1b6ac2282851c,0xc578fc2483e005a952cf,0xd013c6dd338bb27c891b,0x8651323505c0050f2ac5,0x11640ee5b3ebb29a931e],#[0x45090a3487a005a54acd,0xb0c3b6ceaecae2727f1a,0xc4f8f229058005673dc8,0x8db32ebd2ac952167798,0xa6f9542f054004870abc,0xf2bc36f2358c32bc959e,0x5f9142a05e005e363d1,0x524c5b00394d12ca9ea1,0xa6610c2603e005a155cf,0x325432f3368c5abc9620,0x65190c2e048005cb5acf,0x10bbe0db31cb224c7898,0xe550da248320053b3d48,0x307bccd5b1cb325c7b98,0x86794e3d8900050931c8,0xd18be4e1306b52888a1b,0x44b8f02684c0054f424b,0x115bded72f29c1fc6997,0xe578f82d0440058d48cd,0x1033b8d0af0a5a46819a,0x85b1403d078005012846,0x7103d4e0b26b426c8b1e,0x65e118318600054f3848,0x730c5d043ccd2ad0961f,0xe5b9002684c005b55851,0x506398d52d6a5a447d1a,0x4430ce2203c0051729c6,0xfc37eceadca1a287398,0x569062e06e005292a47,0x51b3feebb54b6a988d1b,0xa5690a300600057f4c4d,0x301b90d4318afa6a839b],#[0x65111028048005132cc5,0x31d40ae531eb024a7f98,0xc568fa2d064005753dcb,0x315410eab66bd27e859b,0xa6091a2c0520054d3a4a,0xf143eae0b26bd2928c1e,0xc6212c2b83e005333dc8,0xcfeba6d9b1ab2a78899e,0xc5f91a31064004eb23c4,0x71c3f0e4338b327e891c,0xe50900278620059b48cd,0x90ebe4ddb12ac2347597,0xe530ea2404c005794d4b,0xafd39cd7304aaa50789a,0xa581002f85c004d323c3,0x5113f2e4b18b326a869c,0x45010c2b8620054d3cca,0x8fdb86caac69da307918,0x2490c2210500051f29c5,0x2f0368bf2be9e2187317,0x5d91a2d070004fd2bc5,0xd15bf6e2b34bb29e899c,0x85e9042b0560055b464a,0x7193f6eb338bfa8e889e,0xe528fa248480056d47cd,0xb14be4e333cbf282821b,0x2548f82985a005453749,0x719420eab4ebaa72839a,0x65b1102f86c0057f4c4c,0xb07bb0de324b0a507d1b,0xc4c0f0258380053333c6,0x4eeb74ce2eaa12307898],#[0x65f1243585c004930dbf,0x7093c8d7af8ad2467e9b,0xc521062d05a0052737c8,0xf07be8ebb50b3a70821b,0x47715a360760051329c6,0x320c42fd392ca2d4a322,0x5e11e378800059b4c4f,0xf2943ef0356bc2889520,0xa6614c34072005b755cf,0x12341cef364baa8c949e,0x2619463506c005815350,0x71e424f7374c82ba9b20,0xe5691236074005b754ce,0x101bc4d3310a9a5a7e19,0xc5c91e31076005313447,0x90b3d6e4332b1272849c,0x6530da230420052932c7,0xefcb8ed3af6a926a829b,0xc5e91a2b0520051b2b43,0x71fc30f7b52bfaae929d,0x46212a2d050005673ecc,0x910beedf330b5a948f1e,0xc550f82e052004ff32c9,0xb0f3f6e3b34bd29c8b9a,0xe531042e8740055f40c9,0xefb368bcaaa9da427b9a,0xc460cc248440051928c5,0xaebb66bd2b496a0a7217,0x8500ea28854004db20c1,0xd113cedeb3aac24c7d1a,0x44c8c41c83c0058149ca,0x70a3ccdf2f4aea6a8499],#[0x86613232862005052ac6,0x924c3cf5b76c12b89ca0,0xc589162e056005bb5850,0x6f7baadbb12aaa627f19,0x84c8e42404c004f92743,0x90e3cadc314a72527b19,0x85b91e2d8740054f36c8,0xefc3bad6af0a32387e1a,0x46090a2a0500052734c4,0xb2240eef348ba2868e1e,0xa570f62e8620054744cb,0xaffbaed8b10a624c851b,0xe5c90c2c05c004e72a45,0xd1e41af6b8ac5a988c9d,0xa5c90a2704c0059147cb,0x313c04ee332bd27e851d,0xc630fa2b05e0056f41ca,0xb093c0e0334b4a8c9420,0x8589182e8460051d34c8,0x90dbd2e2334b2a7e881b,0x5e1142b86a005693cc9,0x527c14f3b72ba288921f,0x25711c32878005d15950,0x2fdb92d02d4a4a4a801a,0x558fa2c85e005373847,0xae1b4ec4acaa0a44809b,0xa4c0e626856004830abd,0xef0b6cc4ab699a267b98,0x520fc2c8520047d0fc0,0xaf3b6eca2dea0a3e809a,0x2438c61f044004d31940,0x2eab5ec4ac89fa186d16],#[0x4f0e423038004ab11be,0x4fc38ccbad0a32347618,0x65c11a2a844004f92645,0x7113e4e2b3eb828c8e1d,0x24b8d824840005473ac9,0x2e7b54c42b09b21a7498,0x4e8e82304c004770dbe,0x4ecb64c3ac2a1a447f9b,0xe4f0f22804a004991140,0xef1382c9ade9b22e7918,0xa559002f05e0049d1440,0xcf2b5cc62c09ea227c1a,0x8508de258460049b1b42,0x2da30eb228a91a1e7519,0x4f0fa2c05c00451003c,0x80421b09aa8972147198,0x950c8981a00a381c10c8,0x802b009042a0e0c0e430,0x1a41d11898024e108e0,0x20742228245782608282,0x3085a828410108060f07,0x20ba188701889864181,0x74300a0c230f8311288,0x19044091a0a80122142d,0x212180592e020006931,0x70041e1545d1c281d13c,0xb63894530ba28442e260,0x892c3d22371289e14949,0xb191ca616cb0c5c33219,0xa00d14b8ca2a3c521642,0x60f8478aee01a2bc4056,0x9e40cb6f304cab2e2754],#[0xf04642eab5b225e37151,0x9cb6c2364de319648e5a,0x267de315923771001d09,0xf00470ef823277f3018a,0x7c59991615ee94902207,0x65c2073c0472dbcc132e,0x8ac919b6f304cadb7982,0x18b6c23646dbcc132ef1,0x377f30106a2681cc62a9,0x19577aeb246dea452a,0x41fad508a5b710b2779d,0x91bbe4586a099cb6e216,0xa3f7d9315a2671cc62a,0xa9532ef18cb2474bc2e0,0xbe2bb80661cc786a355b,0x3171b42c9dfcc062899f,0xafc0cfce0123be1b0e53,0xafe3be4e01233db0e532,0x6065dbada5462cb9e132,0x1200ae39028ef2079f52,0x9ed9665333c81ad3ee60,0xd25af0464efe602c1cce,0xb3d48999fbfc28bdd848,0x81169a17981fb7d3488d,0x98f5e441b538456d3f01,0x8452f3bec0cb85a37665,0xcf08b04197860324fe10,0xa31c366b065ef6e89900,0xbac51925e9feb1091ab9,0xba64d719a1ac1072be8e,0xec8ca459f1424536820c,0xf15091beae0188f80ffc],#[0xf3a9e023a629c6459c35,0xf7a4614e7a3770d019c2,0x158be1b06533b6213c7e,0x47d37f5f446c702341a,0xb2338cfd5030481df510,0xd1520a1c165c66ae51c0,0x8c11f3fc058399a6feb2,0xbe6733a76f9919478aef,0x44c63f490cf95426aa42,0xb2f43a4233573e8193be,0x2e84839fff62a7ac1004,0x832e776f032af95d288d,0x2a8475e7ebc323171a27,0x694a328430db40cdbea2,0x1043c8680cdce9341a7b,0x284e8918fa3a030218c9,0x332c35820d2fa844dfae,0xfd6308ad5d87465cce18,0x8fb7fc4a91a7ebe09154,0x3f35c99a81a32fe79c50,0x23d5b2b732c5e302291e,0x4dc1a02d5c1937ae574a,0xfa04270b6fa84b8df850,0x658c6e4b5e546438cf0,0x1f3dbc21a824682e344f,0x3326a3c6a833afe20501,0xcb0cbea6a33870ae01b,0x5b458c9db09010a4c1ae,0x32ffc4e0920b08f140cc,0xf01194b87664656e0ac7,0x4e401a17ff1e582472e1,0xfc0ce3f8c9515ba7e10],#[0x604d3b79e60e0929310a,0xd3c3346494da4d087f1e,0x7424dbb64835f5c8ba11,0xc9388fd52012071ea2d5,0xc29f8899e58464ce9e08,0xc710e0c85ef52508fd18,0xfb9ea08422fb9321fd11,0x668dba42650e91c25033,0x2387c691880cf5f14094,0x2812073c68459af5e974,0xd62c291e69f308a2388f,0x7903dd78e88a677884cb,0x1e5a08e0670f96475466,0x38d644101a2bf2d120ca,0x4bc020d7e1218ae6e117,0xdb8332c6d1fd032db241,0x236fd63a81187e921e72,0xf365d07cd974185e74be,0x50069a2756f08b1d69b1,0x6d84739e74be0923333b,0x518b0473d11a7d75b059,0x9e1461c188e67148d3ff,0xabe3d6c446afff121049,0x15820d00cb08386cd60c,0xcedf2f13808cf9f5f08,0xbe234f9bc914bf62c520,0xa2b5ee46aae38324f839,0x6b286cc93d4fd1006094,0x808334e17cc22e9e2a11,0xac02cc9f6c86819b3d23,0xc186dd8d2ddfa03207c4,0x23bd04d255da70656e50],#[0x83a7383ad043aacd5ad1,0x7157e68478fa4f62a833,0x8b0ecaa4e7cc50f2920e,0xb7cc8ca9edc02724cebb,0x582152b3ff9b91a09a13,0x9388d35f03046dfcc627,0xb05953d720c54cebfe1,0x9bc23247fb3484067ae5,0x32dbeebdaca35627591b,0x1127ebdce508f1ed4c8,0x99eed41212fbf54265cf,0x93bac8d3f2bd0f914060,0x9cc24858ce9915c21a27,0xb996980cd4c9c50d85a4,0x960b554d19d332be8998,0xbbc9954d7f2114d461c1,0x3e2ac935e3988c23c7c1,0x90b1df49935d41092142,0x7347ce5e4e4ccd493984,0x8d193ac66cf018d2f526,0x2428436eccca3f066046,0xcabefe7518b049813d28,0x74fcbec030034737d2c0,0x367e054a3287d82bb806,0x899744475023e079ad03,0x51983d3112db19e3cbc8,0xb04547819cb465caf283,0x94bf928c93dfad5de47d,0x5a5907ea92450f8e901,0x9bf10d22ed37f5d423d6,0x3023774137874c8ca720,0x98c0fc1d122fa7738c28],#[0xd89085ed06318f88c246,0xf80203287fd86ec28c03,0x9f8ca1d166c8ea3a2ccd,0xd22f7e9cc6b5df0bd88e,0x80c08da76718fc8eaabc,0x11fb1cbac91af98d7fe,0x4c91fe82678c671aaef1,0xfe330490bf94b22965ae,0x39e4728471d45422c1cf,0xc758c3f66659c2f1508c,0xa00a4d38486a1b0d9e44,0xca01989aaae2120faf0b,0xd4108be15f228521becd,0x62f285191bd93c8cb2e8,0x98cbcb4c732e7197c246,0x465062fe64361d1071c8,0xd813323d38b0d0adf0b0,0x1d11bbc2b8360cd1f85b,0x2b846395fe104a1202f5,0x3b27ad919abd09e8021a,0xd41913b59d99613d4190,0x10a32e567c46bc670fb,0xaf05eaa0689335e22a7f,0x32fd303a32dbc79d84ed,0xec3a0cb587c13213d608,0x1e9e8e860901cbe26658,0x9efd40ca9e6c8c92d38c,0x8388f5c52320639680cb,0xed15c8cd49f50c93de73,0xca1bf690ccb71fa808cd,0x234edc25033093fa8a11,0x65f05422eb92d71a1637],#[0xcd5fc17880067438e744,0x669f5718c3123ba15bc0,0xbdd1886ba808b54e074c,0x16cec66d1c907b58af88,0xd08c3ebd8116bc1604ca,0x2f5f0227a526084cbd7b,0x3e62368e4834f8ca5633,0x44990e34615aaf90f127,0x5ad28cabe7ea81824477,0xe7e27920ce9d9b4e65ee,0x13336de609955579a454,0xcecd10cbcc6a33e77ab0,0xd36c9053de0ca2c7c448,0x79f8a3823c7f23a1b4d8,0xff44618c552289fcb115,0xf097a11e34a699967f14,0x81f5ac691dbe1608cb27,0xe9528a071fc7c236334,0x199a47456b8a91a7d155,0x960452f869232d7f12d2,0x479cfa81145555d6137e,0x9933be101c0cf17aae94,0xc455419a1f9c742576b4,0xd4822686cec52a39c187,0x68a126be9498833579f7,0x7585cd1d9a3920e7dbf8,0xd9183f2c20516f9c12d5,0xc11f657e20233981ed0c,0x9d98fbb6090466de3ed2,0x127be44c67ee4e918530,0xebd70209aa3409f62440,0xd05f9b0dd852dcd18]]
private def groupPage12 := limbs80 #[#[0xe98807037135e7f0d537,0xca3fcf1b2847a66820fc,0x3f12023b78231a7ed000,0xf5c08074684eed8322e3,0xcc27a69172f93f454708,0xf1c8b14eaa517e100e04,0xc0d0b23cc0461183c22a,0x508f5ff09cc9deb89641,0xdda84487ca480cca07c9,0x30279032fc45a20cc0e2,0xcc81b768083316a3ba65,0x3d4f52e2a457d5b1b673,0x88f3515ae9c906d1c907,0x8f5970464b446be6698,0xcca057bc4012447cf8dc,0x4be237633e648f1ca420,0xbf591b57feb6081227dc,0x58eb286cc9b13f1132f8,0x8cb9d9893ebcc04cdd5c,0x5965019fa11e1642c8ea,0xfd420d40cf6ed920f3cb,0x32c60984996293e8c89,0x5f62458e540f465ec790,0x3c6a3248a87f01a82675,0x429616e3996b98c99356,0x1ce93d6f1a84997e0238,0xa656f9cc733e09163923,0x32f74629981a846aa792,0x276625eb7ce88d9f95e8,0xac888e093826e6b40a33,0xf6b80908de46bccb97e7,0x4c7dac01810d59798265],#[0x3423e1c57bd08f4d0cb6,0xc168cbb4ef88469cc6bf,0x132cf8fd258caa1096d9,0x22a7a16598c64696dbcc,0xedecc49e8b06b2ec2f1e,0x342e04617b479eea0608,0xe845e2001a33c7a26030,0xf88005b89a39d910a123,0xf8a8482fa0c6b18bc8a5,0xecc75d29ee8901a2682a,0x31e6644b5f6286f8ccd0,0x8c8687bd6308c35f0542,0x73b312ebf007662a1287,0xcb0133927e8934fb2951,0xee52301e875f447af997,0x8942457982e653021bf9,0x81811e7eef942479a95f,0xcc69f0263297b3326ff0,0x61a066ae485ad033b65f,0xd4ca483d3cfb2951d3db,0x2e69c98cc915766e500c,0x4999d3509f399a394633,0x403201e875f4476f862f,0x5a4644fb161c32534079,0xf1bd08f1bdd427cf98b3,0x8ddfcf3264656035c9e,0x83824898fd3811a63e94,0x7ceede0652fe931cf75f,0xdef3d09c47af5dac9006,0xbeff408bbeb5e324c049,0x78c0ccbde31133fd8cc9,0xb7d391dbbe1548cc5fe2],#[0xcf9e031f78e1da03301f,0x940d277884b9e11968a2,0x5393237d88992b91a641,0xc150c8086c6ee1823340,0x5f6d5921bb7aeb0133ab,0x97f2a9046657a0907b1f,0xb9d2683dfa5910d87441,0xd7a5242abba085623b91,0xccb5c231cc78f0a211f5,0x98232c8f932847efe72d,0x7875130f1f5090892197,0xb2c42466e491f51e0196,0x71bd16cccdbf029515db,0xb95325b69a0f5d410921,0xe508fa2f43a91d12ab,0x545a70659ffea40230fe,0x62f84845f4a2277e80c7,0x2a3920b3fa4878a40687,0x36650f88aa8336f5ecba,0xc1d8194b63c128cb91a4,0x65f33460679ddd4229fb,0x4d4335153fe9e6a4033f,0xd09219a7fdb224bec428,0x7b499a001a62231644f4,0x1e06bac10ab9d6722c78,0x5eb8104d51a178767009,0x2cd055f8942499e5ac4f,0xe6e8ae2b1552aaad953,0x537e52238d21b32c3582,0x7f13ac8dcdfa9326f7e4,0x871f80d704ce5ed08c92,0xa4e0ea3c20c85e6212b2],#[0x39c65c28cdde85406580,0x3831c694d332f7e28193,0x3393d6083438e7446ae,0x989a141cf18468a71487,0x92de222aa0ce1e5fa807,0xc2218800d0239fda8c64,0xeb889199be474674cf9f,0x1603d6c7a2d7d4f02427,0x2847da7f0c52a40df5a1,0xbfc2f048334708f0f3ce,0x117fece111a30f0d8996,0x8908de1e1732cdadb00a,0x6ee4d0640bd47446c03d,0x8b2e7b78190bff42a406,0x88c5648edf768196b88e,0x67af593c196478a22ef,0xf129d067ac8495ca294a,0x2e6fa3703361f2a115b3,0xe12d640671fefc964630,0xd279419762bcac0324c7,0x4d38d919244e24485472,0xe0446159f232353ac608,0x98d4780485ebab514677,0xf99bf2802675b1f226ff,0x4df546c27f59888e7c88,0x978d452321dd5d08f15,0xa3b7d3819878f8a89849,0xfff1212513456bb50197,0xf44613c7dac468cf98eb,0x131ce1c57ad509287eef,0x20e7705233bf45242279,0xc3875c288026967f0124],#[0x36355f8388e3c25f1d11,0xc91b27239333d650d99,0x7e12d22819fba3137f40,0x77afd15647df18c2123e,0x65d3ccf131122be09999,0x9d932fe79c508edf0b04,0x27048fa6b9d48e89340d,0xb0133a7fdb1109b1a363,0xe4585919f96e283efaa0,0x21e5b0681f3e5a60488a,0x62f2bba0cee1d627ad48,0x9d339bc346776f032e76,0xad5232e7f80835133f71,0x40fa327070e4c865234f,0xadb8032307f1f08d8ce1,0x66197f0891cb20ca067,0xfa422d781783227d938a,0x9ab0ea8999a71ce220d7,0x80ca4eda1d089fcab581,0x33192243f3a011bb96de,0xe233078a5a8cb1e1b940,0x8b38e7110bda0c65e01d,0x8c81c20c70938293fc1c,0x7ccd15eb94c4b6346730,0x97c246757741227f4429,0x48ee40c401e63a245671,0x9196b8b616466d3f8c56,0xca5a574ccabd621f57c8,0xa984cebf94b22e7deccc,0xd04ce858d1ce7051fa2f,0xc0f221183d7d680198bf,0x7302678966b065577416],#[0xb377ca9394410d35f369,0x3b9197b006a11db13111,0x3477e418ea3d18c562,0x888e9eda528cb9fc8214,0xb251976fe634230f55f4,0xf3a6a80ca3f8c9514be5,0x97d5766223cf93fa1a11,0x41b302e116f1588b9d98,0xf1f2741a07eb88dd219a,0x9824140c86dde0ebe198,0x250faf42ac5485c5ffe6,0x90c2f9c1167e9ec5a18,0x31b570638fadac4cabf,0xa267cfa131807c2ac99e,0x658f4dd08a668cff0106,0x9d60834d7a40656e1b92,0x8c85dbb66654d3f50197,0xe9af28fbaf43423243c2,0x637c7446ccb0d7e6599a,0x10cbd0afe88c0719c118,0x7a4354b600a5e30e1710,0x118e758f0d17ba069196,0x7befa5914003cc7447ae,0x7fcc132ac7e3439e9893,0x22c7808f00cd19e03237,0x4982133c88c23361adfc,0x2149e819a62c5bea8fe9,0x8ce5f3c48c4a59af8116,0x943edf482266a66c907b,0xe271197af7a117235a41,0x8fcf79079f06a265d8f7,0x88e03bc2a0cc977f7184],#[0x9073a31c22c7b940329e,0x6f2f208628cf1c2307ac,0x1c76b7926660e7c8a266,0xb691953c30ce9955e824,0x26834c7a86066cf98b03,0xd2c0cae40ebc2a50cbcc,0x8f81d3e032df611f37,0xd9741d693b2328fe71bf,0x87fe201091e7bfda88bc,0x8d3ed358212ba431d519,0x5c422fa5113b68f28aac,0xdd4ac671c08fa4239355,0xf14df508edb7982654f6,0xa427ca09b83317d918e7,0x64593b8e236edeba6bc,0xccb064d2ba7392901fa4,0x78a792223672e21b0658,0x332c3618b257ae19c806,0x51dbef26358ce4404edf,0xb12a6c83ff0489a2a8f2,0x69cf3ab7a1231e758212,0x3e7fdbc8d04cf38c08a4,0x620d1c44b83cf65a082b,0x119765ff66c4706f9252,0xba0462fcbcc13297e56e,0xc09a2b8e0c6664483ff9,0xcb5cd18ed920a3fc0ccc,0xa33af6a214e121318608,0x60a1967cf018ebe68b0b,0x63d591f63e97c348f95a,0x327b691917e15148c3f8,0x8f2aefa102688a7d05a3],#[0x14e62cd45a467df3a065,0x1a53fa214b486685774,0xff7c66091cb9708cf18,0x1ecf2d627931c7f81824,0x3ed3aa480679affc5a81,0x96269a6c63fca3e3c448,0x342ce08324fe99194e7d,0x335689109cb3a78a8083,0xcf1e896c0b4672ef88a0,0x672f96c94652e9cf9944,0x9052fd8099639c69310,0x33c78c15b0669eff5a28,0xce9fa1e40664fb75c400,0x99b93bd5419a29a44360,0xf10e644eed83277aa779,0xaf81107fb8d09bd554a0,0xe9e10cb3fe630bd31217,0x80b784cc64893f018e03,0x7740d232df6e07d8511f,0x68ce9a0ca1f088d45034,0x609619d328ca9afc8026,0xa47ff20111874751c620,0x1bae1919ab86c104d409,0xc212819d3eda752281a3,0x6c679d201225a71834f6,0x63a13bf948c685613036,0xc12f6e3236de60996507,0x711f5658a945f835a20c,0x23425f39e1174eef28b1,0x34cf796c8990bf487649,0xcf688eefd1490985c5b0,0xa7e0ca011ddfbc83597f],#[0x43a3527849937afcd111,0xf86032cdfd651c8ea2b5,0xc5973f18759a64006a46,0x5d850a94aefa2327b175,0xc124befa800c003447ef,0x54cd1fd031aff72ff2f8,0x71e565a74120c384f8,0x31ff924003313b687421,0x4ffdd591975f22b4c09,0x54ca3cf8bde8471e6a11,0x8a579888abc54045a2f4,0x922bb5a4c9910fc0ca64,0x7454718802963f5b1d3c,0xcc8cf9240578672d1987,0x7be88fbfbe17b828d13e,0x7b9232f351104fdea6d4,0x940d3341e539415332e0,0x12fdeba8c3f3e438d90a,0xd38c187dea0c98e2c107,0x1167a49903a470940cf2,0xe06ca3e9bfaf28475774,0x8ee899a53eb41ca660bc,0xcb3ff6feb0d40929b6d8,0x32a7ea8c153397c0a08,0x2bfc1113a26c1652d61a,0x9cfedf1480cc9e1328cb,0xc6d4eac94befe7513824,0x70be1454cf18f2635e47,0x9163e45f4d1f3f9e0325,0x2ea9a07f510046e8513d,0xdfe6b6346d92627fad42,0x322673cc967f67509f7f],#[0xc47cf4f4840a9468aac7,0x820e30f00606690bf85e,0x4a06a270413bc4583170,0x5eb864a04cf5f84c2f02,0xe345c72d64e33d7b08b,0xd7e11143af063ae3775a,0xe73822f8c3196478324f,0x8d09ff031efcf5d03048,0x198c914708e3f256b42a,0x3281ad2b0e4c91e3056c,0xd192010bd34d634ca38b,0x7858eb2337c4a8c0cc9f,0x1fc69c013363f005da14,0x5da141c5ba0f13c360cb,0x8f7591e9eb81823cbf00,0x69f8a4a1601a56715d64,0x2730f8c0ca5d33df0333,0x64c15a89a277e2b10ba1,0x4f3e684586f4e434cddf,0x273529a93f0c3a152034,0x88a84fe12d624547fb11,0x5aa0b0134c35820e5798,0x9fc8440034079d98dbae,0xa0b3fc2264af2f2032d7,0xabc365806604bd41abb,0xfc606598fc9e091ed92,0x65c0ab31bba0b9b41069,0xd93e20a99a777542337f,0x80cdd8fae24ccd4e1560,0xd28292bff86ac8d10cf0,0x8b5ad123bc50d3a33f5b,0x601a63cabfc80ccb18bc],#[0x16b4d163e0672d23ac50,0xc981f050a83385fe861,0x651968bdb990c9127db4,0xa5d8b1e07e42b819c33a,0x7c23c57700d09f98f1cc,0x121be50192b38795328,0x2147f5e84e88f3dfeb45,0xf3bec0ca5e198f5e9498,0xe82df8f84a88fcda0832,0xb8dff31d7c205e8067f6,0x819829fa0065cf482e2c,0x31884048cfa131a60de2,0x73df1822e5de7aec475f,0xe49315c9321a0680ee8c,0xa7e0b22b13485ffad81e,0xcefbe1c2052abfa2216d,0x996be2a020ccb36c9e11,0x46a3247d3f21103a7e08,0x6be2dce324a22e3c326c,0x207d35eaf23c6065b26c,0xcd1f60464dff261e2b9,0xcc668e9ec18199306f14,0x6a83b00686e34b1d5b38,0x679e4eeb23536820f3f8,0xcc0469ff6c8856b69ace,0xe5e444cabe769608ebc3,0x2467c102899aff6a44d1,0xc08f99d780caabba988e,0xf2297e8c9a419a79ef5a,0x9100349ef8af00cb35ea,0xa54c934f2e7a4a14afb1,0x3879c78e14a9e8fc991],#[0x4d28d2eff2648cbea160,0xa876eebd9424ef5efd90,0x14b4c9ade32c6f7dcb10,0x679596084c81709e4fee,0xd240115da8e6292e6b9,0x38cf5cb5ed495bab1180,0x93b365c8a3eed2c95090,0x4c01184114dde6d2c950,0x1068c3f391e01485ffc5,0x96b033c635935794b094,0x6a847198cc60a6b0fc20,0xa3ccd1bbc1203eaf7326,0x8d3998dea89036e73d67,0x34421ae50d09d2bf78c0,0xcab234472e26d3d9a78e,0x7ffcd1628be2a5927867,0x2079d930c9f9d77ac129,0x8af05487019ebf5b3320,0x6eeefdca054bc7d0db04,0x101d825e5df349467494,0x2c188c079e30497bf113,0xa0a211a93cdfef0a7234,0x3d485ea2be0461af8caa,0x64fa732263c094bc1e2c,0x4b3000669b1d3e2bc661,0xa48d73b006788e23d73,0x42bcfd50919702bec646,0x21a33943f68c87f70289,0xcb47e04888202502785b,0xbf7302d6cc617614ec4,0x76649ff5af113149c13,0x661eefbed085ac13239],#[0x4ce6684237825d78b047,0xd7e3a046481f92aefc12,0x92454184a3dde312855b,0x99bea3e0555a77a5ef7,0x85f0f1147fe7183952d6,0x57ea94c8cd5f4a630333,0xb4ca23d4baeea090e034,0x8a31a07afe682d4758e7,0x1f3680fd2bd25f70a55,0xbdf03a32b6118972cc34,0x3d76505c049a969dd196,0xae04e8952e3b626148ce,0x8110755e00d046a4cde9,0xaf8606736f30cb288bf,0x31091659a214378c2043,0x609f066bfabe20ac961d,0x1b1a92d7e3138487b5a0,0x688e30c09967c6bfbda,0x4b55861e32637f989ec6,0x1b833b7084554611a467,0x879f28464030355603c4,0xd9f14fd22ca6c3a6d033,0xecc23a7f4884d9b3451f,0xc3ac18cd64eaa1525669,0x3e0432e7f287be68930,0x3aff5d5460c1604ca61c,0x1323fc7478999eaff6a9,0x1340069db8af000d822,0x424d2457ececc9b3dc44,0x992e4fa16b06c9d91785,0x4526e98a1c4cce5b5e1c,0x6a22153a29a3fff19290],#[0x46dbeb151027852c6d7d,0xf3a42fc740881226de96,0x84a2ebd261a332c44dd1,0x31506bb2289bba11312e,0x6889973f4a118010698b,0x29d4c5e46874e893dfd,0x91c196bc19e7d4f85db,0xf0b17eb2070470e49685,0xff4e441d2490eff00e30,0x5891f8a8925a81a5b655,0x756cd9977ce70f0238f,0x5241694d37ff98997015,0x332cdf95c3242a94de1e,0xdf6980da60d17fbc808c,0xdf6226482a7818431e95,0x664c11e70dba313d9498,0x2e496648a2fa57a461fc,0x99b7cf288b3fff9a4a68,0x46efd42f22f2b6d57f88,0x4196788709f0181d6805,0xdca509af910b8911e01f,0xe3943d08cc4c4a22e347,0x2671b3de50f43e250d5,0xf018478d14698fe5816,0xa0365df5a00ffbc24a4c,0x184cbf7e166560569fca,0x66985c598e7f31181148,0x3ffc38c2e156d4d16281,0xd4a2f98ad909390ef114,0x25348459735fa5014d40,0x2541607fb32a4b1c5033,0x9b0521c264fee2aaefc1],#[0x24c70a826244d03ff5c4,0x6fd7ea24033ce750e144,0xb99993885386d657c848,0xa5949bb3f60cba76ca4d,0x5cb89303825c9c271189,0xcdfd810909d29308334f,0xd83b4b1cd99e2cfe4943,0x4fd7fb01524813fa0f8b,0x6469833888cf163ce025,0x6e84943f31027424f75c,0x5a7fdd1c25a958f8f10d,0x13e49a6a16dbfc16909c,0xb9328ff8dec6c0403827,0xe8581f169b59b340742f,0x1e0e86b8212eec3e05f0,0xdf49081f0a67754034cd,0xc5e2b5fd219ecab494ac,0x53491ee571823ddfe064,0x23e7f33000cc32ebf55c,0x8af0aae2633099217ba4,0x4231b149c13c7e0ac8ab,0x42f499799f450a3788d7,0x1c31b71826cc0f8b81f9,0x4a8fa044fa1400356ae4,0x23855d44a9fcf381210b,0xdd6260cd4f480508bea6,0xb986b60d262fa57a46ee,0x9f733a88a3f131e0461e,0xfbda1b1a92d3f556c2c9,0x2336655e851984913fbc,0x422b4bbfe613186c2b2c,0x24370262bd267a8f54eb],#[0xde421b126bcf95b81a33,0x259c63e05094ccbe3505,0x812024afff5faaa2031,0xb5508d7f4381de14afd5,0x811571e0e8684542581e,0xf52d614f8bbd624e8fa,0xcdb9e9781287d4f803b7,0x180c254f9e057a4024a9,0x26b116f5905426a1be36,0x9384b09c2628be6202e9,0xd1067de2842ef65247c0,0xf758fc18a09d25f16bf3,0xd555423ed9ce786860d2,0xab4519e2a38c0b81a17e,0xd1f141c2f1aa84b4cff0,0x2b450d52627c0627bb04,0x4d24108e01d19da12bc2,0x9ebded852cbf2f504108,0x4254c0f9006428298b40,0xcfdfd4271334fd135e93,0x70ee4c21068eedd50260,0x27f40a892648297c4241,0x10973caf58dfb34254fe,0x640bf63ce913d5703d24,0xcfa7fda5a090420613c,0xbcb6c310581a5be131c8,0x437d34193be10409159e,0x78ad50d85257b89d6fa2,0x2d81997cffa8d48a121,0x1cb9b36d2e2693fd9cdc,0xc2525034013f9543f857,0x176012b125ef8198bff2]]
private def groupPage13 := limbs80 #[#[0x35cc6d5e3f88fbfffd43,0x77019a2bc8baaaa00ac,0x2126bb2463a84d19c79,0xd21f0a51a819d7e3d44e,0x276174e23f530928e948,0x22304b5f1f9383640553,0x696bb595e9207fe27a03,0x2a18a304dbff8463a185,0x9630ffc088f19247b88c,0xa9ab5302d0b13344c6e0,0xfce7b0472f2eb130666f,0xa334fc464026b0029ab7,0x386965c916cec99b4ad4,0x207e25236267bf9fbb00,0x425f6beea8199d17694,0xd83a51c2684f5cb3cada,0x1374f9cec343072640b1,0x70f45327e3b9c9d18456,0x9193860d14b1ff7ad4a1,0x9449851c90733dd21187,0x16be41eb0242ffcc257e,0x4a7c5fc324674d08cd9a,0xc649e9566ccb7c3925a1,0xfff50c5d804adff0408e,0x7f4319511cddc936146f,0x3e4af0848a9fc5cd2ca9,0x2af84a1d893188e91977,0xa1c95fa3efe25579624,0x98ce0899bade562121a3,0xe7e63f41b8552826c909,0x410226931276f084285,0x84a321a85714a8b9edb6],#[0x2664f841e5919c3e0a2b,0x44049b3366c270fda1a2,0x130671eefac1187cfb29,0x43c495fad81723f76ea8,0x9d49c6f4389257c7e682,0xa99876222561fea2001,0xa5e8af2d485e5a6278d6,0x453730fcc77ffaf111c2,0x235ba11d7ff102600c38,0xdf1328033de33f284e3e,0x9910957ffd6040a42c4f,0x69aaf887d4a49823f7a9,0x2834245b3b207e6b8b06,0x5a3f81b8ca92825f682e,0xc748951cfcbe1e20b42d,0xa6adba8739a53860d387,0x1446ead34a7fa1446eea,0xedccc7cf595e5d15a7fa,0xe2bdfc289447a1293e4c,0xb88f7e58409ecf7347c5,0xbfef51d0a804adfebcb8,0xca1ec9813b634f2c8cc,0xb52abdb18a0668e2ff8,0x1346e967c84611fbaf46,0x7535784480961e6a8939,0x8cbec2a4f847c09281a1,0x534ffcfa88ed22cbf2cf,0xa1818260c81bad408a9c,0x928f2e4e50a17e287c78,0xe58457909a07afb46c2d,0x4661661b1053c7142607,0xc8b0669ed4b91accf087],#[0x13eba26ac79b366682b7,0xd5f804130661f898f023,0xeafdac8c8526bee509cc,0x2fc0b6bf8f00431234,0x8dde0910dcff321fdcfa,0x48ba54fb899194212a66,0xb51c6b3dc34244f38885,0x390f04a0d784648bf9a0,0x2132fff6d5b475f4bf6,0x884b5f5def4601241e8a,0xe66f6fb9997fc75a03a0,0x41c4e858bfbec9314067,0x3099784fb2c4c7cb0fb7,0x3184c0be7f31d41490,0x315977f5f01c5c48bbcf,0x22069bc68cf78f992b9c,0x84b1acf3b22243699dfa,0x13ef44012462d7b59267,0x30508fc6450856006a5,0x80e0d4953ac79b812aa5,0x80af7a891034248ffede,0x29a87c17bd14fcfef10c,0x8fe2249a3a7f464a482d,0xe73d67a3ef189ecc024a,0x21375638400694e60636,0x60c93df8a88e8916f601,0x2a3cb2410735d722053a,0x88fc702633425ef7833d,0x88904b92d2b34f6611f7,0xd4cd0527985a0a425472,0x901f7c19ce3703c25285,0xc74945f2d12093a0d290],#[0x67d3524d09133c2ff6b6,0x1d7ee615423b78f0180b,0x71c1b7d148689e6d7ac1,0x497ff08c520c0bd3e80c,0x85506704d1fe67257112,0x169901f298913388c78b,0x34209459a77385e1a096,0x25cff475265ad2a5c7da,0x936ba3285f1b8323cea,0x18a143494c3f5ad01068,0xd44b2689e6d657a475c4,0xc9234a597f81da3f74d9,0x476375a588a624398a1f,0xc1306b71b16a1494cde3,0x1a510f049423f758ec06,0x226685f0960a8f3b4a1f,0x86d24b0ea4a15657d19b,0x80d03eb05248e3f8d99d,0x28a13034f01923e1d104,0x7e7bbc4308563dd09ad4,0x5f2481ffd7c219270096,0x790340a7ded1831fa199,0x8c36166650da1e03345f,0x987d998112e14b2ffe11,0xa850b03d7cc6ded83085,0xf2f1599b3c8464bdf0f0,0x99f798344251c6069a14,0x4a53f480cc2455b39f88,0x600425184c5d7de8482d,0x58269d7619862659bf1c,0x960104c19c46331ace0a,0x20ce87f868131a1826b7],#[0x1306646ae45d961bd614,0x7828e1fdcaab1662f2eb,0x3350943def0304755af4,0x77faf10b52704a5b0a34,0xd15d06eeeece1d159f0a,0xa2223574d31fc610820c,0x54126275c0eb4c92d3e9,0xa224556094b922755521,0x99df08c69e11298332fe,0x55854e29ca7274210270,0x13445e25560481bc076b,0xb7f992a7452f39742851,0x758191534740571d471b,0x4282eaed16dc68151d0a,0xcb5f32fd8c04d17ccc9c,0x293ef7332212cbe3e18a,0xb28819f2f0f94221919e,0x9eab81a52684d3fef09e,0x9ebdf8c26c5b0b6a1571,0x7109535d72277522dd91,0x75fd7bd08d9237810d7b,0x99c3da0f91332cd3d984,0xfa23e4126069a0af06e1,0xa0b6652fda2837150692,0x81a3417fb24a9381a1be,0x465a43901385ae1805b,0x2ccf8584f89913437f6d,0xbc2122038ce5973caa09,0xa6012ab826280ccb1f92,0xb31a472eff6e23cfd5e5,0xc5a55a2f403640439713,0x9d93034353349f333072],#[0x689ffe2f60e1895dfc86,0xb7680e0683afe05096f1,0x6eb8665af8409a5664c3,0x420cd3f759e6c6040965,0x424c6614bca4cf5f085,0xc2af1a2f94a4cde01af6,0x83ed254a1f1bc7a14252,0x30331ca561d154f5beb4,0xbe30ea80a11a93b9bbf9,0x1dc7623337f1a0c90ce2,0x1d12c47ee909529904d3,0x1c4fd60d263a460aecdb,0x706ba3689d0cd4240ce,0xf60bf5e65eaff5359987,0xe4ebd6421e04a823eb22,0x740ad0339bfcfd11dc8a,0x208f93fd1193cba464ad,0xa1c546b98c0c959fac23,0x551366cd53f83da92824,0xe86ab2c4ba7b132878e5,0xd8cd09b7fccb8c8b0ae3,0xc81bd713a956fad037b8,0x49a1317a88aa11e33e68,0xbd4f68c5029726b59c69,0x1564983a31e54ad884c0,0x567d31820510691c7c37,0xb9eec1327f3ce0d105a,0x24684fa25525933cc6d9,0xc71808868c26f7112c1b,0x6ddc4d34610c57a44fef,0x6b9220f049a3421c269f,0x646c54bd9cf08ab5e047],#[0x53355461f57c198efcb,0xbc420b11425c7f8b8144,0x91a37fce093034384b9f,0xf4060c48e66a8ff4b219,0x5e1f12adfeaa2c38482f,0x7b01073d4b9e85a41c6e,0x4a1eaec8b5a78284e673,0xfa62248ccb5e3943df34,0xfe5f10d8526c3926c286,0x7c4c359b7afb1821724c,0xbbe182427eaad85933e3,0x85b2ccf5cbe885113449,0x4608fb27518518256438,0x317fd136a54da264e79e,0xc28cc24ad9ac62919515,0xb04ddce6637e090bea6b,0x3da85414d12627c1734b,0x92f7ffd95d8082304d0f,0xa307c424affebb0061da,0xde89ab3397bc0c099a68,0xa83095be31ed31dc9340,0xe9fa45e785130a56f248,0xd478797928c2b15e2e0,0x9d8a0dc26375fa929005,0xf0aebe5294cccebc63d7,0x908f07f3a88b7fbc8a30,0xe8c89f9e59404cf3c6aa,0xcf5091a9bd416619c123,0x80d26a3f65ae182326f5,0x47bf2d64a9c07ea83226,0x49bd76c2415a2793e8c0,0x5af06715005e8627b293],#[0x7818252e2735023a4256,0x4a4fa25525933e89c7dc,0xeb41826cffe483595f2,0xd24cdcadd3706643df2c,0x24d57f93e608f20591d3,0x51f75446474e0bb6a536,0x618d4a0f944a1ff40046,0x4a22b632f60266dacd4c,0xb90ccb8ddc936140f7f,0x7a23a0218d4987c33f90,0x84adc7e6dfa5c910c93a,0xb917a1c240ffaeb4ba01,0xd66249a379ab9f704923,0x8887f168e960c137bfa6,0x99d4ff8112b187996026,0x7fe1c5060676fc65432,0x333d5808f5af94630534,0x408a19d377506b1c5093,0x2a7c09a0a304a1351f25,0xb2160c0344ddd6d631a1,0xe30495db42d6a744d1de,0xe126a1a09eeece35c079,0xcfe50ff3049235d7c246,0xc0fe2417fe5ea4800685,0xb7af29610a0c0d486363,0xc7c3cae2d29a23ada8b2,0x7a72819c6e7c7cd47824,0xb66e127831f92606786e,0x4d5393a10da712f2ff86,0xe2f1e8f51b2b1d11ab45,0xb5eb2b18484f90bc2899,0x531b578fe23e336b1082],#[0xd290ee4cddfd55443e09,0x2427d12a94e1346cf9ce,0x4deafd060019e79cf6d8,0xd4384d43f0684daaa17a,0x90fd0a237569a6aa8308,0x2fb3b42aafe00a485006,0x6624f4cca125b4368b9e,0x983d764498c447c9c1b0,0x62609c59975d60bd8970,0x801a02560f21c19ee7f8,0xa3afd5081a12134e904f,0x50af5e85c0a176575a9b,0xc78fec504e92a9372fca,0xe99bf033f6460f395320,0xa521834d0bef5a850548,0xf731bcd4206cba0a8ce7,0x1247ff4d4dc8f72d39c4,0x23a71e73a8ccbbf442a0,0x84e0925fd6928ff6873a,0x14293be403ca2a58ff07,0x12c30a5347da321e5c9f,0x7d7ac801a82d347ffe5e,0x8bf771e18505fb47320d,0x515f6d50336c78c603d4,0x370346adfffea18bb009,0x819d7c02a1e24078c926,0x66afe5575084980fdaad,0x55815066abfe61898361,0xde228c8bfcc772457b75,0xf261820254f5a8951b21,0xccd10a0652bafd4240f7,0x10e9c4cbfe613186c2ba],#[0x4b4f4840b80675f5393a,0x9f8cc548c3033cfb1491,0x9d20f5811a2a9a872267,0x61827cf88e200c12e80,0x936080974ddf1a41827,0x2034a7d12a92c99c7af,0x469e6b3b94a911fac934,0x8ebc3432dd09a07b6fa8,0xe6637e0933d4b22b69d9,0x66569a1473470b9217d4,0x684b8e10da907b3f43d0,0x3fc05a194d1263c1d4c6,0xf256cff7d0c108184cae,0x8c91c868cb3e7381701,0x3cdc2e71add825efcdc9,0x2671e21add091799b2e1,0x7c1ae320224cee1e30c2,0x669f149f7b95c425effd,0x2f60655fe18899801b61,0xb0597b85b9c9014690f8,0x60913f1f9a090f1269b5,0xa140c0b8423c24ccd4bc,0x12ce6e07d1942cbb397d,0x601040c9830cfade499e,0x590bd824987dc4a3ff60,0xaa6e001a731a368cbbf5,0x42fc8450c6d1546682e1,0x9431a27388e5875250aa,0xed54435258cedc9d773a,0x6965fd4419801a375feb,0xfe622684918a55b38f30,0x7e68479ab9a416e92a27],#[0x18ba587e201054cf39ac,0x33024e12f84b9f406a10,0x6289ec109656db36651e,0xdb242ee7e17c760913dc,0x933467c044165134c3c4,0xcf35450034a0ffea0160,0xa5c2eea0471edbea1187,0x53801a60fff09d0a1a84,0x33457c7396b25ce63c11,0x6b35f8d8521250396cc9,0xaef5609a3caa859194a9,0xd01c31af03467c330d73,0xb457ec80c959559a9a60,0x9c0f54301253fb2b8849,0x61a33ef038f3f1b8a254,0xae78189ec1825027e12,0x7158eb0609b7fbc8c617,0x9e511d57ec7158244587,0x2722679b83e86c240fa8,0x9ffa9980825c2995f969,0xff9b100333601d59bc67,0xd252fefa316a071424d0,0xc9f1823e858bfa514f6d,0xa5d532fce7c6076c2bbf,0xfab0022651a528f93308,0x73f3e2388030dd013d3,0x30935188c999bdc00921,0x2407e9366669f8d0d630,0xb891772d99c50afa1904,0xc400a201281b37fcbc36,0xc401a84a1ce612d1abf6,0xa49c2417895170675a3c],#[0xcc898ec0975b78232232,0x4d08665ebe558d2b01f,0x34e1f12ab023d6dd6192,0xa317c548d9ec81103a00,0xd282a12c75aa3b1471f2,0x7d2f3a10da744d5d6b38,0x2eba0d14f66d0bbe3519,0x14a3009e866bf72289e1,0xf3695a902685ff8ab20a,0xc6c9d2728f8d0ae28935,0x6192ffe0ea523963d980,0x78a26c244c2c751705b2,0x502b149480f84560cd01,0xfbb233b73fc0645df81,0x49247f4b40da44a985d0,0x9372c81b916cff8adc70,0x4c4c19c69fea1415f92a,0x1f6eafcd29db2930bcb4,0x1ad98f99ca2653e4ae21,0x220019d7ccea2297ee64,0x20a0d2c5fb0c199abeff,0x30709277f8322457f000,0x1dac494a328334edd780,0xe7428d96a7ff0eaa4067,0xb171296f24af08493f15,0x3339e5cf49429dff2f08,0x892bf3a08c048ccc23db,0x824c250870982bc00287,0xe29e8d2effdc1d450bff,0x60ade30863d217ef4387,0xedb04898d1163afd4ea2,0x791bd4bdee911d26cf39],#[0x6408674644d7d295006,0x2cce27f18035b8494d3c,0xa87b27a63069a9fe0efb,0xe8eb3e92254beda065dd,0x3afb03301a24d9ced440,0x256fe75fa0508189337f,0x181c261804c58c98a923,0xc19e7cbfdd6406a12d7f,0xcdbea03a0d49509f4885,0x19bbf0c5113357bd56c8,0x338f88d6e8478fe10a0,0x1f58840f3ad26e4428ff,0xe63b023170e5e4c933e8,0x1573f0ce849a633a2af,0x4ef00ffc50927e3f2f97,0x7841a068debe0a222d24,0x39582507ea95140cf9db,0x60c00602118284ff8554,0x49f5fb82512025efffe2,0x4ad9ea49c6011532ce92,0x742c3c93368f93b14b88,0xac2e50d095c90fbb2330,0x4c1fefbab9f904943fdf,0x88506958c1d189d6678,0xff170c802666aaf66ff0,0xf0c13819dbd96810e678,0x59a0332f81bff09c48ac,0xc0b9617f287f9824a4f5,0x15cd492028073fc204a5,0x1d35c2c6e84bd1f82a27,0x92153a29adfa26260ccb,0xa1303d0665699c6d7d6a],#[0x9381997a499e026293d7,0xdffc0fc560575f004c9b,0xfd8af231cdbac09540bc,0x692ce65d5dc5042e4a9a,0x323a324d602ede456346,0x1d62548a02014177c880,0xcc3ffd8e1064804c9f39,0x394462050969ef836328,0xe05b333357a916ee81a0,0x280d297d7cce40c0492f,0x1739a0809e0962b71a8f,0x3e533e09b5f2848a201a,0x95731bccc81e5630c58f,0x317cf8da11a7d1b41460,0x243e819c6699ae06860d,0x5427cf288c5776427a8c,0xc753890425dff32e30d8,0x9c798fccc0412e14d98c,0xc1d6ac3b1486c053d381,0x2a0019a0e8dd6a066714,0x42061313a76262ccedfd,0xda5d7863c0659feeb082,0x2956e6e835f9431ae0c1,0xd790ad27ccd3e22054dc,0x3796d9029e982c023a04,0x3ad042621ef031f8a24f,0x3ed1c0489399aa7b8c50,0x259dfd68997f1410b922,0x3510959c7e3f1c0dd518,0x7c0ca3e418c09c125974,0xe670304a8b7ca032b53b,0x8c2b1d76aa054d278f24],#[0xc2c99c7f3e2ccbeb24cf,0x58c0d9b4f0c89993f556,0x5d038340fdf9c662582a,0x3cb6c65f918c33310783,0x44d1bcdd4724d8c0813a,0xfd80069226611f6d526c,0x7a8903fe06e26248b3f7,0xe22591a3cb86c32cc183,0xd1c99e5d9b3cb50d866d,0x40e7382464f4c86300ce,0xf86614db8120ccbe2761,0xd4313e581d680534f3e0,0xf70943e0674b50230f14,0x4fa17627853579fb064c,0xffd78ce14509258c7bd,0x53066c179cc81a183027,0x1ca142fec4a00d25ed81,0x51abba35706551cc70b9,0x84b778f996bf05800126,0xdd1ab83327e1e9856806,0x28e014227e020892b397,0xcc478182427f6e113334,0x4794069abf6a326048df,0x91f7c4180ad49dcc1b05,0xb268ac3af06403dcff10,0xe63586864a4f4fd349b0,0xe7472a2aa00a60ffbeec,0x88fbf57e4a9498e0268f,0xe784d099b62220f8113a,0x44c8c9f900328ff26279,0x833dfd794461685c5ff0,0xa1d6c47f86123bc53642],#[0x8f0b833609578607c942,0x7ef40c1243208f832aff,0x799d7ff5f002365a50f1,0x99ccd0846f04b2853948,0xf022bf23e178b0612766,0xe9724d9b8131929c4b5a,0xdc66a0ea24aff9f48a92,0x4312f620e3012ec26b5f,0xa32906a07f9c6e06a129,0x6610763591e081f1a4c,0xe7e93e598bc8b3be2650,0x732f899814a7086a940c,0x7daa62341a0b5f880c06,0xee1d60c0cc9e3a113336,0x27e92350c8f9d270634a,0x3e811d7f8cd916381868,0x61420cf3fd8a8e88f322,0x8118cbcbcfdab702725d,0x20268516fd08f7fe52fd,0xa79912334fcfaf9090d1,0xdf7fac0092accacd8505,0x3d0420fcc40990126739,0x4f838323ce01ae8a918e,0xf8b8d984c49b9a4b3994,0x965c559db846644cc315,0xed234faa8ce20249521,0x46de0435ef109323e2f6,0xfc0e300212ad337f6648,0x23201d0fe40ffeb2197c,0x5333e7e17792617c69c,0x63804a2a62f668a92325,0xdc342424bf8d099747e9]]
private def groupPage14 := limbs80 #[#[0xa76f2a4f44e52919c6b3,0xf3e26b3c9531926d9cc0,0x49d23287179614b22d23,0x8553e7fb2ee018614dae,0xaa3ed23dd19aff961d92,0x6be9009598e94fb02989,0xb3347c4a460c0d0bc4fa,0xa092e9c54f021736494b,0x47393a146712a793c022,0x60fe27aa1238619849ca,0xff86a40241f8eb2f81d1,0xc349e24e7ce189860ce3,0xc15914ff67748ae55a17,0x4e84200cd3603514d957,0xac7624d79711c0cc3d62,0x1517d02a05583468e631,0x914e2a7810b7fccb8c36,0x69d7d88665aa298c7b1e,0x2f60f88832d47e8c67e7,0xb50d8668fe6f945e6213,0x933f1e0c0150061333c,0x8b4511e426bdfc29a23d,0x2a7d4f80226d4ea6476c,0x340fac426ffe68310b35,0x7d8c9280704d37759b0a,0xa700695f6c5478244ffc,0x591abe7ac8899ab15e4a,0x956dfe16909c59a607f,0x7b65d28099d6ff9a0976,0x2818260673e019c3a16b,0x3de07b8c512c7e3c9e6d,0x981a98497bfe4c9232f4],#[0xf7c9391e2fa57a461cf4,0x4143180692c8d9285587,0x8dea240693c8d799d3f2,0x1a61407ea8322681e66,0xbff038606499ee231610,0x34a661500dafde4a4b9e,0x702bbfbe6260381616a2,0x990121bcecc61ffe1c60,0xd1e6335718684b1f3c7c,0xe186d14217cfed021902,0x6f8409907d7b36152452,0xc609b6fdb12135f6c084,0xf920020a0d9ba307451b,0x292a0bb0d507268ae038,0x98545b69464d8abe21f5,0x733a9fa40661223f1139,0x10831f4c772393719c1,0x50833eaf91085a934939,0x912725894d2116586f58,0x11a25cf36b2bd23dfd08,0xf3c9b0405b4963f09917,0xec2ffe82490f77c40e0c,0x6f366cce5f0345c19808,0xc96d98675e50e00921db,0x24c8f1f84eb750951ca8,0x73e320a00340fc601820,0x24cfcfc0e30110d5a6a,0xecfb8489199563f8bd72,0xe6684cc047b0572a93a4,0x5fa4be6c18250e34421a,0xcfeb118a60128bc99027,0x6124b9f0464ae49d232],#[0x9abfaa8ac3c1257e10c2,0x3537254fff04984154d8,0x2e6339e712084a9e79a5,0x464d20cf3cfbac0c8d01,0x84fc412251a00934f8e5,0x530eca4ff38dc0e84ca1,0x38853502edd2a2e34d52,0x25a04cf14c407a39faf1,0xa24ad83f08a8c12ebf81,0x60128a3f4635fcc4c6b8,0x762af910a93bfffd4317,0xa79120339782636631a0,0xfb34f0ea4638b134227d,0x20d7adc19ef19f4a142f,0xff81c61b0ac727d1c468,0xfbe4a49cf4edb4b899cb,0xe9891a1557c408cb63c0,0x3aff8d52148552a38e01,0x534a5c1b9b30762312b3,0x3e25d646653e0089b1ea,0x29960fce301841410538,0x499c7c9cf823dfdf3118,0xc72806ad661e07e36148,0x51190a694e3e3d11133,0x1b08e39b8f829424aa4f,0x920eff78a1c3a15ce773,0x648263d273d6cbc65975,0xfc820465fb98ec11d7bc,0x7868772515a41c3b334f,0x2025cc54c4c6e095a7ce,0xbfae4bcd248afc6aa33a,0x938618278161f7a06619],#[0x86b2958ccd4236e3d268,0x30143ba10c2f725a6f97,0xfd2a00199771d1fe9049,0x7d0301997e4e6248892d,0x6c942a1f520c66254aee,0x8823034d2e5778242164,0x2e250b770f92942b91f1,0x90b5092bc4668ae70338,0x3101a46312b142401eb1,0xfe00a4184c0d51cb00e1,0xbd007038258698604cbd,0x70b647bdfe5130ccaa6a,0xf04b99f1b35a5c094bf4,0x7952d60661e3786b1f39,0x2d76b2bd2467a5b0832e,0x88e149822dfac2822931,0x8a60fce80c40485efeda,0x9f0d7fa88a38f4ac4500,0x29101e201d019ef5c9d4,0xd9f8a1de324855eec714,0xac03528e3f0128220a4,0xa4c253794c1913488f2a,0xe27a729a0c9a3ffe0898,0x38ac75805342f8788a3d,0x50104d589297a0665861,0x84e231352b24d2fd6c32,0x5ff642e48ebd47ac08d3,0x50a438fc10197b987e64,0x468af2d48daaa5de66c2,0xf2a254038264e6637aa2,0x2404693a210f0c8cdbf8,0x5e94b12007a6cae6b823],#[0xf8409a56683f9d44518f,0x2b9ee14c03f03207049a,0x53b32c057e123344384e,0xa1489b8907a14a84c2e4,0x3652b8f8ca12563f9b5d,0x252f9e07788e1f6f1403,0x11776629b3ceac5fb005,0x86300d21f319549d0035,0x7e9eea80324035a7e482,0x7c01092bfafb8b0a924c,0xcff297f815e1e16ef00c,0x3f7740706a4a3fe946c9,0x11bc11e7f17b01046098,0x71a1834b0872fdcca3f3,0x3033de7600d9caa0a8ce,0x99b57dc44ac0496f8c42,0x41752667e982347f0469,0x14fa236b0b006a9e310b,0x4ee3c99d380f846644d1,0xf15a58084a4aebe6448e,0xb22a0d2ab81d52a38f9f,0x95379cf31920255633ca,0x1267b4b91778bbc71160,0x7e4abbf04923fe00f410,0x3fbc2df650a80abed194,0x78978e5a3cf278045149,0x287a1f44a1ebf1c2d91d,0x6952ca1b684a1a332dc7,0x527823eb22a6856a7653,0x8262febd9d0609272f66,0x6318980d03ffc5ea8041,0x671831495255677a717d],#[0x2f60bc62e434757a8c82,0x615d1f9338746559d602,0x2349a3c1d0d6e84c9d64,0xb4e7c1548284d3167ae6,0x7022c494bc335c4f4484,0xc34899ba735314a5ce29,0x784708d3fb4655ff669e,0x64ce1f8d3112467cbc24,0x13b7aefae41993e89549,0x7fd53d4c46e24bbd7dca,0x22844c6269e876a6419a,0xcf826cc462fde2c492ff,0xcf4c752495e23075cf94,0x6b35ee25266f82b322fb,0x82025f726832179377b,0xd61d48c0220d23c7e062,0x98f52a79d74b40d23526,0x88ec4f94cf8272e1f366,0xcbffc49841409b44e98d,0x975fac3aa694bd7aed08,0x68b95546ce95659fc8e3,0xc5974a1f8f36aef4a252,0xac46cf2a5ac0cda47f01,0x84d1d7088118314c0877,0xc8ff9003600134a8d2f5,0xa0454e29d731bce840f2,0x4ea4b00f548d03780ed6,0x9d59c69160668c717068,0x7092bc46618ff2915e0,0x80da60d2dfd131c9c203,0x4b6fbe0c0590cd3d9743,0x7198c1a98a4f6b6d6678],#[0x21f8e39e8c0495fbd0f4,0x8f9be42671ebf1b0a424,0x88494cefe9b5989268af,0x1388c0eb4c9367ef1114,0x43c1347fa704e2a24ce,0x9eb82404366dfd7c1a88,0x89c1ba80925d69e0a139,0x7f801e09067e0efa326f,0xa8490b1e0e9650904275,0xcd35c48fce0494bf7b02,0xc52704dddb3e4f4c64a4,0x2445fb93ac11c46b55c6,0x552a7ce702e1a392d67d,0x8a20702d4cd3ffc5a428,0x8c8878fc20b10404c9ee,0x1931f141440069c1fe00,0x3a646699c56a9c518264,0x812278f2fc7b3824b794,0xdf71f6368884a9ff60c8,0x2b8468ad667d18d51847,0xc90096b1e2f9c340c13,0xfbf81123874256fffc5b,0xe7694860d37abfd5cccc,0x11906adf753c7c49dd9c,0x8cff032f7f7001b2d70e,0x94a1d0b13e8954964ced,0x58b897d0f0a4db314ffc,0x43a4d4f0cd19278f9784,0x973e727446dc31bf0d6c,0xf788298b02f71d0eb410,0x9b09e62a6855d512cfce,0x90a2b7c6a04667532ccd],#[0x3a39e3e4ac4813b4b070,0xf0c8b862b3e8a317c109,0x330942f925463a326662,0xb086a74add0f2d04248f,0x11f7debc8a3424cfc99e,0x858c32dbcc8cf17b047,0x625a7a290c9d9c9aa1a6,0x8f8d4404e126085f0d27,0xccd1e01d64662f798232,0x947c99865754c687d560,0x510caf72fe761ad1c97a,0x46422fafd4a02683f320,0x8899e79812200935e7a,0xd0841a02f5461183e85e,0x691a92f13eb0470e7d0e,0x79f2513c4961d31085e3,0x21aa24153096d286711c,0xd9499bd75400484a5e3f,0x39b81f8742b9384e2313,0x59800d5b4b5080c934bb,0xc73f85b9978496c3f900,0x9338be60126bd5368a19,0x9237fa5eb4309414834f,0x195703d0a1a38f131e15,0x7e7032d5de5116b02fc4,0xccf5b7a266459ef26395,0xc19fea149fc93dd2a0d1,0x6901260fad41030c18a6,0xb3cd903e21a295303fef,0x970f2e4c933f7f4dacc8,0xfb9983103d492f3060b2,0xa96384022a66f75bc588],#[0x360ed9b6bc25138489fe,0x668d3f81123ee8c79fac,0xb9ceba05b2487f0e0880,0xb22bac22ebcc68c1484,0xe267a10915c39a208334,0xa97183b2a4aaccf09d3e,0x87197452de64b90b2e41,0xa415cd017aa308d7ff,0xb0118f949f2b23f0b33e,0x284c1945fc5278953c6a,0x29e506d3067c04c5278e,0x64a4d1351f255615bd32,0x51de909d1976cc567868,0x81a03c70a9998dfe0762,0x233f570b232e7f1258d3,0x5fd692b7f44c69e11ca5,0xa86340498d62f72d890a,0x47d2d700ab223a4eaf22,0x3d62349b0ce7028e8d36,0x651cf0d8829ebd09bb75,0x8f08fc99c3a3297f45da,0xcbabc4cdc1fb4649b598,0x4a848f5a63d2ea5234d7,0xa917ac480397d4232fc5,0xe0604cbc5804ea636883,0x1591e7ffc4971010a971,0x4b5febef4408812948fc,0xedccc80681ce09303438,0x4233cebfdba10bb44be4,0x4647e0fd4248cd5f62b7,0x6616ed2fcaf08481f4c6,0xcfd00fba8331f7f4209c],#[0x3f198c100d3dfdb0d444,0x89ffc2aa900830102864,0xd307f8eb7b4473f6cfc0,0x5248d49417deb5420a91,0x640ef702285629a35fdf,0xf083303417a694d8919c,0x486788506d16fa3267d8,0x35cd784006983ccd1bd4,0x81cd83e79aa282d4a19,0xdfd9db5e48af20f46025,0xa00df66649356eb80499,0x306cc30cca3cf90a15e0,0x24207eb30d04cd09f096,0x440684a9d1aaa91f5ca0,0x6975fc32b19100d2bec6,0x338446259ab696a10192,0x5012c2ff6e8465a52e22,0xe1a0488184d5319d8d01,0x1ac9f563d93ced9497df,0x24e0264e01a9ac907f98,0x4d3fc012406858ce90c6,0xe144242ee3217f8b04a,0x953e3ff988689012e79d,0x71fe3950091345522f8a,0x3fd2140033ae2714211e,0x10e802519fec38c2d0b0,0x4e7845acfcec419b7c1e,0xabc84d2c1f14d90a0d13,0x4804a5e067d246ae9e52,0x9760663ff448dffec761,0x5926927779e44dce9d11,0x90359e76729b92e6388],#[0x4199586b0424df3035cf,0x36419e21a52165cfc4f2,0x524a59e5cdc94290cadc,0x4a6cf2f64919d6ab1aa7,0x24a96df336d6a727139c,0x602681f8fc700732084b,0xa657e4802a91a2bf94ce,0xd23314d9b7c880228742,0x645c64261eef12840aeb,0x52704c9e90968db38d2d,0x8a5d614cd194631f9e44,0x21f94a70246f1530a220,0x4272f5a6392666ca1b32,0x9a12bbc6b185067b3338,0xf2e324262469dfcc887d,0xe8e4cc826713637f8921,0x2020ea275f87ee880f2b,0x3643e646c4cebfd67334,0x4ce18e35404ce063e842,0x7a4c250870969faaa712,0xd8124687ba086b99a137,0xcc26bf612c24289f1c8f,0xb47f40df614aafc04340,0x35ccd098bd831c86e096,0xa4e2f6c0a98336e87ba1,0x9c7aec8829735c119411,0x8967170920ebf17cf909,0x48cf968b8dcc341735d1,0xd1a5759d4455fbe7b220,0xc07975450d15c34caac0,0xd1df08c831f7f1494482,0x178005085a6e65f8c04c],#[0x85a047c8685ad033af8c,0x2900d204ff231d11d7e3,0x193328f613ea848dfe3c,0xaf927f2457bfd840a3bd,0x8a29344f578d8d490393,0x4a0e98f4b1b48d35a169,0x5e2b86d217e12884a3cf,0xdc26b6118f521986955,0xd81e61092f7fd624e84a,0x30265af2ee030661f53f,0x870b2f7ad026030688f0,0x449ae38348d56c0d29c8,0xf4003a3825d60bb0d564,0xc83b72666c746e31987a,0xa0254c46a79d12084c0a,0xc452aace0a5cf3eeb1d1,0xaf8092be069aaac7328c,0xf64151d0a7a62c8a9c5f,0x6f57aaa4a457827c35b4,0x3cef26047acb98d459a4,0x446ae0534ed784a27090,0x685e17dff46490497df2,0x731120345efefebcc4a1,0xe0b08cd287257c921bff,0xfffa153410c0c304facb,0xecb3f1f393a3602b09a3,0xabe8ca3287a23075602,0xd1985377f81919702c8c,0xd8d63e24b46d8ab29be9,0xc47dff52a0542494316b,0xe09859f20a1669d8039,0x9919a7d99966abd0078],#[0xd6909815cf3f3c931a06,0x7a1303387a0d3199aff7,0x95257f3e2021e5129b9d,0x34d477c340cd3f11f828,0x1f5a342674e1d0bc10c8,0x7f2bb0924af9350f91da,0x47124647ae97cc493b9e,0xfe8873e0c1da60c6b830,0x3f48c0812d7c250f11c2,0x232e05a797b8e138e2b,0x13070e05c49dc4bb9fe1,0xacac61237ffe2f60208c,0x84661b0ac90ed92126d7,0x7a7cb80808a2021b6cff,0xfe47944e86639f60424e,0x9463a1fc21e1ed64332b,0x9329c554a5fa5cd44f28,0xf9167af1e67b2204a5f1,0x498acc767ba0aa6e9ad7,0xbe05c2fc472f6c0a9833,0xc48effcc08cb72d39c4e,0x28686d97832af81bff09,0xb06965f41c065bb96cce,0xa6f024cc8b38ce1c0f38,0x1040813466afbf16684,0xffd731640724b9ffc6c6,0x408fa49163aa06452b3a,0xefc130019ca5c33413bb,0x6b5ac9d149bce851b29a,0xddd6833e52238532d9e5,0x54a0c1e8c1f4ac0658d7,0x745d5ff048468e1da366],#[0xf0a6fad1d63521144639,0x57b1c848cf1a42d066c3,0xff51630347eafa2649eb,0x376b32ca0cc55c209b2a,0x23135e39b8480ca3d423,0x2d49b4b20e5f8e8f1c49,0x734443f82c8330c56f9a,0x32911c2996ce0d8754bd,0xa434875ccd2b8537c612,0xa752118db5dc4275b6b1,0xd6abd849d8cfc7b423cf,0xde62ccdc4df15566887a,0x9059a4e7c2b9052b3f4b,0x46da59756f43459e7e30,0xc5359823e4c7a8468ce,0x823c841a1718c07a347d,0xabcc5be49c85bc19113c,0x5348ca66b2862252d523,0x8eec9b74e30a3cd2e147,0x5051d4d1d6af63908f49,0x58e988667884ad97419f,0xd900b4e1fb1def786921,0x6ab377d170019abc803c,0xf781996d78e0f46486d9,0x4f5712b69e936964ce07,0x15672e725945501a7299,0x5479467e860b64ef1061,0x1c959c3bca099259c238,0xabd1482e3982d942dcd2,0x39221b3f170226895ad6,0x5068e4f2b419748a59ff,0x7bd8a70a283477b14e14],#[0x79896b49c3f63bfbda12,0x1c1c8491c437bd1a7f41,0xa1d9661893c0d495fc03,0xc25650bf57122169885a,0x23e4b8b3afd7ba007bd,0x696692b9f35e85781243,0x667ca169961d9974463d,0xc169770e789a0ad911e3,0xde35a88f0a476a93ca0c,0xf498d0670c647471d669,0x98ec4b427bf6329cce51,0x2e184d8eebaed0915e21,0xe5da0cb5d50cbe467822,0xd7fb0a3e7b3046416708,0x5275ccc19f63566ce378,0xe46da594350fc644cd5b,0x3cad06599d1de9e034ac,0xe5c42b9b284b587019b9,0x32c11170c209f17e7c08,0x255956b1a1b847afe360,0x4d167ef363bb125a2ba8,0x1d91a078e299c9ade8ae,0x963fccdc32c061942566,0xcdd2cd95f4832278bdb9,0x11751cb4d12a52b3f442,0x800d948328aa6ace3e17,0x432a9685ef58e52122a1,0x28c2cf9e6e5c066ca479,0x1a0ccc5c3d20b662f498,0xf01a447ea97ab99e3e93,0x43c420632fe0d97703d9,0x9428c0d0c58c003d3158],#[0xeca9ceb85010b441117c,0x3d7328b2bad8a1535682,0x7c15019aa1629696604e,0x74a024e914a3e3ee496a,0x9256673bcec709c78cfa,0xe90b942d32c3b356a1d,0x1887a416ceb9c844e719,0xbc5eafe248d53c2d08ed,0x1ad79491d3021e61165c,0xb86132810f24b0ed1148,0xdd5617a66913b8112088,0x29568b9c4b395733f665,0xbf400e5adc2541117c94,0x993ce0b64084708160ce,0x8f1a032a9c21f7e42301,0xb3f38c8748508fe22c8d,0xb13178f3348ca17c92c3,0x662ad17389679f0f908a,0xd6b563000f494fa42610,0xb5e9bcd06653e49bfcd1,0xae651f4f5211939ea6cc,0x75a1997d0f106a3f7953,0xf505e658d3059359abf3,0x77]]
def g63D8 := groupedPages #[groupPage8,groupPage9,groupPage10,groupPage11,groupPage12,groupPage13,groupPage14]
private def groupPage15 := limbs80 #[#[0x10100401c1e05804,0x400e00007030060000a,0x40f004070102a00002,0x3005010030500200c0a,0x240001c2f0600501011,0x440d044020080000400,0x185603401000020000c,0x24270000b0000801000,0x3405000400480001001,0x100e000040800a00008,0x4010582a0500003000,0x50130000102c0000834,0x10040080b0001700001,0x106700c0e0100701400,0x101c04000000a000,0x6038000040204809,0x3c0000c340000202411,0x209c050101a,0x1401054040500700002,0x53020020180300400,0x8050041f0340600007,0x40e000010000201806,0x807000110040000000,0x18000001000c0000028,0x423004030000200009,0x1806000130000800c1e,0x45805017004000ac18,0x2c000600e0040b00002,0x70000341002c0000001,0x440406003014020e000,0x380001000000190cc23,0xc23004000180007005],#[0x8020080202c2d00800,0x13c2c0080701c070001f,0x201b038000100503412,0x20080006c0600000,0x1c000080b0e80204c0d,0x140600c020600002c01,0x4c0110c1b0080000402,0x805010010001e0080a,0x240e000000080f00014,0x803000050040000001,0x2406050060001602801,0x908c01c420000000000,0x3c0404c0008c0a03c04,0xe44200c000140103c01,0x140a000450cc0200414,0x38120184b0f81514011,0x5800010060480104804,0xc00000030300c01402,0xc0702006020200040d,0x44360040400c0d,0x800008030080300401,0xc02008130041401000,0x5403000000d80b00012,0x413018020000b00458,0xd4000540006c040540e,0xc020000e000070440f,0x2000100640c00001,0x140001c140506d00400,0x806004000040a00803,0x2c0a0b4070000001843,0x2404004070180800c00,0x10fc000200200817],#[0x1800038010704200009,0x806000170001f0043a,0x806008060a80000011,0x80701c3a0042006012,0x3866000200342b1b000,0x2900200c0e0341300405,0x100f41d0080000c18,0x4c1900c090c80200422,0x3c1e020010100a02000,0x540b01808030010a030,0x7835018130000000c03,0x30130000a40601813,0x40805c070483500428,0x48050100c0000200801,0x14c570300f00c0004802,0x3800000150042002400,0x5c0d0080c0980003402,0x140a06c000347906c00,0x28220180b05c130e402,0x580f0340d0000a08426,0x3c25004000002e0240b,0x401e00c1106c0402008,0xc0090b40202c1f00821,0x7433118010081200004,0xa014000020500a00093,0x180f0080b0040e00c21,0x580604c180880f13c02,0xc300040023c1002c23,0x411034040283807007,0x880000405060000240e,0x140f0305f0842c0083d,0x18030a8000080416c07],#[0x1d02d108072245d03c75,0x1800008030400002027,0x340c050000d81006000,0xe82c014030980000828,0x240504c040002b01435,0xc40a0c8140f00303802,0x35004070880200404,0x3400078000040504003,0x3e0980c000150f02d,0x1c0a12c050440c09408,0x1dc0e030550001600c3b,0x181311468000000080b,0x4035090000700700c00,0x2c0e00432024081280d,0x808020050100001c39,0x281300004000060a406,0x5855008080180002c1c,0x6011030000a024008da,0x4470900f02c001602d,0x40c0503b0080a0480d,0x440000432000200103d,0x12c02000c5008fe00809,0x400b1cc160b8001ec3b,0x80042317c1001c15,0x3800058ca000030a402,0xc0e018190782305008,0x30190040a0680002800,0xc03050020389b01800,0x5c0e20c535851201004,0xc248fa4dc160081a,0x780e01c000005301404,0x50a44e80b0fc1d02421],#[0xac000cc14054000941b,0x180c014a41d4010d233,0x8010842b0184902804,0x7df30941e008762ac1a,0x8a80140600c0900421,0x4303e024000000226c02,0x283e08c060900803c44,0x11c00000050000900004,0x302c000080400006,0x50070a01f000210a400,0x8c1014250003100419,0x235014010c513c0f,0x54370d44e130240005b,0x30001280a0100818839,0x21cdd020030080002c02,0x8c8070bc1e014450c022,0x40401c480a92e2b400,0x14550000b01c330c815,0x13030000160705f00005,0x2802c140400200802,0x104020384114c001bc36,0x13c073b82840c0a00c01,0x4000006e0e05a00006,0x3b08d410d400d0200055,0xcc45044010049401008,0xa0020341c0180200ce3,0x281503cc1000fe00c02,0x54a2020001f40800423,0xa8080443202c1409478,0x401328002083e2a40e,0x580217c060c05521800,0x4080300806c160280f],#[0x1d09d000440801006402,0xd620210e202022000221,0x18855b01bc0015fd8a1,0xb93d342a404048180000,0x100018cd5b81d400741,0xaed343cb00089014400,0x44000000499115bc1ec0,0x20000ba57e2c005a8000,0x5887c1000801019555c0,0x15c421800ea4a3383d53,0xd6d88278288000002199,0x19cd5d024400d267d07,0xb63b4f4249c4b0024004,0x120009a115d827000cb5,0xc88050bd333aaf40806,0x202800001a595e42980,0x2cc015e127f7fc1e5808,0x2de8d400048041a815f0,0x95f42e801fdfd2172820,0xeda3145d1200100101ad,0x1b2560031001c5ce3a2,0xa2c0ee015d1710004010,0x80001b6960833c021fe,0x20dfb7893f204876c200,0x8002008009bb16103640,0x38c021d47f5b762b8024,0x2018c800022021c01618,0x561c3ac02874ddc71703,0x5c804a78a000000021c5,0x21c9961c3d40377f9586,0xe7059c4818fa60000010,0x100021ce96203f8037b7],#[0x37436733c0b808cc0c20,0x400500001d396284200,0x44803f7fafccf8801033,0x4e509800041009d7962c,0x9630460041a7b1af6658,0x6e50cc789000800001dd,0x11e2563c488041af3387,0xd9836808267884002004,0x881e716404b8043f7,0x49cabcd53231432acc04,0xec00000049ec16444dc0,0x50c04e49dba911b62456,0x8d657000080001f0564c,0x165454804ff5729a8c0a,0xb18a448e4c08000001f4,0x11f8d65857804e75bb71,0x6642ee0219bc00000001,0x21fd965c5a804c9d,0x560d215451909a212100,0x200400090201965c5d00,0x5f0054f39fb6c80c2048,0x22cf800000a082045664,0x566c60005ad3dd10752c,0x3c025a61c00000000209,0x20d967462c05ff9a59e,0x85ab060d6a54a8011200,0x200212d67465405df2,0x6179bf95d686404a2880,0x842000010216967c6840,0x6a80679661ba78499e44,0xd0ce18000000021bd680,0x56806d806fd42f31e42b],#[0xafa2851a510000100220,0x224d68071006c1d7ae5,0xba1c2a96458390000000,0x80010629568873c06c69,0x6d662a408a11c4bf1409,0xa0040008022cd6887700,0x79c073417ec248be8035,0x888e00800000822f9698,0x569c7cc0767e75717981,0x6e0514d0900002000233,0x23856a07ec079fae92f,0xd14f89a50a9074000090,0x23d96a081407e4a,0x7de91a4bf61605240810,0x84104001024156a88400,0x86007fe61e927809a16d,0x31c0c20000000245d6ac,0x56b088c085f3ce3f3e0c,0xcc49540130000080024a,0x24fd6b48b0087b2ab7e,0x76322bb9898dd5020804,0x8000825516b48d408844,0x8c8c6eff7e7391000250,0xd4000008025816c09100,0x924090d7787729288688,0xa8ba06000000025d56d0,0xd6d4950091a51745f81a,0x3c005508410140208261,0x26616d498009646aad7,0x752df4358ad208040800,0x220026a96d89940a6ca,0xa45e590af581a4d50820],#[0x20000024326f56e09bc0,0x9ec0b0d4d04b85002eb4,0x4f8140000401067356e0,0x96eca080b763103eb09c,0x7c84b5d9804000008276,0x427a56f4a300bb3b4a26,0x86b58325790a3d001040,0x2410027ed6f8a600bcda,0xc50d92edfaf26d0204a0,0x4e00200042825700a980,0xabc0c96fdbabb0900454,0x84d11e0004000a86d710,0x1714adc0d0d87b2ee327,0xb4230c4848004009028c,0x42905720b0c0d3dcb3b6,0x7d9f9c0b822060000040,0x2959724b2c0dbf4,0xdde06fa15a17905ea408,0xd0040400029b5728b480,0xb840e14bba1e2eb445e1,0xa6d4ac000001229f5728,0x9730bb80e172592a528d,0xd8c195662430000002a3,0x2a71734bf80e70e6a99,0xd47fb0042b004c000280,0x2006ab5734c2c0ed7b,0xf27acfc2f085303c0c00,0x6000420082b09738c480,0xc6c0f3f789a91c087656,0x8292081040000ab55740,0x1748c940f7403d6df49f,0x1b1a808c8402000002ba],#[0x2be9750cbc0f8e57f73,0x5af52ac0a50054002000,0x2c35754ce40f93f,0xfb91f7ff786e08008404,0xb280000002c81758d080,0xd240f87ff89a4f800765,0xab008460000002ce175c,0xd764d500f99d54ff7a22,0xec03246a1000000c02d2,0x82d81768d740fffcdb91,0x74747d888b8b80040000,0x202dd976cd9410073,0x71c59fce8e0a6031001,0xa820000006e21770dc01,0xde410bdbe75f500418a0,0x49d02000000102e6d774,0x5774e0411198b62ede67,0x3e80e1c5c001010002ec,0x2f0d774e381157c1e1a,0x623b35619d84c9001440,0x400082f51778e641189e,0x1fdb8cfe682473019420,0x8000002022f91784e901,0xeb011ef3bed85d084001,0xa20e2000020402fe5790,0x9790ec4126c15cf1dc16,0xe763a000011000000303,0x3081798ee41248c5f56,0x3fdf9fd2002060084000,0x30c579cf0012825,0x3281956f2d766a90d040,0x8002311579cf241],#[0xf5c132c3571ad11ca8a1,0x2105e0000400031557a0,0x57a4f801359fc2fa1a60,0xe0310dd31c0080000f19,0x31dd7a4fa813bce700c,0xd7edbd8c201240800800,0x32197acfd813e73,0x41b4fffb264b0004d802,0x21084042032757b0ff41,0x18140278f39dfd030c6,0x16010080000c32cd7b5,0x57c103c14b94fe9f2c43,0x256b3c0f80620000331,0x833697c1058155a94c3f,0x1ee32b22a11c55006000,0x33a17cd090154dd,0x5ebbb526ad444ad95100,0x10080000033e57d50bc1,0xec15df7ef7cee081083,0x807970440001034317d9,0x57dd10415d127f868ee9,0xb9036291440004000349,0x34d57e5138162fc996e,0xc80f7ce923f080401700,0x202035257e516416716,0x6e2d3d3c7dd2c2c38000,0x140000000b5697f118c1,0x1b816df0bae7e20f4518,0xcac098100800035b57f9,0x17f91e817021353f6596,0xa0640d2a500000001760,0x363d8012181739bf2c5],#[0x8c1fb99c63a044841080,0x410368580524017662,0x7b4ce7b4fcb1104b0000,0x4480a090036c58112681,0x2841796f500d92900fe2,0x3801d400000003719819,0x18212b0187f0c7fe280f,0xdc1e3a10200000000375,0x437a18212e0187e1c5e7,0x9a63adc5259c50000100,0x37f582130818638,0x851cf3d1e2e30c2c1a00,0x10001000038358293381,0x36818787664dec7899b2,0x6a70c0000000387982d,0x58313981879cf958f063,0xfd32509f00104000038c,0x2f9118313cc186cdac60,0xf24d52b00db2a8100020,0x400039598393f41850a,0x8a0d1823ed8222941000,0x140000089399184941c1,0x44018f437ba468ac005b,0x60a100000439c9849,0xd851464191e7fff98408,0xb68b46024800400003a0,0x23a6985147419d74b1fd,0xba198ca745c44000008,0x40000bab985549c19f25,0xa234bafe35cb4501c800,0x48048200c3af18594d01,0x4fc1a040613f35bf1a40],#[0x72247000008013b3d861,0x186d5281aa2a805b8d10,0x1f063500e000510003b7,0x3ba58715501ace882af,0x9cf64720400192004000,0x880213be18795741b05f,0xb25a3548c8054ab42000,0x400000003c298815881,0x5ac1bc00000018000000,0x601c30c28bcb0bc61885,0x2b145078abc1f703049c,0x32e712e08f60c9e18040,0xd20458706c3e605039e8,0xa836ff8b5a0020400000,0x7de9a3ea3d1c89b6141b,0x72f13db42e4a725f280b,0x46c7bd1510d86a48b9e,0xe3032313c8018f507ab9,0xe78a0f297a32c2cc827b,0x3c6c4cfe39246bea6c59,0x6324c91a93f1ba6598c9,0xf816031e62de5a4c3dd,0x471f4a1f41344b1d3f12,0xb95a75e73e21f2f3ed3d,0xe155d472a9b5ee0720eb,0xa18da77efa12e0488bff,0x41db2912eef7c4875441,0x58c787fa0273ec20751f,0x325b505cf92373efda44,0x72883275debce4e73d5a,0x2faf0a2081a59d708141,0x6ecc9d1a29a7870ecdba],#[0xfe430abac99d2d37a05f,0xc07910d33bdfa88ac5f5,0xff965bd41f5043077890,0x366f8d039592f46363ad,0x36b67e6dea40b1167fae,0xb7106c464799bd717414,0x8fd51f168b5e961f9d46,0x3f786150430351619b88,0x1fefbfe00fcdb04c1f96,0x7185020401c9a19f335b,0x624e07643610a3d15708,0xbcf41421fbe120c42298,0xebb633bf6c1128b21803,0x4508d4fd7487a9cdb399,0x33e55000660c8ec1775c,0xaa4633ab9eb1c874a73d,0xdd07a2ca14a7e444bc37,0x7f936794acc4f703cf3e,0x2d19964554abf014dd21,0x8674369954a902e3d738,0x5d3a63f03260599b457,0xf4024709adbf4bfb4700,0x428189be73a8d0092fcb,0xa2ad1b76608fb0f8af08,0xfecfe84a33cba3a0a31e,0xb016209655936794bf94,0xc10b33c3c38e3a555425,0xeb4469b330450a40a105,0x753e519ab00754d11022,0xcced837cd3f91baedce,0xb911be965f3fd14a9175,0x7020e3b6bcc4905728d5],#[0x299d189e021b6061b7dc,0x6cc837cac49667d8ce64,0xf018ef5261cdb612a0d,0xb23ec7885581cc295f64,0x2e39503dcf4eacb7ac44,0xa1112cbd33e4c1fa2827,0x72411545cfc0401ea02e,0x6552c48130bea2a14f3e,0x10754a503cc29571e0a7,0x461c0344ec8d62811819,0xe186c1f63e5975711444,0x6d18311fc23329eff60f,0x42c78ee6e5910b36d7b2,0xa46eb2020338cd10df05,0x8f8d600ab4ebdf661df4,0xb1c8f0f61835f7991f96,0x11c61d51cc37f2251ff4,0xd8a690a2570d699c93ac,0x27fe352474c3b5b3434f,0xfff9635355051a30d68b,0xb36df14f4e9bb723762f,0xdd5524199f384ffdb7af,0x51209990aaa4c67f64bc,0x76e6bae5cfa4bfdb48b2,0x853b06b98d3abdf5fc8f,0x8f1bf021b96b6c189b07,0x498adb177aeb64b56b90,0x81463373c0bd54f14eee,0xe24104fd5c2e56c8e827,0xd570558d4403e33385fa,0xc70861e489c2556fa009,0x562817b317fec8296f64],#[0x6dd9653442e2da3c7e0c,0xbee499fc38b51318c0b6,0xb7e66e20622ee248da28,0xf758b87c9ffe6f85005f,0xc1150cb99968ec627411,0x28ffe05d01a1eb1d3fae,0x71b4299c17848b414cd9,0x6024fd9c1293c2cf195e,0xb64e00e222334a7f0d8,0x411903b740cdceb25140,0x15e5a3a3f81e4704302a,0x31311c7b9572c5f0cc50,0xe8552934a0cef7586eed,0x620074f1498aa88039da,0x35a36d8fcbf9e2a31f71,0xeb1c11001e818024504,0x91f1f2b0f4fa8260be8e,0xb033d3e7d6f460f2310c,0x2ca711687f878cccb8d,0x475afdeb14701e206298,0xf4381e8f951e49c5821e,0x5b4653b611e2c2bf62,0xdb76b0211a8c5f894fec,0xd85352ea9976bf6940d4,0x1fd91fc8685094ffa310,0x2d42e210caecb47170be,0x93d8475dc6dfbfa0cba5,0xbe1986eb4237a39984bb,0xd20594c4ed49f99589a9,0x40c1e35d9c69f8fcf2a,0xf472846e4d31277df6bf,0x276ff4002a764b88d918]]
private def groupPage16 := limbs80 #[#[0x95e3a20daec74c9b41f7,0xa49abc7dfcea630c6bb2,0x14a1ecf744f7991d9514,0xee03ed744cf4a6d02f69,0x583abaeceae9340e270e,0x75b2dc9d74123e8d592c,0xb04a9040a9c544845fc6,0x834248c72db70c4a2c00,0x2783470f6abd7d251789,0xa90fa91fb0308195065a,0x15b506202a3518d57dc5,0x550c10c12673d04fcd86,0x397558df56b70987569b,0x89ba9d1f4fadb7273c11,0xf210a75d690c9739ad,0x2c9a619407b4000e7524,0xec77dbd944cd29ead1c0,0xe098f94145be02bd9417,0x8b39e70f637de05b3d46,0x800cc6fb82fb6494c093,0x1208fa99e392e8a36214,0x5b73c8c02ee106033161,0x6e9a00369034710e3813,0x787b80a18398987036a8,0xe97e54be4f02dc803ded,0x100596055e5829ee5e40,0xfcd00fcdf72042bc831b,0x2b5ded9668bc316054a0,0x69c4dfcb4e650beff93c,0xa6fae6b4e2a02127ee33,0x85ee0085fd5310b85806,0x1c6600e383a55da037c3],#[0x270837420f0ee09108e8,0x88cb2141ab16ca06800d,0x8a81c579b3f7fd0d5fcf,0x5]]
def g63H8 := groupedPages #[groupPage15,groupPage16]
private def groupPage17 := limbs80 #[#[0x104400c8310c02108010,0x4405414c521445010c42,0x88620841324c53048520,0xcc730c8720c42328c630,0xd4b51d4343d0b41d0332,0xefdfbf7efef6eebe7f53,0x6504d611826513fffbf7,0x640c46448a6228664002,0x6408d610ce61189620c6,0x620c66464e610c065406,0x639496228265802650ca,0x60927105526371163051,0x103d262011602d264091,0x626d26031262192621e6,0x63222321526261b43852,0x316d2626936045064711,0x4209160111631d1630a5,0x608116179064452639e0,0x425db401a120051605d1,0x609d1603516329f300e0,0x60893637516031363052,0x618d262352646d0647d2,0x638e5313d2620d163311,0x60690623d1633d1638d2,0x63450644d263326610d1,0x611506475161366313d0,0x6355260662620d264691,0x63951637116105264492,0x61961321656119264652,0x604d0624d26035361491,0x650d9640d1632e7314d0,0x60911610d26455264956],#[0x60392632e73165063552,0x639e23242320595650d1,0x6405262112601d260151,0x600ab306126405163750,0x64112626506249063751,0x602ea300d2623d2600d2,0x625516169864492605d2,0x6039b418526099361510,0x63193633d0633d161212,0x420a510011607d263851,0x6295b42892642eb304a3,0x3062320069300d1636d2,0x6451262a12622d26319f,0x643526429665052636d0,0x6015160751608d160992,0x6461b432506441b64491,0x6051260012644d263390,0x6181160892608d2627d0,0x300d2628653112661191,0x327184319064151609dd,0x636526205161312631e2,0x64612623916139260211,0x628916171161291619d2,0x601d2608126025263052,0x6359264710640d263991,0x62251638536051163611,0x61592620926309263592,0x63893637126459262291,0x64790645536345161911,0x64691606633269161552,0x64012641526011263750,0x32712649926321260092],#[0x65052649d263292605a1,0x6069161852607d163015,0x62792633d26255160212,0x61a106305160a1262992,0x63992630116161161191,0x63112638a1620d3604d1,0x648184389160251635d2,0x30490644906045363412,0x6215264310647926475e,0x630d0643d16339363552,0x647d063725610d063412,0x640d2629116355a640d2,0x6061264a12645d260a12,0x607536141161252643d2,0x614af4352d32552635d2,0x528af521ee621ac314af,0x326ef535af3106f217af,0x424ae6372f520ec643ee,0x306ed614af527ac5042c,0x3202f328ac439ee6476f,0x4106c5386e323ed212af,0x607ef210ec321ac324ef,0x303ec4296f534ee6076e,0x214af531af5372c3266f,0x324ed3042c5162c614ad,0x321ae6122c306ec4366d,0x5366e650ec5412c436ed,0x3006c3186f321ec303ef,0x3266c524ad2196c3196f,0x6356e304ac217ac538ed,0x433ef5042c5392c624ae,0x4106e217ac4376c5356c],#[0x4212d2186d6306c535ac,0x4312c644ec5446c210ef,0x6092f5186f5062c5442f,0x4256e627ac326ec4306e,0x315ad6372f4042e210ec,0x536ec534ec5372c430ac,0x4062c5286c323ec5462f,0x326ec514ac504ae327ef,0x5376c435ee6416f533ed,0x5366d620ef429ae6456f,0x3172f4342f5382d2056c,0x439ac5452d323ec624ec,0x604ef5306e328af4346f,0x6022f417af515ac531ac,0x5256f4262c424ec311ae,0x530af4362e3202e611ac,0x4332f410ec5086c4266f,0x6026f3002f535ed624af,0x4042c5376f5172f504ad,0x5212e647ec623ed211ac,0x5186f511ae327ae6386f,0x321ee320ed6292d3142c,0x521ac4302c536ef422ee,0x404ac533ec544ac417ac,0x432ac436ac524ef422af,0x3072e3142e640ec515af,0x6462c426ed3162d627ee,0x6126e6322c328ac410ee,0x5266d6106f5086f514ad,0x511ac530af537ec5172c,0x3056e617af432ec423ec,0x5262d327ef424af538ad],#[0x3106c535ec5306c3202f,0x6376d305ac5072d328ac,0x4296d627af5302d206ed,0x4396e606af536ad312af,0x3202f434ad631af5056f,0x526ef2162e6406e312ad,0x329ae306ef537ae3162c,0x327ac653ef505ac321ef,0x4056d203ed314ac5456d,0x404ad617ad6022f5106f,0x545af531ef530ec523ec,0x314ae303ef405af3262c,0x3196d321ed320ef5326e,0x4352e624af501af5072d,0x606ad3072f212ac538ac,0x4356e646ac2162e3196d,0x6192e631af624ac5472f,0x620ef4256d3186c544ee,0x5302c427ec506ef322ee,0x4072e6286f524ac536ac,0x3186c5466c503ef435af,0x633ee2162c5106d621ae,0x322af5316f214ac633ef,0x3142d6162d306ee614af,0x3212f424ec531ec4202f,0x5286e657ef2196f4372e,0x303ef5352f434ef2056f,0x4142c527ef506ef324ad,0x4366f3162e6556c427af,0x5476d3006d6172d315af,0x315af503ec528af4266c,0x610ee329ac212ad2002e],#[0x4162d6262c214ac420ed,0x5256d6386d6116f406ef,0x4072c5202f5006c546ef,0x654ef439ed217af2186c,0x543ef403ee6586e214ac,0x3262f517af3296c5482c,0x3042f624ed210ed311ae,0x510ee311af312ac3042f,0x3172f426ec5406c527af,0x3062f4006e2196d6226d,0x6592c654ae3172c4142f,0x607ee6126c5352f4376e,0x4162c520ec540ae654ad,0x524ee6162c2186d6322c,0x6472d616af521ad6192f,0x5312c439ac4342f3286e,0x517ac545ef4382e2186f,0x314ae322af5322e6172c,0x4306e6016f436ed3212f,0x211ac521ef433ee206ef,0x3256c507af5266d6076f,0x412af3196f414ac4346f,0x322ed6186f423ec329af,0x5346f430ac644af206ee,0x5342c432ec4332c406ef,0x2196d3002e212ae6562f,0x6256c3262c403ec510ec,0x3186c412af435ee324ad,0x3106d6286f304ae6262f,0x4196c432ae203ed329ad,0x526ef3266c547ef5362f,0x5002f321ae3296f324ef],#[0x300ed3262e3106f203ef,0x4362f507ac322ec414ad,0x546ac5322e610ee6256c,0x6306f427ee211af4002c,0x500ec4196c322ac211ae,0x627ec434ac547ae6186f,0x322ec5402f315af523ee,0x5346c4396e6376e3286d,0x407ac5342e657ac4212c,0x437ef400ed611af326ef,0x604ef415ac540ee6116f,0x436af3172c324ae3256f,0x427af323ec206ed6092f,0x3142f3056f437af311af,0x322ac203ef4302f534ac,0x3296d6356f4172c429ad,0x616af4202d324af305ac,0x3162f420ec5362f623ee,0x415af2002f430ee651ac,0x3296c5416e324ec4262c,0x527ec5212e321ac3286d,0x4356f5142f3072e6526f,0x317ac407ae6292c435ac,0x2162e6106f5386e3266d,0x4172e3042d3286d6016d,0x317ad310ec422ec3072c,0x4316c4372f5162f5202e,0x644ac434ec3256c312af,0x310ed6122c534ac422ae,0x6026f5356c5262f538ee,0x647ac5142e6226f5392e,0x1f502c6038b02ee0002e],#[0x725f443207500c5913f0,0x491e5337fe668cbbd952,0xb2394fd27804a568b210,0x70bed7cd9c9b1515df2,0x53444983f0fe79e9d3ad,0x47e67d64d58962123323,0x8bc3f6de6c93d6d5a8f3,0x2169f2cef794af161e09,0xdf8babe732be18bba3f6,0x3188815828007c43f401,0x8e214749a65e14c470f6,0x3e0ac16826002c6a6a64,0xc6ae2a7258871d66294c,0x3e0bc1d844003daeab54,0xb5a8a96a2c799aa6213e,0x428c622040003bedcb26,0xd9314b02788a1d66494e,0x400bc1f83800440ff3a8,0xcd2f8b1a74871d462158,0x510ea27046003faebb7c,0xe8b54c1ad6a2a4c77990,0x4e8e2220420047f09bf6,0xe0b38baaa69e2287598a,0x458c82005000438ffbc2,0xccad0a424a869da67968,0x428c01e02800402ee374,0xdf328b9a96921fc6c158,0x4a8e02403c00428fbbaa,0xcd302ad268879e06916c,0x430d6268480040aec36c,0xe0b52c02ac942006895a,0x3f8ba1e82e0045d043c8],#[0xc7ad6a2a467e9bc6193c,0x490d62704800408ee36c,0xe4b44beaac9620271974,0x480ce2083c004690bbe0,0xe8b56bfaaa97a026c16e,0x4d8e4290560045b073d0,0xd1316b7a9a95a0c76184,0x460ca2404800440fa39c,0xd8b14afa8c901f46a95c,0x4b0e22503e0042af7b96,0xe5b40c1ab096a0a7417e,0x490e023046004790a3d6,0xe3b38b9294939fe6b974,0x4c8ec2885800479093d8,0xec366c4aca9820e6e17a,0x4d0f82c864004ad13410,0xf8b9ccbaeea022e76180,0x488da25052004e723430,0xee374c5abc9aa126d974,0x539002b04a0047d0f408,0xeab72ca2cca223277192,0x3b0b81b8200046310402,0xceadea62608b9ec6413e,0x4b0ca2284a00434fa382,0xe2336b9ab29aa0a73182,0x560fc2b85a0047307bde,0xeb36ac72cca62467d9a8,0x5890c2a85a0048311be0,0xf138cd1afca1a4a831b4,0x511002b8520049b1b40e,0xed35ac22ac9fa2a79192,0x470d4228520048b0f404],#[0xe5b36bdab89ba2672172,0x4c8f62984e004870c3d6,0xe2b52c5aac9721c75988,0x510f82a85400457053c4,0xdfb3cbd2a899222759a2,0x438be1b83e0045906bdc,0xee35cbfaae9a2147296e,0x408be1f048004710e3f4,0xc32c2a0a347f1ba6014e,0x438ce24840003feefb56,0xdbb1cb6276889de6a952,0x4d0e42505200436fb3a2,0xdeb2abc2a495a1671972,0x490e42c04c00442ffbb2,0xe6346bcac097a0e74180,0x460d8270460045f09be2,0xdf318b62949320c6f170,0x5d1203286800457033be,0xf9b82cb2f0af274851ba,0x4b0d82484a004b11e424,0xee366ca2cea022a7597c,0x488e227856004790f3ee,0xec360bc2928c9ea6a166,0x468da2304600455063d6,0xdc322b3a88951f86a962,0x5d9162d85000461033c8,0xabc8d7b18b3a66821cc,0x4b0d82a05e005032fc75,0xea37ac7ab09ba146f16e,0x3d0b220044004a3163fa,0xc62eea9260891da6214a,0x508f22684a00404ea35c],#[0xdd336bba9c93a066e986,0x4a0d222848004990f3e8,0xe7b54c02c09a21c73978,0x561062984a00453043da,0xebb5ec0ab0a0a367d1a6,0x458d023050004a11440c,0xe5336b8aa2939e86915c,0x470d22084e0046106bd0,0xda326b62928e1da69968,0x530f02c06400454fe3b2,0xdfb30baa94951fc7117c,0x4b8da2784a0044300bc2,0xf5b80ce2eaa5a547e18c,0x440dc258380047d093fa,0xe6334b7a98932026a97a,0x488c81e83c0046908bd6,0xe4354c02b49720872184,0x428be1d03e0047d0f3f8,0xd22eaa5a52851e262154,0x508ea2984200406f637e,0xd430ab3a9c97a227618c,0x20c102003e00444febac,0x886508980070642040a1,0x104264080843619820e0,0xc0002385a33090256830,0x8908e16204634445c243,0x10d11183a2d0f0a148a9,0xb161a4e8c482a96283e3,0x8b729e25d9a489438484,0x12edc43d8ca441fc884,0xace025d9548974812dbe,0x3259604b6991af90a311],#[0xdb424a702439c0903e42,0xaef3394204563ed122,0xc9193ffe8b600e3ee528,0x284e23dcf23004563cda,0xa6fdb98028be61a09e66,0x72404e733604d63d69e8,0x54fcd40d7cce61000acf,0xcc96fdb90228a53daf80,0x930de909ee2e1d51550e,0x4063f8668014df3ae082,0x26f6438314bf1cb2125,0x659f6480054b0728839a,0x54bf7c731061f955c001,0x448d7ce334145f38c800,0x65bc64e14f6be452b98c,0xb7bf39802e3fd4f027a,0xc02497bfb98029ffce40,0x984537ef9421054bcf30,0xb901537f7f9e08184e66,0xa40005932e96e239cfd0,0x873284547bd590149f7c,0x98f5a6c054efcc0137e,0x2b025975e70514bfab64,0xf72901056fc4410708e7,0xd9e49200161ff1238141,0x50aea00ab7f41701165,0x8bf0132ffe720065dcd4,0x172681d08ad7df8e700c,0x650fd918802d3feb5205,0xd627a43204b5fff67400,0xd0fd8700456befc53806,0x6dd6e231fff679224002],#[0x82cb894260ceb1cc8aa,0xae8fc224095daf918,0xf7cf000e7e21083dddd9,0x99ca188a68f76642873f,0xcfae5409012567d86023,0xf941704161f1e21c0416,0xfd61124058bffc730061,0xd0137230945ffe3b8034,0xd1c0a6f27864214bfdbc,0x17990813a5eb11235e70,0x5743c387400b1edce21,0x4ec054fcd00e6e79182,0xdb8f700c2cdca904597d,0x9df8e7a08ae8a0c8fe,0xc73cc988a1f98c1af9cc,0xcfb7cc0c8005b32fda08,0x551fea7813dbe67209,0x86a8677fd2200aaccbb3,0x66f9a60052afbf16c21b,0x576659e000ae3fa82045,0x5dcc7b240547a5e71a64,0xd7ffd1c401afcbc5fa0,0x4058bf8f440b3effcb01,0xf37ea89c750051dcd912,0x5e22eeaab08b6ede3263,0xa404158e170a46893263,0xeb0c0463fca401151f7c,0xa205ce17808b319948ab,0xf3081149f7cc300a1fc5,0x8a8e680ab9963204567d,0xe7a0069e7bec414b1994,0xc8428bf7ca1082a7fafd],#[0x1ce01473fca1082a3f78,0x51732c6420ae360d323f,0xa796ff59ec21d4a7bbf0,0xac3e897022ebc9e49202,0x7fd20002b55fbe2da038,0x2047bde704052fd40107,0x13c8a97ffae600b1f81a,0xdbfcec1023dc8c250ceb,0xb013dfb721051b88f008,0xcf48130e1a577120f37,0x4145adc8e0056fe3db02,0x750152fdf1cc01b7edc8,0xe1d80a6f279590155cb8,0xfec0029b9940c812bbc9,0x7ff8b620d5ffda600bb1,0xadfef6528069ee1809d5,0x452fb99000acfd606480,0x40dbe7930800577089a1,0x545ee81d20acb7fb8f6,0x1056ffef390032ffa400,0x9013beb7cf410c0fd870,0xe8e780a3ffeeb400c3dc,0x5afff54c0196f99300a1,0x3deec64002b3eecc2001,0x4947df90e0a2a98c8c22,0x1a5dfa80115cfce80302,0xd33d40c8416bbfd51fc0,0x8082bb3284abffc53006,0xbd1d60187a2f68a2cf94,0xa11a1159fc30a1802c7f,0xf9c29100ae478b7118f9,0xe792e000adfdbc5b2065],#[0x5de669400aade10263,0x394f131effec012ff6d3,0x82ddff9e3e8034724051,0x97bfdfce400d7ede2d9,0x684155fa7c0014b78f66,0xf7cb1002a7bf310447e1,0xa2fc34a0056f7e730851,0x863f7f16c8176be49022,0x92408b11c9016bffc530,0xbafc077fff9c04177653,0x85ffe3b802ef70b880a8,0x2344a7f1ec8137fd2222,0x8a8fcb448115e1c179,0xc812b3bfec000159fe52,0xc16400ae6daf48b6f740,0x43a00594cfa06420b0f9,0x57e560458f7e6009be3c,0x6fe82e082ca3864a2938,0x3fd44800567ffd96801b,0xb0fe19a4141ff58b028,0x38ff54f027b7f42e00,0x2240959cc9289cfbff2c,0x896a23bef3e7b0061f94,0xfa2d8038f9676408aa47,0xc9015139fa0b842b4ff,0xe58800b28fe89082b3dc,0x7fec3388a54ae680933e,0x619c98310aa6a148e890,0x9ca0e753398a08e7a6f0,0x2e02958389264c94182c,0xa0e77e16f83405d7f367,0x29bf3769140acecdc38c],#[0xa3f33602002974c7db4d,0x457f8a171a0172fed228,0x7e7bb0502596eac1a2ca,0x2a5df89c0cbf0c593a53,0xe6950f32127091dec363,0xca4fe48333615599f0c5,0xfff1748450171fdb2d2c,0x43e947584befafbc898f,0xe8edb6295c6c8ca8e79b,0xe28c0937f20d922516df,0x6be1b06a5b6c25947f92,0x6bbf2a8171e427b277f2,0xe764ec5102c5e3220547,0xabfe88135c0b205bab88,0x4fad60d02cd5f9108a04,0x393c090adff227ab3c1c,0x83172715de1c2125078f,0x80566766124e336f22c7,0x425d7e30d9ca0fce4266,0xcee0076472bd9c459503,0x85ae8f2288e7261a568a,0x959ffd3328b2958e5bfc,0x42e33738ec9e9f170a4d,0xa2d7ea0f9ca2e6c3b441,0xe022dfd50481e160e6f2,0xc887f92104241d48e781,0xfb3f660164eee6c0ca4e,0x856be60ccb049b31d499,0x63e1b3a68ccaefa804c7,0xb79c498e9b84a23d4014,0xf850528cc5d928c6311c,0x68a525b3265166f9c945]]
private def groupPage18 := limbs80 #[#[0x688b272bdf9856151d7d,0xf7d7de44d12f764b29af,0xcce78e744285a2726d88,0xe7c081108f7f8ba4238a,0x37ff0c198e8560767949,0xb2024969e84c7acafa25,0x4062b11e6619a24e03cd,0xd91815dc61cd939cefec,0x91202c27cd6c9c5279c1,0x9814df30925e2557f374,0x72c3bf361c830aee7099,0x8149e16b04c2b3640562,0x3446f26b75a0717f03e4,0x661b0ac74630cd126703,0x2d8b7a190fcb4ba4f5c0,0x94196459407cff910070,0x436050c272d9f30e1064,0x398e28a65a78e39d0057,0xb9140594f8e4f890aaf7,0xe61118a3c89b360b6f8b,0xdc912f2417c90bd88cba,0xf2a9450f3b11ca6fe49,0x6c9e3101920d93d89acf,0xec563b6d129f9908d611,0xc40b2fda053ca551050e,0x48d7ced9a062a3e7ae98,0xb48aaff3a701944fc3ea,0xb9a4aab8ecaa151fe01c,0xe588eb0968e0f43bfa18,0x98b13ca97cd076209369,0x47e59313383e56151f1f,0xc1cbb22caa99dc9e014c],#[0xe299e215451cfc00d124,0x34571d79d425278e8cc,0x3956fe090eb8483fad9e,0x11cb6989e4a4ff33b0b2,0x4c71196a7c9234f81022,0x9b11ce7855f0680b82d,0x49ea159fc9862850b372,0xaec8b1568513d11ef725,0x61bd8a4fcd83c860acfc,0x22562182d3392f09af98,0x3c7d66831feebc8a061f,0x997cee9c885316eda28e,0x5937571187d8e6408060,0xd784c55b8d1a459f9724,0xaf21990acdbc4a0521f2,0x2d2715df90d92c0577cd,0x72e4543dd0856922fe94,0x36d1493b92ef8096532d,0x865c5583a98ee73829d8,0x93ef238294905aefbc93,0xcac2c9f90d1239f67e15,0x15c91aa4c25941f9f042,0xbbec44119de7be4217b5,0xdf0557fdc5f165173884,0x8567cf584c6805a67656,0x2a3efb636141f79e4641,0x6554bfb22ca2ff46e903,0xb33f946706c584f23709,0x472521cc9c33be4de482,0x9c8923bc14192793105,0x8e69ef039806b239501f,0x8a32a34313b4a4668d2a],#[0x279a932231d34c96879d,0x8b2d25333e208a4e56fb,0x8c976ff0bb06663283fc,0x7f80deb80ba7f4e1b68e,0x7e48b278a654f0351acd,0x14f342e4a056d9e3fc11,0x764b27d9ae694695e945,0x3cb781f71cb202992aef,0xebf80d9290ac562c1e47,0x8e00af48c79e1b1a41a2,0x211cedbe251e9f0022a4,0x58a2b3ecb30914afc0c8,0xaa11dbe18e37c1d7cee9,0x70361556d99c84954e6c,0x6c70940b06ce5ca35f2b,0x510b7846bf822c9d2ab8,0xd33c8398241f26194b29,0xec94ec36c40cae6a4ac8,0xe396c27aff8b13ca2cbb,0xfe88ac48ea3b5585922f,0x1d34c4c7ffa41d10a16c,0xf6fe9298c816572a4d94,0x12c5cc5088cbff029b68,0x81f3fc0954c2cbdc458d,0x442cdf0cacd112667c88,0x9949df19efe0177b50b2,0x563c7ac2a731ee083d79,0x5f3c027812a320564e52,0x2185a7e59164f1764594,0x68962fdab5a88e7b0856,0x319f14593984939ee514,0xb517d9250b33c1223999],#[0xd3e422a387f338911e45,0x93c9a430152f918b4048,0xd7f82961580c2ecd21a2,0xcb4b195df9b02981b0b4,0xfc940cd0bd0583924f86,0x305a2e3eeb990b815b59,0xd4d44370c669298cf0a7,0x5f958720c2b1da2f9197,0x8fcc764d279d02941226,0x520704c51771cba06049,0x1940f0b6611227851881,0xc278392cfc0a079d9b87,0x5d42a8e71364b2a7e4f3,0x815d33ec477a557df3ba,0x857ba8bc45922ff142db,0xaa53335ed118ff2d0e09,0x2620a91bfb6d10e7dde4,0xa9670e311854707451fd,0x8e758c42a561cd8613e4,0xd3994906f25946d092aa,0xd3fd2b89e8e3a1853580,0xbfb42514817181d9f114,0x88eb20c03cff4cab815d,0x350cf4a17348acf969e5,0xe2a18d14d18be6bf04e3,0xd593997f64b278f91364,0x71e2505d38e258acfb37,0x66937985073cd2e05163,0x7d204d702cdd45e22c90,0x116d30bc21291b47116f,0xc2baf68d84e554b36b82,0x40acfb194c28a4ede40c],#[0x210aeddbe8229aff3634,0x5d7c6c7243890b8e45f2,0x2214818c5c7795130218,0x62ea4463f34310f8547f,0x8604185c7ff72c6568ae,0x31091cc9f2c96517dcdd,0xe0b2f7fb0ef41885b86b,0x28bc585dd9487f333123,0x98945f3ba184f78c2667,0x2a3dfcf12741b2bbf647,0x85c104499a1544de2ae2,0x7ab3d08245ccb22ca17c,0x620220d2b7d2e28a0126,0x1260214309ac59a23ef1,0x70887d32c4eb8165f736,0xccc1c0577ea264f12a82,0x95918906771b0c293cdf,0x843a6e139dd427e4fbe1,0x39d4159cb79c49e79b68,0x8a595857b6a96118e7ac,0xeb138aa28c1c507120cf,0xe44b9b5826154c24b928,0x67990d194d7086f851b6,0xac3906159ff4a4609858,0xff182d08ef59f9990bbc,0x4cb92c553d682844894b,0x4539897321cbc842501e,0x4595aefd88d235fb1ddb,0x329437d91c6fc30e81d6,0x11ac00c0666ac231c8fc,0x8a8fcdb12cc2a3e53f32,0x1a299e25145be674eafc],#[0xf3c185072df19273b65e,0x9a982bbf381298c5769,0x765615af90b61344ab7b,0x823704a3a197258a8b90,0x9337102b9df7904611e6,0xd946c8a32e2cabad1c9d,0xb06c5957349b2822f964,0x30218593d205aa48b816,0xa15df3c72431d165f870,0xd23dee168692aaff1b1a,0x180245943f08a078c70a,0xbfb3021c48b3a04b3c62,0xe3cc92949bfd6f120a58,0x75df09cf2e1e684b1607,0x83588e2ca1d3d4f52ab2,0x219c2593d0dd0bb0959b,0x1520e6cd2d941d0ac9c5,0x6c9650702fee051849e9,0x915249fc3c4244517de5,0xf29c0d9fa2a2461f120a,0x528d7f9908c700b1fd9a,0x3b19a0c8bdd906156ca9,0x7567c129241e1db293bd,0x9293e49b10c2a1d2551,0x7b2313ad637c5460779,0xf6925241c4ba523c9866,0x79f4bb27399b094b1964,0x48da33111e21cbb25950,0x249d9f19a0c3b36ba61,0x52c33b8e9c503c759463,0x6a7376424a6f99e16f83,0x8eef01b8c282e9e30304],#[0x7319516c9ece60a3bc25,0xdb3c7f822fcd40349caf,0x91e3fbb41549ddcd818a,0x88c13bcf71387f4b9b02,0xa687a4914e046ca2008f,0x4f697f47709552cd9bc8,0x185a7e674d02955e7954,0x7bd86728a52ebf0d0302,0xfbb7227b9fb238ea0b2f,0x6cd20d1599e4cb92c541,0xea301e4924f1c9dc0a0e,0xf8f70902b98aa1998473,0xc21f09263601ac472ca1,0x4365ce31499dc3670962,0xb774cfe28d612e1d3451,0x16507a1bca5165973884,0xbf227afe3631ca4fe665,0xc068b97fc0e8302453fa,0xe7115461d0c28be6d790,0xa3395452b9e9bc171817,0x6a91c26f2593ae98c88c,0x10b6ff8cca26056b8f48,0xa8d828e2e239c7ce6984,0x895def01e7c4543b10a,0x50903ca9e06a39f99863,0x4285ca217c228f11543,0x69144d3c4a28f73f9c4c,0xfcaa234cca9158249e2f,0xca57e064108f33b91172,0x744d6657bc029bfa34e8,0x72fc07bfce640c8151d2,0x2d24ade2502a58eca88c],#[0x29fc90a40632d9e6e209,0x6125fe250c954b0441ca,0xb8bae9b81716c9c9ae6,0xadb88a8a66b9cf72946a,0x46e3d06c9229f064293c,0x51abf62cf25139084e82,0x78b6da29e799f081c834,0x205a6716df0a086e6b2,0xe0a4990634e95dcd86f1,0xce70469066ae23999893,0x5ccc24d3c13123c8]]
def g63D9 := groupedPages #[groupPage17,groupPage18]
private def groupPage19 := limbs80 #[#[0x50060101a0001005811,0x1000030000004004,0x5815000010000100001,0x3813008030042509400,0x100c034000a40009c16,0xc0b03c000c80000c00,0x40c0080004c0000405,0x4458018010040200401,0xb401024060741b0080b,0x9000010040000004,0x101500c0d01c2101c00,0x8010e80c0103d02804,0x20110047702c0106c01,0xc08004100580102801,0x801004000003b08001,0x26070100600300804,0x2b40006c0601c0200809,0xd024050700001c04,0x83f00806028040b006,0x34170002100042,0x682503801014090000e,0x5c06044160000100006,0x4040000007404808,0x14010780a0140000800,0x13c0000c000e00005001,0x100b010030d80a07413,0x4c14014001801200c09,0x2804800044051943d,0x2818000040040002000,0x70000d0000100001401,0x401000020100000000,0x94030c407034000081c],#[0x3034020140102805,0xb11c0304c0001811,0x7c03018000400003800,0xbc3f00031078050203c,0x30100e15000,0x100c00c110300200c01,0x10640000c0a00402,0x1000000000107002,0x30800d0000302400,0xd81d014001e40001400,0x7014060001112801,0xc020a8000200900807,0x9402008100440700000,0x2d0480800c2b12400,0x502000400000000f401,0xc1a050360740d09826,0x102c010000813405,0x6405008180d402,0x102b0000903c0c02801,0x40e020130000811028,0xac13000040082e00005,0x1400008080140e01409,0x400000100340205412,0x1a00400008111087c,0x8120240200c2403400,0x5034190580602003,0x41d038040080000806,0x83003c040b00100400,0xc0402c040481700801,0x200202c560140705416,0x2380800400034230bc47,0x441d04c0a00c0000002],#[0x4c1f01c231e40301001,0x14250000a02c0301800,0xc030002b0000e02800,0x87c04c2b138040a017,0x380001c8800c0617805,0x2800020001200000c10,0x18000281a090000f800,0x1800024011380600427,0x582c224180106f0140d,0x441e1b4000840601022,0xc235bc0703c850580a,0x4b1f85b39c1c0583c,0x8000cc010000104453,0xd41303c0109c000040f,0x203c0f0b41706407,0x78080c0000081a00c05,0x804024051e41b02c0d,0x16804010000100100405,0x700f02407060080342b,0x8000040c0580000cd7,0x80003c000283100400,0xd4000000202c0f0080c,0x1cac0101f0748900000,0x48490100301703800,0x101900000000060000a,0x48024060080307000,0x640307c050002417400,0x18170dc5d0344000000,0x49004141ac0009822,0x401f00c0d0042609c0e,0x183b09c6b04c0203400,0x2c08040021340205407],#[0x12c05028020a8030002c,0x40360bc6b0200300015,0x8020003f00c1409806,0x8802018000382a09000,0x52802000000d82103439,0x500015c0c1803701400,0x204c23008010f436,0xb8150cc010086900005,0x2c4041dcb21f40a2a00c,0x3400048570b40225801,0x1101426004060dc0e,0x700e0d4040080609884,0xc403080040586600c14,0x34900181800c0b02405,0xe800280062d0021140f,0x7c0402c020281d254dc,0x7c0000c200080001c2c,0x14010143a00c0913817,0x28a009008018003a432,0x14010074010000106801,0x44190183d0040000027,0x1004004070740710018,0x2b0080f0280000001,0x90010181d0142d01400,0x108724ac5c044090b811,0x1500200006000500a00e,0x103c008240000309406,0x150100001404c0412018,0x180105c0200c055e03a,0x24000140524c4403c67,0xa8530111312c2d024db,0x380000c1e0f01204455],#[0x4383d0503a00c0706813,0x7015050000700400000,0x802084060000500c78,0x14c0000402000001280a,0xb4020b4220ec0000019,0x1cd3024100304e59c02,0x4062d81e000350b81d,0x5c250141a0680100000,0x12c010101d10cbc058e4,0x1602f018190340d0c067,0x6806000350003c08401,0x2d2b042000170000f,0x1851a6bc000980a5fc0c,0x80a110542b00514800,0x18800000370500705c0d,0x7c0803c030d40400d50,0x24010f8353d0141680f,0x4c2001c963c40002849,0x180c03c3e0044f00c04,0x440003000000001301b,0x1400000570015809828,0x842102c190441200c00,0x380d32c0902c2400400,0x1144b01005844000009d,0x7ffe559f97010012e82b,0x3800000400180fe3dfe,0xe9e446ce58dd2ac734e5,0x803f000000081015ddf7,0x5fb3b9625f12d2dc734f,0x304b00120808000df6f,0xefcdda2fcb4cfd30c735,0x51205400140410102a3b],#[0xb75be8103713bbd31c75,0x8523059001000000173b,0xeeedf847f428c06d33c7,0x7952f061001410020023,0xfe8e7752f6c60172d36c,0xc7a53a06a0010040008c,0xffbfcdaf7feb58d5d39,0xac7d5470710020040025,0x1ddfdfb7efecbe912d3,0x3dc7e55807a003220204,0x15dcadf56d4ae5d46d,0xd40c8056808400380250,0x2fd73defdff92d87f,0x1d43c8257608a0030280,0x8fffffff7dcb28f7,0xe2d46c82589090003000,0xd80080bf27ff7f1931f3,0x9f4d46c8359b09d00340,0x40000040aa4f9f900a4d,0x9b4ad48c875a90a90030,0xf6efdbce967d,0xe58a7d49c885b50ae003,0x4803522087fca9de75ea,0xf7866fd49c885c60b500,0x500000001ebfefffe0a,0x7a7fff9d4bc8e5d50bc0,0x603000c60f4fff39b5,0x6be56ff7d4cc8e5e50c8,0xe0060060180aff9fe7f5,0x6536cd44fd52c8e5f70c,0xd5006d04000882fbfff7,0xeedb17c1aed56c9060a0],#[0xe200701001000da5fef,0xd3b817e3553d5ac92616,0x70e9007100850c089f5a,0xfb3b67ede50dd5bc9362,0x330f000800000404ffed,0xeffce34f6c00ed5ec966,0x6440f9008914100206eb,0xafe5fee3b8bfb5d60c96,0xa65010500804401a01bb,0xfffffffe49d1279d62c9,0x9c65f10e00a00000000f,0xeddfbfff9eb748c8d66c,0xc9c66f11e00a12204000,0xfffff7df8b196dc1d66,0xac9c67b12e00a0000082,0x20fffffedf7485f879d6,0x6bc9d68913e00a000001,0x80ffbaff7f52d6dfb1d,0xd6cc9e69914c00a00440,0x200f77779fd3a561b91,0x2d6fc9e6a915800a0800,0xa1010d7f1efee441bdd2,0x2ad71c9e6b616400a200,0x8c040f9f53fbf50beef,0xc5d74ca06c117100a04,0x10048003effb7d5df170,0xb29dd77ca26cf17c00bc,0x100208cfeffdf735c3d,0x9cfebd7aca46db18800b,0xb0004a0a4fefb5f5b1d1,0x3d022ed7eca56e919500,0xc800600107759faab67],#[0x4edfc3bd81ca86f819f0,0xe804080085fbf7ff7c,0x9e1b8b7ed82cab7041a8,0x300e0002a406fffd5bf9,0x703c09e71d86cab7141b,0xbe00ee08580001f7a7ff,0xffeb77d33ed8acad7231,0x1cb00e400011009fffee,0xfff5f2f6ef3d8ccb272e,0x1d500f10022000efadc,0xbbe70fe2a2efd8fcb274,0x531dc00f00004000affa,0xfe55de6734585d92cb27,0x7641e301000300080ffc,0x9c1effa08c1e7cd92cb3,0x37711ee01008010000e7,0xf3ffffbb359bddfd95cb,0xb577f1f601000c00004d,0xf91bbd5dbc1faf5fd95c,0xcb67921ff01106e442a0,0xafeebfff5ad9776a1d97,0xacbd7a42020120114000,0x8fffcbef7ff73f260d9,0x9dcbf7b320e012000041,0x6fefffff9bf1088ded,0xd9ecc17c421801401000,0x2120fffbdedfa5d7ebdf,0x9da1cc17d12280140004,0x221dfffbddef76a74e,0x5ada4cc27e5230014200,0x80ffffff7f02e65b,0xb5bda7cc37f523b01500],#[0xc1040bff3efbfa347d,0x8db9da7cc480424b0154,0x200008ffdffff76499,0xd0f51daacc6814256015,0x540010000bffeffff9e1,0xf66df3dabcc782326501,0x150b050021f4faffde5f,0xadc77b8daccc88322740,0x1502703222fd8fcdd5f,0x279398ffdb2cc984327c,0x501600010421fffefbde,0x96a2d2ab1db9ccb85028,0x9101640180046bfe7ffb,0xffeda91da3dbcccc8602,0x29e016822000007ddfff,0xfbfc67ccff1dbecd086d,0xd2ab01600004040ffffb,0xfffaa2b7ffa4dc0cd187,0x8f2b701644000001bbff,0xfdeff1e76fb1bdc2cd18,0x8a22c0017600021009ff,0xfedfffb7f773f6dc2cd4,0x68b42ca01720012000df,0xdffbf7fef8f52cbdc4cd,0xd68c92d201710004080e,0xff7faf7fbcfddfefdc7c,0xcd78da2dd01800805000,0x17ffffffe5fe79d1fdc9,0xccd78f02e30198000000,0xffdedfff7feb7efedc,0xcdcd89052ec019002120,0x440fbbbfbbf47cd3f3ed],#[0xdd0cd891c2f201904440,0x7defffffeb4acbdf,0xbdd4cd992c2fd0198210,0x10407db7efbfddfbb56,0x3dd6cda93f307019824,0x8c00085f73bff72765ee,0x6bdddacdb95130f01a80,0x158318ffea7ce7ac4e7,0x516dddbcdf95e31b01c0,0x500019ffad7fe6dd9d,0x61cf9ddfce396d32401c,0xc0c008030d3e71fcfce2,0x77edb6de2ce597d32d01,0x1c00240405fc53fbfaad,0xdc2fc2de6ce698a3360,0x1d4200220095ffddd7a,0x12a9d3e2deace799b33c,0x801e21000048deffd7b7,0xfd73c15a4decce99a734,0x5401e01040000faf8ff7,0xd7dbfce736dedcec9b53,0x36202000000028cffce5,0xffc1539ce3cdefcec9c1,0x436602203022002dcfdd,0xbcfd55b468f5df0ced9d,0xe33700221000410067fe,0xcae3f230d0e39df1cf19,0x9f237902200010080aff,0xeffdfe7ee62d5fdf3cf2,0x39fe38402202000201fd,0xbb37fff909cbf7fdf4cf,0xf4a1138d022900c80002],#[0xb81febfcb25dc3b0df6c,0xcf4a2039602202400000,0xe47ff5ff3aeec4bcdfb,0xdcf4a2e39d0221b800a0,0xfab7ffff3ed11aabdf,0x1cf7a3c3a8022050800,0x402dfa9fbfd6cdbfde7e,0xe02cf9a4b3b502320560,0x811defff7ee493c3b6d,0xbe08cfaa5c3bd0232100,0x122f7fffed58fbd81e,0x3fe0bcfca6a3ca023000,0x820400fd7dfbffd0c1ea,0x203e0ecfca783d702502,0x504000cfafbfff3347f5,0xa9bde0fcffa883e30250,0x40002441bff3db9e58d0,0x567f1e11d02a953f1025,0x60080000dfb777ff2d7f,0xed76ffe14d04aa13fd02,0x2700000000ffffffff7a,0xdf73da3e16d06ab44030,0x272a00010055ffbefbd,0x4e775c3e16d06acc40b,0x1028a15210005eadeffb,0xbd58f9dd7e18d08adf41,0x1c028800012147fffede,0xffb8e8774fe1bd0caec4,0x42602802130000fdecff,0xf9f6bdbe6f9e1fd0dafd,0x42f02843000060aceff,0xffdadc557e8be1fd11b1],#[0x2043802904280005f957,0xfbc6ffb7de75fe24d11b,0xb3143f02941004190bed,0xfbdfffb78d75dce26d14,0x5b4344502b40002000bf,0xcffffff3fcebafae2bd1,0x16b5545002c01000000f,0x7fbdbf7365470704e2cd,0xd16b6945a02d80424088,0x27fae9ffd302a9f63e2d,0xfd1ab7246a02e0000600,0xffffe5fffbcf4f00e2,0x30d1cb8047502e000002,0xfcfd7ef36e0f5adbe,0xe31d1cb9048202f02028,0x20fffbffdf3cafbb1b,0x4e33d1dba048b0300004,0x108bbfff6b579e6fb2,0x2fe34d1ebb3496030440,0x100a0b77eff5f9fffe5,0xd9be36d20bc349f03148,0x8084000f7f79fbfee7b7,0xef8be39d22bd74a50320,0x9d0010ff62ffafb6ff,0xf32e6e3cd22bea4ad033,0x300051008fffaeff7fff,0xfdfdf1e41d23bfd4b303,0x3308069000b7e92fffd9,0x879f6b8e44d24c124ba0,0x3640010000bffeffdf3,0xdd5f9e51e48d25c234c1,0xe03700000000ffcfdff7],#[0xf7a4a336fe49d26c334c,0xd703800211010fbde23e,0xff7afdd7ffe49d26c464,0x4dd038001008007feff7,0x1fc000000c6e4ad29c57,0x4e10380000000200000,0x5a3e9d3ef5d4e4bd2ac7,0x8010b16ed7e01ee3c1,0x300b0014869e4aa47eaa,0x4739ac30be6ac02f360,0x339c0001fc62c61030eb,0xc02d1c642be76194d100,0xd657c9e0004802303942,0xf78ad1e018f02a640388,0x14f2a977e0c005e81ca1,0xf08ff4824b3b48676113,0xefc1fec1240f0a19a2f7,0x86051c1c241c60c17084,0x1805809fc430e471032a,0x9d2b6c819de9cb548014,0x5fa40d2c4a7e03d54cbe,0xfd2a07b785bc10818622,0x2800018062ee01e0d3c1,0xf686b45c026807a80005,0x5f902c6d81c02a01d8fd,0xe9a4d2580b326965a19b,0xb2327d00198eece1c045,0xe60190f11e64b60a0f78,0x8941097a3a93b2ae5768,0xcbb6833ad11b0cf43bfe,0xbabe64f01a8d961c1e8,0xc70d0c20a80a3e0c7f94],#[0x9e86a06804a0ee7a665c,0x85529f928e00be15b100,0xf3ed12c74ed5924a8db0,0xea44506c52fa30dedb1d,0xc010f01d851e83464226,0xadef4762dc2b916dcfd,0x679c984c68d3cd8e3b01,0x1af399f0ea305db84205,0x5f49babd93f481d3a5d,0x9f408516091212d5252d,0xb6e3754a4c01815643e,0xaea42be8b6b54405c042,0x1e5933c1677afc1940b7,0xe1f0851deba4ff9e7f6a,0x5bd29fffe919acf01101,0x676e3ce96a4f4e13b363,0x85b07b5963da8e086d38,0x801eaabb0b3e3fea11b,0x4bd75d701b1dacd857dc,0xc460a547bb0a1cdd5e9a,0xf448af33c9b67d357847,0x26380c2d8977055d120,0x3056930d6b0861bb2003,0xf476d452e3d0ad14a734,0x136f9dae8830cae2609,0xe183d2901628c19c3fbe,0xf346837b8b0105ec5546,0x6c6005178755efb278f,0xec0f21f364d3350cde80,0x5ceb3a9a0675d97549a6,0x9d76471b800ab45d73f3,0x4671ed6e296735dad09b],#[0x92310607e162a18c7091,0x31eb336b114718270162,0x288fdb92d8aca9be833f,0xbd8ec122ad1a905ad636,0x95ac7670e2afcd40d74c,0x4d382e059b1abc90b488,0xfedb95f1188e9840433a,0x4b265318652ce87646a3,0x1412e5523a8cb803279d,0x9a323dc36280e73860e,0xf01b8f75f9293bb7aaf6,0xf1e6b2df83d28ac081c3,0x5f4f178ac8f3dd7996d7,0xfa72d43ee62e53a82d19,0x1721636eeb7f0d3e5628,0x8e80ed5410e3ed03d65f,0x190e2b892c78a4944a41,0xc815bc37e23ef4d151e0,0xd418c894d88eb7efd1da,0x270d47d01e18d041583f,0x94ae34bf036ae9c2ca06,0xb1b51233887b3b8ffad9,0xb9e842f2926122805ac8,0xcc313c7caa15d02af521,0x48c5d58a54954223970e,0x23065559cf2effaf5bd,0x5f8fa14a7c6eea65499a,0xa7f09e5c63c0762744bf,0x95b1dc0d0c0d96d0ea79,0xc08ef4f68798ed40f67c,0x3a4c5389745b7b492a77,0xd345032e12cf0c6f1f83],#[0xa0748983da32f465afc7,0x2ed6f53e7011c19201dd,0x20d0448fc30bd090b1f2,0xd9410581f03697f0cf00,0x50453b94c411b4d8858,0x23403cbb60335beaa511,0xee01c28bb2c8e3ad3219,0xd33ad4786c2e297fcd40,0x8c402816aa06a3ea59f1,0x1cb007ee62f0060e80b5,0x684e96450308e0831c30,0x853f3c0810722d0cc007,0x6e8e0f8cf32a6e800174,0x32dd124063e03c83c8af,0x40d943e600000b6a6888,0xb89eb319154507431523,0x9082a996bdffd09feeb4,0x8d1c827df4894c8205,0x818b2ce46e0e0e9f8317,0x34605327532832a20ac6,0xe9815cd3d68946f5d677,0xe7389750337e175593d2,0xf4c911879f7c82780a98,0xd00df02a7fff529cbdde,0x17834f0ef12285c7ebbb,0x74ba72d1ec49555781aa,0x2205e02be606fedc4ad1,0xf50c177a4bc74075840b,0x84fbf467c44e001dc618,0xb62aa66aba63bba6f460,0xed06fa350c5f27acc9cf,0xe84fd138e89ac0aee024]]
private def groupPage20 := limbs80 #[#[0x10e3c701e32d5a458249,0xf2124303864268b9ad68,0x7ad73511168323efe944,0x3f55a13131aa87aa4a8b,0xb692f996b337c41ae83d,0x9b536c8297d8a39aa440,0xb6b466e5415ce5e62c3e,0x51a8a008f385488e3c7,0xcd56d425e50bd01cb53e,0xf63fbe8400d3e23673bf,0x1adb36918c7ecce8e83d,0x98a058815462644897d6,0xa080fc43ad30c4779575,0xb6a29cbc8fa8a19c04bd,0xf419d4b1bf65b462439e,0x4b212cdb338165d8fd11,0xaab432e9349eeb6fbd8e,0x45f4542fe114fa646e5e,0x200406fd27c603250713,0x69b57e0fe1722028fb10,0x541443d3e86f846c81c4,0x565402603955d9528fe7,0xb2d37d490fd8d9c000a8,0x16da8c0119d98ba4528]]
def g63H9 := groupedPages #[groupPage19,groupPage20]
def g63D10 := limbs80 #[#[0x221a42188a628220207f,0x5a96651086098440106a,0x5a868190e842146398c6,0x2a64020e21a0ea7980a,0x61086490461080a29902,0xc442100043c8680098e8,0x6aed589c449e0cc55218,0x6218d04212003e9d8da6,0x4df6830d5a9f469e0d45,0x8ba4a1e0b0360d00405e,0x50c000c18010182431c,0x80338018a01858712304,0x19a80670033800ee8032,0xa001280198019a803b40,0x7003bd0064015c007002,0xcb401d402b9806400c,0x74015e0067e803200af5,0x300af80194028015ea80,0x660063003a00a0052007,0x19ea019f400e7401c00,0x38]]
def g63H10 := limbs80 #[#[0x84800030082c0c0c,0x402018080a000180c22,0x8040204020040700024,0x6824220100018020a010,0x488c02020001800070,0x1000160105060060,0x50e010000c000080,0x80468000880828020381,0x1780c0001058080c0f04,0x12800061b078102200,0xc010288c4408010000c,0x20080d000180a000a014,0x480c0201000100200000,0x3028b8460b0403834050,0x110e000025d0080c040,0x680209030040e0388c3,0x34d018010b806101802,0x1054364405000020102,0x9000980606058140000,0x261e000040c360292c03,0x780405020200a0301010,0x40180c00010140a1a158,0x40100042080191c08510,0x4000c9460000000020,0x634060081604000040,0x8c41a050708804430500,0x1c0202068c404000f,0xa048141e0000800dc06,0x2000c440001507806,0x420070280c003e06818,0xb00c080d000083619050,0x904c580701021e6090],#[0xfb9ffddf084d03058120,0xee3bdc24009001ffffff,0x76e9b036007fffff7cb5,0x9212803feffdf7ebce95,0xc00ffffffffbdda04df2,0xffffffffd16b74c6ae85,0xffffaffef6b82de1e003,0xe4d0bbd38c089400fffe,0xd3654b2e29802fffffff,0xb0d38c400feffff577ef,0x634805f7dfbdffa55629,0x15f6fffded96db69ab7,0xf07ffddbf03fed0e50ec,0x7febd3cf73ebba3f005b,0xfc539fa2f8904016ffdb,0x694dc0a44809ecfbdfbe,0xf0b92202dddefd5dc916,0x4d00ab97bdffeb86bdff,0x2fdc0e3fbf5c0e2abc4c,0x7fffffd4d75df11e9380,0xdf775ffa3749c5000b7f,0xff8edfb3015803dfffff,0xfffcea5a013f7ffffff2,0x4597a057dffffffdf6bf,0x817ffffffffefe9e2bf,0xffffffff9fb8c7f7d4c6,0xffffebd26d69b5e99405,0x79764f317da66a017fff,0xdf2bff729c405e767f7f,0x325ec750197ffe6ffef2,0x59e2073efdffb32fecaf,0x1f76ffffce777b6e4b8],#[0xf5ff9cf7357d98463a7c,0x9e3e29b9902f98200087,0x458d3db768284021fdfb,0x37a7a26086ffffefe,0x26be8f8240000003e000,0x76dad23f51205cfafc6c,0x614941a5573b9ca0263f,0xb3444a830d8d13d896f0,0xe258db8050c91150ff44,0x5047495c6364487a3a61,0xa90a11634eac6d461b19,0xa588b8b4024ba4ae11b2,0xe686df7d7620e731eb18,0xe1723f470047a896e1ec,0x9807db391d38b2195616,0x338232bd00fb03c0183,0x3172904213f5af7a7a5,0x71b10001992fe1cba82d,0x3fe1d668410f1ae60a20,0x3d1c78cee0cc9160ee34,0x60440d2070617d80ca96,0x35e1fe05f1e5038433d9,0xd0a3640313163d5c69da,0x503d000012800957ed04,0x2022541780ac158136de,0xf91bee987d0c5c48bb6,0xef897d64a7370f0b40cf,0x18f6b15f47f774018ff9,0x44d6c095a71aa8d89d4a,0xf6d77b95fb17c3d82452,0xc3912b9dcd978b6a0895,0x36c50ad4004bbb36c0e0],#[0x48c7f86e137dc1269604,0x4383e1007dc6005c6cf8,0x9a285d7135dc0b8958,0xd3b8d81056612518dc02,0x772b6b8c85dcc80f3056,0x304081bc0129411f50f5,0x5b6802db1b4c6b85145f,0xf49464cb842c7da3e80,0x4e8158e02c93cdb8c496,0x368]]
def g63D11 := limbs80 #[#[0x8103f]]
def g63H11 := limbs80 #[#[0x40d0e9102044040600,0x700079f42c0ff73ff7f0,0x91e301796dea609b782,0xe60176b4300062398cd]]
def g63L : Nat → Packing
  | 5 => (26,6,6,1245205,85,8,8192,g63D5)
  | 6 => (842,5,6,9503245,138,295437,8256,g63D6)
  | 7 => (3866,4,6,7341614,123,6427281,8401,g63D7)
  | 8 => (3660,3,6,2687683,106,13804178,8318,g63D8)
  | 9 => (867,2,6,786473,70,3551887,8255,g63D9)
  | 10 => (41,1,6,65537,0,168522,8206,g63D10)
  | 11 => (1,0,6,65537,0,4096,8194,g63D11)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => groupLookup 9 53 2 1 5 1 g63H6
  | 7 => groupLookup 281 929 9 2 10 3 g63H7
  | 8 => groupLookup 1289 4099 10 3 12 4 g63H8
  | 9 => groupLookup 1220 3881 10 3 12 5 g63H9
  | 10 => groupLookup 289 967 9 2 10 3 g63H10
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
def cubWitness : Array Nat := #[37699209382,8104412988,15671723836,8104347452,15217471879,37732772646,37699309116,15671628003,8104363836,64918461745,7701541511,8104313254,15150355209,28102430729,15151404553,23375349564,14312350362,22667372058,37699218598,41055435427,37766327078,28307886601,22768034970,28154811477,37766326950,12046590151,52970245692,8104333414,11929569446,22768033946,15150354953,22766732377,12048745557,12399296934,37699217574,11929462554,22768167994,37766417724,37699218086,8104321446,15151403529,15253772451,14077470234,14077420302,52735364668,15471284565,7701646652,14077486878,7701761340,37699218094,8104396604,9782453006,14196811875,9782085798,11929404046,37833435814,8104329638,64935180387,7869923994,14077421342,11929412238,7752171853,9782119996,49621899427,11929408141,37766479945,15285620745,37732863292,28104596529,14077404698,37766417468,37766310566,11929603644,37699308604,12399363900,8104354214,15150895885,15151470105,27200348814,22768107918,12399285353,22768176444,37699217446,37934190140,53209212442,37766401340,29109281422,37699308092,15150363275,48805319757,12399288742,33226363107,37766416700,8104396092,11929408589,8104412986,55202036387,7701561742,7870040892,7701569934,52970154150,32599183881,11929538108,14077421326,40921275441,15671707452,15219635607,12399298364,37833526332,11929502805,49336631637,7752730389,27857732721,37699215526,7735656846,9781928590,12250187889,55202035875,42128253575,9781920398,64851352881,37816749372,12248158729,22768043097,32152700017,12250071381,64918403235,15285628937,53037354300,7769211150,28104597041,37732772518,14312342170,11929411726,37766372913,7735705626,15219627797,40921217187,15150879241,28343031047,9782019157,28104480533,7735706778,37699275836,7769473037,7769473033,7701561417,37766472078,12398897291,11929436359,15151411851,28104481813,12399163531,63145792009,7701599765,12399155849,29432222217,28343146659,22667339290,28104480021,53309908122,32603919117,15219569031,22768168122,53209245210,28104595505,15219627285,14077569123,31498207305,22667505210,63145775625,37766471753,15186547079,28104596657,64935192870,40921275697,50124566919,63196127886,64918461489,28154973756,27200540220,58884903303,62873212441,14077158158,28171588629,46817370766,14077569318,58850816391,22701067580,37699284150,63145783947,41038761276,22700926106,23460467110,32599708169,14077603386,22768034842,15151403785,15151420173,65207838234,14381289813,15151470089,14077420046,22768175420,32603910795,11929412110,44619293454,65071490586,28104479765,28104613173,7735656718,64935192614,8155514684,44619343386,28070925717,15151536681,15251558791,28154811413,65191040277,64918469811,12250221372,32152633766,14077403918,15219560839,32706154887,63059809365,42262403185,29381911182,14077419790,48982418190,22768131633,64918404259,57827942727,32599716491,32603902473,41532535175,15151553325]
def cubTag (k i : Nat) : Nat :=
  match k with
  | 5 => cubWitness[((#[0,1,2,3,4,5,4,6,6,2,4,6,7,6,1,1,8,4,6,9,10,11,12,4,13,14] : Array Nat)[i-0]?.getD 0)]?.getD 0
  | 6 => cubWitness[((#[15,6,16,17,6,18,19,17,20,17,6,21,15,1,11,6,22,23,24,25,4,17,26,27,28,24,29,1,6,30,31,32,17,33,34,35,17,36,17,17,6,2,17,37,1,34,24,6,6,37,6,4,29,34,6,38,39,6,40,34,6,37,41,29,42,43,44,6,1,6,6,45,6,46,41,34,37,26,37,17,47,30,6,48,17,49,41,6,50,51,30,6,6,52,17,1,6,34,5,34,6,53,17,6,23,6,34,17,6,6,54,6,6,6,1,55,26,56,15,37,50,19,57,17,6,58,17,59,17,50,6,1,23,6,43,1,6,41,60,24,43,38,29,60,37,55,61,62,26,42,63,6,6,64,24,65,38,34,17,6,19,41,6,66,50,67,43,6,68,34,69,17,70,71,1,30,0,37,72,37,6,73,74,41,6,1,75,48,76,19,6,72,17,6,6,64,6,37,42,1,17,34,77,34,6,78,23,79,43,80,81,6,1,71,17,82,17,83,38,37,58,60,84,30,15,6,85,37,86,38,6,38,87,17,34,23,34,82,56,42,88,89,6,6,29,37,34,6,90,17,6,6,24,6,91,92,4,6,93,6,1,72,67,70,42,6,94,56,95,60,72,1,57,38,15,70,40,34,6,56,60,96,1,97,1,98,6,6,71,99,2,100,41,34,1,30,38,6,6,6,63,6,1,41,6,1,6,37,6,37,30,20,9,34,37,101,34,6,60,60,1,30,26,14,37,102,103,60,34,69,43,57,6,104,45,41,6,105,43,57,6,6,34,6,60,17,102,106,26,34,107,37,39,6,17,99,108,60,10,19,109,1,110,10,60,111,1,16,29,17,4,34,43,81,71,39,6,17,34,6,57,112,43,113,38,37,37,37,72,72,6,6,114,92,39,5,66,1,1,50,115,6,99,6,116,117,106,1,38,62,6,42,17,37,60,68,1,6,6,17,34,23,118,81,43,81,29,43,17,6,1,17,1,6,38,47,6,37,92,119,34,85,33,75,60,37,60,22,92,75,10,68,37,100,17,120,6,6,1,49,121,30,6,119,1,43,54,6,34,15,77,17,34,60,6,6,19,69,17,34,52,47,72,5,34,114,42,122,41,70,68,106,1,77,6,6,19,6,70,15,17,4,123,124,82,125,126,15,15,15,75,39,127,1,128,1,104,16,26,72,40,40,129,1,39,41,74,1,1,119,6,6,11,1,2,1,40,130,40,6,1,131,6,34,4,22,132,60,6,6,122,133,114,6,39,6,43,134,76,6,37,6,135,14,29,136,83,137,138,23,72,37,9,68,6,6,22,139,55,67,67,17,6,111,6,30,109,17,6,29,140,34,41,17,6,99,67,2,6,60,41,141,6,6,6,6,116,17,17,17,142,143,17,63,47,39,68,24,119,26,34,6,6,6,144,26,6,17,6,34,6,6,17,68,72,145,41,146,5,6,6,147,148,43,74,37,17,149,11,6,6,1,74,6,34,6,41,6,67,6,1,6,150,1,38,1,22,104,6,60,34,17,1,25,119,6,26,43,26,42,82,6,104,72,1,6,20,6,45,22,6,34,38,66,151,90,152,42,34,153,40,38,34,60,42,86,42,1,17,58,1,23,60,30,1,37,1,6,23,119,6,6,40,1,42,29,40,15,30,6,112,6,37,73,43,15,6,6,1,6,18,42,37,71,154,155,120,6,113,156,42,16,157,42,6,124,26,158,6,34,114,6,43,77,1,38,65,6,37,81] : Array Nat)[i-72]?.getD 0)]?.getD 0
  | 7 => cubWitness[((#[17,17,41,22,159,22,41,42,37,17,34,17,23,40,160,41,161,17,23,17,162,34,6,163,164,40,34,17,17,165,29,78,6,130,6,42,1,34,17,22,40,60,58,41,45,166,166,63,81,26,37,40,15,68,81,17,26,167,126,23,100,164,6,60,17,17,6,168,17,26,78,169,17,42,34,17,23,17,41,68,22,170,171,39,1,141,34,17,126,34,15,60,23,172,17,6,60,37,108,172,72,17,170,41,26,6,6,6,37,41,60,78,6,17,6,68,17,34,157,6,58,45,17,34,6,34,37,41,34,42,17,17,60,41,6,34,17,26,72,34,34,17,22,17,17,22,68,173,37,6,60,41,174,160,72,160,17,17,6,6,57,40,37,17,6,43,17,15,6,37,58,37,57,68,175,40,128,6,126,22,128,6,17,17,60,23,6,17,26,34,22,17,6,34,6,43,126,37,34,6,17,34,17,100,1,15,23,72,6,60,17,60,17,22,6,17,6,104,34,60,72,6,118,164,57,57,17,42,60,6,81,176,34,58,6,34,17,34,37,68,6,72,15,6,26,60,6,6,15,34,177,17,178,60,6,22,26,130,76,17,81,17,17,6,24,6,6,60,34,41,17,6,43,6,179,60,34,41,6,6,41,60,37,17,6,26,17,60,40,60,100,58,34,17,6,180,6,181,6,164,17,159,26,60,30,182,60,60,17,5,6,26,6,6,26,22,6,37,60,60,17,40,17,34,42,34,26,17,81,22,17,42,82,17,17,17,6,183,184,6,60,17,34,60,43,26,22,185,186,181,17,37,187,17,34,40,6,82,34,17,6,162,26,6,5,17,6,17,23,41,6,40,15,26,6,159,43,100,188,34,17,100,15,6,42,37,68,6,37,37,60,6,41,100,37,37,6,162,17,6,34,150,4,22,57,6,17,34,23,42,6,6,42,34,17,43,6,6,17,41,34,34,17,17,162,22,6,6,15,100,180,141,40,164,60,43,17,34,17,41,138,17,189,130,34,41,60,60,6,26,42,41,6,23,34,72,69,26,37,26,120,29,160,6,9,41,26,17,6,60,57,6,60,41,23,42,60,16,17,41,34,43,42,58,190,22,6,106,26,29,40,26,6,15,22,137,17,126,34,26,150,6,81,6,138,22,17,37,22,41,17,26,29,22,47,184,60,17,42,37,126,6,178,37,43,180,6,58,42,17,72,17,37,6,6,17,17,26,6,37,17,37,37,37,37,60,22,17,128,72,17,22,81,6,6,15,17,57,60,22,41,6,126,17,6,22,6,191,34,34,22,137,170,60,41,17,6,164,192,17,17,193,26,17,128,34,42,42,17,159,6,23,6,68,6,6,1,34,17,34,68,58,26,162,34,17,26,37,17,178,41,6,17,34,194,195,6,40,72,57,22,26,17,196,6,17,17,34,17,60,81,17,15,17,6,26,34,17,164,60,41,26,100,15,34,6,100,34,136,17,17,26,137,34,37,26,43,60,159,164,6,189,26,41,41,137,26,26,6,180,37,34,161,178,6,197,26,160,10,47,177,47,26,41,126,34,198,34,199,23,17,200,37,167,37,188,72,6,41,23,26,6,104,6,17,201,6,100,6,115,168,6,34,37,34,72,78,17,106,1,41,17,42,17,68,6,22,17,34,60,202,41,17,47,37,26,167,26,196,100,203,17,34,22,6,26,17,81,17,164,6,17,17,17,162,17,60,104,22,204,6,6,34,160,22,17,40,17,205,37,206,17,34,37,43,6,6,17,82,207,6,60,208,23,37,17,29,41,17,17,68,128,72,17,163,159,37,22,30,195,34,67,34,141,72,6,57,126,6,17,15,150,82,22,17,199,6,40,17,42,34,163,34,41,41,34,34,37,60,43,5,126,6,6,6,29,34,6,22,41,34,34,174,6,197,6,60,37,17,37,6,130,209,60,6,42,34,23,6,178,15,6,6,15,210,40,133,17,17,40,22,72,34,6,17,211,60,6,176,5,17,17,100,126,100,17,34,159,22,23,68,6,26,6,160,26,22,43,6,17,6,17,190,6,40,212,17,37,72,17,43,57,34,6,6,34,22,34,100,17,34,23,17,34,41,17,178,72,15,17,174,34,6,40,17,15,6,34,30,37,34,159,34,26,100,34,17,40,6,9,164,29,174,26,26,47,169,17,60,6,22,43,23,34,213,37,34,100,214,34,9,37,37,17,6,60,34,6,34,157,42,157,17,6,42,41,215,137,34,23,17,47,43,57,6,60,40,6,17,68,22,136,37,17,58,17,17,6,189,17,17,41,159,170,60,22,37,60,100,17,34,6,60,17,68,60,6,17,164,57,72,72,191,82,72,22,106,190,34,6,37,26,6,17,17,23,163,17,6,22,212,15,22,15,1,216,15,6,160,26,17,34,68,34,34,17,217,34,47,72,6,6,23,6,178,6,6,23,16,170,41,178,17,81,17,26,17,6,156,6,17,166,17,180,6,164,60,6,165,218,163,43,17,37,22,17,6,37,23,34,15,17,163,160,120,6,6,60,26,34,6,34,169,73,6,34,26,104,43,6,157,17,112,17,60,22,104,219,17,82,6,34,34,68,17,17,39,22,6,73,17,22,17,34,6,22,72,218,22,164,15,68,23,15,57,58,17,128,23,17,34,6,6,17,126,197,6,100,34,43,34,17,164,17,6,17,157,161,100,169,220,6,34,17,37,126,37,17,150,34,26,221,6,6,26,43,60,6,6,191,6,34,81,60,17,130,34,41,6,81,17,6,34,22,40,1,115,42,156,17,6,72,34,6,41,34,17,37,6,6,6,43,17,68,34,26,222,34,43,169,40,42,204,6,34,100,17,17,37,22,191,22,17,6,17,41,42,106,17,126,34,26,60,6,166,57,6,60,37,17,17,6,72,17,23,34,17,15,17,60,6,178,58,60,15,174,43,223,26,34,34,17,6,126,15,26,34,34,34,60,57,6,17,34,68,6,23,60,6,17,164,17,6,206,15,41,24,138,6,40,218,60,15,197,23,10,23,15,15,72,72,72,39,60,6,6,159,37,57,26,6,17,22,17,163,81,34,26,34,34,43,17,81,202,57,17,34,34,100,39,106,170,6,100,41,157,160,34,17,159,42,82,214,41,26,43,100,6,6,37,34,15,81,34,34,224,34,172,178,9,6,41,37,170,164,34,34,6,50,60,6,17,57,68,6,17,42,6,6,6,34,22,17,22,6,6,72,167,175,183,34,17,81,199,34,34,68,22,128,60,225,104,58,164,26,126,6,23,9,68,226,37,37,169,37,179,40,22,42,68,82,34,34,6,82,104,138,17,37,126,159,6,6,6,17,6,37,34,17,6,34,34,6,17,34,6,164,37,6,41,17,6,37,22,183,100,6,17,17,37,120,77,60,17,17,17,17,41,34,17,39,60,34,34,17,17,6,17,213,160,34,137,22,6,6,37,6,166,41,159,128,218,34,189,60,150,126,17,6,60,17,17,157,17,43,6,128,6,17,17,42,17,37,17,178,6,165,26,17,6,17,17,23,34,17,37,17,39,178,37,6,60,6,37,17,34,17,17,164,34,60,22,34,6,42,6,34,23,17,17,34,17,189,17,34,26,22,22,17,104,17,34,22,43,6,37,41,6,34,6,6,41,17,34,17,34,37,15,37,29,22,42,43,17,17,100,22,37,109,60,41,17,37,43,34,6,6,41,100,227,60,6,34,22,34,37,57,175,41,60,43,60,166,37,159,6,17,159,6,15,34,34,34,15,6,189,60,17,42,6,26,29,6,22,40,82,6,195,164,23,26,17,6,34,29,43,60,164,22,37,6,34,60,37,43,22,34,228,160,137,229,96,100,41,23,6,17,58,60,26,159,63,82,34,26,45,159,17,43,57,17,60,40,60,82,17,60,23,17,230,34,29,190,175,29,34,17,6,6,34,60,22,22,40,6,17,6,60,43,45,6,68,34,17,17,126,41,17,17,212,162,57,126,6,6,37,34,6,60,6,17,34,6,172,17,15,22,60,6,17,60,41,26,6,17,41,17,26,17,81,26,60,60,69,37,34,17,26,60,26,231,68,60,197,162,6,34,60,104,100,68,60,34,17,15,6,6,60,6,161,34,57,39,6,232,34,34,41,17,6,126,6,6,60,6,17,170,60,72,73,41,81,22,137,43,81,23,160,126,156,41,23,42,196,233,22,60,34,6,100,60,23,6,34,34,159,22,6,17,104,41,6,6,6,68,26,17,22,6,9,106,34,199,17,34,6,57,17,23,34,105,42,34,60,34,17,6,68,43,60,234,17,220,22,17,37,37,26,60,96,37,164,100,40,57,191,17,34,17,34,26,72,37,159,206,96,24,57,126,34,186,43,6,123,37,17,159,6,26,6,126,39,6,17,60,137,81,34,104,17,34,17,163,209,17,175,24,68,164,17,206,100,6,17,17,164,37,72,34,42,43,197,17,162,100,26,37,17,42,26,17,57,60,22,17,17,43,34,17,42,17,15,72,6,37,17,17,60,23,41,68,68,6,26,6,29,26,164,43,128,169,6,34,179,15,15,6,235,17,57,42,6,43,6,175,6,68,180,37,22,43,6,41,81,26,81,17,6,60,41,39,26,6,43,1,43,6,17,22,29,17,172,26,6,6,37,17,22,68,128,23,37,60,17,6,17,159,22,22,68,195,78,160,6,181,34,37,160,29,17,6,60,23,34,34,177,68,34,60,17,43,42,6,69,100,60,60,6,230,17,15,68,34,23,17,17,23,17,17,1,202,42,43,6,17,15,60,68,6,17,72,40,17,24,68,100,17,23,17,22,42,160,34,179,17,17,236,17,6,60,42,34,6,43,72,23,1,34,164,17,166,17,187,37,22,17,6,26,6,34,60,43,34,58,100,17,42,164,6,40,72,6,17,164,37,58,41,26,37,37,34,37,26,23,60,17,26,60,23,17,159,34,6,17,15,17,17,174,6,78,9,43,17,29,60,157,6,218,37,126,128,6,43,39,60,34,34,15,130,6,17,17,17,6,29,34,126,60,58,126,34,100,39,42,60,37,175,34,60,6,37,17,206,37,17,34,17,37,206,57,22,22,41,157,6,42,6,42,60,6,26,34,6,37,6,126,68,136,6,40,23,157,17,6,41,37,161,42,128,37,40,22,60,6,58,92,6,43,17,34,22,22,40,6,34,6,34] : Array Nat)[i-1569]?.getD 0)]?.getD 0
  | 8 => cubWitness[((#[6,128,17,23,17,164,190,190,34,191,23,164,128,60,23,17,128,23,177,23,68,181,26,164,6,26,128,17,34,164,22,17,34,37,181,26,34,164,22,34,34,17,23,128,23,17,17,181,164,34,34,26,26,6,57,181,23,60,22,164,34,17,178,179,164,164,190,17,164,34,164,60,23,22,190,26,174,57,190,23,177,60,26,26,218,57,34,68,34,43,164,34,191,26,34,164,164,160,177,164,181,68,190,23,6,26,22,26,179,23,23,218,160,164,17,37,57,26,22,17,68,17,81,81,6,164,34,23,23,34,57,34,26,164,34,68,34,34,17,34,34,22,164,23,23,57,34,6,37,178,23,17,164,26,37,164,128,160,190,218,34,17,26,34,22,178,22,177,26,164,23,26,164,60,17,57,23,26,160,23,128,43,22,57,26,22,164,164,23,34,128,26,164,17,68,164,43,17,128,26,179,164,23,178,34,26,57,26,23,17,23,68,22,23,34,17,137,6,181,17,57,34,23,17,190,164,199,190,164,179,6,37,17,6,26,34,34,17,23,26,34,57,34,23,68,17,26,26,17,17,22,34,17,22,164,174,34,37,178,57,81,26,34,17,17,17,23,128,22,68,128,43,22,17,137,81,17,26,23,23,26,17,17,181,17,164,60,179,174,34] : Array Nat)[i-3370]?.getD 0)]?.getD 0
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
theorem crossP6_72 : spanOK g63 6 72 256 := by
  apply spanSix
  decide +kernel
end PEqualNP.Outside.L_meta_43236
