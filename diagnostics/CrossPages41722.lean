import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The truth table, restrictions and search certificates below are instance-specific.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_41722
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
def graph : Sig := (bitLimbs [0xfee8eaa8,0xeac8c888fee8eaa8eac8,0xc888fee8eaa8eac8c888,0xfee8eaa8eac8c888fee8,0xeaa8eac8c888fee8eaa8,0xeac8c888fee8eaa8eac8,0xc888fee8eaa8eac8c888])
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2 && x 3) || (x 1 && x 2 && x 4) || (x 0 && x 3 && x 4) || (x 0 && x 2 && x 5) || (x 0 && x 3 && x 5) || (x 1 && x 3 && x 4 && x 5) || (x 2 && x 3 && x 4 && x 5)
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
  if m=4147 then (x 1) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 4 &&& x 5) else
  if m=4139 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 3 &&& x 5) else
  if m=4135 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) else
  if m=4123 then (x 0) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) else
  if m=4119 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=4111 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=2110 then (x 1) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2109 then (x 0) ||| (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4 &&& x 5) else
  if m=2108 then (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2107 then (x 0 &&& x 1) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=2103 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 4 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=2099 then (x 0 &&& x 1) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) else
  if m=2095 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 2 &&& x 5) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=2087 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 5) else
  if m=2079 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2077 then (x 0) ||| (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 1) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) else
  if m=2071 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) else
  if m=2063 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) else
  if m=60 then (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4 &&& x 5) else
  if m=58 then (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4 &&& x 5) else
  if m=57 then (x 0 &&& x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=54 then (x 1 &&& x 2) ||| (x 1 &&& x 4 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=53 then (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 4 &&& x 5) else
  if m=49 then (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 4 &&& x 5) else
  if m=46 then (x 1 &&& x 2) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=45 then (x 0 &&& x 3) ||| (x 0 &&& x 2 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=43 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=41 then (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 3 &&& x 5) else
  if m=39 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 2 &&& x 5) else
  if m=38 then (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) else
  if m=30 then (x 1 &&& x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=29 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3 &&& x 4) else
  if m=28 then (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=27 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3 &&& x 4) else
  if m=26 then (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) else
  if m=23 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2 &&& x 4) else
  if m=22 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=15 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2 &&& x 3) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=13 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=11 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  if m=7 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) else
  (x 0 &&& x 1) ||| (x 1 &&& x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 0 &&& x 2 &&& x 5) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 4 &&& x 5) ||| (x 2 &&& x 3 &&& x 4 &&& x 5)
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
  if m=4147 then (x 1) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 4 &&& x 5) else
  if m=4139 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 3 &&& x 5) else
  if m=4135 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) else
  if m=4123 then (x 0) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) else
  if m=4119 then (x 0) ||| (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=4111 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=2110 then (x 1) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2109 then (x 0) ||| (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4 &&& x 5) else
  if m=2108 then (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2107 then (x 0 &&& x 1) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=2103 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 4 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=2099 then (x 0 &&& x 1) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) else
  if m=2095 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 2 &&& x 5) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=2087 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 5) else
  if m=2079 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2077 then (x 0) ||| (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 1) ||| (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) else
  if m=2071 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) else
  if m=2063 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) else
  if m=60 then (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4 &&& x 5) else
  if m=58 then (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4 &&& x 5) else
  if m=57 then (x 0 &&& x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 3 &&& x 4 &&& x 5) else
  if m=54 then (x 1 &&& x 2) ||| (x 1 &&& x 4 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=53 then (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 4 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 4 &&& x 5) else
  if m=49 then (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 4 &&& x 5) else
  if m=46 then (x 1 &&& x 2) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=45 then (x 0 &&& x 3) ||| (x 0 &&& x 2 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) else
  if m=43 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=41 then (x 0 &&& x 3) ||| (x 0 &&& x 5) ||| (x 3 &&& x 5) else
  if m=39 then (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 0 &&& x 2 &&& x 5) else
  if m=38 then (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) else
  if m=30 then (x 1 &&& x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=29 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3 &&& x 4) else
  if m=28 then (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=27 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3 &&& x 4) else
  if m=26 then (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) else
  if m=23 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2 &&& x 4) else
  if m=22 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=15 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 2 &&& x 3) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=13 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=11 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  if m=7 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) else
  (x 0 &&& x 1) ||| (x 1 &&& x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 0 &&& x 2 &&& x 5) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 4 &&& x 5) ||| (x 2 &&& x 3 &&& x 4 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases h0 : m=4147
  · simp only [graphGoal,liftGoal,if_pos h0,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h1 : m=4139
  · simp only [graphGoal,liftGoal,if_neg h0,if_pos h1,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h2 : m=4135
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_pos h2,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h3 : m=4123
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_pos h3,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h4 : m=4119
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h5 : m=4111
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h6 : m=2110
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h7 : m=2109
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_pos h7,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h8 : m=2108
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_pos h8,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h9 : m=2107
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_pos h9,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h10 : m=2103
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_pos h10,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h11 : m=2099
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_pos h11,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h12 : m=2095
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_pos h12,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h13 : m=2087
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_pos h13,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h14 : m=2079
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_pos h14,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h15 : m=2077
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_pos h15,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h16 : m=2075
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_pos h16,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h17 : m=2071
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_pos h17,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h18 : m=2063
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_pos h18,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h19 : m=60
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_pos h19,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h20 : m=58
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_pos h20,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h21 : m=57
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_pos h21,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h22 : m=54
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_pos h22,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h23 : m=53
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_pos h23,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h24 : m=51
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_pos h24,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h25 : m=49
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_pos h25,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h26 : m=46
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_pos h26,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h27 : m=45
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_pos h27,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h28 : m=43
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_pos h28,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h29 : m=41
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_pos h29,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h30 : m=39
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_pos h30,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h31 : m=38
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_pos h31,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h32 : m=30
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_pos h32,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h33 : m=29
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_pos h33,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h34 : m=28
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_pos h34,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h35 : m=27
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_pos h35,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h36 : m=26
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_pos h36,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h37 : m=23
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_pos h37,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h38 : m=22
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_neg h37,if_pos h38,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h39 : m=15
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_neg h37,if_neg h38,if_pos h39,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h40 : m=14
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_neg h37,if_neg h38,if_neg h39,if_pos h40,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h41 : m=13
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_neg h37,if_neg h38,if_neg h39,if_neg h40,if_pos h41,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h42 : m=11
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_neg h37,if_neg h38,if_neg h39,if_neg h40,if_neg h41,if_pos h42,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide)]
  by_cases h43 : m=7
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_neg h37,if_neg h38,if_neg h39,if_neg h40,if_neg h41,if_neg h42,if_pos h43,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide)]
  simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_neg h37,if_neg h38,if_neg h39,if_neg h40,if_neg h41,if_neg h42,if_neg h43,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
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

def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/80
  let shift := pos % 80
  let lo := word i >>> shift
  if shift+len ≤ 80 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (80-shift))) &&& ((1 <<< len)-1)


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
  if marker<1024 then
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



def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276677288 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[⟨.and,[3,4]⟩,⟨.or,[3,4]⟩,⟨.and,[7,2]⟩,⟨.and,[5,6]⟩,⟨.and,[8,1]⟩,⟨.or,[6,5]⟩,⟨.or,[0,10]⟩,⟨.or,[12,9]⟩,⟨.and,[3,12]⟩,⟨.or,[14,2]⟩,⟨.and,[15,11]⟩,⟨.or,[1,16]⟩,⟨.and,[17,13]⟩], 18⟩
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

def lowRow (i : Fin 6) : Row := Fin.ofNat 512 (([2, 1, 10, 6, 6, 5] : List Nat).getD i.val 0)
def highRow (i : Fin 6) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (([2, 1, 10, 6, 6, 5] : List Nat).getD i.val 0))

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

def g7Y : Array (Bits × Bits) := #[((bitLimbs [0xb5dfb5dfb5dfb5dfb5,0xdfb5dfb5dfb5dfb5dfb5]),(bitLimbs [0x942094209420942094,0x20942094209420942094])),((bitLimbs [0xeeeeeeeeeeeeeeeeee,0xeeeeeeeeeeeeeeeeeeee]),(bitLimbs [0x281228122812281228,0x12281228122812281228])),((bitLimbs [0xdb7bdb7bdb7bdb7bdb,0x7bdb7bdb7bdb7bdb7bdb]),(bitLimbs [0x38803880388038803,0x88038803880388038803])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g7C : List ColumnInfo := []
def g7A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g7D3 (j : Nat) := if j=0 then 0x7 else 0
def g7L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g7D3)
  | _ => emptyPacking
def g7I (_ _ : Nat) : Option (Nat × Nat) := none
def g7 : Forest := ⟨7,3,fun i => g7Y[i]?.getD (0,0),g7C,g7A,g7L,g7I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7P3_0 : block g7 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g7B3 : block g7 3 0 1=true := g7P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7T : checkedTables g7 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g7 0 0 0 = true)
  · exact (rfl : block g7 1 0 0 = true)
  · exact (rfl : block g7 2 0 0 = true)
  · exact g7B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g7G : graphValid g7 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low7 : Lower true (varsX 7) (graphGoal 7) 4 := lower_forest (g:=g7) (i:=0) (hints:=262658) (before_sound [] baseKnown) g7G g7T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K7 := extendKnown [] 4 [(7,[]),(11,[50]),(13,[33,49]),(14,[16,32,48]),(22,[16,32,64,48]),(26,[16,48,66]),(28,[32,49,64,16]),(38,[16,32,80,48,67]),(41,[49,82,66]),(49,[65,82,49,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[((bitLimbs [0xdefdfcf7fefffffede,0xfdfcf7fefffffedefdfc]),(bitLimbs [0x880848080000400888,0x8480800004008880848])),((bitLimbs [0x6f4e177c79577eab6f,0x4e177c79577eab6f4e17]),(bitLimbs [0x41c61683e6220c9241,0xc61683e6220c9241c616])),((bitLimbs [0xa9b78bcded7ccf27a9,0xb78bcded7ccf27a9b78b]),(bitLimbs [0x10d781320c92362510,0xd781320c92362510d781])),((bitLimbs [0xf522e75b2feb5e5df5,0x22e75b2feb5e5df522e7]),(bitLimbs [0x3430a7a450709a9034,0x30a7a450709a903430a7])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := []
def g15A : List (List Nat) := [[],[50],[33],[33,49],[49,33],[49]]
private def g15D3Page0 : Array Nat := #[0x2b10910ae42042b50810,0x19d43887948421af4244,0x91e61230602790e2]
def g15D3 := limbs80 #[g15D3Page0]
private def g15D4Page0 : Array Nat := #[0xfc21fe21f843e887c10,0x48f30918301f887e9]
def g15D4 := limbs80 #[g15D4Page0]
private def g15H4Page0 : Array Nat := #[0x33000000100000,0x0,0xda0000000000b8,0xf200,0xf400,0x0,0x8600,0xe9,0x21000000250000000000,0x9b000000]
def g15H4 := limbs80 #[g15H4Page0]
def g15D5 (j : Nat) := if j=0 then 0xf else 0
private def g15H5Page0 : Array Nat := #[0xc0028400f3010e4dd0f9,0xf41abbe04880020bc480,0x40b1a0544616e8,0x8000008e000008980000,0xb770d349dc0000047]
def g15H5 := limbs80 #[g15H5Page0]
def g15L : Nat → Packing
  | 3 => (7,2,1,0,0,6,0,g15D3)
  | 4 => (7,1,1,0,0,6,0,g15D4)
  | 5 => (1,0,1,0,0,0,0,g15D5)
  | _ => emptyPacking
def g15I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 2 97 0 8 3 1 g15H4
  | 5 => lookupWord 6 37 3 10 3 3 g15H5
  | _ => fun _ => none
def g15 : Forest := ⟨15,5,fun i => g15Y[i]?.getD (0,0),g15C,g15A,g15L,g15I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P3_0 : block g15 3 0 7=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B3 : block g15 3 0 7=true := g15P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P4_0 : block g15 4 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B4 : block g15 4 0 7=true := g15P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P5_0 : block g15 5 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B5 : block g15 5 0 1=true := g15P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15T : checkedTables g15 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact g15B3
  · exact g15B4
  · exact g15B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15G : graphValid g15 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 6 := lower_forest (g:=g15) (i:=0) (hints:=134480386) (before_sound K7 V7) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K7 6 [(15,[]),(51,[66,83]),(2075,[16,50,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g23Y : Array (Bits × Bits) := #[((bitLimbs [0xfe7faf77fffbbfbffc,0xff5eeffff77f7ff9febd]),(bitLimbs [0x28070c080040612850,0xe18100080c250a01c30])),((bitLimbs [0xa7b1d7bcdbfe6bff4f,0x63af79b7fcd7fe9ec75e]),(bitLimbs [0x8070d303550092d100,0xe1a606aa0125a201c34c])),((bitLimbs [0x5beef8dbb7cff7ccb7,0xddf1b76f9fef996fbbe3]),(bitLimbs [0x1350b0e442a08e0426,0xa161c885411c084d42c3])),(0x0,0x0),((bitLimbs [0xaba87d9d523df74357,0x50fb3aa47bee86aea1f6]),(bitLimbs [0x12ac6da2a9e8513225,0x58db4553d0a2644ab1b6])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g23C : List ColumnInfo := [(0,16,7,0,4)]
def g23A : List (List Nat) := [[],[33]]
def g23D4 (j : Nat) := if j=0 then 0x1f else 0
def g23L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g23D4)
  | _ => emptyPacking
def g23I (_ _ : Nat) : Option (Nat × Nat) := none
def g23 : Forest := ⟨23,4,fun i => g23Y[i]?.getD (0,0),g23C,g23A,g23L,g23I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23P4_0 : block g23 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g23B4 : block g23 4 0 1=true := g23P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23T : checkedTables g23 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g23 0 0 0 = true)
  · exact (rfl : block g23 1 0 0 = true)
  · exact (rfl : block g23 2 0 0 = true)
  · exact (rfl : block g23 3 0 0 = true)
  · exact g23B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g23G : graphValid g23 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low23 : Lower true (varsX 23) (graphGoal 23) 5 := lower_forest (g:=g23) (i:=0) (hints:=412317123074) (before_sound K15 V15) g23G g23T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K23 := extendKnown K15 5 [(23,[]),(27,[50]),(29,[33,49]),(39,[16,84]),(43,[50,84]),(53,[65,82,49,50]),(58,[16,48,66,82]),(60,[32,49,64,16,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V23 : Known true K23 := extend_ok (m:=23) V15 low23 (by decide +kernel)
def g30Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xf8ef9fedfdb7fff1df,0x3fdbfb6fffe3be7fb7f6]),(bitLimbs [0x272b10255c88124e56,0x204ab910249cac409572])),((bitLimbs [0x7fff6f7ff2eebcfffe,0xdeffe5dd79fffdbdffcb]),(bitLimbs [0x81c4284fa0d1070388,0x509f41a20e0710a13e83])),((bitLimbs [0xf79ffb9e6ffdf7ef3f,0xf73cdffbefde7fee79bf]),(bitLimbs [0x8c6583126b02a118cb,0x624d6054231960c49ac])),((bitLimbs [0xbf77fef79f5f6f7eef,0xfdef3ebedefddffbde7d]),(bitLimbs [0x1a824e809761903504,0x9d012ec3206a093a025d])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g30C : List ColumnInfo := [(0,2,28,0,4),(0,4,26,0,4),(0,8,22,0,4),(0,16,14,0,4)]
def g30A : List (List Nat) := [[],[67],[50],[50,66],[66,50],[66],[33],[33,67],[33,49],[33,49,65],[33,65,49],[33,65],[49,33],[49,33,66],[49],[49,65],[49,66],[49,66,33],[65,33,50],[65,33],[65,49],[65],[65,50,33],[65,50]]
private def g30D3Page0 : Array Nat := #[0x23ca621021e02108010,0x8028]
def g30D3 := limbs80 #[g30D3Page0]
private def g30D4Page0 : Array Nat := #[0x2f90810bc42043e08010,0x609085870]
def g30D4 := limbs80 #[g30D4Page0]
def g30H4 (j : Nat) := if j=0 then 0x3c0a else 0
def g30D5 (j : Nat) := if j=0 then 0xd1027c10 else 0
private def g30H5Page0 : Array Nat := #[0x8000000000000000002,0x102008e000000072b,0x1a60000000000,0x180000189c]
def g30H5 := limbs80 #[g30H5Page0]
def g30D6 (j : Nat) := if j=0 then 0x3904f else 0
private def g30H6Page0 : Array Nat := #[0xc4005c00000310000000,0x101,0x1956800000]
def g30H6 := limbs80 #[g30H6Page0]
def g30L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g30D3)
  | 4 => (3,2,2,0,0,5,0,g30D4)
  | 5 => (1,1,2,0,0,0,0,g30D5)
  | 6 => (1,0,2,0,0,0,0,g30D6)
  | _ => emptyPacking
def g30I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 3 0 5 1 0 g30H4
  | 5 => lookupWord 2 31 1 9 2 3 g30H5
  | 6 => lookupWord 1 23 0 9 0 5 g30H6
  | _ => fun _ => none
def g30 : Forest := ⟨30,6,fun i => g30Y[i]?.getD (0,0),g30C,g30A,g30L,g30I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30P3_0 : block g30 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g30B3 : block g30 3 0 2=true := g30P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30P4_0 : block g30 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g30B4 : block g30 4 0 3=true := g30P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30P5_0 : block g30 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g30B5 : block g30 5 0 1=true := g30P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30P6_0 : block g30 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g30B6 : block g30 6 0 1=true := g30P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30T : checkedTables g30 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g30 0 0 0 = true)
  · exact (rfl : block g30 1 0 0 = true)
  · exact (rfl : block g30 2 0 0 = true)
  · exact g30B3
  · exact g30B4
  · exact g30B5
  · exact g30B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30G : graphValid g30 (boundsBefore K23) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low30 : Lower true (varsX 30) (graphGoal 30) 7 := lower_forest (g:=g30) (i:=0) (hints:=413124794368) (before_sound K23 V23) g30G g30T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K30 := extendKnown K23 7 [(30,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V30 : Known true K30 := extend_ok (m:=30) V23 low30 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[((bitLimbs [0xff7b7d9fdfff1ffff7,0xb7d9fdfff1ffff7b7d9f]),(bitLimbs [0x364015162080a62364,0x15162080a6236401516])),(0x0,0x0),((bitLimbs [0xf5d6c3f56fb9f35f5d,0x6c3f56fb9f35f5d6c3f5]),(bitLimbs [0xe80652b590149cce80,0x652b590149cce80652b5])),((bitLimbs [0xbebffe7bbeeffefbeb,0xffe7bbeeffefbebffe7b]),(bitLimbs [0x88b80a49403c01188b,0x80a49403c01188b80a49])),(0x0,0x0),((bitLimbs [0xf1f6abe675b7e5ef1f,0x6abe675b7e5ef1f6abe6]),(bitLimbs [0x131aa9e28849338131,0xaa9e28849338131aa9e2])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := [(0,4,41,0,4)]
def g45A : List (List Nat) := [[],[82],[48],[48,82]]
def g45D4 (j : Nat) := if j=0 then 0x1f else 0
def g45L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g45D4)
  | _ => emptyPacking
def g45I (_ _ : Nat) : Option (Nat × Nat) := none
def g45 : Forest := ⟨45,4,fun i => g45Y[i]?.getD (0,0),g45C,g45A,g45L,g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P4_0 : block g45 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B4 : block g45 4 0 1=true := g45P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact (rfl : block g45 3 0 0 = true)
  · exact g45B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K30) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 5 := lower_forest (g:=g45) (i:=0) (hints:=175922003312648) (before_sound K30 V30) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K30 5 [(45,[]),(46,[16,50]),(54,[16,66,50]),(57,[50,82,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V30 low45 (by decide +kernel)
def g2063Y : Array (Bits × Bits) := #[((bitLimbs [0xbe66fcef77bdedfdbe,0x66fcef77bdedfdbe66fc]),(bitLimbs [0x12c660108049081112,0xc660108049081112c660])),((bitLimbs [0xdddf0ffbeadfff56dd,0xdf0ffbeadfff56dddf0f]),(bitLimbs [0x81080e071100312481,0x80e071100312481080e])),((bitLimbs [0x51bbc39fabf33e4f51,0xbbc39fabf33e4f51bbc3]),(bitLimbs [0x22d3c160a488cc4a22,0xd3c160a488cc4a22d3c1])),((bitLimbs [0xeb20f7b5bf2d6cbbeb,0x20f7b5bf2d6cbbeb20f7]),(bitLimbs [0x6830974a4382752068,0x30974a43827520683097])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2063C : List ColumnInfo := []
def g2063A : List (List Nat) := [[],[16,50]]
def g2063D3 (j : Nat) := if j=0 then 0xf else 0
def g2063L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g2063D3)
  | _ => emptyPacking
def g2063I (_ _ : Nat) : Option (Nat × Nat) := none
def g2063 : Forest := ⟨2063,3,fun i => g2063Y[i]?.getD (0,0),g2063C,g2063A,g2063L,g2063I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2063P3_0 : block g2063 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2063B3 : block g2063 3 0 1=true := g2063P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2063T : checkedTables g2063 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2063 0 0 0 = true)
  · exact (rfl : block g2063 1 0 0 = true)
  · exact (rfl : block g2063 2 0 0 = true)
  · exact g2063B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2063G : graphValid g2063 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2063 : Lower true (varsX 2063) (graphGoal 2063) 4 := lower_forest (g:=g2063) (i:=0) (hints:=134742530) (before_sound K45 V45) g2063G g2063T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2063 := extendKnown K45 4 [(2063,[]),(2071,[67]),(2087,[83,67]),(2099,[66,83]),(2108,[48,81,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2063 : Known true K2063 := extend_ok (m:=2063) V45 low2063 (by decide +kernel)
def g2077Y : Array (Bits × Bits) := #[((bitLimbs [0xc4ffcdee6badc4ffcd,0xee6badc4ffcdee6badc4]),0x0),(0x0,0x0),((bitLimbs [0xb8d5f2e59eb2b8d5f2,0xe59eb2b8d5f2e59eb2b8]),(bitLimbs [0x98240c128a0098240c,0x128a0098240c128a0098])),((bitLimbs [0x13772bb9b6c713772b,0xb9b6c713772bb9b6c713]),(bitLimbs [0x1889020108f018890,0x20108f01889020108f01])),((bitLimbs [0x6bed357dd8546bed35,0x7dd8546bed357dd8546b]),(bitLimbs [0x6213420d0100621342,0xd01006213420d010062])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2077C : List ColumnInfo := [(1,0,28,0,4)]
def g2077A : List (List Nat) := [[],[67],[50],[50,66],[66,50],[66]]
def g2077D4 (j : Nat) := if j=0 then 0x1f else 0
def g2077L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g2077D4)
  | _ => emptyPacking
def g2077I (_ _ : Nat) : Option (Nat × Nat) := none
def g2077 : Forest := ⟨2077,4,fun i => g2077Y[i]?.getD (0,0),g2077C,g2077A,g2077L,g2077I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2077P4_0 : block g2077 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2077B4 : block g2077 4 0 1=true := g2077P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2077T : checkedTables g2077 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2077 0 0 0 = true)
  · exact (rfl : block g2077 1 0 0 = true)
  · exact (rfl : block g2077 2 0 0 = true)
  · exact (rfl : block g2077 3 0 0 = true)
  · exact g2077B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2077G : graphValid g2077 (boundsBefore K2063) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2077 : Lower true (varsX 2077) (graphGoal 2077) 5 := lower_forest (g:=g2077) (i:=0) (hints:=275416875008) (before_sound K2063 V2063) g2077G g2077T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2077 := extendKnown K2063 5 [(2077,[]),(4119,[49,33]),(4123,[33]),(4135,[49,33,84]),(4139,[16,32,84]),(4147,[16,32,67,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2077 : Known true K2077 := extend_ok (m:=2077) V2063 low2077 (by decide +kernel)
def g4111Y : Array (Bits × Bits) := #[((bitLimbs [0x3f6997f9e86ed67ed3,0x2ff3d0ddacfda65fe7a1]),(bitLimbs [0x48800294810280910,0x52902050122000a520])),((bitLimbs [0xdf4e679d13fb6bbe9c,0xcf3a27f6d77d399e744f]),(bitLimbs [0x10041410c4d00020,0x8282189a00040105043])),((bitLimbs [0x56f6d97ec5bd74aded,0xb2fd8b7ae95bdb65fb16]),(bitLimbs [0xb80211008502017004,0x22010a0402e008440214])),((bitLimbs [0xf69b7ce63e36cfed36,0xf9cc7c6d9fda6df398f8]),(bitLimbs [0x32040c22209000640,0x81844412000c81030888])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g4111C : List ColumnInfo := [(1,0,14,0,4),(2,0,13,0,4),(4,0,11,0,4),(8,0,7,0,4)]
def g4111A : List (List Nat) := [[],[50],[33],[33,49],[49,33],[49],[16],[16,50],[16,32],[16,32,48],[16,48,32],[16,48],[32,16],[32,16,49],[32],[32,48],[32,49],[32,49,16],[48,16,33],[48,16],[48,32],[48],[48,33,16],[48,33]]
private def g4111D3Page0 : Array Nat := #[0x23ea6a1221e12148110,0x8028]
def g4111D3 := limbs80 #[g4111D3Page0]
private def g4111D4Page0 : Array Nat := #[0x2fd0910bd42443e48110,0x609085870]
def g4111D4 := limbs80 #[g4111D4Page0]
def g4111H4 (j : Nat) := if j=0 then 0x389 else 0
def g4111D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
private def g4111H5Page0 : Array Nat := #[0x2000000000000000138c,0x80c1801c00009401e,0x104003700000000000]
def g4111H5 := limbs80 #[g4111H5Page0]
def g4111D6 (j : Nat) := if j=0 then 0x3904f else 0
private def g4111H6Page0 : Array Nat := #[0xb0940024000c15a80000,0xf200000000000001]
def g4111H6 := limbs80 #[g4111H6Page0]
def g4111L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g4111D3)
  | 4 => (3,2,2,0,0,5,0,g4111D4)
  | 5 => (1,1,2,0,0,0,0,g4111D5)
  | 6 => (1,0,2,0,0,0,0,g4111D6)
  | _ => emptyPacking
def g4111I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g4111H4
  | 5 => lookupWord 2 31 2 9 2 3 g4111H5
  | 6 => lookupWord 1 17 0 9 0 5 g4111H6
  | _ => fun _ => none
def g4111 : Forest := ⟨4111,6,fun i => g4111Y[i]?.getD (0,0),g4111C,g4111A,g4111L,g4111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4111P3_0 : block g4111 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g4111B3 : block g4111 3 0 2=true := g4111P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4111P4_0 : block g4111 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g4111B4 : block g4111 4 0 3=true := g4111P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4111P5_0 : block g4111 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g4111B5 : block g4111 5 0 1=true := g4111P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4111P6_0 : block g4111 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g4111B6 : block g4111 6 0 1=true := g4111P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4111T : checkedTables g4111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g4111 0 0 0 = true)
  · exact (rfl : block g4111 1 0 0 = true)
  · exact (rfl : block g4111 2 0 0 = true)
  · exact g4111B3
  · exact g4111B4
  · exact g4111B5
  · exact g4111B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4111G : graphValid g4111 (boundsBefore K2077) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low4111 : Lower true (varsX 4111) (graphGoal 4111) 7 := lower_forest (g:=g4111) (i:=0) (hints:=134480386) (before_sound K2077 V2077) g4111G g4111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K4111 := extendKnown K2077 7 [(4111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V4111 : Known true K4111 := extend_ok (m:=4111) V2077 low4111 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((bitLimbs [0xfa5bffb7edbfb2dbf5,0xc8ddeefdfbff9ff4ad77]),(bitLimbs [0x9c1012dbb22ac104,0xe4c800e10be986d40c47])),((bitLimbs [0xefff7efff7ffefffde,0xff7f73aefddf6efb7bfc]),(bitLimbs [0xf8010480000d443e52,0x103476065012002a31b8])),((bitLimbs [0x97e71bda5e6d5f347e,0xf7aed15a2f466f9b56da]),(bitLimbs [0x69ac96fc68a089129,0x651e814a2d25cf995652])),((bitLimbs [0x3293e5fad85cfa3ce9,0xf3cbfe7b0e3db17d86ab]),(bitLimbs [0xdc33c82031468440eb,0xb283743c4935717186a9])),((bitLimbs [0x9db7cf516bb9550fb3,0x46a6fdff8e68dd27dd4b]),(bitLimbs [0xf0ac5a1b2444b10d9b,0x5600cc1c96d8cb27c94a])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,4,2075,0,6)]
def g31A : List (List Nat) := [[],[67]]
def g31D6 (j : Nat) := if j=0 then 0x3f else 0
def g31L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g31D6)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,6,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 1=true := g31P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact (rfl : block g31 5 0 0 = true)
  · exact g31B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K4111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 7 := lower_forest (g:=g31) (i:=0) (hints:=413124788738) (before_sound K4111 V4111) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K4111 7 [(31,[]),(47,[16,82,50,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V4111 low31 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((bitLimbs [0xd3f77fbebfbefeff7f,0xe45b7fefefffbedad9ff]),(bitLimbs [0xb5c2300802400b3c16,0xe06031220ac0aa9851b1])),((bitLimbs [0xfedfbfe9f7ffbffff8,0x7bedebbf7ffff5a7e7fe]),(bitLimbs [0x2000b640d3b5041c8,0x19014a8dd41d4407a44e])),((bitLimbs [0xffaac477cef97583ff,0xffb6d4f3b88bcb7d7e2b]),(bitLimbs [0xca186189a4cacca6c,0x4ab294eae84341786e2a])),(0x0,0x0),((bitLimbs [0x6e1ce57d6b4db3339d,0xdbf5a27134e157f5f704]),(bitLimbs [0x75e41ca4c026ad2791,0x80b4b63732f01cf5d304])),((bitLimbs [0x55b3d4d7cfaad3409f,0xa7d77fe5eb025adcbac3]),(bitLimbs [0xd8556ba588b1f1a059,0x2f45c445f3063ec4bac3])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(0,16,39,0,5)]
def g55A : List (List Nat) := [[],[16,84]]
def g55D5 (j : Nat) := if j=0 then 0x3f else 0
def g55L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g55D5)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,5,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P5_0 : block g55 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B5 : block g55 5 0 1=true := g55P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact (rfl : block g55 4 0 0 = true)
  · exact g55B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 6 := lower_forest (g:=g55) (i:=0) (hints:=176334182023682) (before_sound K31 V31) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K31 6 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V31 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((bitLimbs [0xffffbfefd7ffffbfdf,0xfc7bffffffffbff5dbff]),(bitLimbs [0xa9411402004040cf05,0xb84022002d08aa9413b1])),((bitLimbs [0x3acbd7fa3effaffffe,0x1bcd775efbf7f48be77e]),(bitLimbs [0x2a00ad981ae961072,0x121555f90b5440be04e])),(0x0,0x0),((bitLimbs [0xffb5691df9de5d60ff,0xffb6c9e7651bcb7e7cab]),(bitLimbs [0x4b0c18693432b329b,0x12b289d5e083416c6caa])),((bitLimbs [0x962e795fad636ccce7,0x73f5a4e255c957faf684]),(bitLimbs [0x59f20f291809ab49e4,0x60b4ac6e49e81cfad604])),((bitLimbs [0xd9b9e53579fab4d027,0xefd77fcbea025acebd43]),(bitLimbs [0x7c4ab2e9311c7c6816,0x4f45c88bca0e3ec2bd43])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,8,51,0,6),(0,16,43,0,5),(0,32,27,0,5),(0,48,11,0,4)]
def g59A : List (List Nat) := [[],[84]]
private def g59D3Page0 : Array Nat := #[0xc629221831906394810,0xc30632]
def g59D3 := limbs80 #[g59D3Page0]
private def g59D4Page0 : Array Nat := #[0x9ed9510042e86244010,0x10b518d10042e4624401,0x810ad993310427765440,0x4810d394e520434d5394,0x14c10d3d8e520434c639,0x414c109798c530426e62,0x5494c10c7951530423e6,0x45384110d914a104431e,0x4c5314910da14b104435,0x34c6314910d3d4c52443,0x431c5414d10d3d8c5244,0x4426e6294d10c7d50534,0x8423e6494d109798e53,0x51842b664cc6109b98a5,0x253c423e6414e109b189,0x9251cc26e62947308f99,0x191500c66c62540318f9,0x302a241e18120c06008f,0x6c66605a544e48423c36,0xa8a29c96908a847e7872,0xd2ccc6c0bab4ae]
def g59D4 := limbs80 #[g59D4Page0]
def g59H4 (j : Nat) := if j=0 then 0x1110000 else 0
private def g59D5Page0 : Array Nat := #[0x6c52442bca6085b94810,0x7ca998cf95030ae29a21,0xe84010fa88021f910042,0xa188217e50043ee20087,0xe52042fca2087dcc410f,0xca6087754c10be29821e,0xc4110fb082217e53043b,0x29a21dc53443d8a4887e,0x10843bea6885f94d10be,0x63085f94210fb88421fb,0x4e10bea8c21f731843e8,0x9e217c53c42fca7085f1,0x10c3b8621877cc030bf2,0x3986f95030bf288617d5,0x31bf28e617d51cc3be6,0x663df310c6fca018df54,0x37ca998df94331bea8,0x251007434150802c1003,0xa84d230fc7437190b454,0x4fc77381b4cc612e15c,0x72a54ca34f255208d422,0xd6a33594c5602f574b55,0x1c040c040ef7639dc0d,0x10041104000401000c07,0x40100401c08f0220080,0x84030003c08802007020,0x802204000812100c4100,0x84032008060481000a06,0x204010580200]
def g59D5 := limbs80 #[g59D5Page0]
private def g59H5Page0 : Array Nat := #[0xa010a282,0x1641cc00000000000,0x30b1427400000,0x2828005aa000000000,0x1dda60000000052a,0xa0000000000000000032,0x107c0000079a0002,0x82665d4754b000000000,0x800000522f380008f319,0x759c1,0x304f04002c90000000,0x6ae00108800000748,0x83400000a0fe6c00,0x600000300d02e20e480,0x24b0000016288a0005,0x83dcd509d86,0x2a308c00,0x486e8e0000]
def g59H5 := limbs80 #[g59H5Page0]
private def g59D6Page0 : Array Nat := #[0xfc30ff10fe10fd10fc10,0x36241200ff31fc31ff30,0x8044601118048d755d48,0xcf2300cd1805460111,0x1a300af23]
def g59D6 := limbs80 #[g59D6Page0]
private def g59H6Page0 : Array Nat := #[0x431290006400e8500380,0x5b8c54fc1e05b78001c6,0x30ce26e492c20c3940c,0x52f92a22e2e51b1cbba0,0xf8dc9f764823a19a2003,0x311e0038f390237d3295,0xa49c00496000ab00069,0x1050d7001e1fec1aaa,0x80000053b45ce9000000,0x185497c0800175,0xd96824000aef440000,0x1350c5c046093f60f140,0x1a1b96ec3001e300008e,0x13846800124]
def g59H6 := limbs80 #[g59H6Page0]
def g59D7 (j : Nat) := if j=0 then 0x7209f else 0
private def g59H7Page0 : Array Nat := #[0x600000000000000,0xe000000000000000000,0x54,0x0,0xc00,0x3700a00000a300000000,0x75000000b2000000,0xfd000000000000710000,0xff00000000]
def g59H7 := limbs80 #[g59H7Page0]
def g59L : Nat → Packing
  | 3 => (2,4,2,0,0,3,0,g59D3)
  | 4 => (36,3,2,0,0,8,0,g59D4)
  | 5 => (50,2,2,0,0,9,0,g59D5)
  | 6 => (8,1,2,0,0,8,0,g59D6)
  | 7 => (1,0,2,0,0,0,0,g59D7)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 7 0 5 1 0 g59H4
  | 5 => lookupWord 12 127 2 11 6 1 g59H5
  | 6 => lookupWord 17 89 6 11 6 1 g59H6
  | 7 => lookupWord 3 101 0 8 3 1 g59H7
  | _ => fun _ => none
def g59 : Forest := ⟨59,7,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P3_0 : block g59 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B3 : block g59 3 0 2=true := g59P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 36=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 36=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 6=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_6 : block g59 5 6 44=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 50=true := (@block_merge g59 5 0 6 44 g59P5_0 g59P5_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 8=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P7_0 : block g59 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B7 : block g59 7 0 1=true := g59P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact g59B3
  · exact g59B4
  · exact g59B5
  · exact g59B6
  · exact g59B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 8 := lower_forest (g:=g59) (i:=0) (hints:=317280105792002) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 8 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((bitLimbs [0xedfffbffffaffffe7f,0xfdfffb5fffeffebfaffe]),(bitLimbs [0x9080eb0649930116a,0xd5fe2841d2209c11a7b6])),(0x0,0x0),((bitLimbs [0x7b0f4fdf1b75f9e7fe,0x3f3935eeb7f27d667ba7]),(bitLimbs [0x41186a10b8bcfb396,0x8abd108ab4c749666b83])),((bitLimbs [0xfffff6b9f6fedf19f1,0xfffeeeb96dfdebf9fe5b]),(bitLimbs [0xe716982c090541c901,0xadc046a28d856aa95e4b])),((bitLimbs [0x7fcef5f4f35bccb9dd,0xbe6f66fd5559cdc2ff5d]),(bitLimbs [0xc882c6579656b59206,0x700e327c4f5901c2b95d])),((bitLimbs [0x93ffcfff2df7fbffae,0x5bd9dfe6fffebf7f51f7]),(bitLimbs [0x584c5107c3361a4000,0x5a03d5062b7ca4fe5074])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(0,4,57,0,5),(0,8,53,0,5),(0,16,45,0,5),(0,32,29,0,5)]
def g61A : List (List Nat) := [[],[66,83]]
def g61D6 (j : Nat) := if j=0 then 0x7209f else 0
def g61L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g61D6)
  | _ => emptyPacking
def g61I (_ _ : Nat) : Option (Nat × Nat) := none
def g61 : Forest := ⟨61,6,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P6_0 : block g61 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B6 : block g61 6 0 1=true := g61P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : checkedTables g61 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g61 0 0 0 = true)
  · exact (rfl : block g61 1 0 0 = true)
  · exact (rfl : block g61 2 0 0 = true)
  · exact (rfl : block g61 3 0 0 = true)
  · exact (rfl : block g61 4 0 0 = true)
  · exact (rfl : block g61 5 0 0 = true)
  · exact g61B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 7 := lower_forest (g:=g61) (i:=0) (hints:=176542626086936) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 7 [(61,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g62Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xfffb7ffd7ffffd5fff,0xbfffff97ffffdb9fcdff]),(bitLimbs [0x90a3a00a0111c06e51,0xd8eb779502a3409cc5b5])),((bitLimbs [0xdddfcfbfdfffeefffb,0xf7fff77dfdfffdfd7bfb]),(bitLimbs [0x4314f7096e2a090060,0x2414e508e53cbcb51a7a])),((bitLimbs [0xef7fffeabfadb3efc6,0xff31ffff87d73f7bb6dd]),(bitLimbs [0x1059042332d6b720b1,0x1b909253a057176bb4c9])),((bitLimbs [0x7aa6be5ffaf7ffb67f,0x7cfeabeb7bf9e7eeff66]),(bitLimbs [0x8b1b5a5415d005aca2,0x64e898aa39c9916aeb46])),((bitLimbs [0x66fdf946b2371ffd65,0x793beafa4f25a772b72f]),(bitLimbs [0x990afe3ae0afc41905,0xc1732e60cf0a2392372f])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g62C : List ColumnInfo := [(0,32,30,0,7)]
def g62A : List (List Nat) := [[],[67],[33],[33,67]]
def g62D7 (j : Nat) := if j=0 then 0x3f else 0
def g62L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g62D7)
  | _ => emptyPacking
def g62I (_ _ : Nat) : Option (Nat × Nat) := none
def g62 : Forest := ⟨62,7,fun i => g62Y[i]?.getD (0,0),g62C,g62A,g62L,g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P7_0 : block g62 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B7 : block g62 7 0 1=true := g62P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact (rfl : block g62 4 0 0 = true)
  · exact (rfl : block g62 5 0 0 = true)
  · exact (rfl : block g62 6 0 0 = true)
  · exact g62B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 8 := lower_forest (g:=g62) (i:=0) (hints:=915206799104000) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 8 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)
def g2079Y : Array (Bits × Bits) := #[((bitLimbs [0xbebf4b5feea7dcbded,0xf3f8bbceffe4ba47bb47]),(bitLimbs [0xa2001001008040,0x8040090c21840a002342])),((bitLimbs [0x3cf77a5dff53aceff,0x8c27c877ea33bdacd45e]),(bitLimbs [0x22151006003e1105ad,0x17c0200a02b5a49414])),((bitLimbs [0xfd74ef96cb7c97726b,0xf71727794dfb51f931b9]),(bitLimbs [0x701114162206e0603,0x521422415430506910b9])),((bitLimbs [0xd3809deebd7b75ab9b,0x3fcffdeb300d67324ead]),(bitLimbs [0x1c2a04468e4203698e,0x6f0904c210010512482d])),((bitLimbs [0xfd49f374197f6f5092,0xbac7c69beb1b5e9f64b2]),(bitLimbs [0xa80ce5085d88e8f010,0xb08a801fec8d829f6482])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2079C : List ColumnInfo := [(0,16,4111,0,7),(1,0,30,0,7),(16,0,15,0,6),(0,2,2077,0,5),(0,4,4123,0,5),(0,8,4119,0,5),(2,0,29,0,5),(4,0,27,0,5),(8,0,23,0,5)]
def g2079A : List (List Nat) := [[],[50],[33],[33,49],[49,33],[49]]
def g2079D6 (j : Nat) := if j=0 then 0x3078e027948421 else 0
private def g2079D7Page0 : Array Nat := #[0x15adc00fe21fd21fc21,0x3144300128398a41c430,0x20c520e2180094148]
def g2079D7 := limbs80 #[g2079D7Page0]
def g2079H7 (j : Nat) := if j=0 then 0x9 else 0
def g2079D8 (j : Nat) := if j=0 then 0x805f else 0
private def g2079H8Page0 : Array Nat := #[0x5c80100,0x1210000000000059800,0x96800000000000,0x617c9f6000305c42000,0x50000000,0x2940]
def g2079H8 := limbs80 #[g2079H8Page0]
def g2079L : Nat → Packing
  | 6 => (1,2,4,0,0,0,0,g2079D6)
  | 7 => (3,1,4,0,0,7,0,g2079D7)
  | 8 => (1,0,4,0,0,0,0,g2079D8)
  | _ => emptyPacking
def g2079I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g2079H7
  | 8 => lookupWord 3 47 3 9 2 3 g2079H8
  | _ => fun _ => none
def g2079 : Forest := ⟨2079,8,fun i => g2079Y[i]?.getD (0,0),g2079C,g2079A,g2079L,g2079I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P6_0 : block g2079 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B6 : block g2079 6 0 1=true := g2079P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P7_0 : block g2079 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B7 : block g2079 7 0 3=true := g2079P7_0
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
  · exact (rfl : block g2079 4 0 0 = true)
  · exact (rfl : block g2079 5 0 0 = true)
  · exact g2079B6
  · exact g2079B7
  · exact g2079B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079G : graphValid g2079 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2079 : Lower true (varsX 2079) (graphGoal 2079) 9 := lower_forest (g:=g2079) (i:=0) (hints:=412451340802) (before_sound K62 V62) g2079G g2079T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2079 := extendKnown K62 9 [(2079,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2079 : Known true K2079 := extend_ok (m:=2079) V62 low2079 (by decide +kernel)
def g2095Y : Array (Bits × Bits) := #[((bitLimbs [0xfa7ab5fb753972f3dd,0xb3e8bbcf7da4bb43cea7]),(bitLimbs [0x80d2004810c021089,0x8050090e10841b400ca2])),((bitLimbs [0xffb7a5effaeeb3df7,0xcc37c873f773bcb6752e]),(bitLimbs [0x8020006000f0440754,0x7c0200502a4a25104])),((bitLimbs [0xf5a7f96e5be65dccd3,0xf717277ca6fb52fc9c59]),(bitLimbs [0x1c0814131105b8180b,0x52102244aa3052548459])),((bitLimbs [0x4e04dee9ebd9d6ab3b,0x3fcefded980d65c923dd]),(bitLimbs [0x70d0446872100da316,0x6f0b04c108010489221d])),(0x0,0x0),((bitLimbs [0xf54f3740cbfdbd4122,0xbac6c69df59b5f2fa952]),(bitLimbs [0xa0675082ec43a3c420,0xb08c801bf60d812fa942])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2095C : List ColumnInfo := [(0,32,4111,0,7),(0,4,4139,0,5),(0,8,4135,0,5),(1,0,46,0,5),(2,0,45,0,5),(4,0,43,0,5),(8,0,39,0,5),(1,8,38,0,4),(1,32,14,0,4),(2,4,41,0,4),(32,0,2063,0,4)]
def g2095A : List (List Nat) := [[],[16,50]]
private def g2095D4Page0 : Array Nat := #[0x2c0108619c5456008430,0x21867151d81210c31d2a,0xf5d46448430c68c8a8a4,0x89510c29b3a0c4a88610,0x3087cec2a24298534745,0xb92c22a2614b1c961151,0x36c2a91e6123060297]
def g2095D4 := limbs80 #[g2095D4Page0]
private def g2095D5Page0 : Array Nat := #[0xbd58720442ac6448720,0x109f59432442f9600c91,0x4309f59731c827e650c9,0x8430cf950210c2f96008,0x48430bed81210c27d650,0x448430cf951210c37551,0x51884309fd95210c2bc6,0xd6588430cf952210c375,0x3e54c8430dd547210c27,0x3756254430dd189510c3,0xc3776254430dd989510c,0x4c27c6548530cf151214,0x14c27e6588530cf15221,0x544c33c54c8530ddd472,0x8544c33e6115130cf584,0x96218c33e6215130cf58,0xa0140027f61540329f5,0x3c8e52d48c1a8641783c,0x62d7e5c56b5954a4a114,0x83dfb79dda751ce6cd91,0x96e5593e428ba2888a15,0x20040c1020a00288042,0x70850a120e010000502,0x8228203040400c28406,0x588044142020c0e15010,0x104182000281800c54,0x4000322601860689808,0x80000820460410a0010a,0xa041100]
def g2095D5 := limbs80 #[g2095D5Page0]
private def g2095H5Page0 : Array Nat := #[0x35920cc02640001d586,0x1c,0x2900283c8000000]
def g2095H5 := limbs80 #[g2095H5Page0]
private def g2095D6Page0 : Array Nat := #[0x3e54042dca4085b54810,0xeca2185d544309f2a441,0xf95030b7290616d520c2,0xea8c213c544ca78a8984,0xd51c83da43905f54420b,0xaa3185fd4530bea88617,0xc8110bea8c657d500caf,0x29221fc52443f864887f,0x210c3f842187fcc720ff,0x42987fc8430ff10861fd,0x8630ff90a61fe214c3fa,0xe001ff21cc3fe43187f8,0x1c3a8630a21081801e01,0x9a917204390600ae1322,0x9dd3906e4cf1802d6540,0x94d495521a2841a7ecf7,0x10307012b554ca7545a7,0x501481c40d0145103c04,0x40e2c051838b01081c30,0x1850e2c05183881c0518,0x4a1e68c24062060e2405,0x40c20704002c91c20501,0x1850c2841c002491c614,0xa10700091440d2070187,0x61438820700082461430,0x700061c6143081c0020,0x7185122081c002450c2,0x51110441c50c2841c002,0x24511104518510308118,0x604081c6142045245043,0x51030818102061440c20,0x1440c18061440c180518]
private def g2095D6Page1 : Array Nat := #[0x5185081805081810109,0x32450811020422451028,0x1c614]
def g2095D6 := limbs80 #[g2095D6Page0,g2095D6Page1]
private def g2095H6Page0 : Array Nat := #[0x7421e7c110e05a11000,0x12200000000e8c000007,0x62b4d49ea3020a4abc0,0x5e84b0f0018178e00030,0xdd9600000189b8351c0,0x112a9900400506001275,0xce4282fc400068fd5d8a,0x234007200440002488,0x104132001210000]
def g2095H6 := limbs80 #[g2095H6Page0]
private def g2095D7Page0 : Array Nat := #[0xfd20fc20fe10fd10fc10,0xfe30fd30fc30ff20fe20,0xcc00fe32fd32fc32ff30,0x69a75e541438d628c6b0,0x20c418009a726e8da037,0x524e6290620c0051cc5,0x620c004a4e6290620c0,0x2527314831060028e629,0x41883001493988310600,0x498a4188300109398a,0x9483106001ce6290620c,0x31060028e6290620c004,0x849c831060021273148,0xe520c4180]
def g2095D7 := limbs80 #[g2095D7Page0]
private def g2095H7Page0 : Array Nat := #[0x4122910068a2480c1045,0x940220000001062,0x117cc280a526000002da,0x370c0fd43422a6b0de2,0x707f1dc75a95038240,0x964405000298aae500,0x5b60028271143546c00,0x33a5800000c3e6780a80,0xf500000000195800000b,0x8003179168040019ceb9,0x3af00000181]
def g2095H7 := limbs80 #[g2095H7Page0]
def g2095D8 (j : Nat) := if j=0 then 0x3f else 0
private def g2095H8Page0 : Array Nat := #[0x2998c4dccfa2943e54,0x3a27648010437a900110,0x60dcd61895a05787,0x6800009500002ac00000,0x4ac00006]
def g2095H8 := limbs80 #[g2095H8Page0]
def g2095L : Nat → Packing
  | 4 => (10,4,4,0,0,6,0,g2095D4)
  | 5 => (35,3,4,0,0,10,0,g2095D5)
  | 6 => (35,2,4,0,0,11,0,g2095D6)
  | 7 => (14,1,4,0,0,10,0,g2095D7)
  | 8 => (1,0,4,0,0,0,0,g2095D8)
  | _ => emptyPacking
def g2095I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 2 29 1 8 4 0 g2095H5
  | 6 => lookupWord 10 59 5 11 6 1 g2095H6
  | 7 => lookupWord 12 71 6 11 6 1 g2095H7
  | 8 => lookupWord 6 37 3 9 4 1 g2095H8
  | _ => fun _ => none
def g2095 : Forest := ⟨2095,8,fun i => g2095Y[i]?.getD (0,0),g2095C,g2095A,g2095L,g2095I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P4_0 : block g2095 4 0 10=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2095B4 : block g2095 4 0 10=true := g2095P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P5_0 : block g2095 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P5_1 : block g2095 5 1 34=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2095B5 : block g2095 5 0 35=true := (@block_merge g2095 5 0 1 34 g2095P5_0 g2095P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P6_0 : block g2095 6 0 11=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P6_11 : block g2095 6 11 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P6_20 : block g2095 6 20 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2095B6 : block g2095 6 0 35=true := (@block_merge g2095 6 0 11 24 g2095P6_0 (@block_merge g2095 6 11 9 15 g2095P6_11 g2095P6_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P7_0 : block g2095 7 0 14=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2095B7 : block g2095 7 0 14=true := g2095P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P8_0 : block g2095 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2095B8 : block g2095 8 0 1=true := g2095P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095T : checkedTables g2095 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2095 0 0 0 = true)
  · exact (rfl : block g2095 1 0 0 = true)
  · exact (rfl : block g2095 2 0 0 = true)
  · exact (rfl : block g2095 3 0 0 = true)
  · exact g2095B4
  · exact g2095B5
  · exact g2095B6
  · exact g2095B7
  · exact g2095B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095G : graphValid g2095 (boundsBefore K2079) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2095 : Lower true (varsX 2095) (graphGoal 2095) 9 := lower_forest (g:=g2095) (i:=0) (hints:=175921995186690) (before_sound K2079 V2079) g2095G g2095T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2095 := extendKnown K2079 9 [(2095,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2095 : Known true K2095 := extend_ok (m:=2095) V2079 low2095 (by decide +kernel)
def g2103Y : Array (Bits × Bits) := #[((bitLimbs [0x69d8fff7ddfe3f3ff8,0x5b9ef8f9b929bf66385d]),(bitLimbs [0x801020001000b03a40,0x8800003021090122004c])),((bitLimbs [0x947f23e47a7fe7759f,0xa779e3154fff11898db7]),(bitLimbs [0x3601c480110400198,0x261182018e1004888991])),((bitLimbs [0xffa470ede2b9f1dd47,0xc4b597c666fd5917d7a8]),(bitLimbs [0xb81501a6bc200b3e22,0xc0a0016650a119171628])),(0x0,0x0),((bitLimbs [0x72b3543ae7e136982e,0x7e48dceeef42da9d634b]),(bitLimbs [0x4c4cd2c8454042003c,0x6bd4cc8240921d6103])),((bitLimbs [0xcb6fa92df7c258cacd,0x7ade37565623e4faf232]),(bitLimbs [0x330941304294010005,0x521e300954b244c0f232])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2103C : List ColumnInfo := [(4,0,51,0,6),(0,4,4147,0,5),(0,16,4135,0,5),(0,32,4119,0,5),(1,0,54,0,5),(2,0,53,0,5),(1,16,38,0,4),(1,32,22,0,4),(2,4,49,0,4),(16,0,2087,0,4),(32,0,2071,0,4)]
def g2103A : List (List Nat) := [[],[84]]
private def g2103D4Page0 : Array Nat := #[0x88690221785c44348110,0x29056a7510d20442b4ba,0xa5c064cc520b92e021e6,0x804348275b8ac021a413,0x208d8eab0886906c8535,0xbaac221e41395c46510d,0x6629861c5498e214c237,0x1c59c454cc530e2ae22a,0x550c4348697b92c22a26,0x4443a3eeaa188710e1e6,0xcbb8a86a8887a350f625,0x312a221c9f7650d5110e,0x88765dc54394443ad2e0,0xd71d954310e4fbb28728,0x28211a17140d0a030049,0x4643403d3a3734312e2b,0x4982000020524f4c49,0x2a608]
def g2103D4 := limbs80 #[g2103D4Page0]
private def g2103D5Page0 : Array Nat := #[0x3c7153314c2e96010d20,0x10a7d954310e9f6150c4,0x110fa14d20443e843481,0xd10be58331443ea5348,0x10d10bd58443442f9601,0x110f109f994434427d65,0x6010d209f59443c42f56,0xc43cc5209f99443482f9,0xee64cc520bb19331483c,0x2ed6110d20fa58043482,0x82ec6510d20f314c4348,0xc82ee6414d20bb994434,0x1c83cc43cc720bb99031,0x43c82ee64cc720bb1933,0x1210c3755148430bb584,0x95210c33e5448430cf55,0x552210c37551884309fd,0xf596210c33e5488430cf,0xddd89510c37562544309,0xcfd51214c33c5448530,0x30b798e214c27c654853,0x530cfd52214c33c54885,0xc530d7153314c27e6588,0x10530be580414c35e65c,0x3d05309f994414c2de63,0x63d09309f997414c2de6,0xd61151309f997424c2de,0x3e6115130cf584544c27,0x2dc6348630cf588544c3,0xc27d65886309fd95218c,0x486f56110d219f58454c,0x34867e6510d21e750c43]
private def g2103D5Page1 : Array Nat := #[0x434867c6550d21d714d4,0x4438867d6014d219f996,0x94438879d4310e21bd58,0x952438867f6550e219f5,0xf582538867d6590e21cf,0xe710d414c67d60950319,0x19f195414c6dc6350531,0x31b798f414c79c43d053,0xf31e710f41cc75e6510d,0x5331b759743cc6dd6010,0x953329f58254cc67d601,0x2544439fd855010e7d60,0x6054443e750d5110eef6,0xf6254443db1895110e7f,0x9d4354843e750e5110f6,0x8cc1622583a059060003,0xe2945109f11c2023986c,0xaa704cf9993185fcb915,0x8dd18a2443c861021e93,0xd4ca934fe9e532a4a47a,0x2adf5b2b4d66ab954aa7,0x2462ec45822fe5f0bad7,0x728dc9b2b58696cf998b,0x102dfbbea7baf41e53b6,0xb22fc4487d0e215c2583,0x55c9e93124a464868f31,0x514a013ce734d998b2fe,0xcac356eaad48a774d694,0x29d20035b7b55676c857,0x280830e1a213042870c9,0xc830e1928618a0260206,0x1030e182860010c08608]
private def g2103D5Page2 : Array Nat := #[0x40040000c1010020a12,0xd2100080930408218004,0x800326042080420c129,0x60010002608000400115,0x280008013082130800,0x4000000012882a000200,0x8114085040260800020,0x4040094011408204502,0x20801c104289826020a,0x40120800408008002001,0x10408004503021800090,0x2002820810200000004,0x41030410207002081020,0x40300004082040040c30,0x4102001020810010905,0x50]
def g2103D5 := limbs80 #[g2103D5Page0,g2103D5Page1,g2103D5Page2]
private def g2103H5Page0 : Array Nat := #[0x15748000000000000802,0x2ca00000001,0x8e0000019b4f00000900,0x84f04430000000000002,0x5300028c00142,0x33400f1e0b91800000,0x7240000113000,0x14000002211100000814,0x28205b]
def g2103H5 := limbs80 #[g2103H5Page0]
private def g2103D6Page0 : Array Nat := #[0x5e53042baa6085b54810,0xdaa5087a48210f490221,0xd94430baa88616d52882,0xf2a0613d540c2daa4185,0xd528c27ea8984f151309,0xca918cf55231b7a92636,0xc8110f6902219d4310e7,0xa8c217e53442f8a6887b,0x53482fca7887bc8310be,0xa6907b10d20f798a417c,0xf20f798e41ec31c83d8,0x8a61df314c2faa2187b1,0x1cc2faa3185f15130bfa,0x690dfd4121be2a661df3,0x31bf29c437d50886f8a,0xa637e540c6fca618df54,0xcc6fca918df15131ee21,0x98f7d0f31ee21e637d50,0x32be2a2657e54cc6f8a9,0x877d5010efca9995f543,0xefaa321dfd4543bea88,0x87f10d10ff98a217e539,0xfe21e21fe53443f8a68,0x1fe210c3fa42187f10d2,0x3f882987f88530fe90a6,0x7f48630ffa1261ff414c,0xff10e61fd21cc3fc4318,0xff42cc3fe83987f10730,0xfc8690ff50d21fe21a43,0xf90e21fea1c43fc43887,0xea8663ff414c7fa8298f,0xe54cc7faa998ffd0731f]
private def g2103D6Page1 : Array Nat := #[0xca221ff54443fea8087f,0x7202700a8001fd5210ff,0x5e82a012c08103481500,0x26a12008703e41ce0d50,0xdf868430016e0ae0528,0x84f825b11b88703f61e3,0x21920c185dc2d615c0a6,0x907863ab1cb0dc86ae34,0xa123e917087c4202010f,0x524a62510279135c97e4,0x5e82e516b0b225732b09,0x9a28cea65431c9890c18,0xa70e37c9b6cd866b7352,0x71d88ea67443991c98e3,0x967bc3d39e60f0c77a3b,0x12a06501a7f53f31f68f,0x128885439a19109e83a4,0x61440500068d646222bd,0x2071851301471440b014,0xc69444462071a5111400,0x40401871a51014001c81,0x122c061c6122c0520718,0xb01471848814001c7185,0x40b01871848b01461038,0x500061a40c2c052871a,0xc2c05206942050187102,0x6502c05206142c051850,0x2481c69448e205000a24,0x81c002c81c69448e2400,0x60d20401ca2461440d20,0x20718510308140028a24,0x820402c71a5123890008]
private def g2103D6Page2 : Array Nat := #[0x308180028a2481851034,0x5444d284180928920614,0x91c6564113481809206,0x34a00072065444d20600,0x91951134a000719511,0x820700091c65641134a0,0x2061444c28461c61038,0xc207000b286103081c0,0xc7103081006287185913,0x44e20402891851130a11,0x2040c20600092891c616,0x92892040c2060009289,0x20600092891440c20600,0x1440e208100a2891440c,0x481851030814002ca206,0x11ca2481440c204024a2,0x1840c204020918590309,0xa2061440c2070009289,0x30911ca2461440e20810,0x1491859030911c918590,0x45103081c0024a244040,0x920614408180020a2,0x1020600092881850c206,0x855230e208100b289205,0x10062891030810072471,0x247103081c0020610308,0x8218a2461440c205000a,0xa2471851030882481844,0xc21c91820c918448214,0x4610308180024a247185,0x510100424510204018a2,0x28510308508100308108]
private def g2103D6Page3 : Array Nat := #[0x8100328308110a1c3084,0x60810052460430810030,0x2891c60c218918508424,0xc2043245040109182044,0xa2450c20401c90c20440,0xc28101830400c20400c,0x4488218a2480c2806205,0xa2450c214a2430842461,0x1c61230e20882450c210,0x89143085289143090189,0x500032]
def g2103D6 := limbs80 #[g2103D6Page0,g2103D6Page1,g2103D6Page2,g2103D6Page3]
private def g2103H6Page0 : Array Nat := #[0x101514d1407820c02c3,0x508e0040c99431009c91,0x123000000e1b000ed,0xa5d000000a4d000,0x63e9c3b08e52334a370,0xd295034152,0x1a00033100000041f000,0x3000f12e4e4390008213,0x92ad5796253245685,0x4279ad3b000000509a0a,0x8b3300052fa0fb02f49a,0x65a74b00000021175525,0x18b60d040008d6bb1000,0xc62e05f730e270009266,0xc0c00000000000005984,0x47000016536000000e14,0x8d300535b72261080b9,0xd07803b1ce86e5e00000,0xdb6706e15000838f01,0x5d6100dccbc40b43f4ad,0xe2542cc0ea90ab4a1e64,0x3dc5c64f13ff95285554,0xd93c417719000a1d72bc,0x6b213500000000034432,0x48124dd0728513629000,0x3a846351f]
def g2103H6 := limbs80 #[g2103H6Page0]
private def g2103D7Page0 : Array Nat := #[0xfe10fd10fc10ef20ed20,0xfd30fc30fe20fd20ff10,0xfc31fe21fd21ff30fe30,0xff32fd32ff31fe31fd31,0xf812000fe43fd43fc43,0x4d917f298464708a90e2,0x8afe596a4d37a4642679,0x8100d0d603bca72eda59,0x90620c0049cc40088398,0x2907314831060028e62,0x83106002907314831060,0x128398a4188202507314,0x20c41800941cc520c410,0x20e6290620c0049cc5,0xcc520c41800939483106,0x29062080641483104039,0x4180094a0c520c41800a,0x906290620c004a0c520c,0x18820212831483106002,0x5a506290620809418a4,0xc418008524e6290620c0,0x127314831060028c520]
def g2103D7 := limbs80 #[g2103D7Page0]
private def g2103H7Page0 : Array Nat := #[0xa088104a149060a58200,0x1c9b2a3800caa3c2870,0x170d863c98c079c48002,0x15a78000006315ca9a75,0xbe542b82a310ee3097e2,0x8a22fc1c98608d4ae607,0x7d8873050f7968000005,0x428fa089ee8708cc82ee,0x8500032212521180b56d,0x68a31e584f2e73163938,0xa61510463e05fcd95a78,0x8319bc55ab086441251a,0x9800321895ca2d18114a,0x2e2ba68093088007ccd1,0x8c0000003cb10a80049b,0x5988000697a80df8007,0x80056818fd59fa631c00,0x408ce8293995d7f0262d,0xe1ab5a9d2e812d25e111,0x4a4fd4fad6e4fe6be629,0x9c6091302c80e601c41,0x681000583d140002801,0x21558eea3eaf58431a00,0xeac04b8b8001200002a4,0xdb4d00041d0000007ec3,0xdac1aa88091d80029f48,0x59f9e8c4f]
def g2103H7 := limbs80 #[g2103H7Page0]
def g2103D8 (j : Nat) := if j=0 then 0x3f else 0
private def g2103H8Page0 : Array Nat := #[0x140010c9180040333b50,0x4f82628000f395800147,0x430000000000528006a8,0xf04000000002fd58c5,0xe0ae9a4c00339f211c,0x76d3400dbcc4b1400648,0x2b00000ec050db800a23,0x1]
def g2103H8 := limbs80 #[g2103H8Page0]
def g2103L : Nat → Packing
  | 4 => (23,4,4,0,0,8,0,g2103D4)
  | 5 => (99,3,4,0,0,11,0,g2103D5)
  | 6 => (99,2,4,0,0,13,0,g2103D6)
  | 7 => (23,1,4,0,0,11,0,g2103D7)
  | 8 => (1,0,4,0,0,0,0,g2103D8)
  | _ => emptyPacking
def g2103I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 6 67 2 10 5 1 g2103H5
  | 6 => lookupWord 28 157 6 12 7 1 g2103H6
  | 7 => lookupWord 33 157 7 12 7 1 g2103H7
  | 8 => lookupWord 8 53 4 10 5 1 g2103H8
  | _ => fun _ => none
def g2103 : Forest := ⟨2103,8,fun i => g2103Y[i]?.getD (0,0),g2103C,g2103A,g2103L,g2103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P4_0 : block g2103 4 0 23=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B4 : block g2103 4 0 23=true := g2103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P5_0 : block g2103 5 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P5_4 : block g2103 5 4 95=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B5 : block g2103 5 0 99=true := (@block_merge g2103 5 0 4 95 g2103P5_0 g2103P5_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P6_0 : block g2103 6 0 19=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P6_19 : block g2103 6 19 44=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P6_63 : block g2103 6 63 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B6 : block g2103 6 0 99=true := (@block_merge g2103 6 0 19 80 g2103P6_0 (@block_merge g2103 6 19 44 36 g2103P6_19 g2103P6_63))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P7_0 : block g2103 7 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P7_2 : block g2103 7 2 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B7 : block g2103 7 0 23=true := (@block_merge g2103 7 0 2 21 g2103P7_0 g2103P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P8_0 : block g2103 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B8 : block g2103 8 0 1=true := g2103P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103T : checkedTables g2103 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2103 0 0 0 = true)
  · exact (rfl : block g2103 1 0 0 = true)
  · exact (rfl : block g2103 2 0 0 = true)
  · exact (rfl : block g2103 3 0 0 = true)
  · exact g2103B4
  · exact g2103B5
  · exact g2103B6
  · exact g2103B7
  · exact g2103B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103G : graphValid g2103 (boundsBefore K2095) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2103 : Lower true (varsX 2103) (graphGoal 2103) 9 := lower_forest (g:=g2103) (i:=0) (hints:=35253092090370) (before_sound K2095 V2095) g2103G g2103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2103 := extendKnown K2095 9 [(2103,[]),(2107,[16,82,50,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2103 : Known true K2103 := extend_ok (m:=2103) V2095 low2103 (by decide +kernel)
def g2109Y : Array (Bits × Bits) := #[((bitLimbs [0xeffe7feffb81efe56,0xd11917dd777d3d66cc64]),0x0),(0x0,0x0),((bitLimbs [0xf617fa6995efe159f7,0x2ef6bfa1e982cf1811bf]),(bitLimbs [0x58921802402200a40,0x2068e4101010708013c])),((bitLimbs [0xdf72790b2ffaec2938,0x7bff6c2aa93088eb6783]),(bitLimbs [0x42728628402c1905a0,0x107960282a8c88636483])),((bitLimbs [0xf7470ed2ceb76b47d9,0xdf7de316c08a5393b25a]),(bitLimbs [0x82240a05cacc049033,0x5d102114ccc800b39242])),((bitLimbs [0x7e46deb52a5f3a16b,0x52c3618e8721ff85b7b0]),(bitLimbs [0xed1955f788a2490806,0x46c189b397215944b7b0])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2109C : List ColumnInfo := [(0,32,2077,0,5)]
def g2109A : List (List Nat) := [[],[67]]
def g2109D5 (j : Nat) := if j=0 then 0x3f else 0
def g2109L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g2109D5)
  | _ => emptyPacking
def g2109I (_ _ : Nat) : Option (Nat × Nat) := none
def g2109 : Forest := ⟨2109,5,fun i => g2109Y[i]?.getD (0,0),g2109C,g2109A,g2109L,g2109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109P5_0 : block g2109 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2109B5 : block g2109 5 0 1=true := g2109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109T : checkedTables g2109 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2109 0 0 0 = true)
  · exact (rfl : block g2109 1 0 0 = true)
  · exact (rfl : block g2109 2 0 0 = true)
  · exact (rfl : block g2109 3 0 0 = true)
  · exact (rfl : block g2109 4 0 0 = true)
  · exact g2109B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109G : graphValid g2109 (boundsBefore K2103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2109 : Lower true (varsX 2109) (graphGoal 2109) 6 := lower_forest (g:=g2109) (i:=0) (hints:=844700347006976) (before_sound K2103 V2103) g2109G g2109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2109 := extendKnown K2103 6 [(2109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2109 : Known true K2109 := extend_ok (m:=2109) V2103 low2109 (by decide +kernel)
def g2110Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xfeff2f4ef79ffc66d5,0xf36fb667493917274249]),0x0),((bitLimbs [0x671ec6979d640d43f7,0xab9cc64ea08efa9e3562]),(bitLimbs [0xb97a006834a81cb20a,0xa28cc843dc0af00e2560])),((bitLimbs [0xad5c74f949c7e69f4e,0xc5a9c99abed13c72acb5]),(bitLimbs [0xc04a052103a0184420,0x10c88800c81692204b1])),((bitLimbs [0xde5e5e3b7a71a7a40f,0x202a7bf3b29722d52d8e]),(bitLimbs [0x2b95e08e0c09602a8c,0x10324273307c8255290e])),((bitLimbs [0xbb39dba5d5e7493d2e,0x8eb2d4d82766eea9d932]),(bitLimbs [0x8002864854620014,0x40701428226006c1d802])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2110C : List ColumnInfo := []
def g2110A : List (List Nat) := [[],[66,83]]
def g2110D4 (j : Nat) := if j=0 then 0x1f else 0
def g2110L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g2110D4)
  | _ => emptyPacking
def g2110I (_ _ : Nat) : Option (Nat × Nat) := none
def g2110 : Forest := ⟨2110,4,fun i => g2110Y[i]?.getD (0,0),g2110C,g2110A,g2110L,g2110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110P4_0 : block g2110 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2110B4 : block g2110 4 0 1=true := g2110P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110T : checkedTables g2110 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2110 0 0 0 = true)
  · exact (rfl : block g2110 1 0 0 = true)
  · exact (rfl : block g2110 2 0 0 = true)
  · exact (rfl : block g2110 3 0 0 = true)
  · exact g2110B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110G : graphValid g2110 (boundsBefore K2109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2110 : Lower true (varsX 2110) (graphGoal 2110) 5 := lower_forest (g:=g2110) (i:=0) (hints:=141289400041472) (before_sound K2109 V2109) g2110G g2110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2110 := extendKnown K2109 5 [(2110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2110 : Known true K2110 := extend_ok (m:=2110) V2109 low2110 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((bitLimbs [0xdfff996defe3fdefaf,0xfb7aec71fb3acf34f6fc]),(bitLimbs [0xc26c00280249200a21,0x4d6a4450ab224d04d4c0])),((bitLimbs [0x7b3177df54fefebef0,0x36d7f7d2f15fb0cbe93b]),(bitLimbs [0x1991445504224ea4c0,0x908583825059808b2938])),((bitLimbs [0xac926f3bb29e5393de,0x67b9ddac4fe77be78b22]),(bitLimbs [0x64988d0a98fd51339c,0x67590cac4d263be78222])),((bitLimbs [0x2d4c86f2495bfa5d5f,0xb98f37af25859ddc1edd]),(bitLimbs [0x28208284494bb3545a,0xb00a332b258598540add])),((bitLimbs [0x2c5ffdcd9484b88958,0xcc6c766f14e97f0bc557]),(bitLimbs [0x8c0bb14d90809ad950,0x9c40766d10e97708c517])),((bitLimbs [0x94c36af9ff97c16e77,0x413f0b4f8eec42bd36ab]),(bitLimbs [0x86c26af16c96c56886,0x834014786cc42b9362b])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,4,2107,0,9),(0,8,2103,0,9),(0,16,2095,0,9),(0,32,2079,0,9),(1,0,62,0,8),(4,0,59,0,8),(0,48,4111,0,7),(1,32,30,0,7),(2,0,61,0,7),(16,0,47,0,7),(32,0,31,0,7),(0,2,2109,0,6),(4,8,51,0,6),(8,0,55,0,6),(16,32,15,0,6),(32,4,2075,0,6),(0,1,2110,0,5),(0,12,4147,0,5),(0,20,4139,0,5),(0,24,4135,0,5),(0,34,2077,0,5),(0,36,4123,0,5),(0,40,4119,0,5),(1,2,60,0,5),(1,4,58,0,5),(1,8,54,0,5),(1,16,46,0,5),(2,4,57,0,5),(2,8,53,0,5),(2,16,45,0,5),(2,32,29,0,5),(4,16,43,0,5),(4,32,27,0,5),(8,16,39,0,5),(8,32,23,0,5),(1,24,38,0,4),(1,34,28,0,4),(1,36,26,0,4),(1,40,22,0,4),(1,48,14,0,4),(2,1,2108,0,4),(2,12,49,0,4),(2,20,41,0,4),(2,48,13,0,4),(4,48,11,0,4),(8,4,2099,0,4),(8,48,7,0,4),(16,8,2087,0,4),(32,8,2071,0,4),(32,16,2063,0,4)]
def g63A : List (List Nat) := [[]]
private def g63D5Page0 : Array Nat := #[0xa9381c75a0c7158043]
def g63D5 := limbs80 #[g63D5Page0]
private def g63D6Page0 : Array Nat := #[0x1d043440101cc4344010,0xa107344010dd84344010,0x20f7644010a0c7444010,0x5d843104202137644010,0xa126510c219957010c21,0xa1275084306027499421,0x20d6108440a044258430,0x6045398442a043258440,0x14d709844210d7098442,0xa0c71580431d47158043,0x60472580431d47258043,0xe0475580436047558043,0x5d8540c4501d77158043,0x60053104505d85310450,0x2057014c5014d6110450,0xa044258450a043258450,0xa04435845260053d0450,0xa0c640851018c4308510,0x18d700c910a0e6408510,0x14d701091010d7010910,0x191701091018d7010910,0x10d711491018d7010d10,0xa0443189109d06314d10,0x18e71c8110a045318910,0x18a71cc11019271c8110,0xa0e640861018a71d0110,0xe057010f212057010f21,0x9d66308740e1d6118730,0x14d7114b40a127508740,0x2117098f512117014f51,0x7d4f65ec9f20d7099351,0x87b0bd8faf95baabd4fa]
private def g63D6Page1 : Array Nat := #[0xf47e5ecbb95b1f63dc3f,0x5766e6dcbb93f1de2fc3,0x24754d4bb36e9cdb490b,0xc9309a43856dd81beec0,0x7611bbb06d2602b12815,0x6c19435e3a4c61d282b7,0x8e73ac4ca1b2650d8b28,0xaa31cd719655ceb22e75,0x74b4e76467352d360639,0x4b5a2a5ab35274d864a0,0x98eb9d7398cb60696b83,0x9aca4b60d2e616932eb4,0x24a4f89529b86973973a,0x3a4da9ce6e4a9466731f,0x211d0d2ef86977a1cbc1,0x1740126521902654a110,0x7c590bdaf86e9e42eaf2,0x1672e7899146a41a0b21,0x9528951914834bc21642,0x528a2c755654a3146458,0x80640c0023422f1a1169,0xc1905c1504c1103c0d02,0xc2909c2508c2107c1d06,0xc390dc350cc310bc2d0a,0xc4911c4510c410fc3d0e,0xc5915c5514c5113c4d12,0xc6919c6518c6117c5d16,0xc791dc751cc711bc6d1a,0xc8921c8520c811fc7d1e,0x21a11250229123c8d22,0xc06e02103f05d0907584,0xd413]
def g63D6 := limbs80 #[g63D6Page0,g63D6Page1]
private def g63H6Page0 : Array Nat := #[0xe0353c0]
def g63H6 := limbs80 #[g63H6Page0]
private def g63D7Page0 : Array Nat := #[0x4401098c420404310810,0x4073440101c91004043,0x1d03108376440101d110,0x1042010c41081760c420,0x80735842010d6108176,0x5c04308673d04201d161,0x10c21994430857110c21,0x8443580215c05308670,0x1cd60084545802114d60,0x580211d5600847458021,0x8675580219d16008673,0x9c26508570994219ce64,0xcc4219d2650867399421,0xc176d04215db3108474,0x990210c1760843058421,0x108305d8410c27508430,0xc47258430109610c271,0x5c0640c570148315d842,0x58031109600c57019431,0xc47258031151600c452,0x98d600c475580311d160,0x58031995600c66458031,0xc675580319d1600c672,0x1d5600c87458032d4560,0x8440584211017098432,0x101760c44098c2110176,0x1c96110032584409c432,0x148415c443105760c841,0x1057014c415c05210453,0x1496010432580415c065,0x580411c9601045358041,0x10663580411d56010473]
private def g63D7Page1 : Array Nat := #[0x9cd60106725804199160,0xd4441d45601067558041,0x1097114c425c05310853,0x1d560108735804214d60,0x9844214e611087358442,0x10c72580431c56010d70,0x5c66010f71580431d560,0x8450584211404308450,0x14273084509902114176,0x5d831140540c45010831,0x104509c432142720c450,0x141611045014c4114032,0x5c05314271108505d841,0x58450109611403258450,0x140725845014d6114043,0x9ca6414074584501cd61,0xc845010f211427399050,0x14042cc4509cf2114264,0xc96014673d045014f41,0x580511c9601444358051,0x14a73990511d16014473,0x10d6014a7110c525c043,0x580521cd601487158052,0x1484358452dc56014874,0x1d161148735845214d61,0x9845210e6114b7058452,0x14c71580539ce6414970,0x1c96114f71580531c960,0x851014c214404308510,0x44263085101902144063,0x14831442730851099021,0xc91015032440620c510]
private def g63D7Page2 : Array Nat := #[0x440650c9101903244063,0x99432442640c9105c032,0x105109d432442740c910,0x44053105101484144043,0x9cc41440631051018841,0x1091014c424404310910,0x44065109101904244063,0x98c4244176109105c042,0x109109cc424426510910,0x4406410d1018c4344276,0x1d8434407510d1019443,0x10d105c4434417010d10,0x44043145109c44344265,0x18c52440531491010c52,0x149105c4524406414910,0x44273149109c45244176,0x18c5344276149109d052,0x14d105c4534406414d10,0x44064151109d05344271,0x14c6244043189101d854,0x1891018c624405418910,0x442641891098c6244064,0x9d062442731891099462,0x18d10150634427518910,0x4426518d101946344064,0x9cc6444265191109d063,0x9891018e624404398910,0x44274989109ce6244064,0x10f1044274995109ca63,0xc41101931044063c4110,0x44043c8110d031044330,0x5c72044064c811018f20]
private def g63D7Page3 : Array Nat := #[0xc81109932044263c8110,0x44274c81109cf2044271,0x10b3044064c851010f21,0xcc11018f3044062cc110,0x44032d01109c73044171,0x18f4044062d011010f40,0xd01109c74044064d0110,0x44053d451010f5144273,0x10c2184274d45105c351,0x861098c218417608610,0x84331086109cc2184264,0x10c41841760c610d0421,0x10a1010c428417610610,0x84042586100c96184170,0x1cd61840725861010d61,0xc861010f218407458610,0xc405310b109cf4184264,0x14c52c404314b105c043,0x18f109d052c417114b10,0xc4273993105c064c4170,0x9cf20c4263c83105c720,0xc7205c031c8274c8310,0xc8053107209d431c8265,0x9c443c8273107205c041,0x5872010d61c804314720,0xc8074587201cd61c8053,0xcc730c8261cc32058730,0xd032058740c8170cc720,0xc8053d0720d0740c8261,0x9d351c8273d07205c341,0x10f215d841c85760c721,0xc867414f215c053c8570]
private def g63D7Page4 : Array Nat := #[0x19021cc274d472114d60,0x87305c021cc16108730,0xcc331087309d421cc264,0x58461cc17114b30d0421,0x5873098861cc17018730,0xcc0629873014961cc042,0x19721cc064c8730d8661,0xd033098731cc170c8730,0xcc065d473010b51cc321,0x5d842cc4651073198b61,0x183319d052cc57014b31,0xcc4425833198860cc560,0x98b60cc67498b3114960,0x874014c21d004308740,0xd0263087405c021d0161,0xd0421d0331087409d421,0x14b40d4451d01610c740,0xd027114b405c452d0053,0x10f21d0052587400c961,0xc87405c321d0053c8740,0xd05760cb4114f51d0263,0x5c053d066314b415c052,0x583410c960d067319741,0xd40420c7505c263d0452,0x10b31d4351107500c841,0xcb515d832d45700cb51,0xd457610b515c042d4664,0x5c053d457010f5198c42,0x98f5110960d467414f51,0x8be73993515c264d4570,0x9f6779be5f8fe3e8f637,0xafebeaf6b7abe9f9fe7e]
private def g63D7Page5 : Array Nat := #[0xc7afebf6f7bbedfb7ad7,0xd5f4fcff3ecdf35cbf1f,0xddf76dbf6ed9f5fd7b5d,0xedfafe9f9fe5f8fdfb7d,0xf3631c2bf6fbbe7f5fbe,0xb65b18d920906d204835,0x1ee4c70c770b87afb631,0xeec0277760181c31243e,0x7482033bbb015ddd808e,0x5d31801d2100ce90606,0x4c61800d2ec00ae650,0x1a22450d0b2286815c42,0xceaa46675515c31c348a,0x667552b33aa8c461d48c,0xa5831c52e18d64230ea5,0xaf6718d5ae0c6ad2e868,0xd97170c6b894645eca21,0x50cd384536899432e1a9,0x2e8667333b33ac18d9c4,0x1914332c521590e0c6c8,0x3684a198c4b00c6b8646,0x95b8e4e6f5b0656b9143,0x2ed1f66758d333ac66b1,0x697690ca21c88461a56d,0xa0a42cb595da5f08a730,0x26e98c12230c0711809,0xd44eccea2511860734bb,0x4eb5c1186151d408ad99,0x1387ac333ad60761eb90,0x4a342da599d6b4cceb57,0xd844e1ebe93016c1d87b,0x1ec8cceb646675b288c3]
private def g63D7Page6 : Array Nat := #[0xcea412780af3939db446,0x1186229d4091999d486c,0xd333ade8661efefceb7f,0xdf199d6f8fceb781387b,0x1f0124e7877e84be88c3,0x4c86cb263c15931e2c4e,0x498039b2bb1b9a99106d,0x324c021595d8e704e673,0x1ecea04f275027811864,0x18ec230c716a64389742,0x108778b813bc4409dc46,0x3d800a1940a00ca04ff1,0x188c30899994447b0015,0x83c8e041e27002413801,0x1820ccca10138607b332,0x70c13238109d7420444e,0x2c830f08c008046003a2,0x96c0084b600405d061f,0xc84e02a22701502e831,0x1ee6270c2e1380169ec0,0x7016f1187b73939ddc46,0x3d80281ec013cca0caa2,0x509c312c4e009164c65a,0x131c98c98caec4ab2632,0x95142301901380c609c3,0x701991180461ec022199,0x1580d033c367c4e03382,0xe88c0691921746c90ba2,0x985a10cc42300603d802,0x12c7502943d80479cc0,0xd066311804d9cc0a6446,0x647532323a99991d4c66]
private def g63D7Page7 : Array Nat := #[0x6d42a2b7018df95d0865,0xb7a910da350a6bda8655,0xe60f4c9377a749b6031,0x4e74abc43a55f31d2e91,0x7a63c1c629e0e69cefef,0x16a39808a602ecf2ec68,0x11721c058eec02d0740,0xdf6bd08fa5e8302af42,0x506f9c0637baf41bef41,0x5c867be8323df518dee8,0xfaf41be57a11f0bd0cf7,0x40a918e05488702a4437,0x9206f4e9007a747ed232,0x5070142837f3d3240de1,0x428683d23142caa0e088,0x8d13a42701921380c708,0xc36f1921c850d0ca4628,0xe2130c912bc6487e631,0x4eca08e75506031a814a,0x428650e031a850a1940f,0x13d3b28a39d54544e6a2,0x299e9d148f4eaa27a745,0xd9471ceaa37a64533c32,0xc705428352a141a8de9,0x428653a141c190a1a0b8,0x93d3b2d50a1966f4eca8,0xad90a196944e6b4cc635,0x1998f4cab778655bd139,0xd0914428689d4194550a,0xa86456bc322b4aa0e2c9,0x5513a2ab09915580c8aa,0x2a689d55584caaac0655]
private def g63D7Page8 : Array Nat := #[0xd95cad06ae7a7655bd3b,0xd06af7a765615432c1e9,0x98435e95432c5e9d95ea,0xed431af4a20d7af0c6bd,0x2e269d97198c6b8a8655,0x1972f4ecb959815ca943,0x4ecbabc645d21432e506,0x986460bd3b2fef1917ef,0x13d3b301e9d978a506bb,0x34e918da74886d32a836,0xd99af2eccd5a8166d232,0xceccec863672143335e9,0x7a7667da32b3d3a199d1,0xabd3b342d195a118cad4,0xb58aa19ab18cad52a836,0x19bd78c8de5a816f1541,0xc6df5a816fa14337902,0x7a7470d139b850a19bf8,0x1bd3a38de9d5c28508e1,0xb99e991ccf0c8e642847,0xdc578c8e07a65733c32,0x506e74283723d3ab890a,0x2a837421423950a0dca5,0x85e323c289cde180c6f0,0x3c5e9d1e2850cf040867,0xde88506f2786479a142,0xd08c3cc6461d232b2caa,0xa07561e132b0f0195879,0x53d3b316fd818944eac3,0x31caa198cf4ecca56836,0xd1af80c8d7a4646d3db0,0xecd8b4656c6542b5e89]
private def g63D7Page9 : Array Nat := #[0x2a866dc632b6de9d9b0f,0x520433a6d195d378c8e9,0xbaaf9d1d58506ea56837,0xd5d6f6c0ed4285753d3a,0xcaef2a836ea1423b2d9,0x2a837b2141bb9e995def,0xbc73ac5e99ce3b4ce91c,0xc69e99236f4e91979768,0x1a52f1091878838c2141,0x1091e78828f2141ca906,0xc07391bc41c81e20a40f,0x33c39c9af1d249788724,0xc950a124cf0e92642839,0xd24e810f25bc7492e039,0x88735428394214249de1,0x4186962cc0cb0aa0e714,0x93c414c8aa0e62f2ed2e,0x21e20e66f1053378849,0xc14f1060a7a84043c42,0xe80c408705de3a02dea,0xc264a3a1418350a1018f,0x4a941d2de9d28cf4e945,0xce9e99272f4e749bc43a,0xe7af4c94879769da0c3,0x4e73c28839ebd31cf661,0x7a63a6bd32cf9061a794,0x7bcbb501e9969c830d4c,0x50d0a128578e9412a83a,0xd04af4cb3f4283a22142,0x5082678841347420a1e9,0xbc7415bd410a5e20852f,0x521420b1e1d058850e2b]
private def g63D7Page10 : Array Nat := #[0xd7689d2b8f4c959a273b,0xd6b4f4e9582987aec73a,0x4c9688d86adc74256e39,0x5d80b3a0c05997602ccf,0x1a142d8aa20ac0530f6b,0x909020c82f4e6414284b,0x888f104447a83213c41,0x50647787323a143919ea,0x8e75bf3d31dee610ef68,0xce131de5e9cef4530f7e,0xe25e9d6f91ceb7c4186b,0x1b1184c7887a63c4cc21,0x50b85b663c0bd3ae2906,0x7a63c22141e1ad14f0c8,0x5a0c31a1020cd2f4e669,0x9a9e20cd57d066b42833,0x1902f5086a7884353d41,0x2ec6dbe83412141a0906,0x7976385f321c0a61cdaf,0x7bc421bdea08def1046f,0x9d2d14ce8530e847a843,0x8ea530e727976393d39,0x5067578833abd411d5e2,0x42873ca1419e50a1cf0f,0xd3c3a1f10a0cf8f0e67c,0x1f6d150fb68e87bc0733,0x1f28f4c67642833f3c3a,0x30f958e73cb14c3e5ca6,0xc0730a63400531600285,0xaa143851021c2978e814,0x5d0a1c2a850815c0730,0xd42e8508177a740bbc3a]
private def g63D7Page11 : Array Nat := #[0x5081a78740d3d3a85de1,0x42830c5e3a059e1d4348,0xda14186de9d430f0ea18,0x8710a103285061978750,0x941eb7020f42840e2141,0xcca127a6507a64283ed9,0x2a83ab2142556d994216,0x95240d493216a4b70352,0xd4a3216a4f4cb52a781a,0x1aa74903537b86a947c2,0x4c63441861914c0551ee,0xb4751cde3a0e301d06f8,0x921420caf1d06368ea3d,0xd1e1d068850e32b4751,0xd468f0ea3442841a3d3a,0x5083a78741d21428d1e9,0xb47519a1428e9e1d4748,0xabd3a8d5e1d46a810e33,0xd90a1476f0ea3b42851,0x1060f1042f42841e2142,0x70d704284baa142dd1e2,0xc0732a5f32144a602e2f,0x75a3a966d14cb37cc852,0x93d0a0c9f68a64fc0732,0xcca3788651428727da3a,0xea51428328bd39945e1,0xbc432b2142945e9d4a2f,0xb3c3a9590a0cacf0e656,0x942d1d4a18b005042852,0xd4a4f0ea524287282043,0x50a5778752ba142949e9,0x7a6325a1419610a0ca68]
private def g63D7Page12 : Array Nat := #[0x95a29e490a1722f1064d,0x639ee1b1af4c78d4283c,0x1726f105937b86c7a0c0,0xe689c07343db32a21e2,0x4287443c3a2250a0d12f,0xc2141e850a0d16f0e88a,0x675e98f3683019a7a64c,0x1b3cf10d9e8c85cf20c0,0x109a27882d1464267dee,0x7883d1bc4168ca60348f,0x3c421010a107ef0ea3e,0x9790a1cba83025d78852,0xcc4f0a66242832fbc3a,0x70c5b2b812dbc42989e2,0x7873483dc3170ae00b8f,0x9bc39a4de1d120850690,0x2450a1d1ef0869378744,0x128f086984283493c3a,0xe896b4744aa143a5106,0x8c8546bc21a690a0d2ef,0x2c6c0994a6011cf70c8d,0x98de1d4c6f0e4638e813,0x4c8f0ea667872332142,0x302654285323c3a99106,0xb48232dbc0996d604ca8,0xe3c39272820ccf6d0465,0x275e1d13cf0e49e78744,0x3f006400078744fbc3a,0xf403600bc024c07a0178,0x10608166052c12d04400,0x90c22908141dc06fc1a,0xbc42c70ac829d0a1c267]
private def g63D7Page13 : Array Nat := #[0x983c20e683700d303200,0x84b6123845a10cc4110f,0x56c154853e1494502135,0x3918345e917205a915e8,0x71b606c41a7467619146,0x1e907831d647301c4c6f,0x168831205c7f41f6c7c3,0x848f9237c8ba225c87b2,0x9bc2668981259494124,0xa9429c4a5528d4a1627a,0x742d34b222bdcad02aa4,0x7306cbfc2f6cbb02e50b,0x339ccb53244c7e3130c3,0x780dbe3664d7334f8d11,0xe9439c8e4f3878e073,0xcf9f3dccf503c84eea3b,0x8a41950404068ff13ef,0xa345f514c44890f24301,0xe4a2d26d493921647791,0x4d8533b4c712f44b1129,0x12d4264fe13da4ebd37f,0xc150053a14bf529147a5,0x15d156e159b55c955654,0x6b75a55665592961757c,0x935dd174d5cc170a5b81,0x260f98225fbd7d15eb57,0x64398ea63218a5620186,0x79d9c2667d96e6541930,0xe5a9869eda5468a9a086,0x9b456c7db0b6bd5ad76a,0xc1a6fddbda6ecdb946da,0xec7325c9671edc5d7121]
private def g63D7Page14 : Array Nat := #[0xc7451d0c7411cfc73d1c,0x7511d3c74d1d2c7491d1,0x5d1d6c7591d5c7551d4c,0x91d9c7651d8c7611d7c7,0x1dcc7711dbc76d1dac76,0xdfc77d1dec7791ddc775,0x2c7891e1c7851e0c7811,0xc7951e4c7911e3c78d1e,0x7a11e7c79d1e6c7991e5,0xad1eac7a91e9c7a51e8c,0x91edc7b51ecc7b11ebc7,0x1f0c7c11efc7bd1eec7b,0xf3c7cd1f2c7c91f1c7c5,0x6c7d91f5c7d51f4c7d11,0xc7e51f8c7e11f7c7dd1f,0x7f11fbc7ed1fac7e91f9,0xfd1fec7f91fdc7f51fcc,0x9201c805200c8011ffc7,0x204c811203c80d202c80,0x7c81d206c819205c815,0xac829209c825208c8212,0xc83520cc83120bc82d20,0x84120fc83d20ec83920d,0x4d212c849211c845210c,0x9215c855214c851213c8,0x218c861217c85d216c85,0x1bc86d21ac869219c865,0xec87921dc87521cc8712,0xc885220c88121fc87d21,0x891223c88d222c889221,0x9d226c899225c895224c,0x9229c8a5228c8a1227c8]
private def g63D7Page15 : Array Nat := #[0x22cc8b122bc8ad22ac8a,0x2fc8bd22ec8b922dc8b5,0x2c8c9231c8c5230c8c12,0xc8d5234c8d1233c8cd23,0x8e1237c8dd236c8d9235,0xed23ac8e9239c8e5238c,0x923dc8f523cc8f123bc8,0x240c90123fc8fd23ec8f,0x43c90d242c909241c905,0x6c919245c915244c9112,0xc925248c921247c91d24,0x93124bc92d24ac929249,0x3d24ec93924dc93524cc,0x9251c945250c94124fc9,0x254c951253c94d252c94,0x57c95d256c959255c955,0xac969259c965258c9612,0xc97525cc97125bc96d25,0x98125fc97d25ec97925d,0x8d262c989261c985260c,0x9265c995264c991263c9,0x268c9a1267c99d266c99,0x6bc9ad26ac9a9269c9a5,0xec9b926dc9b526cc9b12,0xc9c5270c9c126fc9bd26,0x9d1273c9cd272c9c9271,0xdd276c9d9275c9d5274c,0x9279c9e5278c9e1277c9,0x27cc9f127bc9ed27ac9e,0x7fc9fd27ec9f927dc9f5,0x2ca09281ca05280ca012,0xca15284ca11283ca0d28]
private def g63D7Page16 : Array Nat := #[0xa21287ca1d286ca19285,0x2d28aca29289ca25288c,0x928dca3528cca3128bca,0x290ca4128fca3d28eca3,0x93ca4d292ca49291ca45,0x6ca59295ca55294ca512,0xca65298ca61297ca5d29,0xa7129bca6d29aca69299,0x7d29eca7929dca7529cc,0x92a1ca852a0ca8129fca,0x2a4ca912a3ca8d2a2ca8,0xa7ca9d2a6ca992a5ca95,0xacaa92a9caa52a8caa12,0xcab52accab12abcaad2a,0xac12afcabd2aecab92ad,0xcd2b2cac92b1cac52b0c,0x92b5cad52b4cad12b3ca,0x2b8cae12b7cadd2b6cad,0xbbcaed2bacae92b9cae5,0xecaf92bdcaf52bccaf12,0xcb052c0cb012bfcafd2b,0xb112c3cb0d2c2cb092c1,0x1d2c6cb192c5cb152c4c,0x92c9cb252c8cb212c7cb,0x2cccb312cbcb2d2cacb2,0xcfcb3d2cecb392cdcb35,0x2cb492d1cb452d0cb412,0xcb552d4cb512d3cb4d2d,0xb612d7cb5d2d6cb592d5,0x6d2dacb692d9cb652d8c,0x92ddcb752dccb712dbcb,0x2e0cb812dfcb7d2decb7]
private def g63D7Page17 : Array Nat := #[0xe3cb8d2e2cb892e1cb85,0x6cb992e5cb952e4cb912,0xcba52e8cba12e7cb9d2e,0xbb12ebcbad2eacba92e9,0xbd2eecbb92edcbb52ecc,0xd000abc52f0cbc12efcb,0xc0d0a00bd0b80042c1,0x5f81016c2e0809d1741,0x42001a240891402b0184,0x5148d61c0012a1707a84,0x705070a6c5087831220b,0x5804b0f04a081483a49,0x828c3824498224281c2a,0xf0a4aa0413065c208fc0,0x5784c2012c1d0f83f85,0x529c508a47068433140c,0xbc4d074875068710483,0x30b0525d0e090c93048a,0x224869000e03c2ee1e05,0x6260012e2170d0542fc1,0x222856148f300c88524c,0x8105360509d134331147,0x119425384e1308028447,0xa1a226085e47bc383543,0x289c09208e90481a2917,0x1006101d047102b5249e,0xa0d0386a024001c61882,0xc94f8806142fbcb20c18,0xdef2c834e14a648fe504,0x8a8c093168db8e38c3cc,0xb214033d900e68a8f8e6,0x42e794640ad32c898565]
private def g63D7Page18 : Array Nat := #[0x3d96c816d65b2620a3b8,0xfe64612307d7e6635980,0x5acb3f991848dca85c1c,0xee682773410bcd05d1d6,0xb22ec013404a52e69ace,0xe6c00a23c388c0019dbc,0xeb1006686ee1800218fe,0x32e78c673ef30e0284d3,0x55d516d0a4fc3bb42241,0xb2266ef8279c798268a,0xe814428660e62b656f3e,0x82f6b0c18372e7265b7d,0xac65267cd86a3ab64f76,0xbf000a13bda03b21784b,0xd7f371032467f892332f,0x6480cffa3fc2333ea0c,0xbcd8abf0ac45332f9cb8,0x25347405b6c88cd8da12,0xc3000432f010f801238c,0x6271891195f1649090dd,0x8fc0c561056c307dc56c,0x4478f4ec00333e9f8489,0xcbd816ca3dca28a27942,0x332fb0288bfd01d446a,0xc53a34e18e023465fcc8,0x265b598c1ce17922ae7b,0x1223ca09ac019c9ba63,0xe02353c7b0271ff8fb4d,0xa9e64784274f7ad1ce18,0x204198ef2049e14820e0,0x120865716502410d9f86,0x536137e268b02403a2d8]
private def g63D7Page19 : Array Nat := #[0xdb7f1c419b9fc1a0e180,0x48b3dd671140fcf804f4,0xadd1a98c9a3edd45ba83,0x1439e7e8701427e620d,0x3e7f2b5004ce0f7c1422,0xf4310400880ffc904003,0xfc4b2142324aabb0bac3,0x12eb19499a29a64d6533,0x800de1f2c3267ea4f44,0x3aa187f384246073fba9,0x288a6f7fc5119814fe56,0xe2d42a23383c3c2c5084,0xe9384790d19403d197bf,0x18aa14050e2ed6c9094e,0x7454a66dff79483a3cbe,0x52ca0bc28256505e143a,0x41361e1c1a368c92e880,0x6043361216487470e952,0x1f874c119cbffc50046,0x2c10080d5dfab5303346,0x4ff0fe208040690ffacd,0xf206644ff8f904004069,0x74c08529c0c7f98a1337,0x52216bfff0181819f1fb,0xfc4d8cd6b7122101efef,0xe9e5ccd0ce7e41414273,0xd9c8a34fddab690ce1f,0xe9fc4865b7403d911218,0xa0220482ffed63890ce5,0xb6e1ea2ccd5da01907fe,0x15bfedd812b19cf54098,0x2d648a02db64e6ce0662]
private def g63D7Page20 : Array Nat := #[0x2a21e20cce4884e0788c,0xdcd12f368102147e2af2,0x1633dc91c262fa79f544,0x430aafda294237ffb094,0xc666e03fe039991f7664,0xa15a23dc84909fbf9246,0x32f7108c9d9107d927f3,0x10850eb1aa72377e198a,0xf9c38456b178337f27c4,0x1712fc9997bcbc664043,0x828a79b41210b9cf0494,0x6351161f6468843ffa60,0xc23c4220681f1311157f,0x6fa48448593b744090df,0x848f609a9e10fbf8224e,0xa8abe7c8b211c0f9f22c,0x794b51fb9a9ee127c8b,0xbedd05775510195e347,0x85af0f3c632eb0fc4d9,0xe8b0b5fda9190dc1f90d,0xcd76e2cb76801a36330e,0x51f5d28806ddcbd9086e,0x8b99448737e2106752f5,0x35fe7ce42035f6]
def g63D7 := limbs80 #[g63D7Page0,g63D7Page1,g63D7Page2,g63D7Page3,g63D7Page4,g63D7Page5,g63D7Page6,g63D7Page7,g63D7Page8,g63D7Page9,g63D7Page10,g63D7Page11,g63D7Page12,g63D7Page13,g63D7Page14,g63D7Page15,g63D7Page16,g63D7Page17,g63D7Page18,g63D7Page19,g63D7Page20]
private def g63H7Page0 : Array Nat := #[0x500820053e1042600400,0x509c801c426240000c29,0x1b7001088000d93aa002,0x388c8cc0078e14cca800,0x112f9c58000008e80005,0x76a000000bc2,0x1ec00043f562,0x5dd22a9a1c0000017800,0x319348900068d00020ed,0x3080022598c00030b981,0x180045a8186e5d800,0x1ac9820005280000,0xa2000001ae0002b50000,0xefd22000001a0000d93,0xf000001d3cc300000000,0xbbeed4cb9ff50000d4c2,0x4e4980000000371a167,0x8002b700178696b51a7b,0x5800001c8b8c4c000085,0x9c0018adda20f0000007,0x18588000000d2a09d717,0x4e14001b200162541710,0x7a5ea39b3aa5325000a1,0x1b101a47cb80049f524a,0x4c4b2f6b45f800948003,0x183d700080d9b800,0x6a05180]
def g63H7 := limbs80 #[g63H7Page0]
private def g63D8Page0 : Array Nat := #[0x4401010c10108100c810,0x9901098c109881098410,0xc420d0410cc410c8410,0x984205842010c2010420,0x10c21d0420cc42099020,0x99421990215802114c21,0x8430d4421d0421cc421,0x99030584301083010430,0x1483110831d0430c8430,0x98031580311943119031,0xcc431994319903198831,0x5843258032d4431d0431,0x8440994329903298432,0x98440584400c8400c440,0xc841cc440c844098c40,0x1944114c411484110c41,0xd044198c419804158041,0x584425804214c42d4441,0x58443580431944398442,0x8450988439844398043,0x10850104500c8500c450,0x984505845014c5010c50,0xcc450c84509905098c50,0x10c51108510c851d0450,0xd44519905198c5158051,0x98452584525805210c52,0x98453584535805399052,0xc9100c5100851099053,0x1451010d101091010510,0x189101511014d1014910,0x98910195101911018d10,0xc4110995109911098d10]
private def g63D8Page1 : Array Nat := #[0xcc510cc110c8510c8110,0x8610d4510d0510d0110,0x10a10106100ca100c610,0xc4210992105861010e10,0xcb10d0610cc610c8610,0x14f1014b1010f1010b10,0x99310197101931018f10,0xcc310c8710c831099710,0xd4710d0710d0310cc710,0x1472010f20107200c720,0x99320987205872014f20,0xd0320cc720cc32099720,0x107210c721d4720d0720,0x5832114f211472110f21,0xd4721cc7219972199321,0x1473010b301073008730,0x1933018b301873014b30,0x98b30987305873019730,0xcc730c87309973099330,0xd8730d4730d0730d0330,0x14b311473110b3110731,0x197311933118b3118331,0x9933198b319833158331,0xd8331d4731d073199731,0x10f400cb400c74008740,0x1974014f4014b4014740,0x98f4098b409874058740,0xd4740d0740cc740c8740,0x1974114f4114b410cb41,0x98f4198b419834158341,0xcb500c75008750d4741,0xc875010f5010b5010750]
private def g63D8Page2 : Array Nat := #[0xcb51d4750d0750cc750,0x5835114f5110f5110b51,0xfaf4fe7d1f9935198f51,0xfafcfdfefd7dbdddedf5,0xfedf5f7f7f7fbedeeef6,0x13ab183bb00ffffefefd,0x3403a9286b815413aba4,0x2021b318221bb00c13a9,0xd310244bb02173282193,0x25732825932025b31825,0x2829b31829d310284bb0,0xb318005398104bb02973,0x44bb001732801932001,0x18144bb005732805b318,0x4bb009732809b31809c2,0x19a3a019b39019a39018,0x981d93901c53981db3a0,0xb8a09138a010b8a0193,0x110b8a11a31a09138a09,0x820453b1b493a9b5138a,0xa31a0d2b820c53b1b92b,0xbd2b82192b821453b1c1,0xb1bc4bb1bda319bd2b81,0x53b1c44bb1c52b81c453,0xd04bb1d11389d10b89d0,0x19c91389c90b89c853b1,0xb89d453b1c84bb1c9a3,0xd44bb1d5a319d51389d5,0x81f20b81f1b319e053b1,0x5399e44b89f1eb89f04b,0xe85399f44b89f44b81f4,0xb21c93aa1c5399f85399]
private def g63D8Page3 : Array Nat := #[0x2b82444bb2212b82404b,0x484bb2285bb245b31a45,0xb2252b8224439a352b82,0x4bb2304bb22d2b822c4b,0x7d0b8a7d0b8a74539a38,0xb2804bb2790b8a85b31a,0x4bb2504bb24c4bb2884b,0x550b8a544bb2590b8a58,0x82604bb25d0b8a5c4bb2,0x539a6c539a644b82644b,0x444bb02c539a70539a68,0xb0305bb0444bb045b318,0x53983c4398384bb0484b,0x404b88404bb035b31834,0xb2b84bb291b31ab45398,0x4bb2c04bb2945bb2b84b,0xa8439aa44bb2c44bb29c,0x8aac4bb2a04bb298539a,0x539ab04b8ab0539aac4b,0x704bb0804bb06c93a86c,0xb085d310844bb071d310,0xd39b304b887c4bb0744b,0xf04bb2f093aaf0d39af0,0x832c53b3284bb32853b2,0x930b2e8b0b2eb3832eab,0x3453b2f44bb2f4d39af6,0xb2fcd39afc53b3344bb3,0x53b3384bb33853b2fc4b,0x19fb0b19eb0b052b8304,0xb2f84bb2f92b833c93ab,0x53b3004bb300d39b0053,0xc4b830d2b830d2b8308]
private def g63D8Page4 : Array Nat := #[0x8b112b83104b8b204b8b,0x4bb0cc93a8cc4b8b244b,0xe9b318e84bb0d04bb0e4,0x98dc4398d85bb0e84bb0,0x93ab804b88e04bb0d453,0xb44bb3844bb3b04bb380,0xb390b39bb85bb3b44bb3,0x93aba4439ba04bb3bc4b,0x944bb388539ba5821ba4,0xb399b31b98ab8b8c4bb3,0x539b9c4b8b9c4b8bac4b,0x699321684bb13d93213c,0x196c4bb1419321404bb1,0x5bb16c4bb16d93216db3,0x596299584bb1704bb148,0x214453995d62a1584399,0x4bb1504bb14c4bb14593,0x644b89644b896093a154,0x91659389658b89645399,0x73286043985593996593,0x684bb0657328644bb061,0xb0504bb04d73284c4bb0,0x4b805c5398584b80584b,0x5d73805d6b805c53985c,0xb2c8439add73a05d7398,0x4bb2d44bb2cdb31ae84b,0xe04bb2d84bb2d1b31ad0,0x9ae44b82e4539ae04b82,0x4bb0b44bb0b1b3189853,0xa44b80904bb08c4bb088,0x3504b80a84b80944b80,0x1b0364f393510b8b520b]
private def g63D8Page5 : Array Nat := #[0x744bb3410b8b7cb3a366,0x9b44d39b784bb348d39b,0x4bb34c53b3444bb344d3,0x590b8b590b8b5453b34c,0x8b5c4b836c4b8b584b83,0x4b83704b8b5c4b835d0b,0xc439901821901932100,0x88f04bb0f44bb0ecb399,0x4b81084bb0f9b318f8ab,0xc0439bd05398fc4b80fc,0x83dc4bb3c84bb3c44bb3,0x732980539bcc4b83cc4b,0x7573218d73198c439981,0x81844bb17c4bb1784bb1,0x439c1c5399884b81884b,0x184bb4144bb4104bb40c,0x84244b842093a4188b84,0x5b80bc5b88b8539c244b,0xc84b88c44b80c44b80c0,0x19185b89184b88c84b80,0x43991c5b811c43991982,0x145399218219204b8120,0x81984399945b89944bb1,0x4b819c4399996299985b,0xa04b81a04bb19053999c,0x892883a9285399a04b89,0x5b812d7ba92963a9285b,0x244b81244b813493a934,0x81ac5b81a85b89a44b89,0x3900c4b89b04b81b04b,0x2703a00f03980f02180f,0x200222181233182a3320]
private def g63D8Page6 : Array Nat := #[0x1901fe33180662180633,0xfe2319ff1a01ff1981ff,0x19ff0311ff0291fe2321,0x321ff0319ff0299ff02,0x1539a02331a02231a03,0x1a0953a2023322022322,0x43a20a33220a23220ac3,0x12231a12621a1153a209,0x19b6632211539a12331a,0x2321b55399b63319b623,0xb553a9b553a1b63321b6,0x2205539a06231a0553b1,0x3321ba2321b953a20623,0xba3329ba2329b953a1ba,0xa20e23220d53b1b953a9,0x3319c22319c26219c153,0xc23329c22329c15399c2,0x9a16231a1553b1c153a9,0x231a1a429a1a2319cd53,0xbd53a21a42a219539a1a,0x21be2321bec319bd4b81,0x53b1bd53a9bd53a1be33,0xc62319c66219c54b81c5,0xa9c66321c55399c63319,0x2319d24299d153b1c553,0xd153a1d15399d23319d2,0x19de3b01dd53b1d24329,0x2321dd5399de3319de23,0xde2329dd53a1de3321de,0x99ee2319ed53a9de3329,0x4b81c953a1ee2321ed53,0xca2329ca6321cac319c9]
private def g63D8Page7 : Array Nat := #[0xb1c953a9c943a9ca3329,0x53a1d6c319d553b1c943,0xe153b1d543b1d64329d5,0x29e153a1e23321e22321,0x3391e153a9e23329e223,0xda3391f153a1f22321f2,0x99e543b1da4329da6321,0x53a9e63329e62329e553,0x3d53a1f95399f95399f5,0x1a1efa0a1ef98a1f021a,0x53a21e33221d539a1e33,0x42331a42e20a42e18a41,0xa2153a242332241539a,0xe20a4553a222332222fa,0x2a621a2953a246332246,0x9a4a331a49539a2a331a,0x23923622123621923553,0x2623a236239a36221a36,0x1a2e621a2d53a2263322,0x231a77198275539a2e33,0x76232275539a76331a76,0x227e23227d53a2763322,0x621a8553a27d43a27e33,0x8d539a86331a86231a86,0x1a52621a5233224e429a,0x331a5a231a5a429a5a33,0x554b825553a259539a5a,0xaa5543aa56332a56232a,0x2b082e532a5d53a25d53,0x2d53a02d43a02e33202e,0x83153a0463320462bb0,0x5398323318326218322b]
private def g63D8Page8 : Array Nat := #[0x3953984a33184a2bb031,0x183e23a03a23983a2218,0x330ab62b0ab6d98ab622,0xb63322b5538ab54b8ab6,0xabe7a0abd53a2b543a2,0x538abd4b8abe330abe2b,0x91539abe331abe621abd,0x22922b0a92d98a914b82,0x332a9153a29143a29233,0xba3322b94b82ba2bb292,0x8296332ab953a2b943a2,0x621a962b0a967a0a954b,0x96332a95539a96331a96,0x9ac2331ac14b82c22bb2,0x539a9e331a9e332ac153,0xc5539ac6331ac553a29d,0x9aa6229aa6221aa553a2,0x221aaa23a2a622a2a623,0x994b8a994b829a229aaa,0x8aa14b8aa2332a99538a,0x33206e2b086d53a2a153,0x7153a08233208153a06e,0x907a22107a2bb0722b08,0xd98b3153887623a07a23,0xf2d98af14b82f27a0b32,0xa2f23322f22322f22b0a,0x2323294b832953aaf153,0x2d53ab2953a32a33232a,0x932ec2132ed30b2ec20b,0x4b82f6d3932ed3132ec2,0xf6d39af62b0af67a0af5,0xaaf543aaf6332af6232a]
private def g63D8Page9 : Array Nat := #[0x4b833633b2f62bb2f553,0x3543ab36332b36232b35,0xa33953a2fe5a8afd53ab,0x4b8306432b3953a33a42,0x162313163313062b0b05,0xa3162393162293162213,0x22931a23131a3b0b1a22,0xf94b82fa33133d4b833e,0x8b0153aaf9538af94b8a,0x4b830953a301538b014b,0x1d4b8b1d538b094b8b09,0x98ce3318ce2b08cd538b,0x2b08d15398e63318e553,0xda2390da2190da2bb0d2,0xb814b83815388d62398,0x331b82621b822b0b827a,0xb14b83b153ab81539b82,0xabb1539bb2331bb2621b,0x7a0b86d98b854b838553,0x86232b8673a3862b0b86,0xb38553ab8543ab86332b,0x232bb54b83b633b3862b,0xb953abb543abb6332bb6,0x9b92331b925a8b926193,0x539bbe331bbe429bbd53,0xa22393a22293a22193a1,0x838a229ba62293a6229b,0x53ab89538b894b8b894b,0x96429b95538b954b8b95,0x8ba94b8ba9539b96331b,0x4b8bad538b994b8b9953,0xae338bae2b8bad538bad]
private def g63D8Page10 : Array Nat := #[0x993e33193e2b093e3393,0x53996a33196a33213d53,0x4242a1422b0942332169,0x216e42a16e2bb1423321,0x33194a42994a2b094a33,0x7233197242997153994a,0x915a22115a2191595399,0x23a15a23995a22195a23,0x4e33214553894622195e,0x9be553994e33194d5389,0x53abea5a8be9539bfd53,0x5539bf25a8bf233b3ea,0x8bf5538bee421c09539c,0x398855538bf9539bf553,0x562218563a88563a0856,0xa0563398562398562298,0x23a85633a05623a05622,0x6143a06233206233a856,0x804e33186a3318663328,0x4b805233284d4b884d4b,0xde221add53a0514b8851,0x82cd4b82ca22a2de229a,0x53a2ed539aee331aed4b,0xd94b82da332ad14b82d1,0xa09a33209a33109953a2,0x3a089943a89a33289943,0x9a22909a22109a3a889a,0xa09a22a09a33909a2390,0x33a89a23a89a33a09a23,0xad53a09e33209e33109e,0xa08d4b888d4b808ec290,0x3313523328a14bb08d53]
private def g63D8Page11 : Array Nat := #[0x6622a362229362221362,0x2b414b834233137d53a3,0x53a37a42a37953ab4223,0x4d4b834d53ab454b8345,0xa36a2323694b836953a3,0x33110153ab6a232b6953,0x23a8901439902331902,0x91022391022291022191,0x33990223990222990233,0x633110633a90223a902,0x19124299115399063319,0x4298f54b88f54b80f633,0xf94b80f95398f63318f6,0x9bd22293d22193d14b88,0x4b83c2429be1539bd622,0xc6429bc54b83c553abc1,0x9bd94b83d9539bc6331b,0x2b83dd4b83dd4b83c953,0x822191814399823383de,0x99822219822391822211,0x33217642198e23a18223,0x1e21941d4b817e33197a,0x240d4b840e221c1e2214,0x539c12331c114b841233,0x222b84214b84214b8415,0xa0b9539c254b84263394,0x22a0be23a8ba23a0ba22,0x1a23991a22991a23a0be,0x992223991e22991e23a9,0x2389954b89154b811622,0x962399962219963b8996,0xa19a23999a22199a23a1]
private def g63D8Page12 : Array Nat := #[0x4b89914b819222199e23,0x295b8929438929538991,0xa92a23912a3b892a2389,0x23912d5389314b893223,0xa54389a55389394b893a,0x91a63b89a62389a55b89,0x23a1aa2391aa23a1a623,0x72219b7219213221a02,0x92172299c32291c3221a,0x2321bf22a1bf21921b21,0xd32219d32299c72329bf,0xa1e32321d72219df2321,0x21924b221a43221a1f22,0x5322a24f219287221a77,0xa293398abf221a5b229a,0x229ac3229a9722a2bb22,0xf33a8af3221ac7221a9f,0x93372292f722a32b22a2,0x229b83398b8322133b22,0xb72293b7229387229bb3,0x193f2193bf2193933393,0x22116f22114322196b22,0xff221be721917321914b,0x94072193f3221403221b,0x232203231a032219ff21,0x1323220b23120b22120b,0x19b72299b7231a132312,0x2311bb2291bb2321b723,0xc32311c322120f2321bb,0x1a1b22121b2219cf2319,0x2319c73329bf3321bf22,0xd33329c72329c73319c7]
private def g63D8Page13 : Array Nat := #[0xa1df2319df2299df2319,0x2329cb2219ef2321df22,0xe32391e33b81e33329cb,0xa1e323a1e32321e33391,0x3391e733a9e323a9e333,0xb722127f2212473399e7,0x8a9733aa933a8a933a0a,0x3322f33a0af3390b333a,0x2b33232b23232b332af3,0x93373a8af7332b2b232b,0x331b8333a33b2212ff33,0xeb2213eb339143331bb3,0x884f33804f2b804f3393,0x3382d32b82d3221aef2b,0x9b23909b22909b2b8ad3,0x910322137b23a89b23a0,0x2b88fb2b80fb23990323,0x32219832b83cb2193e3,0x3c01c0014800e4008000,0x5804140370032c02ac02,0x64061c0578051404a004,0xa8083407c0072406ac06,0xf40a800a3c0984092008,0x640d040c7c0c040bb00a,0xb40f400ed00e540dc40d,0x3411c4113010bc10300f,0x1813cc136812fc12b012,0xd4164815e8154c148414,0x2018a0183c17a4173416,0x381b901b041a3c19b819,0x401e841e081d8c1cfc1c,0x542190210c20881ff41f]
private def g63D8Page14 : Array Nat := #[0xf8244423e4237c230022,0x4826d82690262025b024,0xb0293028b0285c27b827,0x202be42b582ab42a4429,0x282da82d282ce02ca42c,0xe82fa02f2c2ef02e702e,0x3431e83178310830602f,0x943404335832c8327c32,0x2c36cc3614358c351434,0xc8395038d8384037b437,0x403bb83b283a983a2839,0xe43e683de03d483cb03c,0x7c40e4405c3fc43f343e,0xf0435c42dc425041e041,0xc8461c457c44f8448043,0xf8493c48b44800477046,0x84c744bec4b184aa449,0x884ef44e804e084d804d,0x5851dc512050784ffc4f,0xdc5478541c538c530c52,0x6456d8564c559c553854,0xc4594c58dc587457e057,0x285bc45b605ac85a4859,0x905e205d6c5d185ca85c,0xfc60545fd05f6c5f0c5e,0xa86318628861fc617c60,0x586604657c64e0645c63,0xd8684467bc674066cc66,0x786ae46a6469e0694c68,0x206d9c6d2c6c986c0c6b,0x4c6ff46f946f246e946e,0x9c7228717c712870c870]
private def g63D8Page15 : Array Nat := #[0xec756074a473bc733472,0xfc786c77e07728764c75,0xb87b247ab079f4795c78,0xc07e3c7d987d047c5c7b,0xa8810880687ff87f487e,0xc4842883b882e4826481,0x878086c88624857084,0x788aac8a24897c88b488,0x788dd08d248c948c088b,0x3090c490488fb48f108e,0x9493009280921c91a891,0x95a4954494b0945093,0xdc9828979c970c968496,0x7c9b189ab49a24999498,0xe49d549ce49c549bf09b,0x189f889f1c9eb49e409d,0x6ca210a1b4a11ca09ca0,0xa47ca404a36ca2eca2,0xd4a728a680a614a584a5,0x60a9d8a958a8c8a838a7,0x34acb4ac40ab84aaecaa,0xdcaf50ae70ae1cada4ad,0x44b1e0b17cb0fcb05caf,0x98b420b3acb33cb2c4b2,0x48b6b4b614b5a4b524b4,0xccba14b958b8a4b818b7,0x78bd0cbc58bba0bb1cba,0x4cbfa4bf10beb8be20bd,0x4c294c228c160c0d8c0,0xd0c50cc47cc414c390c3,0x94c7dcc768c6f4c658c5,0x78cad8ca4cc9d0c92cc8]
private def g63D8Page16 : Array Nat := #[0x88cdf4cd60ccc0cc44cb,0x14d090d004cf80cefcce,0x18d2bcd260d208d1a0d1,0xcd558d498d43cd3b0d3,0x70d8f4d838d76cd6dcd6,0xecdb70dafcda9cda2cd9,0xe4de2cdd70dca8dc48db,0x7ce1a4e0f8e040dfb4de,0x30e564e4d0e414e334e2,0xfce954e858e7ace6f0e6,0x4cecb0ec30eb9ceaf0e9,0x18ef88ef08ee7cedf0ed,0xe8f300f224f184f0ccf0,0x64f6b4f5f4f53cf4b4f3,0x8cfa90f9e0f8ecf828f7,0xfcfe48fd88fcccfc44fb,0x79027d01a500a8ffe0fe,0x2d067505ad04f1044503,0xc50a09098508b5081107,0xdd0d490cad0c190b810a,0xa910b9101d0f810eb50d,0x111451135d12f5125911,0xcd1819178d16cd15d915,0x891b151a911a2519a118,0x5d1e851dd11cf51c111b,0x5922ad21ed214120391f,0xa92619255924c9240523,0x6d299528e1284927a126,0x512ce12c512ba92b112a,0x9d2fe92f1d2e8d2df92d,0x95331132853211318130,0x25358534d1345d33e933]
private def g63D8Page17 : Array Nat := #[0xa1381937b5375536d536,0x793ac13a3539b1391d38,0x553ddd3d313c753be93b,0x9140ed40353f813f0d3e,0x91441943a142bd423541,0x6d4705465545d5455144,0x7149f149494881480147,0xb54cfd4c394b754ad94a,0x2550754fb14eed4e654d,0xf9534952a9523d51d151,0x91569d55f15539548553,0x315a7559e1592d586157,0x895d195c995c255bb55b,0x55f8d5f1d5e7d5de95d,0x5961e9615160fd608960,0xd16415639d633162c162,0x1675d66c16625656564,0x8d6ac16a256939687968,0xc16e056d4d6cb96c1d6b,0xc5712170896fd96f796e,0x2d747573b57321723171,0x6577f57769768175bd75,0x317b397a5979a1792978,0x657e897dcd7d157c9d7c,0xed81d5815580b57fe57f,0xc5861d859184cd83c982,0x5897988f18845873586,0xd58d098c418b718ac58a,0x3d90798fc98f318e818d,0x1938d92fd924591f191,0x19967995e9954d948d94,0x7199ad98fd984597cd97]
private def g63D8Page18 : Array Nat := #[0x559d399c859bc99b0d9a,0xd9a141a0699fa19f059e,0x89a411a351a2d5a249a1,0x5a795a701a641a571a4,0xadaaa9a9e1a919a899a8,0x71ae9dadbdad09ac79ab,0x1db199b115b08dafe5af,0x6db4e5b411b3adb2edb2,0x9b7a5b701b689b5f1b5,0xf1bb35ba75b9ddb8e9b8,0xfdbe8dbdd5bd5dbcb5bb,0x11c175c0d9c025bf85be,0xedc461c3b5c355c2a1c2,0x4dc6e5c671c5e1c561c4,0xedca79c9c1c905c805c7,0x9ce7dcdadcccdcbc1ca,0x39d155d0d1d019cf85cf,0x61d4d1d45dd399d2d9d2,0x81d7bdd715d689d5e1d5,0x5ddb51daadd9e5d955d8,0xe5df81dec1ddf1dd1ddc,0x1e245e1dde151e0b9df,0x9de605e545e489e3cde3,0xc9e921e899e811e755e6,0xe5ec3deb81eafdea79e9,0x99efb5ef21ee31ed69ec,0x59f3bdf311f235f1a5f0,0x81f6c1f611f575f4e1f4,0x79fa81f9adf8edf821f7,0x75feb9fe09fd39fc3dfb,0x8a01fe018200c60025ff,0x9a051e048203e2034202]
private def g63D8Page19 : Array Nat := #[0xc6081a075606da065e05,0x260b9a0b060a7209a208,0x2a0f120e4a0d8e0cd20c,0x7e139612d211f2110a10,0x921722169615ee155214,0xb21a1a193618b2180a17,0xc21dda1cf21c221b4e1a,0x2a21ba211620521fae1e,0xe2251a2462237222f222,0x36289e2812275226c225,0x8e2b922af22a6629b629,0x2a2f7e2ea22dfe2d4e2c,0x4232c2320a318630da30,0x9635ee352a346e33a233,0x7a397a387a37aa371636,0x963d223c563ba23b163a,0x52408e3ff23f023e3a3d,0xa24412439642e2421e41,0xa246d2464a4582452644,0xa64abe4a0e4952484647,0x2a4ea64e024d2a4c824b,0xba51fa515a50664fe64f,0xce54fa548253fa534e52,0xf25972586a576e569e55,0xfe5d1a5c4e5bb65ac659,0x6a60665fea5f565ede5d,0x2e63866302627e61fe61,0x2e66a26616653264ae64,0x8e699668d26872680a67,0x3a6d8a6cb66c166b4a6a,0xbe7112708a6fb66f0e6e,0xca742e737a72da724671]
private def g63D8Page20 : Array Nat := #[0x9676fe762a75c6754674,0xae79e2791278ae781277,0x2a7d867cd27c367b8a7a,0x8280b280367fae7ed27e,0xba843a83c682e2825681,0xf6875686c6860a856a84,0xb28a0a897a890a888a87,0x228d628cba8c028b3e8a,0x4a908a8ff68f568ec68e,0xb6941a938292a691c691,0xfe981a9732967695c294,0x269b5a9ad69a1a99aa98,0x529e7e9de29d1a9ca29c,0x52a29aa1d2a102a01e9f,0xf2a63ea57aa4bea402a3,0xa6a9eaa932a89aa7b6a6,0x46ada2acfeac26ab4eaa,0x26b152b076af96aed2ae,0x82b4c2b41eb366b2aeb2,0x92b872b7c2b712b64ab5,0x32b912b8f2b8d2b8b2b8,0xd2b9b2b992b972b952b9,0x72ba52ba32ba12b9f2b9,0x12baf2bad2bab2ba92ba,0xb2bb92bb72bb52bb32bb,0x52bc32bc12bbf2bbd2bb,0xf2bcd2bcb2bc92bc72bc,0x92bd72bd52bd32bd12bc,0x32be12bdf2bdd2bdb2bd,0xd2beb2be92be72be52be,0x72bf52bf32bf12bef2be,0x12bff2bfd2bfb2bf92bf]
private def g63D8Page21 : Array Nat := #[0xb2c092c072c052c032c0,0x52c132c112c0f2c0d2c0,0xf2c1d2c1b2c192c172c1,0x92c272c252c232c212c1,0x5ec312c2f2c2d2c2b2c2,0xe018340a2c1d0f41058,0x40488e85c0c1084520dc,0xc502e14544524b08101,0x9124a240a385c1840282,0x417068e270901c85c208,0xc38721c4715801140f60,0x1e2104d00020c8743440,0x401a250e1f044270e12,0x285c250b23c2a8813105,0x3a0600c309044084c0c4,0x40640c8c4327911061b0,0x68c4345c3e278080e04c,0x12e20638b0974717b1a1,0xb200d14169520d49a40c,0x8d3a06c62fb501088d45,0xcc3d8ac9cf312422740d,0xd752317da80844f4c564,0xc97211dd48cbe380e4cc,0x1f1a0823f78598ea9e80,0x1cb4f4064b908ee4231f,0x3909a3fc80c83fe14a81,0x4120f6484b9d67432df4,0x3f5ccc975239fbe79d0,0x19917ac863d7ff052812,0x99cf581a71c73046cfc7,0xf9dc1153fab81198ee20,0x76196cf2e84d91db0c8b]
private def g63D8Page22 : Array Nat := #[0xc98ed864ecf8a90cd89d,0xe85186af891673c6b828,0xfb8226c4b145dc486268,0x200ef1a36258a2ee243d,0x7c6b1e7c12589668f874,0x34192be358c3e7481b2d,0xca1e1363aff3a40d96bd,0x4523007b425acc995624,0x3598bf5ca09620681be0,0x503405ff3015e8f5a545,0x6269f4237346ae5f2a43,0x1e7289244c6d0a315dfe,0x48195be1181950d1b9f8,0x7c0f246ef142cb287fa4,0x521659dbf6d312240d00,0x9697f12537f7c44c9b7a,0x2c342c7aec5a0926c70c,0xe9a0c95e9a0c95faa004,0x67841b257a68325c8475,0x724cbbe0431d6d630d24,0x7bf0b828cbcf4908c1a8,0x940fe4131e51cbe12193,0x8f5afc24fb9080fc7a6,0xc2723e71091329f447b9,0x4dc854fc64c4fbf214ae,0x919f8e3326fc841fae66,0x5822de5b3136ff4519a4,0x6b2ef043bd08f78218df,0xd94397b3c01b3872f3a,0x6bad212515916113fb21,0xedf08e1419e3c3ab065e,0x48194adec97650f14630]
private def g63D8Page23 : Array Nat := #[0x6bf093d7eb92a0cd1e1b,0xdef323704b1d7a87a4f5,0xceb72b823b5396543327,0x40cc8fc0d075f9e6413,0x50c08e1f0c0013307c30,0x9a19a84c92714302349c,0x9822652ffe3101973cb0,0x74ea626cfe09909983e,0x93cb648fcab28ca8fb91,0x1f95812cbbf789d0466e,0xe9662f87a993bb5ae909,0x733e70e5a6e06724c68d,0x84d1c50f964cb9c3d0e4,0xc268cf1cb81973f634a2,0x1a5cb154414347c8b682,0x72f87402aea6348e7689,0x228fff64811a3cef642,0x3eab022def0ec84f3eab,0x31317f9688996f0ec84d,0xd01b8b30f197046bc33,0xc90284ec3a105698d0df,0x6bd81846fe01cd4133c3,0xb31f6d06362387d8859,0x6cd678fb8b1f6d063ef,0xbedf13f7cac526588783,0xe781a9ce8c1f665d903e,0x3cae865cf08364a76e20,0x2b35738f432d73a40d97,0x247dc58e3ee2c71c3902,0x78b751337b8b2315e8b4,0x4c88fb9106dfc03cd526,0x2cade0d633dc625efd32]
private def g63D8Page24 : Array Nat := #[0x1065dfe8a334921ad62f,0x7daa51650d7a10650d7a,0x3b63f42133363f421334,0xcd34726047cfda8c1e63,0x9092e7cbc8270fe8c880,0x4c4e7cbc2263e5e41313,0xfd1489973aa4a8663e12,0x9b890f99473e1f11307,0xae12165af606111f0499,0xc8cd0462793332c2e3c4,0x65cf0836457fbcc042cf,0xefc0d976e8748b5ce903,0x35a88340d8e0b10d9333,0xd992479031f7e99264d,0x663d0fc1337f50014267,0x806a9fac5891bb0f4a42,0x2d01e56125bf2b7a0ab0,0x69ee90636f47740cd3e,0xb4bb36824b7f5f264142,0xd9e871047efcf540cabe,0x96126b2d249266ee9063,0x8eba153ee60c8bf582b1,0x4ee766ccb4945133c337,0xf388239705d64598b3c3,0x17ec52cb5b6b4d655fd9,0x387a9a3244694a889344,0x4a7c161c9334ebf421d2,0xa10f5ee1167d7aa430d2,0x3927e83207ff92081541,0xf50fc0d8399f63c72642,0x7848a92d993f0b1dcc2c,0x3f7ad08a9f9410eb0b3a]
private def g63D8Page25 : Array Nat := #[0x65df291a2be8d1bc82cf,0xa32d943c690ea4676fc3,0x873297c3090064168ed3,0xfeb0595b082f4b2a70f3,0xa061ccc1f8644d859a32,0x97342cc1fc6d873287f1,0x2c47e22f7ff5b8195bfb,0x3a6b2258fb68bcf5620d,0x8b0b2d7b03095c7b632f,0x2c714fc2819419c125a1,0x8dbb058e59beba90adc1,0x8fb4e595de860309c1ed,0x3e7e11c5654dbe2a5654,0xe1b49305674fed2a882b,0xdb9a3f159b4fb56ad1cb,0x6dca8564af4931d7b418,0xd34190a3c15419abd24c,0x9ac84ef093597645a16b,0x3b2e3e1d8377b020cbce,0x93cb64ef0a5032926dee,0x84879b090a1fe4a0666e,0x70d7a10650d7a1065367,0x1065efeb41907da9ad84,0x6fc6ad19b1f820cad8fc,0x390786ed80cf91a41937,0x26b2836da0ea1e969373,0xc7903277e1204b2a6df9,0x58fa349acb027e0a4227,0x1fedd4e0a59d1fe08148,0xc5e0f73d8e11683d12c9,0x240d316ea276b5d21002,0x45ec3d0a0ca1fdb81241]
private def g63D8Page26 : Array Nat := #[0x93274fe70353661ff248,0x16124a8707541f63a7b1,0x4cf08364e6bad2125159,0xba2f32e7e38cc81fae66,0x59802c5e0e0b8b4197bd,0xa345435a40d9b30d42da,0x260fc6ea23174fd40a41,0xf8b50d30254ff96c9841,0x65998431ad7ea1869277,0x33f7f8e8178ace5e7c01,0xe143570e06484fede2f1,0xbc21943fc1c0cdaeac24,0xf89602899eb96b21ccc2,0xd05f9c7032d74e841650,0x590b1873247fd483a912,0xf3d4c4e9d3d34997b9c0,0xe68d81e568473d098983,0xb327cedc0cb5f5c50340,0x36522873b05933e092c4,0xe0b819b3fc921c2267df,0x79b2508bdf4854a484ed,0x748dcbcb34fc8e1846d,0xb3ef2d15bf2296c56cb4,0xdbd290b2cd99e7e08acd,0x66270f6083265c75da91,0xf2622d96ee4ec84f7726,0x8abd6046118f671f44fd,0x22441cc488673124dcc4,0xdf429408f2702342246f,0xb387f90a901034067324,0xffe9414a04902f085656,0x404d1a269e725a42855f]
private def g63D8Page27 : Array Nat := #[0x18191bfd20a8d13437fa,0x18d648f1a507ac0d0dff,0xb2d081f05264833b440f,0x18250cc4a229194457c,0x8dffa97a16093bff7e10,0xd40109a63efe282426,0x3714490bd738c118bf8,0xd0a0b03ed10821338fff,0x7d7af0090490ffcd9f7,0x7b209287cfe2086b2093,0xc12fbe91cd0cc97f40,0x43f35ad006095878f622,0xf164622480b7e8462449,0x19f7c1f5a9171802a6cf,0xefac4168734c6f0d38a0,0xf42065afc706ac8cfb0b,0xfbb8e928f966e98cb5f8,0x6f0f120ca1f80241366d,0x9336b25904267b6eb265,0x491f868d71224d6a552,0x32de683be4a47e18eb11,0x5c61089bbdac8ab8c211,0xa7ead04216225aded645,0xc0fcbd7110499f8129d1,0xc7742c924fede35f6c8a,0x42537187578029a77e,0xfb58b54c34d4d1f1cd0d,0x8a108993d67e0c48913f,0xbf0b41086685c7fdac9f,0x1fdea2008499f8129d1a,0xb39ea404bfac0624250,0x925b7ea0a9802a6ad8fa]
private def g63D8Page28 : Array Nat := #[0xf90d1d12729ff5af2844,0x6d15be05c805a57e3493,0x134ef23c2ff21b1a24d,0x13f5db88c923bf6802e8,0x6ca8402692fb8872804d,0xe226aafec5828359cbf9,0x67f20c2f68f1fa7550e2,0x5fe015187fff0625b492,0x422989a2a31ed2931346,0xf192467baad16cd4df9,0x8d819b357b5422566d33,0x8924b2fe232600a694e,0x666cf96210cd97ff03e0,0xeffc40dc5125b27cf24d,0xc89b367e80d68533efc,0x1e3840324cbf710973e1,0x292d6fc902100d12be7f,0xe3e2c081262f9fc8b58d,0xa47ed3e900420689dacf,0x24a6fd9342a233e998b8,0x9e01cdcc8ebfc7c74040,0x8f9609ee93e584f1b4b0,0xfe28a4c04953115d4231,0x4935fe8f4800589a77ff,0xd93efcf208b37e58d8e0,0x12697ec9f7e74822d2f,0xb1c888923ff19d6821a1,0x59675ffcf900dc48d14,0x88ac03f1608433a75da1,0x341a5f1e24299ffd83ed,0x713c36f89476be520a92,0xbc3053b59fdd8b270812]
private def g63D8Page29 : Array Nat := #[0x3c82576f3aef9141ffba,0x6dfe9d44610092e9fd71,0x48d6b81848f5fca99046,0xc93d2a5a08e7feeaf0c1,0xc4c287f8518b0cc9e9a0,0x1a2a4b173db488511a9e,0x4aa7f5cdc2095cfe4885,0xf4b70d0abfff4f3c0402,0xc506c39c98a2907384e6,0x640afc1320e450eb0bbc,0xa59b7faae304c9099f82,0x1963fa0d50119e3d6520,0x328385a0ebf798d3bb53,0x4b2665b7af9d08dfdd13,0x350bc091c5c1c2d091fb,0x3d7aca320f8c72610893,0x207e0fe1009266a17812,0x9249f65684037e96e949,0x24935ec09641f1ae3005,0x6407f4230a9254f9f1c1,0x93fe951d0ccdf1f90a86,0xf13c1859224b5c65f891,0x4d16eef3130ee6448cbf,0x1945c1c2d081fd072400,0x760fbf0e088899fb9583,0x1fa410cb5fdb0a065c75,0x7f16433c738b7c40c0d2,0x335fe504adc3410cb11f,0x4e3ebd78051243f26c30,0x53c904a03ebd7804825,0xe450a17f414f241267f1,0x609598e32e000869327]
private def g63D8Page30 : Array Nat := #[0x9c2fea4c4c1240f8fad0,0x7b44ac354c9dec92f439,0x22326b3b7fb4c153365f,0x3fc1819dbfe90432927e,0xc0cf196bf1054340582,0xffcfe28862104bc0fc9b,0xd0896b85f27c6108943,0x8e33ad2e210491d64f10,0x823f901f2412b657b888,0xd181165e69a0f84f4d90,0x82257aca323716d232cf,0xd1b94248df3f108236f0,0x2109f65684ef6e664df,0x10b6e424af604b26bf02,0x7b3683d7a2f3253e8610,0x3441465ef448b3e2448a,0x3e7608c1c87a61981a36,0x35819975f83c5651247e,0xe660674f8879b0cc1eff,0x48b1103448ef288d9edc,0x1dbf916e1468343537e1,0xff3f3a9b28933e3e7241,0x27c43cd8660ffcd60651,0xb87f08c6067efa473433,0x344420931eb0f41181a3,0x660df79833f07db1efc7,0xbfa93b48cf1fda71a32d,0xbdd04759a08d6d58d193,0x2688809283ce1468cc9f,0xb20655d7a79b509277f5,0x48d7bffb536d4249ef0e,0x93a73214669c50414b9]
private def g63D8Page31 : Array Nat := #[0x237306fbb241a038a419,0xb5578057e0dccfc838b4,0x23400135c6bc25c16020,0xe460460e55ac85c3f55b,0x881de68af00afc1b99e6,0x137f1aafe61012546bc3,0x860471c82b052e9b73a2,0x13a9b73a2112df026959,0x7a24b9ffbd6be34d884c,0xefbdc58152721ffe0683,0x2cb58453e4966685ae98,0x351590cbaa0686af6914,0x6b96077dc1c94353f696,0xafa3d888c09e0bd1999d,0x29e850f705a21fa18242,0x7f4d9a0955fa6823d99a,0x824ef5af1cd1a8923cae,0x5f6ad88899f7f838e0f4,0xdfe13928fbe70b812493,0xe04a41346f9c2e04924c,0xdc849878efc092492ffb,0xe23c62466ff293a109a2,0x68dfab5928d76666261,0x48ff9b1b047ce5de1006,0x24670f0b84b35323cb21,0xc9257bce545dfea78b14,0xbdf2e40c4949df5f1320,0xfc04a80cd3a58b431264,0x4a0313477de4b4062684,0x93276df68788a127beeb,0xc2d259e7fffa7d191060,0xd276d03f276b611fbf8c]
private def g63D8Page32 : Array Nat := #[0x5ac03dac99b3496b8807,0x21577b68322ba244710a,0x92010943e71a114c694b,0x2204926e3046d083e33c,0x7ecc7fdb25458bed64fc,0xac56068f07c6a4401c95,0x13ef87e12d183c025902,0x9706b27d60492593ec32,0x20480433641ac9f58124,0xe7fd922320168ed7a078,0x8bee92c01a4851cf01a3,0xf0b42c0d75e111d8016a,0x2739211fa5f064fff382,0x3db41964ed48847d27e2,0x67f0ac9269687b06b2b4,0xc8363edb1f441a668284,0x52211e32f874b834cd29,0x7c92b4cccd0f6d06593b,0x103da148e2cd5cb08326,0x6272d429c0250356eb39,0x354c669fad758176224a,0x8852b28fe3601c12abf1,0x17f7d6b716093957ef60,0x9a07caa845dbeab39812,0x6c656f65c64cfa565120,0x281253f0f88899bbc3a,0x4811e3b6da36332ffac8,0x2124931fbd0a0cbbff90,0xe4691099f7841114f1df,0x8b7cb26265f871c48c9f,0xe40c84cd43c853bf7ce8,0x3c6210080685c67112bd]
private def g63D8Page33 : Array Nat := #[0x45a17cfa9f3cf900c932,0xfba6042cc95944e5930,0xdf59c62100a695f49023,0x84b5e17d4fdafc80649b,0x67089264b9e0c7c52f4a,0x47311a298c4bc82a5ff4,0xe338c888248c7ac4411e,0x3a64a4111aba50c68ca3,0x6222250a9fc84224227e,0x641f56a0c162258d8c68,0x99904f18a9528cc5e803,0x2ff12234ed41fc48904f,0x5844444b1b5e97541205,0xd1da1e154eb2dcd3bd11,0x81f43c0a80052828e780,0x11876084a9a24f74b8d4,0x4b9f0b571a224a5fbff5,0xebe1724d23c45f14bdb0,0x6c65f3cbd14ccd05260,0x73332f7f1bad15d92939,0x703e440ff25cccb9f289,0x2af4e897063e3f4e4126,0xc240fa37a18104a835f0,0x7e5fbc4885247e1fc620,0xbcb8c008683bfcd42ca0,0xd9f58cb9cb6c82981a02,0x93f4baa0901b67d63286,0x48eda3288bc697ca248,0xafca12e116ce091db465,0x55bdc9a6115e50942286,0x3c300109cab8cd19d792,0x8c930525bd9b0ababbb2]
private def g63D8Page34 : Array Nat := #[0xeeb4200536aebde8ad03,0x8c92d0bfcdc9953faeae,0xdd9ef8e0490baf7a2b03,0xcdb3d604236f7bce2447,0x92017e021217a9eda40,0xbc3ece14e495b193a8e2,0xe7e1a21097a871e80a90,0xa693ee9f1c5372bd51,0xa8a6c0c854d6dff8a21e,0xaa4c9d091532152587fe,0x732ecd254ebe0f8072a3,0x27346f82630fd244fdf8,0x9e7c4c772a9233e55693,0xbe878ab32127b6b55449,0x5a42ecf988462da9e8c8,0xcd3afc69108e3bf422f5,0x84cd5b22d6cd1f04c99a,0x845feaaf184224f340a3,0xc08119e9d6024253ac04,0xa1304f1a91a6a4b7ff83,0xeab299b0d2bc2f246533,0x6a91f59ab9b6a68cd9d3,0x78e532b127350e3eb2c5,0x4b6e068e869e8e7c0d03,0xa19405e02030b4f7b6d,0xf2425e55cb5de7532509,0xef1d21e86a581c751d21,0x2d11e40791065c0d5bc8,0x7ae14c18d2fb97aa8362,0xecd23bb5e4c1e84bde47,0x596ada88237672f5100a,0x6303ec81d640c9162978]
private def g63D8Page35 : Array Nat := #[0xd9a2547088c00a5bc431,0x651033478aa27a1b291a,0x7259c4b484a83c2cddfa,0x75c4b01f9240d3bac65e,0x62cc25efaf8c760d5849,0x931cf09380d6b5dbee3e,0x2a268d0c865f55886ac0,0x80519ade5035a199a3a7,0x460c95816bf406034c9d,0xcf87f3e6f22ca84981f9,0x96293e4a34a7eba6c784,0xa50a55d618a01604d51e,0xaca9f0e8290d4d10cb26,0xdca100fad8e5476e5a24,0xc0419bbdb6bc0419e981,0x2cd699dafd2b8acd1da,0xe13a9206568dfd8e2330,0x70362b482e9c42ba567c,0x2b48ce13c829120ad407,0xa42c6801b15a4eefaac8,0x533a3e2d4a136b1c0373,0xf6c73f93568b5fd70a43,0xd10685d617cf609295c1,0x64f79e024d2b467585af,0xa1496c3aa1259b803128,0x16a3f0ae04834bbdbaa0,0x12b66f898e2bc2a18c26,0xfc055c23b071ee03a01c,0xe5b702a0cf9ff5341956,0x149ec89e30d690201a4b,0xa0263425431e5c042192,0xd3f438c68607d497aabf]
private def g63D8Page36 : Array Nat := #[0x8c4d78dcb49af66954ac,0x19a0688a7cb59a904d2b,0x2103fc828100ce1e12da,0xa8d6ca9cff900caee98e,0x7c729ac854d31cb58c2d,0x5c2754220d25e783732f,0xeb2137b5fc4812cd9e,0xe13c8246ad0bf1f8ac90,0x6c2c84c2e9c4a1b567c,0x3e33fd0d89352a7ea2b0,0x20000dcb4ef7aec49a91,0x615a1263406c2e919fa4,0x813994bf976824533a3f,0x33d7fdf2124740a9ae3c,0xc95e7cf124a4e17b5875,0xa7dd232aa6737c694042,0xd625f3a871081f995532,0xd7f4319504a9fa05fb25,0xac06c2d06de09dc06955,0x6e068aea6970ee0210e8,0x54d394dfb2ca3d737c4,0x638d2c69692fbe949530,0x4626a4a57a09e92167e8,0xafae4892d005356e227c,0xd438845cbf922750324c,0xb25433c427633ea819b9,0xde82327f240ee2106291,0x2fab8484a6be1d84507f,0x46f6c3c8259abbd2b0cb,0x38297a636cf46a726988,0x8f31dd3051e7f3843c55,0x69f58894d0e6ade55962]
private def g63D8Page37 : Array Nat := #[0xa48889730aa89bdaaa21,0xf2cc7e70a3cc13157f65,0x6f3e0a4f5bf3b5848689,0xc092a03bf8b999e7f3c1,0x446691ad3344f97f5473,0x7208f66df2fafb115925,0xa32a1f9d9489809303cb,0x698467822d40d0d01de9,0xd23eb3446691f5990cf2,0x2d66f6557290943878c,0xd37cca12524db4235b0f,0xd0bf5dc98aea54797097,0xccd1e1ced91ad86dde66,0xd3b5cd2661c2506f0cb5,0xa5fe32c89f3892d0814b,0x800a3b3ccd67f8b9cc24,0xc782929fc0096d983cb,0x8b1b3e722e0ef99f74b6,0x6ef5d20c5a144d59c8b8,0xa1cd2b6bde11409efc84,0x9f8da4588897de8b2a05,0xb86c3958969fd0c51967,0x247ac2b2a7c025907efe,0xdfac8d3a3a5bf51c1d24,0x9ca6e598bf04cc693b3e,0x53378959a2edfec2d1ca,0x24a327e26324fc70c22a,0x870ca5a6ed4d433af1ea,0xad13fd688b62b492d77,0xd39d8b8213b3c7f02062,0x44e21e30909e5d555110,0x9bfac04a99bbd6c04198]
private def g63D8Page38 : Array Nat := #[0x1feba835924b4694b459,0x4da1ea3549a87bdad22c,0x1acd275f8f3c12692931,0x51d36adcaa96b307c814,0xc62204919747e7c18e02,0xa8e96da71eb4111a27f9,0xf40e221ea5c0baf78b98,0xf0b13943f350626791cf,0xe4f121203c2205813414,0xed69160ff93446052533,0xdf55804034c7a35ac83d,0x270023694870e3a0cd88,0x4b0c0ba354666d25efa3,0xa0e3c0d23c9fe159023d,0xb3943ce858846d0597c9,0x18ab6250ece50f3a6611,0xd0901e688c55b12a56d1,0x826828f92a470734863e,0x8bdf68559a2d109ca6bd,0x5a68b317be818803345a,0x868b441539369a2d111f,0x54a484869e499fb91e51,0xdf617cd52a4eb77d85f3,0x8d06cdde5bc6836693ad,0x24d06d13327ee11bbcb7,0xab6c55280da0dab3f324,0xb10dcd5090f6dac04a9a,0xb1b48ce450cd95bed382,0x470f40f094b59d7af1b0,0x1e5e02400cd0979ce97b,0x975e3248ff9b388e0c92,0xcce1e184960ccfabe46]
private def g63D8Page39 : Array Nat := #[0x19c82186]
def g63D8 := limbs80 #[g63D8Page0,g63D8Page1,g63D8Page2,g63D8Page3,g63D8Page4,g63D8Page5,g63D8Page6,g63D8Page7,g63D8Page8,g63D8Page9,g63D8Page10,g63D8Page11,g63D8Page12,g63D8Page13,g63D8Page14,g63D8Page15,g63D8Page16,g63D8Page17,g63D8Page18,g63D8Page19,g63D8Page20,g63D8Page21,g63D8Page22,g63D8Page23,g63D8Page24,g63D8Page25,g63D8Page26,g63D8Page27,g63D8Page28,g63D8Page29,g63D8Page30,g63D8Page31,g63D8Page32,g63D8Page33,g63D8Page34,g63D8Page35,g63D8Page36,g63D8Page37,g63D8Page38,g63D8Page39]
private def g63H8Page0 : Array Nat := #[0x10011d3507010b1f1b00,0x3000108050000,0x2040000020100000505,0xe0608500e0001140408,0x3060004000108190f2d,0x40d0401010000060431,0x80d0d26030421032302,0x1b1c06030209001d2206,0x30002041400000000,0x1040a0515090d050904,0xb081208150301012241,0x40e150604060411934e,0x11218861010d0e03000b,0x51e070a010b0c143e0b,0xc050e61030000000204,0x8040c02030206000201,0x1429202603282019061e,0x427003a2c093e007a07,0x260003095f5b0002000d,0xcc00012002020d2f1f6e,0xb4765abb090000f5bd9,0x947063acc4bace000000,0x688000f59469a158c4d8,0xbda1f9b81e40db86496a,0x7dc6628caf0675287167,0x151f624289252fa5c20d,0x337ab0ab63805710481d,0x40002c22f97912ad2574,0xa94a05f865939099c6e,0x4ddc65b0875d101b7ed9,0xeb6f7f226cadb69c0008,0x3423e18fa8afc37cf4e6]
private def g63H8Page1 : Array Nat := #[0x1e7b89c000d5500ff000,0x6bbb136f19af000013cd,0x7968a31c3eb1de3c26c,0x82dd88c000288e331c00,0x99000010ef6b9d3af814,0x4103a1b5c8aa00010371,0xd45e535b8e0000162272,0x24c02094f134f85c1cc0,0x38e6f30da960ee99e6b7,0x8b68fa33ac14502e1e5c,0xf78f56c58d456ed4195f,0x9dc00088bf2713919d3d,0xb9424b800000009,0xaf14eb37140161fd0100,0x40df3700004376a3dd01,0x41dc222de6442292346f,0x85d1878213ea6226135,0x11185d0286c6dc000000,0x1640000000000963496d,0x2769516772a4fbce0055,0x4ee0003a45766ed992b,0x253a96e254b8b2ad1000,0x1e3397ed3082fd5bb5af,0x4000116700004ca512f0,0x52d21903b5291944a0df,0x455da919820874a0d6a3,0xb4000b682d86ab0b5c7a,0x8121b162bec4bec88e0,0xe4748af1d355598ab000,0x49000250b875fda6d198,0x452cee12d5fc000da5d0,0x61c2a3eb060000c06516]
private def g63H8Page2 : Array Nat := #[0x63994544831bd827586e,0xa101552c9912623f0430,0xc000232f67b1565cbbc2,0xa5236fb61894ede8b326,0x38cb07ab495c3e0000,0x524c6752508000a4b00,0x6bb4000a55f14a82f400,0x67cc6434015b0490c8c0,0x62ead89b70fe1bbf2688,0x9147573ea692920025c9,0x88025cec9cbb18cb1b0d,0xe990081b4000182e9070,0x24c1b05c255707e00010,0x21691f74c598689b,0xc56a11749909f7a74000,0xc0bc000c66bed83,0x864b6db00,0xfb89dd2abac000000,0x75000247442500006710,0xf0000000041f87b364c5,0xe549c7ce65198176e053,0x1fc000c45e61e16bc000,0xe6e867aafcc6091a10,0xf4340003548e44400000,0x11f00000006021114240,0x22a13a0fdfb3eecb0002,0xcda5170184d02e32a319,0xe0f29bbd9fac83337b95,0x9fca4ea4c48a90002e2a,0x360549348dd900026c05,0xc6eae79b06885855fdc3,0xcb01789904929d4d0697]
private def g63H8Page3 : Array Nat := #[0x53683a6c8e0074e8e820,0xd82489fbf43e9780003d,0x2518f2f2226d42028,0x217ea4d9c3ff7a2e86,0x2dceb80fdf3a15c0000,0x740958de6b31b9400000,0xdfc4437969b31958f03d,0xf018d1c9e80b00009561,0xa36a1aaef069991fbd34,0x2fba42b7a85bf888ea0,0x8a0661b01d8af770b0ec,0x9ae9fc350cc25b9f91ae,0x824400036d5c6b0dcd32,0xa0c0002d4617b2dd5aa9,0x5d542b19800015950002,0x557c66ae93c452e7c29,0x28daa1419290cee0f522,0xa468e202ea54375e78cf,0xdc9240001416b537aee5,0x2c6fbbd8913211f659d3,0x8c3b2730000099a29,0xf9c12a1623826edd0b30,0x639a7c1700002ab00001,0x604edf6dc28000a8018e,0x3a8000e8e3687914e48b,0x496a7115a04ca120ca0e,0x281f9722eb8000198a2b,0x287758000f5d8000651,0xff9794580c6ab26c0ac5,0xc30a8000e144000b8a6e,0xa0800000a07c691527a7,0x5a02bfd3bcb0b85f140a]
private def g63H8Page4 : Array Nat := #[0x6d8765aef2309a100002,0x28a1f21ba8284ead21f3,0x1dc85432410000000f04,0x8bd3654732a6000005c0,0x227740000001eb43a4ed,0x24405a6cdc50000ab,0xaa067dab3ac11e7c9132,0x221c63040005ad40000,0xaa4b425ee76a95400000,0x649635c0000001571b76,0x3aa2465a84d0001,0xef18000048f02fd0bf80,0x265625a8d2723efd2,0x37e67c253cc5f00000e1,0x9c391694c4e2131ca6,0x99b1d7f85300000000e0,0x7425eb087a4000b43,0xfa0358530c50cca818,0xa27c45b776715b387840,0x5109403516052b1c3e6b,0x1b07772d54ccb98000,0x1d2701074e8e18b65880,0xf5976a14000b7b45f5eb,0x266d1754c34be9b0428f,0xb701b2ec30003de0e56b,0xc578000a7ac000318ae,0xf1874b5000088d000000,0x384e3000057723ca138,0x701356c4f9b9a7900c8c,0xc00098414bf37b8000ba,0xeda000188a0001a0264c,0x23cb5b42b47fc00083e5]
private def g63H8Page5 : Array Nat := #[0xa0000000d4b5075b1561,0x7be02e9c83c000ec4509,0x9a5c06aa822ea2b2898,0x3f0ed019f8320000a6f0,0x757be2b800046d80002a,0x60fdb50000000720,0xe4000000032daa65b2e4,0x90599215e974000dba38,0x164d000129000025c,0x77c000d836d7d0000000,0x598c94becca21c3300b0,0x1aca3894000dbb07021a,0xe7400015dbe414217000,0xd0c8125a5798d17259e4,0xfb4f0000e1cb14ef1142,0x56300000002300d58080,0xcd52bca0f60000000,0x81400001b7ddd80,0x4404706fa51000000000,0x90310300000000329,0x64a6688fb040000000,0xdd9c8d0c284f46a48900,0xc6b80000a84827000221,0x9b31a459ebef587eb6a9,0x1257e244000934de210,0x57ae9e00000003d1e00,0xd171df8f8fbe4000000,0x1126bd82140009abd,0xb90a79f70001a9e516c0,0x73f00004b0826,0x344100000000001639,0x1116439e2a078ef4390]
def g63H8 := limbs80 #[g63H8Page0,g63H8Page1,g63H8Page2,g63H8Page3,g63H8Page4,g63H8Page5]
private def g63D9Page0 : Array Nat := #[0x104400c8310c02108010,0x8411014c521445010c42,0xd4341d0331cc321c8310,0xfbdfbf7efeeedebe7f51,0x6500cc80298c073103ff,0x110004ca2199147310c2,0xa310724c80498c093082,0xb9264720c8e498dc831b,0x1bd1617c620f4995c832,0x3241263820c704991e93,0x8b085265820cb0499208,0x28b0c52640a4c6149842,0x46932c52648a4c714986,0x866f98cd2641a4c23458,0x19669324d0649a4c3345,0x498cc93099161324cb34,0x5610ea930d5161ab6835,0x2a45854932d5065aa4c7,0xc8a51514931a9453524c,0x4c82498c48b009751ba4,0x24c92498e48b04926512,0x220c847cc488b0112659,0x4a22c144994883291264,0x603a4cb4419689325106,0x653a4c67610ceda09d1,0x9065b24c764582c9329d,0x2d2635aea2b45816932d,0xa61263c28a7845830932,0x30951612a2c0549930a2,0x8b0a1160424ca54990a9,0x8932a126343086849850,0xd8a29b1261622c2c4581]
private def g63D9Page1 : Array Nat := #[0x8528b0a51604a4c8c498,0x585a8b0352654a0ca949,0x9cc41390812646a4c2d4,0xe910c12210243204e820,0x2e9d01d3983a72074e20,0x82e9cc5d218ba7217484,0x864e9d45d228ba741748,0x4cc4e9189d2293a44274,0x74cc6e918dd229ba4437,0x5748cae9991d2323a454,0x317c862f9c85f210be66,0x4427c864f9d05f220be7,0x274084e6109c821221be,0x4275184e8309cc61390c,0x1c2662848a50910a1219,0x324245484cc70914e122,0x220867310c8621999613,0x33a0467308c88619d043,0x633a0c64418ce63190c6,0x523229c64438cea31914,0xd0472208e7211c842391,0x9c867210ce7409c88439,0x39d467228ce7419c8833,0x539d867330ce5619c8c3,0xa93998a72314e4529c88,0xccb3919673324e4649c8,0x4e62690c4d3909a42134,0xac86359c86b210d64323,0x1acac359d46b228d6731,0x53accc55914ab2195666,0x43154e42a90855331d64,0xa43254e82a91055398aa]
private def g63D9Page2 : Array Nat := #[0xde721bc8437910d52212,0x95e741bc88379cc6f218,0xa08a731148877910af21,0x22a0a4531488629d4453,0x53a0ca44194e63290c65,0x25229ca44394ea329146,0x4493a09266024ac04915,0x1509331124522488449d,0x958292305266524cc849,0x49d069220d2760a4cc14,0x54914a922152751a48a3,0xc949192922a52662a48c,0xcc079580f332d2465a4c,0xccc479148f2191e7513c,0xb4cc169582d3319e4533,0x2b48a5690cad3a8da451,0x325cac0b998ed229da66,0x6645ccc6b910d72212e4,0x2443c4885890cb12b062,0xb2453448a8599931331e,0xa65614ccc0995813221,0x30b65616cac0d9989333,0x10402c00580009991b3,0x3980c0029408601ac056,0xf019f05d814f04c81100,0x4246088c20d07b81d106,0x3130bf02d80aa428409b,0xae0e543750d7033d0ca0,0x2114443610643ef0f3c3,0x146c4f113344ad125447,0x7205a716245711564539,0x9c67d197c63618385ef1]
private def g63D9Page3 : Array Nat := #[0x87361c706f81b546c11a,0x7fe1f4c7b31e7877e1d8,0xe322cc89421a483c2064,0xe25fc9632508926240c8,0x2924a2228189e5272099,0xbfcae42b14a9a29fca66,0x1cbb22e48b6f2d3cb282,0xc793160c423058bf42f,0xd4b34b8d083384cc1326,0x1337b4dd936d4d8f35c0,0x43ac4e9839e4e5938c0e,0x3e40f723d1cf223bcced,0x17d03c406cff73f54fa8,0xbd11743c90d142b90814,0x51f9476d1b2460515344,0x2cb4a9d288499d241488,0xa34dcd3564ce13164bbd,0x651e144a50513f64f553,0x54b150f53c54d652d549,0x7cd5cf56b558c55a554c,0x3d6b35a79689594961c5,0x175d5d1971a5c016e85b,0x84160958055f757c55e4,0xed63258a962418756175,0xd6691985656193c64598,0x6a09a5d68d5a1367a19c,0xd19b1b6bd5ad46ae5a9c,0x91c357001bcd6e7db6f6,0x5d2d7419ce172e1c8f71,0xdfa7765dbb7661d6f755,0xae7a4de777965e3e7865,0x7e81f707d09f0f7b81e]
private def g63D9Page4 : Array Nat := #[0x817604880ba0037f91fc,0x51612283ee0d682aa08a,0x761f687521b4864216f8,0xa2c28a92278896623988,0x3868d923438c662fa8b7,0x5290e24188ffe3dd8eee,0xd94064de92a648591ce4,0x973e5ab9636570954a52,0xa6a67a997663c984e5f4,0x127329c4a6f49b566b79,0xa7fc9f627ba9e5e7689d,0x8c7a282885a196848a0a,0xa5a5d695aa4f2916a39e,0x9a8dea13a7de9dca7029,0xac6aafcab8aaafaa42a6,0xeeeba3ae1eb6bad22b30,0x86c79b156c39b016be0a,0x2d3eb482cf9b36ecc1b2,0x508b766dbab65ad75b57,0xf428517870ec2c009c14,0x2402a800a29810541070,0xb840223831447042b248,0x40626212e01032800430,0xc4f4e1d221c48c3190d4,0x51b104616131e8e881a0,0xe2063f3816398258f491,0x1a6f022291ec91f940ab,0x9a3c429dcdb08ab8dc41,0xce8e127bffe03810a4df,0xaaf7c964214c537f09af,0x5125df64a235c9e43094,0xb0893c2a111afcb824d7]
private def g63D9Page5 : Array Nat := #[0x37e0481920ff8e04144d,0x108576ec4ba42a57c60c,0xaa0726feb6c283ef7c86,0x1d65088c6d2073e9033a,0xe3904d9f8480cb678826,0x24bcdfa904dc36504a6,0xbf481f7bb208cbedf2a5,0xf7f48f10a2fe470a4e7,0x7c584a543697e08c57cc,0xf38d582354a5a0f485a4,0xccfac0ccfac0c7f2da84,0x37048be757c13ae56a88,0x79b094a8eff541381f90,0x37d10a311d348e70ace4,0x248787c12aff40b04092,0x6f6bfc20aa6f3c02501d,0x1103f9bcb810a87a5544,0x141b6c14df6c20a173c7,0x609975351b50249c27c4,0x445884493632fc25177b,0x52e94699d11017c933fe,0xf02146fd4488342256d,0x51cf2f509963893c235e,0x65bb723df6e2130c70da,0x8e796a3271fd41601926,0x5e55920fa4d4987a06d2,0x4a28faa512d37d04eba8,0x71a08b5fe6907d0a879a,0xa9fda2e0224df9d8259d,0xa236e3716231f2a21e52,0x51f6816fc7020a17c2e3,0x24bf4908293fe5f2e021]
private def g63D9Page6 : Array Nat := #[0xb25281f78157fe2d0011,0xf1f4804481f30388b764,0x93f5003ea55700f8851b,0xe214dc1db09ecc32be42,0x2037c94d80df82839c0b,0xf08e33287be413a08e7e,0xa941047b03f4934ef890,0x63cfd104e6ed982513ff,0x734827dfde9408c50db2,0xb1794a47d7b20b10251f,0xd7a6114f3d362fa151f8,0x53bfe829020495e19449,0x42145af43d21493c590a,0x58b46a3ddc40f728be52,0xeccfb89cffc7c585a543,0x281f1a168aed7b7b4506,0x210815dfde920141b6e1,0xaeffbff82800565cffc,0x560575bb2493d649e130,0x92560551fa10c51724b2,0x49cd26c27afc28114dee,0x159ed35a8155f992111,0x91227b276100a4f4b868,0xe4fe489015ddd9249aef,0xc820507cfecd0928165f,0x146080004c3f321898fc,0x502279fdd080001287e7,0x9afcce444e799c889eff,0x3ecbe044d65488c7f100,0x20450ed97c08bfed0627,0xf3c9804e7f3750273ff2,0x1ffba400241bfc89014d]
private def g63D9Page7 : Array Nat := #[0xc0001315607f1041004c,0x322ee10d7708631bfe80,0x263b50269db42297ae8,0xb29d137cd6a200126f4c,0xa12502d3ff338902c05a,0xecc9c452b070884f9ff1,0xc0e39dd08a5ea8a0ca6f,0x1265b4fc0e66564a7b4f,0x3dc44ca8e5e665a4f78a,0x3f870470a57eea828890,0x133eea201484ab1aab28,0x3413b9ac28244967e2e6,0xc225938fac500b6497c9,0xe321648e3ebcc2988f7f,0xca12a787c0a32cac987,0x987e4994537f4e2e276f,0x7fea5b58aa2f5f3b6b15,0x39865159fb77a1958161,0x62d359ff1924a05b7ddb,0x15f86a809466f7ff1240,0xdb4e025135d9fc902ade,0xed0dc51874f9d0049936,0xaf113a8fb3c628c922f3,0x637f712651527ab2c9b1,0x3a28c37ea3228eabd464,0x7c6c0848f964c619461e,0x813138fb8f8125d8649b,0xff8f83ed08b0c997135e,0x176b016a5fc01ba024aa,0x4bd5ea3708492affd9c,0x285deca90a19f0364c0,0x16c924970fce2632ffd1]
private def g63D9Page8 : Array Nat := #[0x1495d5c632f748997f23,0x48ab3f0909966bc4c24,0x56065d9c9824a4fe6ef3,0x8544524de9018a9bafec,0x663162a33f951141feff,0x22672221473f72a92736,0x25a15786124d3f3c0409,0xf99c8a22a7b9b1a127bb,0xa498fa8589ccc9a2283f,0xf80929692f764b424f84,0xb568741c475f0ad6230a,0x7abd13941b73e699c174,0x90346375792cdad8d88e,0xb113878749ecc2f255ea,0x2fc60ba5a5fe4c125141,0x34098935ecd12ca4f73c,0xb78409cfadbc20523f3b,0x6023d7b3204f39db745b,0x8cba453d0a79814af3d9,0xbf6158463fd71865156f,0xee1165477891ab9f204c,0x46dadf448d31aa1a2ed2,0x29a0d88f98528a20aace,0x49272f0943e2c3fd6406,0x9f247daaa8d16bd43cb1,0x5289c9ce1cc3202c533a,0x88b38f448dbaace453e7,0xe00141cfcefa2285881e,0x2b011e79e5058202553b,0x963d62912943ce275c62,0x9450e998c933af613414,0x9471741b26555e45119a]
private def g63D9Page9 : Array Nat := #[0x47f786e26bd165fa9f40,0x5266ff6b4453b811fa45,0x926aeb319277c8026d0,0x93c0abe58253b5896fc3,0xa227896b216a96b23fad,0xdc25829a7cd428154c41,0x6b689bfdaba04144996f,0xfd6e0168fbff10688cbd,0xe3131920e4c7b5d5e4e3,0x67500469fe5cc248f4f3,0x1014cba23944bd0f389a,0x9b7b1a51879e10211e3e,0x27e268]
def g63D9 := limbs80 #[g63D9Page0,g63D9Page1,g63D9Page2,g63D9Page3,g63D9Page4,g63D9Page5,g63D9Page6,g63D9Page7,g63D9Page8,g63D9Page9]
private def g63H9Page0 : Array Nat := #[0xf0000600028240605,0x1e5d5305c04070000018,0x20602002800440009014,0x1c1000030bc0860008,0x80301800024102400100,0x20b020000c240518c082,0x814050188c16170002c0,0x42401000642c4b0181,0x68080c2a098205e0710,0x202800729c030001224,0x20f020051c520001c18,0x46e140e8000c0100020,0x800e403000400000078,0x582800020000cc01d0,0xc32000000c2f048a5340,0x81c00018084207068081,0x2004131216c141b0082,0xd88c00160080c0c0132,0x10e1352849081e03c2b,0x6855050c9ca1d0b01446,0x3428650201c060117008,0x280c3204030080e05048,0x8104abb0b805580b0,0xc0808818000304000064,0xa0305074d038018380,0x80050250180016020a80,0x2492c0c0c4780c841e00,0x2e010053c0e030041800,0x148a760005c0f048280e,0x50ba0001001120602a14,0xc81a403b00a2466270c8,0x40b8201270100ac12011]
private def g63H9Page1 : Array Nat := #[0x400140046639130000c0,0xf1d0280a072ad640,0x833c8580001cf3800000,0x15187d9df45d659f879e,0xb50000e6d71368351000,0x193012a262600020a18a,0x1cc0a61b7c4aa225c8d2,0x91695f0d70c0bec63000,0xa3beb22f40cf26587578,0xa2bc0000abfa694417d,0xd20001cd12c05288d176,0x1f1e38a8858abe1d4990,0xbab20a344ba7c1e5c729,0x323243e273e51d0d8213,0x401736eb36125d34447b,0x224b24cc0000d8060002,0xc9f1dca4256197464b17,0x217faa20000edf3826f8,0x7c91d83960adc2940001,0x4c0000696c0002150782,0x1ae5366a2eace219c,0x99119d53ac7df1afa4b4,0x410df1068fd8495633,0x2282a160364000320880,0x62d415a06bff8223c4bb,0x9b979b918bc000000f25,0x42012d86815f19ac243a,0x60003cc4823a00000003,0x9d6924ec640e4233038,0x8b384ee2b2edc8ddeda,0xa0e544cd19a7253966be,0x67f7500bed0f209a183f]
private def g63H9Page2 : Array Nat := #[0x41831da379c33a51ada,0x1c9bc853213611e3835b,0x9c57b552ed1c91bd4088,0xe6d35bd1784373dbae3,0xfe3ef9d632244169e680,0xfaf8574a4400041bf277,0x83f4a00000026dd4371,0xecddf196816351aa6e03,0x99e848c2618bcd94545e,0x233e9b762778335870cb,0x20000d441c0df595e3dc,0x1123bfca27163a829b53,0xb25900165e4dff8b972,0xa0600950e21d24cd6f16,0x5a642aa76d85aec48294,0x21b8b6593f04f07c5e82,0x4e778000349a73aa52a1,0x493b366210487192a6f,0x42d692f000048ad13f8c,0x4c93265f000018d98570,0x8ba13e406819c446fd0f,0x9429bc3d337654d54b4c,0x44d2d08a413c496c21e2,0xf30001cd8d1d6e819b1f,0x93b0000358d0bc2e2272,0x189011ab11e997c80003,0x4726e6018a940135493c,0xd0c8bb620cdef9800039,0x6e178000323dc53e04a6,0x8183228bd70e26ce93,0x97f13b2841b0bd145980,0xeaf29cdf6117331a88f8]
private def g63H9Page3 : Array Nat := #[0xc7116200000005217129,0x1843426f28c5c3731,0xfb2b720b348ed93e6fc4,0x69308f24a14079803a16,0x10e7381f79829405d781,0x60000000239a77ae48a7,0xc3938e4f603800051d,0x4f34b5855bd0c07616dc,0xdca5780f895100016946,0x7f12d40003e1de24ec24,0x4e7593e00014c9c8e7e0,0xc000000000000001433f,0xed567dd1694e062fcf4a,0x2acd0000690d91158,0x9903155ca26262472560,0xa3b6ecc45518262a5359,0x20b886aa8c2cc8521,0x2e8da819e458f89ed038,0xea26de30a3562b86dd49,0x902726832d84d08a42b1,0xe687e9f7b3ebf2456f02,0x6a475326d264492d7867,0x9a9f0f659582b83d46a2,0x3a51a602a417c8920000,0xe670190ca70e424b515b,0x115aa5df633163758,0x20000003b2a0178e0000,0x1a95fb8edfcc3a1da75e,0x48766d58039404a3,0x98f9c0005036f008120c,0x8cb754e8c8229621e857,0x5c7817a1713635055e81]
private def g63H9Page4 : Array Nat := #[0xba4d220a022c2836c9f1,0x6ba4a0fd98ff68,0x818c3f8b53a4d314a700,0xe51ee0fc8000793066b3,0x4b20ea422d8f150aab12,0xc68743dc5c4456c474fa,0x9608b9ba190391d04c21,0xbd25288acc1220b24666,0xa1358e7d01bb2f113931,0x769858046a05b49ad230,0x86407ac537c72610b058,0x5a38000763f2f4203054,0x5cee20a62856c83087cb,0x255628ae00000938b6b,0x53d899500006fa81565a,0x94c4908d8000b07c70fd,0xb7735aca3095f42f9177,0x8e20000c2e6e55a13cd4,0xb52e79b3b30300000000,0xbef91ad15800029f0323,0xa350884782a000000010,0x1a4d78eb11f5084a0003,0x54d442a1a2148000012f,0x9f078710001acf400070,0x110ea9ec5c27e10008ec,0x6bf73dcf740000000182,0x2306183200025f664,0x5040b5fe7bfe74c,0x48e89668a38a90000000,0x41580006363a266886c9,0x7acc2e3c8000d60bc085,0x14a1fc47ad9a9107b022]
private def g63H9Page5 : Array Nat := #[0xcd10a13a3c6325800018,0xb04fd654c4a2d65d00bc,0x96074843f65eb0000338,0x49100003c1261,0xe8313538907364902bb0,0x6d12ea831f1d089fc23f,0xddf3b59000192480520c,0xa421037bb85a70665ff,0x32640eb29c00001a6206,0x9919bcfb41d11c9d11b8,0xb82b1dfb7b87433fc4f4,0x8dd07372f7d61038856d,0xcfbd2a823023277d9663,0xa6e41caf2241b8b6a98e,0xbaf852e9c0d2c53ee01c,0x8d498740000000146d73,0xcad06605cbf900016a07,0xb3490144974c2acb2633,0xc20ab398631a3b12509b,0x752d1a399085280cea5d,0x53a461264c24a7d10b,0xcff6b6975c6b15657900,0x9f11d4a0931e004ccf08,0x8bc810a2db409531cd39,0xc165aa4a5cc057e24571,0x7e5de050b850c4616aab,0x2c0b3a861422ca98a35,0x490fa3af0d7817269,0x3ef8b1c8800034cbac6c,0x4dc7180000c7a0000533,0x9091a8764ae62290610b,0xc4a3b5fed149f15c2916]
private def g63H9Page6 : Array Nat := #[0x4213a17182ce0fcaa808,0x998c823000000024b37a,0x946d88d9892475d70bb8,0x296681f00004398f90,0x8f2e813331da1dc00000,0x9c80559b345fe547497d,0x31768bb4005d384012,0x52cb4b8c14a000261880,0x132e8000000080220003,0x6016f361ac00012ae000,0x13fcc6e189795f443,0x683e399592540001eb74,0xf3b314c9760dc941d995,0x46cb8348926ea0c00048,0x4f024034899372d06473,0xbb43d0000001f80db382,0x871aa2d32966c2800059,0x30cc00073f200000001,0xce17a4e0dedf9bb11000,0x98b546552810b6ed6e1a,0x4b1e000068b05095f15d,0x300006882d17790c94a,0xc7a0001613c87ad2,0x407c753be3b9f3280000,0x52f600000000000d65,0xb48c0801df680,0xf6238d37123ca04e0f20,0x6ca35c4204dfab481b5f,0x430d09581914a2ec3833,0x4c3c15586ba2772843fc,0x34e5a26df6a3b0000e5f,0x53aead653ed0e5b5869c]
private def g63H9Page7 : Array Nat := #[0x362a45750bdb0000ec24,0x42344c8468d42000038a,0xdef000000000002c415c,0x182a1e3f741a70a40001,0x89a7caf0815fb8000000,0x5ea8000323000f08e378,0x346f53fb0001834f,0x481f8a833145216d43b,0x596b0001a60dcb789,0xe78704b0919886acf70,0xb2c6af51728b38142000,0xde3797ed4f570e30ceb8,0x5cb2f98cd21423dda7bd,0x2a5929a6a3415515d241,0x2ea69e687ef8482212,0xa30e4d838000f6f72c57,0x182c24972849413995a,0x92a8ad4b651cade85d0c,0x2e752d591a6b2031e9e2,0xea777ec03dfa2b8e58e,0x22a62ab72facda18aa1b,0x9ee9800050d1e6cc2d3e,0x59d19640b94213b17809,0xa11d887d7400a080c374,0xa8a3e8b2d2bac793d0f9,0x55203703179325ac001b,0x4bb000000014177cee28,0xca171927a01e06d6a4c8,0xe5932b7c00061c2994,0xc0ee93a0000a86954900,0x82d3a954aa2770970d8b,0x396796324558a0000c67]
private def g63H9Page8 : Array Nat := #[0x658abd1b0c9c94e8600a,0x1ea69d7aa88c9041a982,0x1096f120eb96262d322e,0xe0e5c9e8266a28321e08,0x908a92569f4000028e3,0x90a20b6e8ecc8a8f9000,0x8aab3fec261815f9a364,0x48b6b557ab71e64ad25d,0x9b000126e35e9e17cf0d,0x83c99dd0001e7b40006b,0x1e2786175c4e00000000,0xe3212b04000530c000,0xde234752576ab9f99000,0x1d17a27e0000c693,0xae76ba11a6c98db9f05a,0x8e8c92760fc829f90813,0x6d14f5569b21874aa407,0x37372f70090b88000212,0x8318838434a10a89b253,0x112bb9bf7ae8988a0e2c,0x135400000004b3aa86,0xc87511ea20c0002cdd00,0x8d2919c133b50001cbda,0xf3d0d9a328000385148e,0xd05e3f096214f6695331,0xe31b94f4a74e56c32c3,0xf0000a580000408f000,0xb100000000123d012d2,0x6b20a999d0df00000002,0x1ee47f226ac717015807,0x2108273e2af200603ebc,0x46894207802dc4360000]
private def g63H9Page9 : Array Nat := #[0x6e21561270c8f9b9df5a,0xc1a8000000087b000019,0xc244285fc82837f48481,0x53a46eee19061e182c00,0x226a47cd8e0a28c43b08,0x63fdb4896c20001,0xcb361e2fa7dda4c5e01c,0x95a69440000465f03299,0xc1de805b]
def g63H9 := limbs80 #[g63H9Page0,g63H9Page1,g63H9Page2,g63H9Page3,g63H9Page4,g63H9Page5,g63H9Page6,g63H9Page7,g63H9Page8,g63H9Page9]
private def g63D10Page0 : Array Nat := #[0x186401062108220087f,0x218e4210ea0286802066,0x629084196a228e8220e6,0x50200b44013000a82988,0xe0dc642ed5495421c8c0,0x9b2d82b7562852d8c411,0x4002030f021410bd1dde,0x400a1002830f1d0c4010,0x58819a015a411f003001,0xa90077720339015e205,0xc8186c81dce018c60200,0x1db480874a03aa50216,0x60748066bc055ba057f0,0x1f72033a940ec9]
def g63D10 := limbs80 #[g63D10Page0]
private def g63H10Page0 : Array Nat := #[0xd000000054c000e0306,0x4e000723071e06020620,0x7420130b350738030203,0xb0d03090011001f010b,0x9e092a02084d04020109,0x30f010d647b06140109,0xa90007030a013e078603,0xa38727b020547081b0c,0x4dde0b3f005923000003,0x13e07fa975b72d3c99d2,0x3123958e0f9b97186e,0xd28b0c5ce4e7b84c92c8,0x2c5c001a87d957b50007,0x6a2fd3e6098614e3a197,0x54f6b2344793861,0xe9901a21423ede503e00,0x91086e4fa00000031938,0x1a1222399108dc70dd,0xc91d50e1b8ecb00030a0,0x1d714efc5841c562a0f3,0x2692c7850da17000000,0x1fe078940000af9c6426,0xc5e7d5400102072d8b,0x20a502a76ba9695c590a,0xee6c0edbed625806c29e,0x2ba7281d0ed490c40c57,0x7a0d60d092de9b6b9c36,0x340490421d853029,0x23c8475b2ba8001a8000,0x604b66e6bd4f63c7a43c,0x4cb0e8f6ffbe5c6f3478,0x35371f851c667c9810a8]
private def g63H10Page1 : Array Nat := #[0x4680a83afc53463,0xd41c0c1d975102000792,0x790396d18860aa921123,0x5152b20d221395694ec1,0xb5cc598a3000581f268b,0x69f0000003dc047298e5,0x60cd632eedb34532b683,0x812cf20e9bccb0669b2d,0x3800153c5457520aee55,0x888bd1acd55213505541,0xa86a5959b0e16901c691,0x9b10c658f800383cce7f,0x37eeb3d16aecec92c82b,0x2192d3139e305824e000,0x6608001168000041800,0x28000000a4580005fe00,0xab54bac754eaa98d2951,0x9ac60e00071154bb6,0xc49d21a9a80000009760,0x34be318c8338db5e9,0xe0009598000000000d6f,0x8b172a909370005aa397,0x496f5000582666c00067,0x448003dc491b4a98002c,0xd6fad5a0a7343e71670c,0x736f033684a73b3dd0e6,0x18a9d4560b414224d,0x25a310850c3c6ba62d10,0xeca4d30f87b5b6915a73,0x2d13d5951d5d48c96eac,0x1695c227a7081087ef,0x89b0005abe92a53ef948]
private def g63H10Page2 : Array Nat := #[0x1140c6b03cd978000d41,0x6f44e4e0c02562f11e31,0x1028b25781967d000384,0xb679b00d8154110f716,0x7f11fc000a8dd89eb321,0x632107a4b38f8cdb144,0x6c861f8c7737c18c3,0xe84bc513173d5d8166e4,0x9182d4e8a2c2ee492413,0x129]
def g63H10 := limbs80 #[g63H10Page0,g63H10Page1,g63H10Page2]
private def g63D11Page0 : Array Nat := #[0x10308103f]
def g63D11 := limbs80 #[g63D11Page0]
private def g63H11Page0 : Array Nat := #[0x140000661e600210,0xc000000c20,0xae4000000000b1a20000,0x8000000003e800004ae2,0x2e4000036400001739,0x46f1c00d7a8803d20000,0x90802d80000002de00,0x321966280000]
def g63H11 := limbs80 #[g63H11Page0]
def g63L : Nat → Packing
  | 5 => (1,6,6,65537,0,0,1024,g63D5)
  | 6 => (71,5,6,1638461,86,10,1032,g63D6)
  | 7 => (790,4,6,3539365,105,14,1195,g63D7)
  | 8 => (1215,3,6,1704202,89,16,1151,g63D8)
  | 9 => (346,2,6,655385,69,14,1088,g63D9)
  | 10 => (26,1,6,65537,0,9,1039,g63D10)
  | 11 => (1,0,6,65537,0,0,1028,g63D11)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 2 0 g63H6
  | 7 => lookupWord 28 179 5 11 7 0 g63H7
  | 8 => lookupWord 199 983 8 14 10 0 g63H8
  | 9 => lookupWord 303 1399 9 15 11 0 g63H9
  | 10 => lookupWord 86 397 8 13 9 0 g63H10
  | 11 => lookupWord 6 67 2 9 5 0 g63H11
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
def cubWitness : Array Nat := #[62327922217,12048812133,7752812649,48556693925,12233032086,15287193603,8138491578,15219693861,27030480150,7887080252,27533944506,7752830268,57400470714,27030629946,27533985141,40216406202,23858957628,23858811993,57400399977,39847308858,31760787130,15403264698,23741372057,15403127385,23741371929,15151470105,7752657539,15790545547,39847243322,44445313722,62787180645,16344420483,23945943333,32033346153,15151470233,44653039164,15151536681,27533985596,40216407226,62736849189,44619293454,27166794510,44445322044,27533920060,57400479036,62514712124,48808446268,23741388573,62736882477,48808446780,23858949306,44652847758,15151486749,15219693989,62787276348,27030613302,27166927662,15403144029,23858828637,62105538108,15151536809,32033416890,40324342542,63298388622,63298421910,44210433594,44619426606,48808438458,40216415548,27533952828,44652980910,63059971644,50158637187,15151603257,63009494553,32706138243,63145842201,27166977594,12501616314,40324375830,15403273020,32706204819,63059813526]
def cubTag (k i : Nat) : Nat :=
  match k with
  | 5 => cubWitness[((#[0] : Array Nat)[i-0]?.getD 0)]?.getD 0
  | 6 => cubWitness[((#[1,2,2,3,2,2,2,1,2,1,4,5,6,6,7,7,8,9,10,10,11,12,13,14,15,16,6,17,18,19,20,21,6,22,7,6,8,7,23,24,24,25,18,24,25,26,17,13,24,17,25,27,25,24,10,12,25,17,25,17,17,25,25,25,28,17,17] : Array Nat)[i-4]?.getD 0)]?.getD 0
  | 7 => cubWitness[((#[3,3,3,16,29,3,18,30,30,30,12,30,30,16,16,29,12,30,31,29,31,7,7,32,29,12,8,12,22,29,29,32,33,34,35,36,37,7,30,38,39,30,40,16,23,17,29,29,8,7,8,7,32,29,18,41,12,29,39,16,12,29,19,42,19,43,23,44,42,24,24,16,29,16,45,12,18,18,32,29,46,8,8,23,47,48,29,29,49,47,29,47,17,10,29,50,29,51,10,10,16,12,52,19,13,10,29,10,29,10,10,52,52,17,53,29,53,34,7,54,16,23,17,17,8,55,29,41,56,12,30,30,17,34,36,36,19,17,23,17,57,7,36,8,58,36,32,58,24,24,17,12,36,29,59,24,25,35,30,30,36,36,19,7,36,7,12,12,34,30,10,51,30,23,23,30,16,30,16,17,16,60,7,33,23,41,7,44,18,18,7,8,8,61,7,10,7,8,29,8,7,42,62,12,7,12,63,64,30,19,19,19,65,19,19,25,65,8,18,42,42,29,10,10,29,58,36,58,30,30,16,7,29,12,30,12,12,19,66,12,8,18,42,42,42,67,42,42,36,25,42,25,24,33,36,18,68,36,30,18,24,17,18,69,42,16,23,44,24,29,44,62,70,12,36,25,25,24,25,7,32,65,65,42,42,10,29,36,7,65,19,33,32,18,7,19,32,8,19,65,17,13,71,8,17,7,32,39,65,65,18,18,32,39,32,19,19,7,72,29,23,13,19,8,19,19,23,13,8,8,17,17,29,7,24,24,73,65,65,24,24,25,25,73,65,65,74,75,24,24,24,24,24,54,52,25,24,76,75,25,25,25,54,24,24,25,24,24,25,54,25,24,7,24,7,18,52,24,75,19,19,19,19,19,19,23,18,19,19,19,19,8,8,19,19,17,17,19,41,41,19,17,19,19,13,77,78,19,65,17,19,36,18,12,78,65,17,17,17,17,17,17,17,17,13,29,29,33,18,8,8,10,30,8,8,18,29,18,8,8,8,18,18,8,8,8,8,16,16,8,41,8,79,18,17,16,17,30,19,30,69,42,69,41,41,42,41,30,41,42,69,42,42,42,41,41,41,69,42,42,41,41,41,41,41,41,16,16,41,8,41,62,30,8,16,17,17,29,30,19,8,18,8,8,51,80,16,8,16,16,16,62,8,79,81,62,29,17,17,17,41,8,18,8,41,30,52,19,18,35,12,19,47,19,71,29,51,36,17,19,25,50,19,50,50,50,7,19,19,19,30,17,25,25,7,24,30,17,17,17,51,51,17,17,17,17,25,17,17,17,17,17,17,17,17,30,17,18,17,36,41,25] : Array Nat)[i-208]?.getD 0)]?.getD 0
  | 8 => cubWitness[((#[30,29,18,29,29,18,18,30,17,29,18,29,29,18,29,42,42,51,51,51,29,29,29,29,51,29,29,17,29,17,18,30,51,30,29,29,29,30,30,29,82,29,18,12,29,29,18,74,74,76,65,18,65,13,65,65,13,13,32,18,18,32,65,65,24,18,24,65,65,36,36,65,65,36,29,29,18,79,7,42,42,62,25,32,62,51] : Array Nat)[i-1129]?.getD 0)]?.getD 0
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
theorem crossP5_0 : spanOK g63 5 0 1 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB5 : spanOK g63 5 0 1 := crossP5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_0 : spanOK g63 6 0 4 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_4 : spanOK g63 6 4 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_36 : spanOK g63 6 36 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP6_68 : spanOK g63 6 68 3 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB6 : spanOK g63 6 0 71 := (spanMerge (spanMerge crossP6_0 crossP6_4) (spanMerge crossP6_36 crossP6_68))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_0 : spanOK g63 7 0 9 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_9 : spanOK g63 7 9 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_105 : spanOK g63 7 105 86 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_191 : spanOK g63 7 191 17 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_208 : spanOK g63 7 208 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_240 : spanOK g63 7 240 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_272 : spanOK g63 7 272 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_304 : spanOK g63 7 304 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_336 : spanOK g63 7 336 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_368 : spanOK g63 7 368 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_400 : spanOK g63 7 400 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_432 : spanOK g63 7 432 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_464 : spanOK g63 7 464 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_496 : spanOK g63 7 496 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_528 : spanOK g63 7 528 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_560 : spanOK g63 7 560 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_592 : spanOK g63 7 592 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_624 : spanOK g63 7 624 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_656 : spanOK g63 7 656 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_688 : spanOK g63 7 688 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_720 : spanOK g63 7 720 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_752 : spanOK g63 7 752 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP7_784 : spanOK g63 7 784 6 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB7 : spanOK g63 7 0 790 := (spanMerge (spanMerge (spanMerge (spanMerge crossP7_0 crossP7_9) (spanMerge crossP7_105 (spanMerge crossP7_191 crossP7_208))) (spanMerge (spanMerge crossP7_240 (spanMerge crossP7_272 crossP7_304)) (spanMerge crossP7_336 (spanMerge crossP7_368 crossP7_400)))) (spanMerge (spanMerge (spanMerge crossP7_432 (spanMerge crossP7_464 crossP7_496)) (spanMerge crossP7_528 (spanMerge crossP7_560 crossP7_592))) (spanMerge (spanMerge crossP7_624 (spanMerge crossP7_656 crossP7_688)) (spanMerge crossP7_720 (spanMerge crossP7_752 crossP7_784)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_0 : spanOK g63 8 0 6 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_6 : spanOK g63 8 6 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_102 : spanOK g63 8 102 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_198 : spanOK g63 8 198 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_294 : spanOK g63 8 294 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_390 : spanOK g63 8 390 11 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_401 : spanOK g63 8 401 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_497 : spanOK g63 8 497 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_593 : spanOK g63 8 593 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_689 : spanOK g63 8 689 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_785 : spanOK g63 8 785 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_881 : spanOK g63 8 881 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_977 : spanOK g63 8 977 95 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1072 : spanOK g63 8 1072 57 := by
  apply spanOld
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1129 : spanOK g63 8 1129 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1161 : spanOK g63 8 1161 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP8_1193 : spanOK g63 8 1193 22 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB8 : spanOK g63 8 0 1215 := (spanMerge (spanMerge (spanMerge (spanMerge crossP8_0 crossP8_6) (spanMerge crossP8_102 crossP8_198)) (spanMerge (spanMerge crossP8_294 crossP8_390) (spanMerge crossP8_401 crossP8_497))) (spanMerge (spanMerge (spanMerge crossP8_593 crossP8_689) (spanMerge crossP8_785 crossP8_881)) (spanMerge (spanMerge crossP8_977 crossP8_1072) (spanMerge crossP8_1129 (spanMerge crossP8_1161 crossP8_1193)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_0 : spanOK g63 9 0 7 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_7 : spanOK g63 9 7 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_103 : spanOK g63 9 103 25 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_128 : spanOK g63 9 128 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_224 : spanOK g63 9 224 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP9_320 : spanOK g63 9 320 26 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB9 : spanOK g63 9 0 346 := (spanMerge (spanMerge crossP9_0 (spanMerge crossP9_7 crossP9_103)) (spanMerge crossP9_128 (spanMerge crossP9_224 crossP9_320)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossP10_0 : spanOK g63 10 0 26 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem crossB10 : spanOK g63 10 0 26 := crossP10_0
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
theorem g63G : graphValid g63 (boundsBefore K2110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullLower : Impossible true graph 11 instanceInputs.toFinset := by
  rw [show graph = targetOf g63 by decide +kernel]
  exact root_span (g:=g63) (top:=11) (i:=0) (before_sound K2110 V2110) g63G crossT (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_41722

open PEqualNP.Outside.L_meta_41722 in
theorem PEqualNP.Outside.L_meta_41722 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276677288 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276677288 * 2 ^ 32 + 3939027080) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
