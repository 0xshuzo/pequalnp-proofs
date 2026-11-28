import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The truth table, restrictions and search certificates below are instance-specific.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_41932
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
def graph : Sig := (bitLimbs [0xfee8eee0,0xfae8e8c0fee8eee0fae8,0xe8c0fee8eee0fae8e8c0,0xfee8eee0fae8e8c0fee8,0xeee0fae8e8c0fee8eee0,0xfae8e8c0fee8eee0fae8,0xe8c0fee8eee0fae8e8c0])
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 1 && x 2) || (x 0 && x 1 && x 3) || (x 0 && x 2 && x 3) || (x 0 && x 1 && x 4) || (x 0 && x 2 && x 4) || (x 0 && x 3 && x 4) || (x 2 && x 3 && x 4) || (x 0 && x 2 && x 5) || (x 0 && x 3 && x 5) || (x 1 && x 3 && x 5)
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
  if m=4123 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=4119 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) else
  if m=4111 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=2110 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2109 then (x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2107 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) else
  if m=2105 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2103 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=2102 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) else
  if m=2095 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=2094 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2091 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=2079 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2078 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=2077 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) else
  if m=2071 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 4) else
  if m=2063 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=60 then (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=58 then (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) else
  if m=57 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) else
  if m=54 then (x 1 &&& x 2) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) else
  if m=53 then (x 0 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=46 then (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=44 then (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=39 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=35 then (x 0 &&& x 1) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=30 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3 &&& x 4) else
  if m=28 then (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=26 then (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) else
  if m=25 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=22 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=21 then (x 0 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=13 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=11 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  if m=7 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) else
  (x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 3) ||| (x 0 &&& x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 0 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) ||| (x 0 &&& x 2 &&& x 5) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 5)
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
  if m=4123 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=4119 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) else
  if m=4111 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=2110 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2109 then (x 2) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2107 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) else
  if m=2105 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2103 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=2102 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) else
  if m=2095 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=2094 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2091 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=2079 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2078 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=2077 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) else
  if m=2071 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 4) else
  if m=2063 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=60 then (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=58 then (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) else
  if m=57 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) else
  if m=54 then (x 1 &&& x 2) ||| (x 2 &&& x 4) ||| (x 1 &&& x 5) else
  if m=53 then (x 0 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=46 then (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=44 then (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=39 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=35 then (x 0 &&& x 1) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=30 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3 &&& x 4) else
  if m=28 then (x 2 &&& x 3) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=26 then (x 1 &&& x 3) ||| (x 1 &&& x 4) ||| (x 3 &&& x 4) else
  if m=25 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) else
  if m=22 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=21 then (x 0 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=13 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=11 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  if m=7 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) else
  (x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 3) ||| (x 0 &&& x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 0 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) ||| (x 0 &&& x 2 &&& x 5) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases h0 : m=4123
  · simp only [graphGoal,liftGoal,if_pos h0,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h1 : m=4119
  · simp only [graphGoal,liftGoal,if_neg h0,if_pos h1,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h2 : m=4111
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_pos h2,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h3 : m=2110
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_pos h3,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h4 : m=2109
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h5 : m=2107
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h6 : m=2105
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h7 : m=2103
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_pos h7,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h8 : m=2102
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_pos h8,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h9 : m=2095
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_pos h9,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h10 : m=2094
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_pos h10,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h11 : m=2091
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_pos h11,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h12 : m=2079
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_pos h12,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h13 : m=2078
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_pos h13,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
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
  by_cases h22 : m=53
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_pos h22,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h23 : m=51
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_pos h23,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h24 : m=46
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_pos h24,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h25 : m=44
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_pos h25,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h26 : m=39
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_pos h26,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h27 : m=35
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_pos h27,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 5 (by decide)]
  by_cases h28 : m=30
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_pos h28,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h29 : m=28
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_pos h29,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h30 : m=26
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_pos h30,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h31 : m=25
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_pos h31,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h32 : m=22
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_pos h32,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h33 : m=21
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_pos h33,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h34 : m=14
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_pos h34,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h35 : m=13
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_pos h35,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h36 : m=11
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_pos h36,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide)]
  by_cases h37 : m=7
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_pos h37,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide)]
  simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,if_neg h34,if_neg h35,if_neg h36,if_neg h37,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
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



def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276678368 * 2 ^ 32 + 4209567936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[⟨.and,[0,1]⟩,⟨.or,[0,1]⟩,⟨.and,[0,4]⟩,⟨.or,[1,3]⟩,⟨.or,[2,3]⟩,⟨.or,[2,6]⟩,⟨.or,[5,8]⟩,⟨.and,[7,10]⟩,⟨.or,[4,13]⟩,⟨.and,[9,11]⟩,⟨.and,[12,13]⟩,⟨.and,[14,15]⟩,⟨.or,[16,17]⟩], 18⟩
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

def lowRow (i : Fin 6) : Row := Fin.ofNat 512 (([10, 4, 2, 3, 3, 5] : List Nat).getD i.val 0)
def highRow (i : Fin 6) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (([10, 4, 2, 3, 3, 5] : List Nat).getD i.val 0))

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
def K7 := extendKnown [] 4 [(7,[]),(11,[50]),(13,[33,49]),(14,[16,32,48]),(21,[33,65,49]),(22,[16,32,64,48]),(25,[49,66]),(26,[16,48,66]),(28,[32,49,64,16]),(35,[82,50,67]),(44,[32,49,80,16,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[((bitLimbs [0xf3726f175edd8fff37,0x26f175edd8fff3726f17]),(bitLimbs [0xb6401617a14a562b64,0x1617a14a562b6401617])),((bitLimbs [0xffdfd3fdeffefb5ffd,0xfd3fdeffefb5ffdfd3fd]),(bitLimbs [0x6806517410004cc680,0x6517410004cc68065174])),((bitLimbs [0xbebffcfbbf77fefbeb,0xffcfbbf77fefbebffcfb]),(bitLimbs [0x84b80c89401e01184b,0x80c89401e01184b80c89])),((bitLimbs [0xf1f6afa674dbf5ef1f,0x6afa674dbf5ef1f6afa6]),(bitLimbs [0x191aaba288249b8191,0xaaba288249b8191aaba2])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := [(0,1,14,0,4)]
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
theorem g15G : graphValid g15 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 5 := lower_forest (g:=g15) (i:=0) (hints:=403179530) (before_sound K7 V7) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K7 5 [(15,[]),(23,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((bitLimbs [0xffffffffffffffffff,0xffffffffffffffffffff]),(bitLimbs [0x2e01448987032e0144,0x8987032e01448987032e])),((bitLimbs [0xdcbfb7abfd3fdcbfb7,0xabfd3fdcbfb7abfd3fdc]),(bitLimbs [0xdc40593a7890dc4059,0x3a7890dc40593a7890dc])),(0x0,0x0),((bitLimbs [0xebeddafdf3f9ebedda,0xfdf3f9ebeddafdf3f9eb]),(bitLimbs [0xe11a8d00b8e9e11a8d,0xb8e9e11a8d00b8e9e1])),((bitLimbs [0xb776edfedfceb776ed,0xfedfceb776edfedfceb7]),(bitLimbs [0x938f1014698e938f10,0x14698e938f1014698e93])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := [(0,1,26,0,4)]
def g27A : List (List Nat) := [[],[67],[49],[49,65],[65,49],[65]]
def g27D4 (j : Nat) := if j=0 then 0x1f else 0
def g27L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g27D4)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,4,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P4_0 : block g27 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B4 : block g27 4 0 1=true := g27P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : checkedTables g27 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g27 0 0 0 = true)
  · exact (rfl : block g27 1 0 0 = true)
  · exact (rfl : block g27 2 0 0 = true)
  · exact (rfl : block g27 3 0 0 = true)
  · exact g27B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 5 := lower_forest (g:=g27) (i:=0) (hints:=206561088010) (before_sound K15 V15) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K15 5 [(27,[]),(43,[48,16,84]),(45,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V15 low27 (by decide +kernel)
def g29Y : Array (Bits × Bits) := #[((bitLimbs [0xf8ef9fedfdb7fff1df,0x3fdbfb6fffe3be7fb7f6]),(bitLimbs [0x272b10255c88124e56,0x204ab910249cac409572])),(0x0,0x0),((bitLimbs [0x7fff6f7ff2eebcfffe,0xdeffe5dd79fffdbdffcb]),(bitLimbs [0x81c4284fa0d1070388,0x509f41a20e0710a13e83])),((bitLimbs [0xf79ffb9e6ffdf7ef3f,0xf73cdffbefde7fee79bf]),(bitLimbs [0x8c6583126b02a118cb,0x624d6054231960c49ac])),((bitLimbs [0xbf77fef79f5f6f7eef,0xfdef3ebedefddffbde7d]),(bitLimbs [0x1a824e809761903504,0x9d012ec3206a093a025d])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g29C : List ColumnInfo := [(0,1,28,0,4),(0,4,25,0,4),(0,8,21,0,4),(0,16,13,0,4)]
def g29A : List (List Nat) := [[],[67],[50],[50,66],[66,50],[66],[32],[32,67],[32,48],[32,48,64],[32,64,48],[32,64],[48,32],[48,32,66],[48],[48,64],[48,66],[48,66,32],[64,32,50],[64,32],[64,48],[64],[64,50,32],[64,50]]
def g29D3 := limbs80 #[#[0x23ca621021e02108010,0x8028]]
def g29D4 := limbs80 #[#[0x2f90810bc42043e08010,0x609085870]]
def g29H4 (j : Nat) := if j=0 then 0x18f else 0
def g29D5 (j : Nat) := if j=0 then 0xd1027c10 else 0
def g29H5 := limbs80 #[#[0xe0002100000000000002,0xbc2002120000003,0x27000660]]
def g29D6 (j : Nat) := if j=0 then 0x3904f else 0
def g29H6 := limbs80 #[#[0xf52200000000000000,0x80003800000000000000,0x480091001]]
def g29L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g29D3)
  | 4 => (3,2,2,0,0,5,0,g29D4)
  | 5 => (1,1,2,0,0,0,0,g29D5)
  | 6 => (1,0,2,0,0,0,0,g29D6)
  | _ => emptyPacking
def g29I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g29H4
  | 5 => lookupWord 2 23 1 9 2 3 g29H5
  | 6 => lookupWord 1 23 0 9 0 5 g29H6
  | _ => fun _ => none
def g29 : Forest := ⟨29,6,fun i => g29Y[i]?.getD (0,0),g29C,g29A,g29L,g29I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P3_0 : block g29 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g29B3 : block g29 3 0 2=true := g29P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P4_0 : block g29 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g29B4 : block g29 4 0 3=true := g29P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P5_0 : block g29 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g29B5 : block g29 5 0 1=true := g29P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29P6_0 : block g29 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g29B6 : block g29 6 0 1=true := g29P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29T : checkedTables g29 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g29 0 0 0 = true)
  · exact (rfl : block g29 1 0 0 = true)
  · exact (rfl : block g29 2 0 0 = true)
  · exact g29B3
  · exact g29B4
  · exact g29B5
  · exact g29B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g29G : graphValid g29 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low29 : Lower true (varsX 29) (graphGoal 29) 7 := lower_forest (g:=g29) (i:=0) (hints:=344270831628) (before_sound K27 V27) g29G g29T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K29 := extendKnown K27 7 [(29,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V29 : Known true K29 := extend_ok (m:=29) V27 low29 (by decide +kernel)
def g30Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xfe7faf77fffbbfbffc,0xff5eeffff77f7ff9febd]),(bitLimbs [0x28070c080040612850,0xe18100080c250a01c30])),((bitLimbs [0xa7b1d7bcdbfe6bff4f,0x63af79b7fcd7fe9ec75e]),(bitLimbs [0x8070d303550092d100,0xe1a606aa0125a201c34c])),((bitLimbs [0x5beef8dbb7cff7ccb7,0xddf1b76f9fef996fbbe3]),(bitLimbs [0x1350b0e442a08e0426,0xa161c885411c084d42c3])),((bitLimbs [0xaba87d9d523df74357,0x50fb3aa47bee86aea1f6]),(bitLimbs [0x12ac6da2a9e8513225,0x58db4553d0a2644ab1b6])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g30C : List ColumnInfo := [(0,16,14,0,4)]
def g30A : List (List Nat) := [[],[50]]
def g30D4 (j : Nat) := if j=0 then 0x1f else 0
def g30L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g30D4)
  | _ => emptyPacking
def g30I (_ _ : Nat) : Option (Nat × Nat) := none
def g30 : Forest := ⟨30,4,fun i => g30Y[i]?.getD (0,0),g30C,g30A,g30L,g30I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30P4_0 : block g30 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g30B4 : block g30 4 0 1=true := g30P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30T : checkedTables g30 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g30 0 0 0 = true)
  · exact (rfl : block g30 1 0 0 = true)
  · exact (rfl : block g30 2 0 0 = true)
  · exact (rfl : block g30 3 0 0 = true)
  · exact g30B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g30G : graphValid g30 (boundsBefore K29) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low30 : Lower true (varsX 30) (graphGoal 30) 5 := lower_forest (g:=g30) (i:=0) (hints:=824902682624) (before_sound K29 V29) g30G g30T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K30 := extendKnown K29 5 [(30,[]),(46,[33,84]),(2071,[48,33,16]),(2075,[32,49]),(2077,[16]),(2091,[32,16,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V30 : Known true K30 := extend_ok (m:=30) V29 low30 (by decide +kernel)
def g39Y : Array (Bits × Bits) := #[((bitLimbs [0x75ef25b6f9ffa3f75e,0xf25b6f9ffa3f75ef25b6]),(bitLimbs [0x110025800680040110,0x2580068004011002580])),((bitLimbs [0x9af9fe4df6c77fe9af,0x9fe4df6c77fe9af9fe4d]),(bitLimbs [0x1480c0834002000,0x1480c08340020001480c])),((bitLimbs [0xd5b2db235de5bc7d5b,0x2db235de5bc7d5b2db23]),(bitLimbs [0x8cb40223a04a40d8cb,0x40223a04a40d8cb40223])),(0x0,0x0),(0x0,0x0),((bitLimbs [0xaf6772f89edee90af6,0x772f89edee90af6772f8]),(bitLimbs [0x87612706102325087,0x61270610232508761270])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g39C : List ColumnInfo := [(4,0,35,0,4)]
def g39A : List (List Nat) := [[],[82],[16],[16,82]]
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
theorem g39G : graphValid g39 (boundsBefore K30) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 5 := lower_forest (g:=g39) (i:=0) (hints:=35184372351490) (before_sound K30 V30) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K30 5 [(39,[]),(60,[32,49,64,16]),(2063,[33,67,83]),(2094,[32,49,16]),(4119,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V30 low39 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((bitLimbs [0xc7ffeabedff3fd7d8f,0xffd57dbfe7fafb1fffaa]),(bitLimbs [0x800dc0010104000100,0x1b800202080002003700])),((bitLimbs [0xffd51f75ff5c7683ff,0xaa3eebfeb8ed07ff547d]),(bitLimbs [0x22501a4a48210d0244,0xa0349490421a04894069])),(0x0,0x0),(0x0,0x0),((bitLimbs [0x24ee49e71d3bc7e849,0xdc93ce3a778fd093b927]),(bitLimbs [0xcb209d8e4b0371a19,0x6413b1c9606e3432c827])),((bitLimbs [0xfa88b5ebe9fe5edff5,0x116bd7d3fcbdbfea22d7]),(bitLimbs [0x48a025940600d0d091,0x404b280c01a1a1228096])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := [(16,0,35,0,4)]
def g51A : List (List Nat) := [[],[81]]
def g51D4 (j : Nat) := if j=0 then 0x1f else 0
def g51L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g51D4)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,4,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P4_0 : block g51 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B4 : block g51 4 0 1=true := g51P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g51 0 0 0 = true)
  · exact (rfl : block g51 1 0 0 = true)
  · exact (rfl : block g51 2 0 0 = true)
  · exact (rfl : block g51 3 0 0 = true)
  · exact g51B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=35253091566082) (before_sound K39 V39) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K39 5 [(51,[]),(53,[33,84]),(57,[49,33,84]),(58,[48,32,84]),(2102,[32,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V39 low51 (by decide +kernel)
def g54Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xbe66fcef77bdedfdbe,0x66fcef77bdedfdbe66fc]),(bitLimbs [0x12c660108049081112,0xc660108049081112c660])),((bitLimbs [0xdddf0ffbeadfff56dd,0xdf0ffbeadfff56dddf0f]),(bitLimbs [0x81080e071100312481,0x80e071100312481080e])),(0x0,0x0),((bitLimbs [0x51bbc39fabf33e4f51,0xbbc39fabf33e4f51bbc3]),(bitLimbs [0x22d3c160a488cc4a22,0xd3c160a488cc4a22d3c1])),((bitLimbs [0xeb20f7b5bf2d6cbbeb,0x20f7b5bf2d6cbbeb20f7]),(bitLimbs [0x6830974a4382752068,0x30974a43827520683097])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g54C : List ColumnInfo := []
def g54A : List (List Nat) := [[],[33,84]]
def g54D3 (j : Nat) := if j=0 then 0xf else 0
def g54L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g54D3)
  | _ => emptyPacking
def g54I (_ _ : Nat) : Option (Nat × Nat) := none
def g54 : Forest := ⟨54,3,fun i => g54Y[i]?.getD (0,0),g54C,g54A,g54L,g54I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54P3_0 : block g54 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g54B3 : block g54 3 0 1=true := g54P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54T : checkedTables g54 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g54 0 0 0 = true)
  · exact (rfl : block g54 1 0 0 = true)
  · exact (rfl : block g54 2 0 0 = true)
  · exact g54B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g54G : graphValid g54 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low54 : Lower true (varsX 54) (graphGoal 54) 4 := lower_forest (g:=g54) (i:=0) (hints:=70643622610944) (before_sound K51 V51) g54G g54T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K54 := extendKnown K51 4 [(54,[]),(2105,[16,50,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V54 : Known true K54 := extend_ok (m:=54) V51 low54 (by decide +kernel)
def g2078Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0x3f6997f9e86ed67ed3,0x2ff3d0ddacfda65fe7a1]),(bitLimbs [0x48800294810280910,0x52902050122000a520])),((bitLimbs [0xdf4e679d13fb6bbe9c,0xcf3a27f6d77d399e744f]),(bitLimbs [0x10041410c4d00020,0x8282189a00040105043])),((bitLimbs [0x56f6d97ec5bd74aded,0xb2fd8b7ae95bdb65fb16]),(bitLimbs [0xb80211008502017004,0x22010a0402e008440214])),((bitLimbs [0xf69b7ce63e36cfed36,0xf9cc7c6d9fda6df398f8]),(bitLimbs [0x32040c22209000640,0x81844412000c81030888])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2078C : List ColumnInfo := [(2,0,28,0,4),(4,0,26,0,4),(8,0,22,0,4),(16,0,14,0,4)]
def g2078A : List (List Nat) := [[],[67],[50],[50,66],[66,50],[66],[33],[33,67],[33,49],[33,49,65],[33,65,49],[33,65],[49,33],[49,33,66],[49],[49,65],[49,66],[49,66,33],[65,33,50],[65,33],[65,49],[65],[65,50,33],[65,50]]
def g2078D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g2078D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g2078H4 (j : Nat) := if j=0 then 0x99 else 0
def g2078D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g2078H5 := limbs80 #[#[0x5037e100fc3100042002,0x1094]]
def g2078D6 (j : Nat) := if j=0 then 0x3904f else 0
def g2078H6 := limbs80 #[#[0x34000000000000,0x14a0000000000000000,0x0,0x1c4280000068000,0x1e20000000000]]
def g2078L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g2078D3)
  | 4 => (3,2,2,0,0,5,0,g2078D4)
  | 5 => (1,1,2,0,0,0,0,g2078D5)
  | 6 => (1,0,2,0,0,0,0,g2078D6)
  | _ => emptyPacking
def g2078I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g2078H4
  | 5 => lookupWord 2 11 2 9 2 3 g2078H5
  | 6 => lookupWord 1 53 0 9 0 5 g2078H6
  | _ => fun _ => none
def g2078 : Forest := ⟨2078,6,fun i => g2078Y[i]?.getD (0,0),g2078C,g2078A,g2078L,g2078I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2078P3_0 : block g2078 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2078B3 : block g2078 3 0 2=true := g2078P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2078P4_0 : block g2078 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2078B4 : block g2078 4 0 3=true := g2078P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2078P5_0 : block g2078 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2078B5 : block g2078 5 0 1=true := g2078P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2078P6_0 : block g2078 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2078B6 : block g2078 6 0 1=true := g2078P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2078T : checkedTables g2078 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2078 0 0 0 = true)
  · exact (rfl : block g2078 1 0 0 = true)
  · exact (rfl : block g2078 2 0 0 = true)
  · exact g2078B3
  · exact g2078B4
  · exact g2078B5
  · exact g2078B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2078G : graphValid g2078 (boundsBefore K54) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2078 : Lower true (varsX 2078) (graphGoal 2078) 7 := lower_forest (g:=g2078) (i:=0) (hints:=137707915264) (before_sound K54 V54) g2078G g2078T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2078 := extendKnown K54 7 [(2078,[]),(4111,[64,16,33,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2078 : Known true K2078 := extend_ok (m:=2078) V54 low2078 (by decide +kernel)
def g4123Y : Array (Bits × Bits) := #[((bitLimbs [0xd87fc1ecd565d87fc1,0xecd565d87fc1ecd565d8]),(bitLimbs [0x988414121440988414,0x12144098841412144098])),((bitLimbs [0xa4f5fee73f3aa4f5fe,0xe73f3aa4f5fee73f3aa4]),0x0),(0x0,0x0),((bitLimbs [0x13b733b96dc713b733,0xb96dc713b733b96dc713]),(bitLimbs [0x1488820210f014888,0x20210f01488820210f01])),((bitLimbs [0x6bed2d7db0d46bed2d,0x7db0d46bed2d7db0d46b]),(bitLimbs [0x6213420d0200621342,0xd02006213420d020062])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g4123C : List ColumnInfo := [(2,0,25,0,4)]
def g4123A : List (List Nat) := [[],[67],[48],[48,64],[64,48],[64]]
def g4123D4 (j : Nat) := if j=0 then 0x1f else 0
def g4123L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g4123D4)
  | _ => emptyPacking
def g4123I (_ _ : Nat) : Option (Nat × Nat) := none
def g4123 : Forest := ⟨4123,4,fun i => g4123Y[i]?.getD (0,0),g4123C,g4123A,g4123L,g4123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4123P4_0 : block g4123 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g4123B4 : block g4123 4 0 1=true := g4123P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4123T : checkedTables g4123 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g4123 0 0 0 = true)
  · exact (rfl : block g4123 1 0 0 = true)
  · exact (rfl : block g4123 2 0 0 = true)
  · exact (rfl : block g4123 3 0 0 = true)
  · exact g4123B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g4123G : graphValid g4123 (boundsBefore K2078) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low4123 : Lower true (varsX 4123) (graphGoal 4123) 5 := lower_forest (g:=g4123) (i:=0) (hints:=68853694472) (before_sound K2078 V2078) g4123G g4123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K4123 := extendKnown K2078 5 [(4123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V4123 : Known true K4123 := extend_ok (m:=4123) V2078 low4123 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[((bitLimbs [0xdc67c33ddd1dffef37,0x7ae27fb8664f7ad3fea9]),(bitLimbs [0xc448c0a23003220230,0x38c028646609125346a9])),((bitLimbs [0x41926dee3fe7e5fa9e,0x3fbdfbfe9b9b8737b362]),(bitLimbs [0xbe020408814c727982,0x1815431c183a0314b242])),((bitLimbs [0xbbfdfdcffbf62bd4ee,0x97dfee67bdfdfd7c4df6]),(bitLimbs [0x9227408030d8044,0x20a84620585cc284d24])),((bitLimbs [0xae3b9ef1923cf8fd7b,0xfc7ea0914ea77a89e1df]),(bitLimbs [0x4af42a88914c81dd8a,0xe478209a10242881a1de])),((bitLimbs [0x77fdf71ed43f763ffb,0xea6d1f29e4ecc1ea9e1f]),(bitLimbs [0x3086095a88f09c25bb,0x2341a1981f041ea9813])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,1,2078,0,7)]
def g31A : List (List Nat) := [[],[67]]
def g31D7 (j : Nat) := if j=0 then 0x3f else 0
def g31L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g31D7)
  | _ => emptyPacking
def g31I (_ _ : Nat) : Option (Nat × Nat) := none
def g31 : Forest := ⟨31,7,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
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
  · exact (rfl : block g31 4 0 0 = true)
  · exact (rfl : block g31 5 0 0 = true)
  · exact (rfl : block g31 6 0 0 = true)
  · exact g31B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K4123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 8 := lower_forest (g:=g31) (i:=0) (hints:=206561609738) (before_sound K4123 V4123) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K4123 8 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V4123 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((bitLimbs [0xc3bdcafe3dff7f4758,0xf0fff7e8b1af3c5f5bd9]),(bitLimbs [0x1264053dc034d30390,0x20bf2f8c2208244d4359])),((bitLimbs [0x7f673573facbbbbef7,0x9ff55f3f5e74f7e0a7f6]),(bitLimbs [0x81460509a07b1a8594,0x441540c3e6061e083c4])),((bitLimbs [0x3d7ff97dff71deda7f,0xeecf8bd7f6fd7373f479]),(bitLimbs [0x6201aa800804802868,0xc28089d340951a137430])),((bitLimbs [0xcbbe6fc298bff77ffe,0x553a75f8492bdd9f0fae]),(bitLimbs [0xe030d0d41c41247a4a,0x5410103105b89d1a0cae])),(0x0,0x0),((bitLimbs [0xf4e8f6ae951758f5b0,0xffb2b6d0bb9af8bc7967]),(bitLimbs [0x501f1a03be18207db8,0x9923024ab2d258b43963])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,1,2094,0,5),(0,8,39,0,5),(2,0,45,0,5),(4,0,43,0,5),(32,0,15,0,5),(2,1,44,0,4),(4,8,35,0,4),(32,1,14,0,4),(32,8,7,0,4)]
def g47A : List (List Nat) := [[],[48,33]]
def g47D4 (j : Nat) := if j=0 then 0x2786055121 else 0
def g47D5 := limbs80 #[#[0xbd42506fea890df55121,0x2001002a98480bfa9283,0x308]]
def g47H5 (j : Nat) := if j=0 then 0x270 else 0
def g47D6 := limbs80 #[#[0x3300fd41fd21fc30fe20,0x4059cc520e4208099970,0x90620807398b424c7210,0x20a41883001062]]
def g47H6 (j : Nat) := if j=0 then 0x5d9ea8 else 0
def g47D7 (j : Nat) := if j=0 then 0x43b2a190813f else 0
def g47H7 (j : Nat) := if j=0 then 0x6405f48005300000980 else 0
def g47L : Nat → Packing
  | 4 => (1,3,4,0,0,0,0,g47D4)
  | 5 => (4,2,4,0,0,6,0,g47D5)
  | 6 => (4,1,4,0,0,8,0,g47D6)
  | 7 => (1,0,4,0,0,0,0,g47D7)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 5 0 1 g47H5
  | 6 => lookupWord 1 7 0 6 2 0 g47H6
  | 7 => lookupWord 1 11 0 7 2 1 g47H7
  | _ => fun _ => none
def g47 : Forest := ⟨47,7,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4_0 : block g47 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B4 : block g47 4 0 1=true := g47P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P5_0 : block g47 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B5 : block g47 5 0 4=true := g47P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P6_0 : block g47 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 4=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P7_0 : block g47 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B7 : block g47 7 0 1=true := g47P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact (rfl : block g47 3 0 0 = true)
  · exact g47B4
  · exact g47B5
  · exact g47B6
  · exact g47B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 8 := lower_forest (g:=g47) (i:=0) (hints:=175922263623690) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 8 [(47,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((bitLimbs [0xe7bff72fdfcbeb7dbe,0xf2ef46cc6d7f57bf57f0]),(bitLimbs [0x71801c444572e0345a,0xb28f600a4441559745b0])),((bitLimbs [0x5b73fefb6efdfdff5f,0xedd3fdfff6b8b8dfa87f]),(bitLimbs [0x780527250a2205004a,0xc3c1c0f610b8a08e885c])),((bitLimbs [0xffcf3dfdffff5efafd,0xff7dfbbbbfcfef62ffbf]),(bitLimbs [0x80428882908848d8a5,0x30003b01aa040a607623])),(0x0,0x0),((bitLimbs [0x70bbc78bfd0aef3dab,0x14dadef4677396bde3ca]),(bitLimbs [0x8953813a2c000aa9a1,0x55c0dd0f5669039a3ca])),((bitLimbs [0xcd2f8a751347c4a7ce,0x733d8bd86b146d2f350d]),(bitLimbs [0x1fcb4f1aca33b276d,0xc3b4838923f4952f310d])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(0,1,2102,0,5),(0,32,2071,0,5),(32,0,23,0,5),(0,16,7,0,4),(0,48,7,0,4)]
def g55A : List (List Nat) := [[]]
def g55D4 := limbs80 #[#[0x7850486bca610de94021,0x930c0ae29a43]]
def g55D5 := limbs80 #[#[0xc580ff21fe21fd21fc21,0x2108842321010c8404ea]]
def g55H5 (j : Nat) := if j=0 then 0x20000000000000aa3b40 else 0
def g55D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g55H6 := limbs80 #[#[0x1200003d000000,0x80270]]
def g55L : Nat → Packing
  | 4 => (4,2,3,0,0,5,0,g55D4)
  | 5 => (4,1,3,0,0,6,0,g55D5)
  | 6 => (1,0,3,0,0,0,0,g55D6)
  | _ => emptyPacking
def g55I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 17 0 6 2 0 g55H5
  | 6 => lookupWord 1 17 0 6 2 0 g55H6
  | _ => fun _ => none
def g55 : Forest := ⟨55,6,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : block g55 4 0 4=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : block g55 4 0 4=true := g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P5_0 : block g55 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B5 : block g55 5 0 4=true := g55P5_0
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
theorem low55 : Lower true (varsX 55) (graphGoal 55) 7 := lower_forest (g:=g55) (i:=0) (hints:=176128019400722) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 7 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((bitLimbs [0xfdebcf7f3f7fffedff,0xffb7f775b1b7ff77adbf]),(bitLimbs [0x511001005a95f022,0x1db1555880a2d313093f])),((bitLimbs [0xbfd6f9bff8ff32ff70,0xfeeb3febffcbe88efbd7]),(bitLimbs [0xa79b476930c20440,0xeaaa874b5d411884ead6])),(0x0,0x0),((bitLimbs [0xdffdbfd7e7feff5baf,0xf97fdfbf6ffdb7fd777a]),(bitLimbs [0xe808028809a46a4b8d,0xd2458a216818236c7560])),((bitLimbs [0xbebb40af5f754de47b,0x8fd5bbd2f5176ec3fcad]),(bitLimbs [0xf4b46d28098c320635,0x421cfa90bd0564c3f489])),((bitLimbs [0x725ff7d2ddb4967eac,0x3dec6abf6fe85ffbda42]),(bitLimbs [0xb2912573340219922d,0x2d5864eeb3801cfb9a02])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,1,58,0,5),(0,8,51,0,5),(0,16,2091,0,5),(0,32,2075,0,5),(16,0,43,0,5),(32,0,27,0,5),(0,2,2105,0,4),(0,48,11,0,4),(16,8,35,0,4),(32,1,26,0,4)]
def g59A : List (List Nat) := [[],[48,84]]
def g59D4 := limbs80 #[#[0x8f59642043e02108010,0x3]]
def g59D5 := limbs80 #[#[0xf721043e842087e08010,0xfca4085f14810df21021,0xf94a10df21421bd54042,0x138c090784802fca2105,0x30400012410a11c9b18,0x40820050450c21440c21]]
def g59H5 (j : Nat) := if j=0 then 0x60 else 0
def g59D6 := limbs80 #[#[0xfc20fe10fc10de30dc30,0x8a92628807b885522900,0x4a4188202527acc5100e,0x80b49aa520c41012935,0x941aa5a1062]]
def g59H6 := limbs80 #[#[0x2800000795922600,0x20e70000253370000000,0x14c0000000000050802,0x51b0b9145000]]
def g59D7 (j : Nat) := if j=0 then 0x2a19080df else 0
def g59H7 := limbs80 #[#[0x20000b900b10b00a0748,0x8a28732]]
def g59L : Nat → Packing
  | 4 => (2,3,4,0,0,3,0,g59D4)
  | 5 => (10,2,4,0,0,8,0,g59D5)
  | 6 => (5,1,4,0,0,8,0,g59D6)
  | 7 => (1,0,4,0,0,0,0,g59D7)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 5 1 0 g59H5
  | 6 => lookupWord 3 37 0 9 4 1 g59H6
  | 7 => lookupWord 2 17 2 8 3 1 g59H7
  | _ => fun _ => none
def g59 : Forest := ⟨59,7,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 2=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 10=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 10=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_2 : block g59 6 2 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 5=true := (@block_merge g59 6 0 2 3 g59P6_0 g59P6_2)
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
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
  · exact g59B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 8 := lower_forest (g:=g59) (i:=0) (hints:=316865909887498) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 8 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((bitLimbs [0xbfddd4fffffeff5fff,0xf252dffff9effff94eff]),(bitLimbs [0x11a00808002c0dbcb3,0x105001a000e56fe10cc9])),(0x0,0x0),((bitLimbs [0xdc3febbbdf6fbfb3ae,0x7dfdbdf73efbf177f5d6]),(bitLimbs [0x12901dedd3502106,0x6ce09c1776820115f056])),((bitLimbs [0x73f6bfefbbbb76eff7,0xffef7a79cf15ce9ebf6b]),(bitLimbs [0x84468a62ca0aa5244,0x65066278da14c29a3722])),((bitLimbs [0xe737fb4c4af1b9edfc,0xcdffa14dafd675eef92c]),(bitLimbs [0x24fdd291031ca289f8,0x802f23472d60186ec92c])),((bitLimbs [0x9ede37bcfd24d19037,0xb3b7d7ab7aac9e29db93]),(bitLimbs [0xab0991861143f4c864,0x9791b21f5c689c28db93])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(32,0,29,0,7)]
def g61A : List (List Nat) := [[],[50]]
def g61D7 (j : Nat) := if j=0 then 0x3f else 0
def g61L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g61D7)
  | _ => emptyPacking
def g61I (_ _ : Nat) : Option (Nat × Nat) := none
def g61 : Forest := ⟨61,7,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
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
  · exact (rfl : block g61 3 0 0 = true)
  · exact (rfl : block g61 4 0 0 = true)
  · exact (rfl : block g61 5 0 0 = true)
  · exact (rfl : block g61 6 0 0 = true)
  · exact g61B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 8 := lower_forest (g:=g61) (i:=0) (hints:=176266131275788) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 8 [(61,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g62Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xd3f77fbebfbefeff7f,0xe45b7fefefffbedad9ff]),(bitLimbs [0xb5c2300802400b3c16,0xe06031220ac0aa9851b1])),((bitLimbs [0xfedfbfe9f7ffbffff8,0x7bedebbf7ffff5a7e7fe]),(bitLimbs [0x2000b640d3b5041c8,0x19014a8dd41d4407a44e])),((bitLimbs [0xffaac477cef97583ff,0xffb6d4f3b88bcb7d7e2b]),(bitLimbs [0xca186189a4cacca6c,0x4ab294eae84341786e2a])),((bitLimbs [0x6e1ce57d6b4db3339d,0xdbf5a27134e157f5f704]),(bitLimbs [0x75e41ca4c026ad2791,0x80b4b63732f01cf5d304])),((bitLimbs [0x55b3d4d7cfaad3409f,0xa7d77fe5eb025adcbac3]),(bitLimbs [0xd8556ba588b1f1a059,0x2f45c445f3063ec4bac3])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g62C : List ColumnInfo := [(0,16,46,0,5)]
def g62A : List (List Nat) := [[],[33,84]]
def g62D5 (j : Nat) := if j=0 then 0x3f else 0
def g62L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g62D5)
  | _ => emptyPacking
def g62I (_ _ : Nat) : Option (Nat × Nat) := none
def g62 : Forest := ⟨62,5,fun i => g62Y[i]?.getD (0,0),g62C,g62A,g62L,g62I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62P5_0 : block g62 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g62B5 : block g62 5 0 1=true := g62P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62T : checkedTables g62 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g62 0 0 0 = true)
  · exact (rfl : block g62 1 0 0 = true)
  · exact (rfl : block g62 2 0 0 = true)
  · exact (rfl : block g62 3 0 0 = true)
  · exact (rfl : block g62 4 0 0 = true)
  · exact g62B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g62G : graphValid g62 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low62 : Lower true (varsX 62) (graphGoal 62) 6 := lower_forest (g:=g62) (i:=0) (hints:=352671039490048) (before_sound K61 V61) g62G g62T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K62 := extendKnown K61 6 [(62,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V62 : Known true K62 := extend_ok (m:=62) V61 low62 (by decide +kernel)
def g2079Y : Array (Bits × Bits) := #[((bitLimbs [0xe68e7ff7cfb62903ba,0x69f3a6bff65d9b9392b5]),(bitLimbs [0x430418088149340208,0x410808b9464580911095])),((bitLimbs [0x51f7ee7a33fddb7f70,0xf64df8d70dabe4e8717b]),(bitLimbs [0xf480308a160002030,0xa44908d8410300c80139])),((bitLimbs [0xfe685abf3773edd9af,0xdab37d504bffd1adcf44]),(bitLimbs [0x201084704c00c90986,0xa82600018a81520ce40])),((bitLimbs [0xe9d5f713f9ca76bec5,0xbdcca7acbf952e566e8b]),(bitLimbs [0x900264a20c80801402,0x1084e50490900e066602])),((bitLimbs [0xcf43885f9f84fcc25d,0x5fd795d32b88085f9c72]),(bitLimbs [0x6c26b0533220172641,0x58519422ab6a105f9862])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2079C : List ColumnInfo := [(0,16,4111,0,7)]
def g2079A : List (List Nat) := [[],[50],[16],[16,50],[32,49],[32,49,16],[48,33,16],[48,33]]
def g2079D7 (j : Nat) := if j=0 then 0x3f else 0
def g2079L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g2079D7)
  | _ => emptyPacking
def g2079I (_ _ : Nat) : Option (Nat × Nat) := none
def g2079 : Forest := ⟨2079,7,fun i => g2079Y[i]?.getD (0,0),g2079C,g2079A,g2079L,g2079I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079P7_0 : block g2079 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2079B7 : block g2079 7 0 1=true := g2079P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079T : checkedTables g2079 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2079 0 0 0 = true)
  · exact (rfl : block g2079 1 0 0 = true)
  · exact (rfl : block g2079 2 0 0 = true)
  · exact (rfl : block g2079 3 0 0 = true)
  · exact (rfl : block g2079 4 0 0 = true)
  · exact (rfl : block g2079 5 0 0 = true)
  · exact (rfl : block g2079 6 0 0 = true)
  · exact g2079B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2079G : graphValid g2079 (boundsBefore K62) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2079 : Lower true (varsX 2079) (graphGoal 2079) 8 := lower_forest (g:=g2079) (i:=0) (hints:=206292912132) (before_sound K62 V62) g2079G g2079T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2079 := extendKnown K62 8 [(2079,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2079 : Known true K2079 := extend_ok (m:=2079) V62 low2079 (by decide +kernel)
def g2095Y : Array (Bits × Bits) := #[((bitLimbs [0xfebb77f8a5ffb9ebfb,0x535ffccc793a0f03db17]),(bitLimbs [0x90c080240040402080,0x39c00302205011310])),((bitLimbs [0x3582e54bfcdbcc3fcf,0x78ba194faccdb69a96ea]),(bitLimbs [0x4153848d20490930f,0x3003448498221a844a])),((bitLimbs [0xeeff497fdbc94ff43d,0xbf86e7bb96e4e6752cf1]),(bitLimbs [0x612005800039000000,0x1d0060890040c06008a1])),((bitLimbs [0xd7f6bbe557ae374f73,0xecf1dbb05793d9ee614c]),(bitLimbs [0xc160013a586845075,0xe09002040710188e6044])),(0x0,0x0),((bitLimbs [0x2fa5f6ae6b8ec43412,0x58f6ec522fc372d9718b]),(bitLimbs [0xdb89d48736c9624692,0xddc7c81388a90ad1718b])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2095C : List ColumnInfo := [(0,32,4111,0,7)]
def g2095A : List (List Nat) := [[],[49],[32],[32,49]]
def g2095D7 (j : Nat) := if j=0 then 0x3f else 0
def g2095L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g2095D7)
  | _ => emptyPacking
def g2095I (_ _ : Nat) : Option (Nat × Nat) := none
def g2095 : Forest := ⟨2095,7,fun i => g2095Y[i]?.getD (0,0),g2095C,g2095A,g2095L,g2095I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095P7_0 : block g2095 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2095B7 : block g2095 7 0 1=true := g2095P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095T : checkedTables g2095 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2095 0 0 0 = true)
  · exact (rfl : block g2095 1 0 0 = true)
  · exact (rfl : block g2095 2 0 0 = true)
  · exact (rfl : block g2095 3 0 0 = true)
  · exact (rfl : block g2095 4 0 0 = true)
  · exact (rfl : block g2095 5 0 0 = true)
  · exact (rfl : block g2095 6 0 0 = true)
  · exact g2095B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2095G : graphValid g2095 (boundsBefore K2079) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2095 : Lower true (varsX 2095) (graphGoal 2095) 8 := lower_forest (g:=g2095) (i:=0) (hints:=351843855368706) (before_sound K2079 V2079) g2095G g2095T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2095 := extendKnown K2079 8 [(2095,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2095 : Known true K2095 := extend_ok (m:=2095) V2079 low2095 (by decide +kernel)
def g2103Y : Array (Bits × Bits) := #[((bitLimbs [0xdd7bcdbd3f7e19f354,0xc992bff5f8887e23ad29]),(bitLimbs [0x201040020010400100,0x40000284000012002c20])),((bitLimbs [0xbadd6adf55edb60b99,0x55adc44a67faf6954a5e]),(bitLimbs [0x5c900908208005c07,0x1185040040222411404a])),((bitLimbs [0xcbddd3eaedf2f19cab,0xe6fb718f203769da52b1]),(bitLimbs [0x8068c080944260040,0x8386001220149ca0211])),(0x0,0x0),((bitLimbs [0x4a47d724df997d7f26,0xa6ef2ee3896d076d7182]),(bitLimbs [0x40a92274d40210501f,0x96c204625d2800255182])),((bitLimbs [0x66b72bd19d798ecb70,0xbb0c7e7e17e2d92e9646]),(bitLimbs [0x1202996c6520242290,0xa858384a1ec140ae9204])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2103C : List ColumnInfo := [(2,0,53,0,5),(4,0,51,0,5),(16,0,39,0,5),(32,0,4119,0,5)]
def g2103A : List (List Nat) := [[],[33,84]]
def g2103D6 (j : Nat) := if j=0 then 0x7209f else 0
def g2103L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g2103D6)
  | _ => emptyPacking
def g2103I (_ _ : Nat) : Option (Nat × Nat) := none
def g2103 : Forest := ⟨2103,6,fun i => g2103Y[i]?.getD (0,0),g2103C,g2103A,g2103L,g2103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103P6_0 : block g2103 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2103B6 : block g2103 6 0 1=true := g2103P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103T : checkedTables g2103 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2103 0 0 0 = true)
  · exact (rfl : block g2103 1 0 0 = true)
  · exact (rfl : block g2103 2 0 0 = true)
  · exact (rfl : block g2103 3 0 0 = true)
  · exact (rfl : block g2103 4 0 0 = true)
  · exact (rfl : block g2103 5 0 0 = true)
  · exact g2103B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2103G : graphValid g2103 (boundsBefore K2095) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2103 : Lower true (varsX 2103) (graphGoal 2103) 7 := lower_forest (g:=g2103) (i:=0) (hints:=35253091828226) (before_sound K2095 V2095) g2103G g2103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2103 := extendKnown K2095 7 [(2103,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2103 : Known true K2103 := extend_ok (m:=2103) V2095 low2103 (by decide +kernel)
def g2107Y : Array (Bits × Bits) := #[((bitLimbs [0x57dc76cd31f44e7f86,0xbfdc8bb93e5144ec592b]),(bitLimbs [0x2803082200400000c2,0x1000901110040800123])),((bitLimbs [0xfa36e7f2eedb9d4fff,0x5a332576b98d7b11a780]),0x0),(0x0,0x0),((bitLimbs [0xe6f39d49cbc530f56f,0xb18178096ef2eb7b50f4]),(bitLimbs [0x1083044d1aa880500,0x480900486ae4032150c4])),((bitLimbs [0xfd49d9a9d976f3cf98,0x11c47623d2a39dea8a5d]),(bitLimbs [0x2a403910c10005021,0x96c274a080090c4a8a18])),((bitLimbs [0x88fb52ce9e022716ae,0x7d8abffc0ca236ac6ad2]),(bitLimbs [0x1504a319719b40b63c,0x186b62f0ccc2302c6ad0])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2107C : List ColumnInfo := [(2,0,57,0,5)]
def g2107A : List (List Nat) := [[],[67]]
def g2107D5 (j : Nat) := if j=0 then 0x3f else 0
def g2107L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g2107D5)
  | _ => emptyPacking
def g2107I (_ _ : Nat) : Option (Nat × Nat) := none
def g2107 : Forest := ⟨2107,5,fun i => g2107Y[i]?.getD (0,0),g2107C,g2107A,g2107L,g2107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107P5_0 : block g2107 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2107B5 : block g2107 5 0 1=true := g2107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107T : checkedTables g2107 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2107 0 0 0 = true)
  · exact (rfl : block g2107 1 0 0 = true)
  · exact (rfl : block g2107 2 0 0 = true)
  · exact (rfl : block g2107 3 0 0 = true)
  · exact (rfl : block g2107 4 0 0 = true)
  · exact g2107B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2107G : graphValid g2107 (boundsBefore K2103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2107 : Lower true (varsX 2107) (graphGoal 2107) 6 := lower_forest (g:=g2107) (i:=0) (hints:=35253225783304) (before_sound K2103 V2103) g2107G g2107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2107 := extendKnown K2103 6 [(2107,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2107 : Known true K2107 := extend_ok (m:=2107) V2103 low2107 (by decide +kernel)
def g2109Y : Array (Bits × Bits) := #[((bitLimbs [0x94675f72f4efe8e22b,0x54b1aa3fd61b23baaa87]),(bitLimbs [0x60cc0201c142010450,0x50c04825a01201982a82])),(0x0,0x0),((bitLimbs [0xffdecdbf98db7f99de,0xfe9e598378f47c8516a8]),0x0),((bitLimbs [0x5850efc977f6826fcb,0xe377b4659f18ca554957]),(bitLimbs [0x601050c10b8108224,0x21512401228d2050145])),((bitLimbs [0x6865f75ce90b5f2a33,0x94363fdc8aab256ee521]),(bitLimbs [0x971344a026b8da3802,0x63f261809aca406c521])),((bitLimbs [0x9881b4bbd3369c3e9f,0x69ec4cec4d99e342637a]),(bitLimbs [0x312c82b12942e2411b,0x206848944d5324d2623a])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2109C : List ColumnInfo := []
def g2109A : List (List Nat) := [[],[48,84]]
def g2109D4 (j : Nat) := if j=0 then 0x1f else 0
def g2109L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g2109D4)
  | _ => emptyPacking
def g2109I (_ _ : Nat) : Option (Nat × Nat) := none
def g2109 : Forest := ⟨2109,4,fun i => g2109Y[i]?.getD (0,0),g2109C,g2109A,g2109L,g2109I⟩
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
theorem g2109T : checkedTables g2109 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2109 0 0 0 = true)
  · exact (rfl : block g2109 1 0 0 = true)
  · exact (rfl : block g2109 2 0 0 = true)
  · exact (rfl : block g2109 3 0 0 = true)
  · exact g2109B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2109G : graphValid g2109 (boundsBefore K2107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2109 : Lower true (varsX 2109) (graphGoal 2109) 5 := lower_forest (g:=g2109) (i:=0) (hints:=281543830405128) (before_sound K2107 V2107) g2109G g2109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2109 := extendKnown K2107 5 [(2109,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2109 : Known true K2109 := extend_ok (m:=2109) V2107 low2109 (by decide +kernel)
def g2110Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xa696457375f9fd2837,0xd2ac4d95db74ee9b720a]),(bitLimbs [0x496c00242342210108,0x109811109050a6037008])),((bitLimbs [0xfdbdff1d7f0925d65f,0x7eebb3a92c35b84198b7]),(bitLimbs [0x2000010081c022000,0x40210201000410000017])),((bitLimbs [0x77445fbeaa6efa7bf5,0xbb74a652f79a33ac4d58]),(bitLimbs [0x800285000000040e00,0x2008440210000280c00])),((bitLimbs [0x58e7d3f399f263ca0b,0xe045cf6f946bcdf6a384]),(bitLimbs [0x2090780840205040a3,0x46400e04a308948380])),((bitLimbs [0xb28836c85f4ef08fcd,0xdd975172af955d1704e9]),(bitLimbs [0x2d010228f2a339500f,0x881e112c8ed24b1700e8])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2110C : List ColumnInfo := [(32,0,2078,0,7)]
def g2110A : List (List Nat) := [[],[50],[65],[65,50]]
def g2110D7 (j : Nat) := if j=0 then 0x3f else 0
def g2110L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g2110D7)
  | _ => emptyPacking
def g2110I (_ _ : Nat) : Option (Nat × Nat) := none
def g2110 : Forest := ⟨2110,7,fun i => g2110Y[i]?.getD (0,0),g2110C,g2110A,g2110L,g2110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110P7_0 : block g2110 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g2110B7 : block g2110 7 0 1=true := g2110P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110T : checkedTables g2110 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g2110 0 0 0 = true)
  · exact (rfl : block g2110 1 0 0 = true)
  · exact (rfl : block g2110 2 0 0 = true)
  · exact (rfl : block g2110 3 0 0 = true)
  · exact (rfl : block g2110 4 0 0 = true)
  · exact (rfl : block g2110 5 0 0 = true)
  · exact (rfl : block g2110 6 0 0 = true)
  · exact g2110B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g2110G : graphValid g2110 (boundsBefore K2109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2110 : Lower true (varsX 2110) (graphGoal 2110) 8 := lower_forest (g:=g2110) (i:=0) (hints:=140875196270592) (before_sound K2109 V2109) g2110G g2110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2110 := extendKnown K2109 8 [(2110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2110 : Known true K2110 := extend_ok (m:=2110) V2109 low2110 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((bitLimbs [0x5d373b73aed7feb55,0x7ff7eefbe4fc068ff368]),(bitLimbs [0x110502091ca02c144,0x9b2ae3064d0048f7360])),((bitLimbs [0xff7ccfc6f7daf217ba,0xca82829c5d86d176cb97]),(bitLimbs [0xa45046c4a083f2109c,0x40028a880d04c126c296])),((bitLimbs [0xff6ff8f88974577f67,0x2fbc1762632b7df52c3b]),(bitLimbs [0x5b2b80380924040e22,0x16200062402b3c500c29])),((bitLimbs [0x10fea72f742f8b9c99,0xbb4bfd9fbf53bf0854cc]),(bitLimbs [0x10cfa3435021890001,0xbb48259fbb123b001088])),((bitLimbs [0x35b63b5902913cc07b,0xc5adf1c09addabaaaf31]),(bitLimbs [0x64a42d410a1190c03b,0xc49d51c09acd83a8ad11])),((bitLimbs [0x6805c52fdc52fe6aed,0xf676ff25186fa2317bce]),(bitLimbs [0xc28d050e8cf27eaa47,0x321cdb05106fa2316b4e])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,1,2110,0,8),(0,16,2095,0,8),(0,32,2079,0,8),(2,0,61,0,8),(4,0,59,0,8),(16,0,47,0,8),(32,0,31,0,8),(0,8,2103,0,7),(0,48,4111,0,7),(8,0,55,0,7),(32,1,2078,0,7),(34,0,29,0,7),(0,4,2107,0,6),(1,0,62,0,6),(0,2,2109,0,5),(1,16,46,0,5),(1,32,30,0,5),(2,1,60,0,5),(2,4,57,0,5),(2,8,53,0,5),(2,32,2077,0,5),(4,1,58,0,5),(4,8,51,0,5),(4,16,2091,0,5),(4,32,2075,0,5),(8,1,2102,0,5),(8,32,2071,0,5),(16,1,2094,0,5),(16,8,39,0,5),(18,0,45,0,5),(20,0,43,0,5),(32,4,4123,0,5),(32,8,4119,0,5),(32,16,2063,0,5),(36,0,27,0,5),(40,0,23,0,5),(48,0,15,0,5),(1,8,54,0,4),(1,48,14,0,4),(2,16,13,0,4),(2,48,13,0,4),(4,2,2105,0,4),(4,48,11,0,4),(8,16,7,0,4),(8,48,7,0,4),(18,1,44,0,4),(20,8,35,0,4),(34,1,28,0,4),(34,4,25,0,4),(34,8,21,0,4),(34,16,13,0,4),(36,1,26,0,4),(40,1,22,0,4),(40,16,7,0,4),(48,1,14,0,4),(48,8,7,0,4)]
def g63A : List (List Nat) := [[]]
def g63D5 := limbs80 #[#[0x5853108184211760c810,0x81845cc735842065083,0x5892110030e61731cd61,0x48430241741d1210c173,0x615701c1610c98421376,0x1d932443985c07058432,0x443916087050d1061084,0x50d7110d21608821d943,0x18121650735806048490,0x65c8358060485951cd60,0x58060484835cd6018121,0x487955cd6018121e5173,0xe1d6018121a4f8758060,0x18d2165c8058c6348793,0xe438758c6348690e1d63,0x5c0634849058d7018d21,0x4878558d7018d21e1163,0x20c7648540600801d943,0x48550604811d93250183,0x608821d9315418320c76,0xee0de0bc85e053258640,0xe87a87685e4b60fa0f60,0x7b05ea9aa5a8ce8ba89,0x349747329b25b0bb09f,0x45d4974194a0752483a9,0x654090e9038730156970,0xd4ba1ea5c07523458615,0x39a2ea5f0f52f1ea7807,0xa32e5509f2883f873a3c,0x6ce94f6f487bf874a3c3,0x869545348a21a54d4d22,0xe1589f08c13a96cb5318],#[0x9556f48abb976a1cbb32,0x574b48b99a5592d22cce,0x2008003fa521fcc0e669,0x60a048200e0602810060,0x2612088401e0e068301,0x870361a0c8602e160a85,0x128904622108803e1e0e,0xa04e26]]
def g63D6 := limbs80 #[#[0xa0d710801020d7108010,0x589710c010209710c010,0xa09710c010609710c010,0x211760c810e09710c010,0xe11760c810a11760c810,0xc971100105d43210010,0xdd3735881061f3210010,0xe1d628c810211628c810,0x20d614c4200c97190010,0x20d6154420d0d6150420,0x5cc7358420dd04358420,0x20d54584205d07458420,0xdd773584202117358420,0xa0d619442060d6194420,0x58921100305852110030,0x5c921100305c52110030,0x5d521100305cd2110030,0x61d21100306192110030,0xe1d2110030e192110030,0xe056210030e096110030,0x58470484301d07048430,0x5d870484305887048430,0x9d0704843060c7048430,0x1d07348430dd87048430,0x5d074484309d07348430,0xe053248430e093148430,0x2015448430e153248430,0x2116148430e0d5448430,0x50d61484304c96148430,0x59161484305896148430,0xdcd6148430d0d6148430,0x50d6248430e096148430],#[0xd0d62484305916248430,0x2117348430e056248430,0xe157348430e117348430,0x2117648430dd97448430,0xe1176484302157648430,0x98a6148430e157648430,0xdda6248430dda6148430,0x61674484301ce7048430,0x60b4148430dd27448430,0x60742484306174148430,0x1cf70484306174348430,0x5cf70484305877048430,0x5db70484305d37048430,0xdd37048430dcf7048430,0x5937348430ddb7048430,0xdd373484305db7348430,0x2137648430ddb7348430,0xdd9214c030a137648430,0xe0b764c030e07764c030,0x5d074584305c87258430,0x60742584302117258430,0x5c47158830d0f7258430,0x5896188430d0f7158830,0x209619043061d6288430,0x60961904305c96190430,0xe1d6190430a096190430,0x60961944305c96194430,0x5ca6298430a096194430,0x5c962d04306066298430,0x5c07058432203764c832,0x5d074584329d07058432,0xdd170584322015458432],#[0x9cd6348440dd37058432,0xa0f764844060b3148440,0xe1d32cc4406043250440,0x2037650c436087050c43,0x50d72584432014358443,0x211710c910201710c910,0xdcc704851018c7048510,0x50f62485102014348510,0x219324c51090f6248510,0xdd4744c910604744c910,0x604764c910210764c910,0xa10764c910610764c910,0x6087050d104c87050510,0x2087650d10a087050d10,0xa087650d106087650d10,0x9d843881106044388110,0x21973c8510219738c910,0x5d532d051021932cc510,0x18c70485204ca70d0510,0x21943d052050f6148520,0x50d7110d212014310d21,0xa027610d21d917110d21,0x5cc73181215cc6318121,0x60c74181215d07418121,0x9cd43181212013118121,0x201541812121d5318121,0x1cd601812121d5418121,0x50d601812120d6018121,0x5d160181215cd6018121,0x9cd601812190d6018121,0xdd16018121dcd6018121,0x60c6418d21e1d6018121],#[0x5d16318d212016318d21,0x58d7018d21e1d6318d21,0xe117018d219d97018d21,0x58e7018d21e157018d21,0xe1d641912120d6419121,0xa037350921dc8704c521,0xa047050d216047050d21,0xa007650d212007650d21,0x20173951211cd4358121,0x19243981212194398121,0x6036398d2150f6098121,0x20143d0521a036398d21,0x20173d092120173d0521,0x20131d8121a1863d8121,0x21943d8121d8d31d8121,0xa1a43d8121e0d64d8121,0xa0363d81219cf63d8121,0xa0364d812160f64d8121,0x5c4611813260670d8d21,0x195711813210d7118132,0x20c76485405cc7348540,0xe093148540a0c7648540,0xe05324854018d3248540,0x1da73485402017348540,0x60b3148540dce7348540,0x1d8714c94018c714c940,0x604764c940204764c940,0x18d7288540a04764c940,0xe1d32cc54021932cc540,0x211710c941201710c941,0x1d4704c94161c3218141,0x9ca7118143604704c941],#[0xa0c764855020c7648550,0x608764c550208764c550,0x1db324c550a08764c550,0x20d7118152a1f324c550,0xe1d6218a10e1d320ca10,0x2014348610e1d6318e10,0x10f714ca10dd4744ca10,0x59064cca101d3714ca10,0x10d6148620e1d310c620,0xd0d614862050d6148620,0x604435862050c4358620,0x20d5448630a0f7058a21,0xdda70486301ce7048630,0x5cc734864010d7198232,0x2017348640e053248640,0x10f714ca401d27348640,0x1d532586401d3714ca40,0xe0532586402153258640,0x601710ca4110d718ca40,0x211710cb10a01710ca41,0xa11710cb10611710cb10,0x6047050f20e19710cb10,0x20143587206187050f20,0x71de37c3f87d0ee1bc2f,0x7e5f4b795f27e3f47d8f,0xabd3ea7b4ee9bd2fa5b4,0xd7caed5bab6d67abd576,0x6b6b6ced75adb3d676cd,0x7d8f71de37c5f87edcdb,0x9e73b66dccf9772de4fc,0x75b6aed5ba9f4ee9bd2f,0x9f2be4fc7b8ef1bd79ae],#[0x5ce79ceb9cf36e6bcd39,0xcc0580f3015f71ec7d2f,0x7306705cc19a10e62901,0x1cc1f41f307b1e4b2a40,0x9b2c017ab2805eaca000,0x64c100a2f04038a4100c,0x49f2c047ab2811eaca02,0xb7ab28189b2c057ab281,0x40272c0c4cc30289b2c0,0x74ec201ca5200726cb0,0x8213f08081cca81d330a,0xa0e4549838732a094cc2,0xb2788d260d78ca83ceb2,0x2c8d89b9a306b309f773,0x4ba40912e8f88c1a30a5,0xf2a914dcaa844d2e8e25,0x84b290a12c9867caa899,0x3d2c8a90caa29310ca32,0x543b24976ea92274b22e,0x9b22941dcaa55350c93,0x627c8a59370a944ec225,0x5d370a974fc225c772a9,0x9939c8a65372aa01ccaa,0xa714b049b7c32a69f0ca,0xb08134bc2d4f049d27c8,0xb4349b2d0e53cb4216f2,0x270917cc43d330d0c26c,0xc249ce5212751c94294d,0xb2d292ccaca49f2d2860,0x74b8464b28117acaca89,0x9f2e1a414a04d0530128,0x7ec20545b301426cb86c],#[0xc8d26194fba8608f3015,0x628cc2962306a5094b85,0x489d2f114fcba9c992ea,0x1555cb440f32b13264bc,0xcb5db232d17cc451ba87,0x6329c8cb15b0d2b56cb,0x91915f046457cc18d593,0xe61c8ab9070a3226528c,0xb1079570e1c7aba8721a,0x2ea1d82b9875570c1e8a,0xc30814f0c1f53c3875e,0x370c214cc30843130205,0x9cb890232e2409cb889,0x942e62608cb094272c23,0x94cba89d42e6274cba89,0xa65ac42951bb0b218e62,0x288dbb0aa38e8298fbb0,0xb8d1282b12cc0b4a32c,0x4560ccc1398d004e56c3,0xa15cdd2e558fba15a5ac,0x305729cb15cbf2a5735c,0xcb1698b0c5a28cb1684f,0x32c5b37c9960db2c5a88,0x6c3170bf2a5935ca164a,0x36ec5253bb1454eec325,0x264b8ee56e63a53bb0f9,0x4f32a3c264b8e4f72a38,0xb274b8de1eea3d87ba0f,0xcd550e4c4b4b92dd50e4,0x4255bb14d36ec3455bb0,0x904912e3f244b90156ec,0xc544cbb1514d0e4d3aca],#[0xc0c0dd203022cb0bd36e,0xec454fbb1113eec430cc,0xca978c7285e22cb17d36,0xeec3550c3175430c602b,0x4480c546ec36134b8d55,0x2530460bcc0c53b0c313,0x4fbb11d36ec4f20cb140,0x1670a474dbb1293eec49,0x226c89893b08614dc312,0xb4732a624fc218893246,0x708a411c0272c6e8ab91,0x1bc9d3070264c1c22f04,0x47326cb9c89f2e7174c1,0x11d229047480b21e49b2,0xc86926cb9d89f2e758bc,0xba9a03f306625cb199ba,0xf307755cb9e0732a6a4f,0xcca9b047306b27cb1ad4,0x352f1708cc4643331181,0x5043a054eec8268b2a08,0x5f2c8418cb214932483,0xd523b3c548eceb6fcb21,0xa0d920e8234bbb150ece,0xf0563b3b83730e8224b3,0xba94306e908cc3bd450c,0xcf951c3be02530f751c1,0xbd09b22f346c8bc88d2,0xed1c55c0bd89724f554c,0xbb47437311b364846d56,0x531216a42c8c2b311e57,0x2c8c7ccb23201d4bc885,0x4307000acc490cb23243],#[0x194b419450f0551c1c05,0xd4f050427c8c0d4b0502,0xa1a4c2dd5f0eb77241ad,0xd4fb2ab542ca2d55f0eb,0xb87241ae06d30b557c3a,0x2e15f0eb83fcaae10f28,0xebc7241af15f0ebb1a4c,0xa2d9cae8b61b4c2f15f0,0xeb972cbad9cb28b673b,0x49af86d30bd57c3af55f,0xf26be5749af95b26be56,0x231ac15f28be56ca2f95,0x8f30ac094b2c9410cb17,0x70322cc3730ad5ec22b4,0x93d0cae5eba2bc252cb4,0x229cbb51410cd00bcc2b,0x71cec6db20cbb4c232ed,0xda1b4837c6d20dd51c3b,0x3788b30e056cbb846d20,0xcca1a483895b2ee31b48,0xb32c252cd8174b35d4d0,0x2ca932482a4252cd9094,0xc8aac5d2ca833482a8c9,0xb00ce65413359304cc26,0xdc230d2120c357c033d5,0x6130c323cbb0d9f0ac36,0x294831134ecc64f3b314,0x6130c723cbb1d2120c7,0x72ca301cae8c056cbb0,0x5cf2ec072cbb01cf28c,0xc250483086520c251c3b,0x3094720c251483094320],#[0xebf18482fd4728c250ca,0x1391430ed650c3b54672,0x20c91748320252cd164c,0x49b253926c94f4832539,0xd2cfa4e4a3f146e7164f,0x43b3f970eafe33483ec9,0x9b2d2627cb495350cfd5,0x8cc1f0a7307b7cc29ec,0x4252e7e294820025307f,0x77bcab9493227a20481f,0x682530e61d4c39c5530e,0x88164c224852907094c4,0xa1d3f028721cb219bb22,0x52c13fc9b22ff20c8,0x815c07a035013006801a,0xe0af04c8244112072032,0x7849c23e11107482fc16,0xec16e0b0056028013709,0xe286e43621a90ce85f82,0x4001f40f607903b81cd0,0x11988ac44621b1080820,0x8514272135095449a23e,0xe1610ae85622a214d0a4,0xa86443161870be45d82c,0x7f1bb8d606a034519c8c,0xf2476839f1cb8e3c70e3,0x4091fc8fa47c23d91e88,0x913c88e4382141080822,0xc48623f11d88ce45f22b,0x792fc96e4af253925891,0x1e4ff27b93bc9be4d726,0xad954ca9654329d94b8a],#[0xb665ab2d1964cad65632,0x2fd97c8bd45e22e396fc,0xccb464b31998acc3c603,0x33659b0cd766af3499a0,0x50e1870437e1bccdd66e,0x523a31cf8e6c72e3931c,0xedcf5e78f3c39dacebe7,0x7eb3ef9f5cf9e7c73df9,0xa07d02e80f4039ffcfe6,0xc857427a0fd06e82f413,0xda2cd15689c44a22110e,0xd68e346da34d1968c345,0x9aa4b522e90a47e23d11,0x3349924c2a5bd2ce95f4,0x4e527093749b24d52689,0x14149fc4f827a13c09d2,0x53c29c14d0a5151b288,0xe1552aa154c2a41510a8,0x145862c115ecaee566aa,0xd29678b345962c91638b,0xb885c02dc96d4b625ad2,0x2ee1760ba85d02e61720,0x6bfe5f42f817a8bc85e0,0x8b125882c39615307581,0x10c80638b1a58c2c5962,0x5f32d995cca664c32419,0xa0acfd67ab37999ccc66,0x69e34b5a4ad1d68ab435,0xdb5ad9f6cbb601ac6d4c,0xb6f1b76dba6dcb6e1b6e,0x99c30e10701b7edbe6de,0x7e73b39b9cbce5171a38],#[0xb0dd6ceae7533a79d22e,0xefb779bbaddb6ed3765b,0x3d01e70f2878c3c41e10,0x8f847be3dd1ed8f647a4,0x5bf0df76fb37d5be8df1,0x8ffc7fa3fb1fbefd37e,0x1c40c205101c80a40320,0xd106082c41420910408,0x86542b614b09d8464212,0xe20d0fe87b438a1b50d2,0x58a6c51627b135896c47,0xc233b1958c6c6162bb15,0x8ef475a39d1c08dc46,0x94a48523a911c86e4272,0x29e9454a0a4f52729334,0x4bde5d12d99614aea54d,0x3335996cc9663b315983,0xece1a6e33699b0cd5669,0xeb3e49ee4f527793b49c,0x2c514289142ba0a4ff67,0x1c0700d00c0b401005a,0x82000f4020b806009000,0x450089211409982e0812,0xc928262400c0904a090c,0x4311241883194e2c238,0x8600c0b81b0620008485,0x100428910e06f20803c0,0xa382938070860383d176,0x4cc89506c010a116520,0xab02e1603c0d88351345,0x8ab0960b867058012488,0xc0143a00913210e1ac65],#[0x10300c0701221944287,0x14208810d40848e06a0,0x830964086150130b62a0,0x280610c1b80083a0c092,0x125a038468cd15a1341,0x2a83a4059130ce300a61,0x1b21eb0cd0602b05c0bc,0x44eb0fb0215edb18061a,0x8900000df43180000dd4,0xb0cff8836a23cfe604da,0xd84026b0110020000001,0x28117002f6400000,0x3504000003cd080281,0x1007da1a42000000c040,0x810000009ac0440086ec,0x4586d86c0845020000a3,0xa811b810050200c55c1,0xdc33d90029,0x6b0e0b1c3040,0x4ee84025c0802e212e21,0xb702000000014e0,0x87420000003342000,0x726e108a742000097420,0x18cc0000000000003410,0x600642000117420015fe,0x76170600010000470d10,0x66e703df40c6003415,0xa824f88507308415fd25,0x20000bf24880001,0x41b21000000004ed8800,0xc7551080018ed4c9282b,0x82012820000000000000],#[0x8400000000000000012,0x34e86d8167a72108013,0x16e04,0x30009e144341b6040002,0xd1a544000001ffc4003,0x8100000000000000005a,0x90f2caa2a606c8400025,0xe0517b378835f4,0x3820a2d0800040000000,0x2d810004be64420,0x91c14d8400000000,0x136100,0x3418b9a8803507504000,0x63811a08f084,0xb088000003dc0800000,0x1cca299c1000000000,0x87060d08000000000000,0x31e8810fc506770a8a,0x5b096c20,0x93181c60402ac2000000,0xc430000dc42ab0a43b51,0x1561000000ab089,0xb71080002ac20001b884,0x5fc7a0c0003710,0x972a880000,0x1683a8200,0xc0000000000000002504,0x44180006f10802eca928,0x3000087482000000063f,0x6b035a696,0x4b1000000000001bfc28,0xf3412840000d6040001b],#[0xc1007ba5440000da58a5,0x6a8200000032187282e9,0x69c081b7a200e6a8200e,0x100000000438147032e0,0x20754100006a0a812bec,0x3e88000f3d119d9a,0xe756896eed10004f0400,0x35f6ed06]]
def g63H6 := limbs80 #[#[0xb2c00f94224041218703,0x74d9a91549003d7,0x11df5207f0d9be99dc,0x609c6035c4b548e00081,0x96000e780000351a8cc0,0xa65271900054a1f,0x5800d40a000000c3f0a,0xba28853321,0x18800]]
def g63D7 := limbs80 #[#[0xc0105c4200416208010,0x41750c8105c43004162,0xc840042650c8105d832,0x100105c4400416210010,0x417510810cc84004175,0xdd532042654c81099442,0x5881010d620407350810,0x4074588101cd6204070,0xd0d62042435881050d62,0x88010dd1620437358810,0x41628c81058a3004273,0x58a4204171900100ca40,0xd0c105d7430413298010,0x81710c0205843008265,0x1c13108161100205d831,0x504201cd41081614c420,0x816154420dc54308161,0x1c16108043584201cd54,0x584201d1610807358420,0x81545842054d6108143,0x5d56108174584205cd61,0x58420951610825358420,0x8274584209cd6108270,0xdd1610837358420d0d61,0x8c420586300837558420,0x81639002010e4008161,0xcc64008273900205c640,0xcc420586510816190420,0x847050c215874108174,0x1d2600847058c21d0d60,0x980215d2600857398021,0x857498c215c26308743],#[0x98f4308575d0c219d263,0x8430590210c265d0c21,0xc121100305d8210c173,0x5c4400c1621003058440,0x108305d8410c16210430,0xc073484301c1210c176,0x4c5210c076484301d121,0x48430505210c13248430,0xc1524843050d210c142,0x585210c1544843054d21,0x48430591210c16248430,0xc174484305cd210c165,0x951210c176484305d521,0x48430989210c26148430,0xc274484309c1210c264,0xd0d210c34248430d0521,0x48430dcd210c37048430,0xc37648430dd5210c374,0xdd9320c3764c03048530,0x55030dc5540c16150430,0xc07058430109610c372,0x4c9610c074584301c961,0x5843050d610c14258430,0xc16258430551610c152,0x8c9610c1725843059161,0x58430949610c24258430,0xc274584309c9610c262,0xdc9610c34358430d0961,0x58830dd5610c37458430,0xc143588301d1620c071,0x9c5620c1715883059162,0x59030dc5620c34358830],#[0xc14288430dc9640c371,0x592210c1628843058621,0x8c0305da210c17288430,0xc1628c030586300c121,0x10a400c1768c8305da31,0x90030586400c12190030,0xc321900305c6400c162,0x58a420c16190430d0640,0x98030586510c17190830,0xc262984305ca610c121,0x587210c154c84305c662,0xc8430593210c162c8430,0xc162d0430587410c165,0x5db410c172d043059341,0xd0830593420c162d0830,0xc576d0c305db420c171,0x991320c4704c831dd931,0x5883150d620c47050831,0xca708c831dd1620c743,0xdc5540c87055032dd932,0x584321d1610c87058432,0xc97058432551610c943,0x9c1610c975584325d161,0x58432d0d610ca7458432,0xcb7558432dd1610cb70,0x5cc21101650844099743,0xc4409cc211027008440,0x101650c8409083110172,0x1c121102650c8405c432,0x48440505211007348440,0x102434844058d2110161,0x9cd21102704844098d21],#[0x48440dd1211033148440,0x100704c8405053110376,0xdc532102654c84059532,0x504404c9411003250440,0x10332504408c94110163,0x5c96110132584400c961,0x584408c9611017358440,0x10172884405862110272,0x5c642101718c84059631,0xcc4405073110132cc440,0x10332cc44090b3110172,0x1c13210576cc84058f32,0x58c425cd611093298041,0x10f7650c431c14310c70,0x9c96110d725844350d61,0xc91010d621447058843,0x441750c9105c43244065,0x5cc42440651091018c42,0x485105c4434417510910,0x44073485101c12144063,0x50d2144141485104c521,0x4851090d214417348510,0x4437348510d8d2144362,0x4c931440704c510dd121,0x4c51050931441414c510,0x440654c910dc93144332,0xdc532440764c9101d132,0x50510dd532443744c910,0x4407050d104c94144070,0xd062044043881101d943,0x8c9105c6324434388110,0x44173c851050f2144173],#[0x5cb3144132cc510d8b21,0xd05104cb4144171cc910,0x44173d05105cb4144143,0xccb4144270d05105d741,0xd091018f4244362d0510,0x44175d0d101974344173,0x1903148343d891010f62,0xc5209d031481740c520,0x481731052018c4148364,0x50d21480704852018d21,0x4c520dcd214836148520,0x480704c9201913248076,0x5ce2148063885201d943,0x8c5205ce31480648c520,0x48143d052018f4148270,0x1cf6148173d09205cf41,0x10d2150c4348543d8520,0x4867610d219c04348571,0x18c604844318121d9043,0x181211cc604846418121,0x48543181214c46048474,0x58060485541812154c60,0x181215cc604856318121,0x486541812194c6048643,0x9cc60486641812198c60,0x18121cc4604867418121,0x4874218121d046048732,0xd90604876318121d0c60,0x18d21550634846418d21,0x4866418d215c06348563,0xd8c634867418d219c063,0x19121590644876418d21],#[0x485414c5211c13148573,0x1c132487704c521d9131,0x50521d0d414846350521,0x48773509211cd4248773,0x1d9434847050d2118d43,0x54d211c1534866350d21,0x48473551211c15448476,0x1cd6048773551211d954,0x5812190d604854358121,0x4877358121d916048763,0xdc1634876458d211c163,0x59521dcd644847359121,0x4846490d21dcd6548473,0xd0e434867690d219c243,0x951219da534867094d21,0x48443981219da5448573,0x50e60484649812118e60,0x981219ce604864398121,0x4846498d21d826048743,0x5ce644876398d219c263,0xcc5219c33148463cc521,0x48543d052118f4148763,0xd934148670d05215cf41,0xd0d219c34248573d0921,0x48676d0d2198f4348463,0x50f6048531d812118f60,0xd81215936048563d8121,0x48763d8121cc76048643,0x9c36348554d8d21d9360,0xd91215cf6448764d8d21,0x4c064085309cf6448670,0x9cc214c270085305d021],#[0xc530d90214c27408530,0x4c2740c5305c8314c064,0x194324c0640c930d9031,0x10930194424c1710c930,0x4c076485301cd214c175,0xdd1214c273485305d121,0xd05305ca214c07650930,0x4c072d85300cb614c175,0x188604c4421813190b61,0x18131548604c46418131,0x4c732181319c8604c572,0x1c1414c67018931d8860,0x1813210c604c87054931,0x4c97118132190604c861,0x9d0614cb61181325d060,0x551329c0644c97119132,0x4ca70951329da434c876,0x10f614cb61d81325c760,0xd85321d3614c864d8532,0x50374d8532dc3614ca54,0x9c021501730854018c21,0x485405c432501720c540,0x50076485401cd2150063,0x5cd2150132485404c521,0x48540cc5215027348540,0x5036348540d852150332,0x4c931500764c540dcd21,0x4c94018d32503324c540,0x503714c9401d93250071,0x5ca21501328854018e21,0x8c540cca215017388540,0x501738c9405ce3150172],#[0xcc72150173c854018f21,0xcc5404cb3150361c8540,0x50072d85400cb6150172,0x8cb6150132d85401cf61,0x181415c43250772d8540,0x50572181414c86050432,0x9c86050632181415cc60,0x4c9411c1325073218141,0x5097118d425c46050875,0x5c86050d71181439c363,0xd85439c86050e7118143,0x54270d89431cb6150c70,0x1cd2154063485505c432,0x485505cd215407648550,0x540724c550dcd2154363,0xcc931541324c5501d931,0x4c950dc931543624c550,0x541738c9505c63254076,0x5cb3154132cc5505cf21,0xd85501cb6154032d8550,0x54232d85504cb6154073,0x5cc605497118152ccb61,0x181535c46054d7118d52,0x55171181549c86054d72,0x5c46355272181545c860,0xc21098c208417108210,0x841320ca105c43084121,0x59032841630ca1050c32,0x10210d0c32841650ca10,0x84332102105c44084032,0x588628414310e1018c42,0x18e1058c638426318a10],#[0x84063482105906484172,0xd8d2084143482104c520,0x486101c1218406348610,0x842434861058d2184143,0x1c1318437048610d8d21,0x4c61058931841424c610,0x840434ca10cc93184263,0x1d532840744ca101c532,0x4ca1059532841644ca10,0x843744ca10dc53284243,0x1d9428407050610dd532,0x58a1050d628407650e10,0x8404388210d8d6284154,0x10e3284341882104c620,0x9021059632841648ca10,0x84143c8610d8e6384171,0x50f3284064cca10d8b31,0xcca105933284163cca10,0x84176cca105d33284165,0xd0f3284274cca1099332,0xd061050f4184132d0610,0x84362d0610ccb4184270,0x4843088270d8a1010f62,0xc62088430881710c220,0x881211022050c3188131,0x5cc40881711022058440,0x10620cc4408826310220,0x8817110e2050c4388263,0x584618827010e205d843,0x1922058c638826318620,0x880704862010d2188164,0x58d21881614862050d21],#[0x4c6201c9318834348620,0x883314c6205913188141,0xdcd548807355220dd531,0x5862050d618804358620,0x882545862090d6188154,0x1cd648836458e20d0d61,0x8862050e218837359220,0x881639022098e2188161,0x5c66388173952205c640,0xcc6205933188143cc620,0x88341cc6209533188174,0x5db4388161d0620d0f31,0x50a211c142884704ca21,0x8844358a211c14388473,0xdc1628874358a2150d62,0x102304ca608877458a21,0x8c073486301c1218c161,0x5d1218c1544863050521,0x486309c1218c17548630,0x8c04258630dd5218c374,0x86608c1719023058640,0x9823010a608c04198230,0x8c561d0630487308c221,0x994428c57510a3199432,0x586325c1618c84358632,0x8ca7458632951618c974,0x5c432901719823210e60,0x4864010d219027310a40,0x90131486401d12190073,0x58d2190161486404c921,0x4864098d219017348640,0x9033248640cc52190273],#[0x10d32900424c640dcd21,0x4ca401d132900714ca40,0x90132586400c96190371,0xcca2190132886408c961,0xc86405c632900438ca40,0x90132cc640cc72190161,0xcb4190341cc6405cb31,0xd064058f4190132d0640,0x90c7058e425c43290632,0xcc9319407058a43d0d61,0x58a541c16294c7058e52,0xc41710cb101c16395070,0x99132c40704cb1099032,0xc720d0d62c404358b10,0xc80704c7209d031c8172,0x5d741c8143587201c143,0x4c72199743c8175d0f20,0xc847054f211c143c8470,0x1c121cc073553211c154,0x487304c921cc13148730,0xcc1734873050d21cc142,0xdd921cc374487305d121,0x5873050d61cc13258730,0xcc2725873090961cc232,0xdc562cc34358b3050d62,0xd073050f41cc17288730,0xcc4744cb311c132cc562,0x1c152cc47050731dc132,0x58b311d162cc77255331,0xcc77458b31dc162cc554,0xd0660cc44298331dc964,0xd073158b41cc532d0731],#[0xcc870553321c143cca70,0x1c164cc95458732dc554,0xcb405c831d037159332,0xd0163487401cd21d0171,0xc961d0331487409cd21,0xcb415ca21d013258740,0xd06650cb415c432d0565,0xdc532d06654cb4159532,0x8cb411c143d077350b41,0xd0532983410ca60d0571,0x1c162d0c7058f428ca60,0x8f63b8de2f87c4358b51,0x9fe7e9f67b9de6f8fe3e,0xadeb6abeaea9e9fa7a97,0xbb6e7b7edeafebeaf6bb,0xbfafdbf2fbbdef5bbeee,0xcb727c7f1ec771bc5f0f,0xcff3ecf73bceb37cbf2e,0xdef77ddb6fdb75fd7757,0xeb7abe9f9fe5f7edf77c,0xefbbdef3bbee7b7ed7af,0xff3fafe7f6fd7f3fbbe7,0x38602942ca01a859401,0x50e0700e180400c380c,0xe180c00c381a018603c,0x432ba0386084030e110,0x287510010c960061d2a0,0x10c980061d2e01432920,0x61d635232a98a0654c40,0xc3d520f87a9c010cb200,0x75dd562c9ba01e1eab05,0xea2125dd7775b326ec95],#[0x196802c3ad4058759d42,0xaaf0b4645e80d0cb4812,0x7bdd2eeab9ad191744ab,0xbbd01e1efa05c3df2138,0x77d01c36fe9565ded3ac,0x3fc0386e00030fc0a999,0x7fd4ecaff2dd91fe5a32,0xfe26d95ff57b23feac64,0xfd02c3c0205877f12aea,0x406868012ecb0001219,0x492ecb020161e0502c3c,0x48061e074abac0c00868,0xf52b29e00086828030f0,0xa03873b932ca78a6594e,0x8070e7a2b1cd0a01c3a2,0x21d0560b120801873d,0x1cc289aae73da4050e83,0x47841408908280e61452,0x32ea2b8e6144f1dc28a0,0x2105301c30ac0187161,0xac28aa378514c8708299,0xc806882f0ec79320d8f1,0xeea6b81e1da905c3b444,0xe1b3e00c3e7e0187cf52,0x43f7a0187ef0070fdd00,0x85375390a6e80a1fbe00,0xc0d25d962700c39da9f,0xd40864b1012c96200c33,0x3838a985014b702102a5,0x7054350e08866181063c,0xa0a0f614131ec282e188,0x94e44c0a9c658553c7b0],#[0xa6acc634cccb0aa817a1,0x4e17ee69916219358c31,0x9e062193855b2a702c80,0x5455b2aa81a864f156ca,0x7f03654fd1100a006219,0x5956caa1c0d954228432,0xbaad955728432ad03655,0xa3a402b4a975580310ca,0x62c804ac310cae122195,0xd56ca95afd8d2b63b125,0x2a1d94955b2a8ef4804a,0x55b2aa2bc63545570aa3,0xab65560310ca92ad9552,0x7ae6b0862192f0cc3a5a,0x6605650c432c42c80589,0x643d5a1987a647b0ab31,0xf76ab11303560b21eae1,0xf0f668ba1eaf1743d58c,0x98eb164b15365d86b305,0x39d6a1887acd7ee75833,0x80b84a50f5d0621eb95e,0xeb61b6dd6bd13c3d3874,0xdac5543b57edb75b0db0,0x3d501981b1c330f52aad,0x3b98310f6486a1ecb0cc,0xf531d202a60cc3dcace7,0xb740dc3d521981b203f0,0xef25981de19b0dbb32e1,0x918ae411b25c4231ec2,0x13315c82664b884cbd63,0x270cc308c498610d52ea,0x8518830a18ee41433584],#[0xa621081544d0c2a65c38,0x7166042e54ba89619860,0x22e400641a870b8330e1,0xa59810f4370e190621c3,0x17ae61816604381ec287,0x9720035254206049840c,0x25c206a48840d4b7021a,0x59810e57ee61d8fe1435,0x7b0a1e2edd03c5cba062,0x318d6e0cc305abe630ac,0xdb22e2bf735b59d0cb73,0xb645dc330ebb06a19715,0x10cbcaed91790c432eeb,0x2197c0c432d819875ac3,0xc0b0018865f57ae6bd92,0x865f8b302bf8621d802d,0xf782a5d6ed0cc0aea18,0x1f130c43dfece63bf033,0x3de4bd73bc8570f75066,0x1c20330f7c2a5d71e0cc,0x37b0f6170d2dc0e12598,0x71f0dc0dea1f87bcc5b0,0x6f41a87c38370f7c86e0,0xdf99b0dbe335877c63c3,0x42b361b7d0dc3efc5c80,0x8667c090c2c872159eec,0xbabd7317592e22eb3e08,0xdd52ea2f2f5cc5e54ba8,0x1ba1cc6394b08c649862,0x94b0900cd6118dd6e63,0xf22621be42c437badcc8,0xe470437c82086f5fb98d],#[0xc8988788db98df18731b,0x65c395a1a87198430c40,0x108422196e44444d0888,0x52ea65b2e1cbe64b917d,0x6e049464b9182a975331,0xdc092ac772268b3024d1,0x98125c7f0a4796e048f2,0xb0a45966048b0cc392e5,0x604980d43916198722c7,0x439301987260a3064c16,0x80234b3024c966049d0d,0x846926108d62b911a5e,0x10962e4012c3d8523495,0x91363f8525897084b122,0x42387b0a4f16e049163b,0x2620f6149c5dba138b97,0x4b60cc090ec572310b30,0x97ec56230037023106e0,0x28c7b0a5406e04d363c3,0x8ae192110dc09a83d85,0x30c43422ab6584576c9,0x26ab6580d76c901ae192,0x54350f098f616132cc0c,0x42e192082cc0c281a878,0xa0cc0c20ab6582176c90,0x41987cdc95099baa5d72,0x4330f9c0661f3a64b8e7,0x17a033454bae781987ce,0x66b0f0e3d85cd0b3039a,0x1b86e605901cc3361b87,0xb703c812e1b9954baf34,0x661f932cc0f243f85e40],#[0xec2f2c5b81e44b303ca0,0xb763f226e87d2edd8f91,0x30c7c0621cfb5f399f6b,0x5951464b922619863fc3,0xc39e6b9763cc370c8a2a,0x7640c370c792a594f20e,0xec8e14e191880b2a30bb,0x191a54b2a3451864717a,0x12164986420e3028406e,0x643212c686126190b86b,0xe870661d0d2cc0a1a498,0x5120cc3a225981444370,0x1eaa9653d4b702881660,0x45952ca83af98d070dc3,0x8f14e051d54b2a2cc562,0x355eb9c6acc638dc3702,0x74bc868d8310d1b0661e,0xfc350f1d2fdce3a2cc0c,0x68621a4f0d4348a18868,0x50c434a01987934b3032,0xbf638e0310d2b2f5ce5,0x978ed242f1da470c4347,0x8621a5a0c434a6bc6394,0x2dc0cbc1a8796cbd012d,0x5981970350f2f8621e5e,0xa303248621a392cc0cba,0xc607490c434a8198192c,0x8c0eac1a87d443d0fa49,0x680d9c3d0fab1ba0f563,0x303ad97a035b39c0ed07,0x607480ec3ec05b81d70b,0xb9cec5b81ee0b303db87],#[0x869ec310d3c86a1e765f,0xd431421a7e0c4350a1a,0x68b0d43d101886a1ca1,0xd1a1a87a30310f4596e,0x39d4b3034516606892cc,0x74186606820c434eabf6,0xc4c2e418a21886a1178c,0xb1e5080150330c262f98,0x6417ae6c397e1d8f2e41,0xca92211902bc13205b81,0x860cc3b2cbe73678330e,0x84bc737089108c88661d,0x10350ee12add5c25dba3,0x817201f00d43b86bf647,0x42f403e83f857c09708f,0x8bc636acbd00faaf9cdf,0xc310cf292219e43e41b5,0x3850d820c433d0bc636b,0xfc3b024886605c6c8c1,0x29816e4350cdb0a605b6,0x9108d117201a20d43372,0x4e1da228403441b87688,0x7b238e1987690a306d01,0xf637759b02e286a1dc66,0x302dd94a0df85ec3bbcb,0x201a90d433781a866ec5,0xc36405b81ca49106d492,0x81c90330d910661b210c,0xb930621f250d43e4859,0xd50cc36462981c8c7b,0x21b8ba6435997046ab22,0x68707b0a6d06618d85d3],#[0x90d0661e1662b942e528,0x7a80d434402981880910,0x736d475e6d52ebd4b55d,0x4807b0bd08f617a35fbb,0x318661e620cc323e5b81,0x610cc3cccc572998370f,0x765b81f1150ed3538212,0x152cbe12a597bf54b2f,0x16607c82cc0a521e80f,0x42dc09c83d853819ae07,0xe3f8539097087212210e,0x4370e7116e04e267b81c,0x2edd0e85cba1c23d853a,0x63c09bac4803747b0a74,0x4a8488992e31106618de,0x56cb122a1962464b8c4c,0x25c62e55c2c48a885891,0xec2c6659818c156cb16b,0x9818ac7b0b18966062f1,0x6cb142a196280cc0c541,0x607401fc2e825b81d055,0xc0a445b814847b0ba216,0x81f183303b6066066d0c,0x9296605270cc0ee019,0x5245c4024819814a091,0xce859819ccb303392ee,0x1f1c3303b712a036d0cc,0x3b986607720cc0ee2198,0xc007d41802f883004330,0x6f98200df10401c920,0x6da70e013ee08037d41,0x3becc8097c19012d387],#[0xb18c380e618601dbaea,0x10d273020630e05b75d4,0x75f6640f3e0c81e69c38,0x2b421005694000a61860,0xc69c200ad284015a3080,0xf248307e4f080e492101,0x4c50609341cc1293c183,0x1821c153143823177404,0x314382e628705a28e80b,0xd3740620b0a09b41d013,0x7286a798a0c193141828,0xc9d950993b29c918353e,0xfb9a66fc734ce60c699c,0xb734d9fd0699bf60d337,0x1009bc990d3a92a1a74f,0xa1d391843a6e60864dd2,0x43a771c734ee3ee6990c,0x654f0c50c9a41d953431,0x86aa98a193d314327907,0x195348402a726435564a,0x92943087505fb049f182,0x2578c10ca5bfcc94a7e9,0xcacb75d5597f992bcfd3,0xd608aa1ac0dd7557cc10,0x256f8844ada0c6adb45c,0x515beeaa2a3605457dc2,0xa3341d948314328ad076,0x4669c0a8cd18151a0f0a,0x8cd284519a308a334211,0x35fd04a63f6094c69c22,0x6b4a094d68c129ad0825,0xa4941d9cf883a61a704a],#[0x4dd75a89f665518ce1e9,0x1baeb523b5cea418c3d4,0xcc98eb17d995a43187a9,0x4840564ff73ad9f8e758,0x6087acc650f5a0c21eb2,0xfe655ba4202d4314056a,0x8a02d51843d703287aed,0xebadc0ff32b89fe65631,0x80a75a4e772375d6e36,0x30b508ce1e9d31c353a9,0xe1e9e35c2d3c3187a84d,0x3a5863387a80670f4f8c,0x43b0df08761bedd2c37c,0xc961be952c37caa586fa,0x1abc7cb2d86fa64b0df2,0x1d803287b08650f5e186,0x6af9beeb5f0c21ec0404,0xf60b4ddac430c357cd07,0xed119c3da06186b3c610,0x5ae6086b5d21016b8ce1,0xb58d70b6c1a616df31c3,0x6b1a616d68ab25ac8183,0xdd19c3db28383b64630f,0xb66086b6d21016dc5d92,0x70670f6d1a616de31c35,0x518e0eca3041d946b85b,0x430c15a66382aa5a2c75,0x8fa84dd1f309ba3e2137,0x9a70e20b4e1c237dc26e,0x98618478eb188ed38709,0x68c204a6381111a2c622,0x638612a5f0a1434e1025],#[0x5d06244b20c489641854,0xb20c4997c18592c830b2,0x7c18932e831265b0624c,0x2830bda4e617b41cc2f9,0xee81718a0c3a68398746,0x5d03d304386462870ba2,0x4387060870ccc50e1ec5,0x750d62d0818456103031,0xea1f345d43e3141876d3,0x1c39304386860830d1a6,0x186e62830fcc1061b18a,0x35b9fb06b718a0c40304,0xcb7cb90d7096a1ae0fe8,0x17268c22e430875bcc10,0xdced3815d5a302bab4e1,0xba5f2e3748ce1ee77cb8,0x763e5c6ec69c35d03187,0xf176b9de23387bb1baeb,0xdad173bb4630f78b75d6,0x54670377b498eee6939d,0xf4b10efe31c0e28d163c,0xb97a1dfd2e43bfa5a877,0xa3287bed1b037da4a02f,0x8650f801a617001843df,0x8ce1f119721e252d43c4,0x19c3dd66386bada2ed75,0xf371c05a6ed8134ddb04,0x3078e34ddb051843e06,0xa6171d31c36306985c71,0x9c3e323187c6d03078d9,0x173c7a2a878f18e1b1a1,0xa878423607086939e3cd],#[0xe0f0a3041e151743c2e2,0xa1de86283c30c3078618,0x81c1c630383342131772,0x3880c6070f19c0e2c31,0x84b27e4390afd81df463,0x316461862ca4ac4594b5,0x72c8c7025a18e08b331c,0x42e3e5c45c96b08b8ff8,0x45c76b98b8f1721724ac,0x8b86386170c30c2e375d,0x175a2e42e8ce1c5c18c3,0x2f345885f69c38ba6382,0xb896b0970d387178c702,0x7863862e0c30c5c49588,0xe62ac45e98618bc92b11,0xd0ce08bb68b117663822,0x28e4198514842e8c7025,0x2d176165dac82d34e1cc,0xda7082db46105b19c38b,0xa060c6376398c72d6118,0xa9308c7516118da6ec31,0x447318e9cc431d358863,0x8d0631d160c63a3b98c7,0xf5d8637f3a0c6fc7418e,0xe908c6918618dfeec31b,0x3761ed03063dbb1cc7b7,0x4c240545848030c30f6d,0x1cc80a7311014d62202a,0xb99014773201fae64051,0x76201fee8403f5d0807f,0x433a4618807fbb100fd,0xd86977b98d2d37619d0f],#[0xb0fa69851f50b043eb4d,0x31bd0f0437c95886f69b,0x437cb5886f69bb0deef7,0x6fa1b98df4b821be910,0xdf2d651be5cc837cb59,0x1be5a6437cb2006f97bb,0x37cb5486f97a10df2d42,0x6f96a98df2f431be5a86,0xdf2e541be5aa837cbdcc,0xbe590837cbdd06f963a0,0xc4be146f97ba8df2f841,0x847438f12f761e286e63,0x4d3761a0d70a3423e046,0x1a6ec3f236047e69bb0d,0x23e047069bb0d8ef731b,0xa4408e0d3761c1dee638,0x25641c27ee63852e0470,0x4eec38495947093320e1,0xfdcc7993a18e125431c2,0x8bb0d686871e64eec3cc,0x3871ac610e35b4dd86b6,0x6ec3fb45d87f34c28fe3,0x1d06469bb0da61861fda,0x420e68287191dce8323b,0x761ccd70a399ee10733c,0xc40b4dd88131c30e6d3,0xd48177ba102ed74204c3,0xb102ed76205deea40bb5,0x4205030c40c76188177b,0x637242006e76b2902ed6,0x87731c30dcd3761b9070,0x8e2d3761c5a2ec38b4dd],#[0x1e9a2ec3d0ce1c711843,0x32b41d86572ba0cad376,0x7448400e86186195a6ec,0xf863861d1a6ec3a20e0c,0xf1cee83e2060c7c49400,0xe34dd87c683b0f869851,0x230c3104d376208c30c3,0xa90801d5a6ec39345d87,0xcc70c3ab4dd87541c18e,0x18a1c6631400ccd37620,0x35c28ec7b841d8f1083b,0xfb811d9f9003b34dd876,0x67043b3ce087619c08ec,0x72147673c20ece4841d8,0x840108fc80211bf0a3b3,0x182211a3024234a00846,0x5084234610846842108d,0xe148468c2908d384211a,0xb215af9722b65ac456b4,0x842b65a8456bee1cad96,0xe45723e04ae68bb1592f,0xb018c395cd1762b9e2,0x3160d0862c1d906583fe,0x42c4670e57b45d8af19c,0xc63a1e08c792b118ed38,0xcc892b29912564321a2e,0x19263863192100633ce1,0x2d5a2ec650ce1cc968bb,0x30345d86078b90c0d182,0x6119c10c23387180630e,0x7d2c822f9a70430b4608,0x2e5f045f4ba08be96c11],#[0x63c5c8cc68bb19715643,0xc18c3998d1763322ac86,0xe7b82335cac8670ce1cc,0x65b0460cb208c119c119,0xa36048b97c11832e8230,0x1943916318722cc30c45,0x61862762ac84ea36049d,0x59024a0ca1c9d18c393a,0x9dc89492391292f81252,0x7c092c7a84235e2e446c,0x37226d1b024d9e210964,0x2ca4fb49909f68b213ef,0x5c88c8a3a12a6382255a,0x439206182231a6e44634,0x74258c10e4918a1c9d30,0xe84fb4dd49669ba12cd0,0xc9f69ba93ed37427da0,0x11266382245a6864fb45,0x2280c304471821c9331c,0x61bf200c330c1142618,0x46268c096cef8330dff0,0x1a4d381189a302310ce0,0x345a2ec6845590d072b2,0x513e5c4a219c09a67b81,0xa73c4214c8782298f508,0x52d1642a50b0453bedc4,0x94c70252b4594a969321,0x234d0ca968a195314742,0x57fc018afc80314c7025,0x43181228630444bbe0cc,0xe28c9058c604ab18c115,0xb41da0b83b2c17176482],#[0x8bb241d1464838c50d05,0x6286839a0ed0741d960e,0xa0ed079821a0d683b41a,0x4e120c68c2418628683d,0x1c166b3386ceda10d08b,0x182ce867059b3458b363,0x6ed95a0a0f2b7639e566,0xddb314141e62ec73cc5a,0xc36591d86cb1a6ed96b4,0x83cbcc70d972020f2e40,0xed9918e1b2f69bb65e80,0xdb304041e606186cc9a6,0x370ed376cccc70d9834d,0x1e24c70dc421e0b8898c,0xdc518e1b8935c2f128f8,0x38c19c3f163087e2da6e,0x71a6b85e30f709c62420,0xe38c70dc6b4ddb8d4840,0xcc346138f30c371cd376,0x9731c1722d386e61f901,0xef2d613dcc703cab450f,0xfa0aca7f34dd8f782b29,0x415950042c1200d3763,0xa68399f517763e5a6ec8,0x71e733ee2eec7e4b1ccf,0x20aca7c45dd0fd30439f,0xc1594ff30c31f0d3763e,0x3d41a0261863fda6ec7f,0xd283409a1068134a0102,0xcf087934e191473c2228,0x95c9199a99232d3863c9,0x3c2234798146d070e8c3],#[0x98142cf702849e605087,0x70c7ab9e10f53041a1e7,0xa0d1772c222ce78441da,0x4347ad0768f50f051eb9,0x76905dee720a160a4130,0xc71f23e063e69b9c86d0,0xda42304347cd0768fa38,0x9c8862878ea3ee71d341,0x68eddae71d98a1e448e3,0xd1fa42023f3143476d07,0xe4019c0c7e60868fda0e,0x48a6286901a0ed203bdc,0x8f1a1071e18a1a45683b,0x2734e0e3c6941c78d183,0x4e693b49d1c639391f03,0x9ed06393da4ed289821a,0x61dae72ba160a5768434,0x33460a466843470d1739,0xe77c3cb31c86965a7052,0xcd08797a5f032f4b2065,0xc3072e1860e5f69c3cb,0x4718e4a6843472618398,0x8e31c986286929a0ed25,0xd08192cc30325b41da4c,0xa70325b4a064b68c0c96,0xbdcf5342c16a68782d31,0x9bb69a8f81d35a6e7a73,0x87d3cf50fa4b4ddb546,0x8e9a53b5cf4a3143ea26,0xddb5048406a0d376d29c,0x3a6a4ef73d486703a834,0x83d2da6edaab4ddb5272],#[0xedafb45db5e47c0ebc7a,0xcf6276b9ec68582d8da2,0x26c8e572d9a6a65b3345,0x4d95df0fb247e1b649a4,0x3b51ee07683cc0ecee48,0x75c97c0eb92c81d70f30,0xeb8d087d72090bae411d,0xd1dc909a39860f5d69c3,0xad391d35a30c36b0d386,0x5a7221eb4d376d69b8eb,0xc27981d64f303abb9213,0xd8f303b039a13617221e,0xa471cfb469bb76c8582e,0x530c3766d376eccc10fd,0x2d386ee4c30ddab4ddbb,0xa3ee73b34e1bb269c376,0x98a1e7a8e39cf462879d,0x683b4f662869dda0ed3b,0xd1839e1a1073c18a1a7b,0x38ed3fb4e0e786941cf0,0x8a1e80923950082879fe,0x1434f8d0769f238c73e1,0x829f5a0ed40c718e813,0x7053eb4a0a7d68c14fad,0xe068268c0d04d0869d5a,0xc209cd186131050fb7b4,0x7363e6486c7cc50d8f8e,0xe6c7cc9cd8f98b9b1f30,0x18b99ba31f317463e66,0x1b32338762e38c6c5a42,0x1618d30acdc7d8d998e3,0xec30c61d86314330c8d8],#[0x98c7739b189080630650,0x3243387630610ec61821,0x6752500ce98a19928a32,0xce8c61d9d314333a6985,0x8d304331a9080634650e,0xe628664c670ec68c21d,0x1e6300c3bb5cd8749403,0xac79cd878eb9b0f32806,0xe494033c6187654c506c,0x27984625dae6c4bb9cd9,0x4f108c89a615893d4231,0xbbdcd9735c2b227b8464,0x484031cd26465da0c8cb,0x3087638c10cc7451918e,0x2500c418a199419c3b1c,0x8a0d968aba3106283621,0xc1b14928067cc30ecb1,0x985629cae8c520a0d8a4,0x506cd9861d9973ba3306,0xe05913141b386187668c,0x43b806086701d8e6e018,0x846fda50ee118a19c118,0x86edcc50ddb30c1b86ed,0x19d718c3ba8628675264,0x33b11464760670eeb982,0x7768c50ced1a615da314,0x6eb34191d968c3baa318,0xdee8fb1bdc90807b8c50,0x3de90807be3ec6f98ce1,0x7b4c50cf90ce1def3043,0xfa18a19ed76b9bda9280,0xf199403e8ee737d12500],#[0x5661837d52500fa98e0d,0xae38c6d5bcdc9ab78393,0x5bb18dab3143356d0766,0xe694335630866addec6d,0xec63784650ed6bcdc9a,0xf50cd8c7d91e28e323c,0x3418de6194336514646c,0x3c433c87880791a4c6f3,0x30867946100f2b75d5e3,0x6500d9b4a19af3d403ce,0xc201e86831bd232806d0,0xc433027880605cec8c18,0x806106500c21ea01853,0x502db3e605b66940308d,0x619b6794136cf1826d9f,0x3b36a32866d9a50cdb34,0x876e1a0ecdc0ca1db568,0xdbb4201b7194036e32,0x19cd69c036ed2806dda3,0x3987a8673cf500e78ca,0x57adbaeaf50ca01ce3d4,0xcdcbe605b919403d8dd7,0x1ba1943372d2866e5a30,0xb463280744650ce80ca0,0x68cf708d19e211a38eb1,0xd2c758da5693b3466b85,0xa23040344d264695a0c8,0x428383684c500d3c75d1,0x80670ed098219a18a323,0x2455d1a0314034081836,0x640c1b506187690c500d,0xaff84715fb08e29a615a],#[0xa3b00ef18a01de68323b,0xa3605f731403b91e8077,0x78c13eefa817ddf302fb,0x33877d90106fb3ca09f7,0xc8c8ddbe605bb4141bf0,0xca19bb6943376d1866ed,0x943378e4646f06500de0,0x2806f4650cdf0ca01be1,0x500e98c219d218403a43,0xa01c9194039030806a86,0x40bf4f9817e86100ef8c,0x807ec6100fcbca09fa7d,0xd900ca01cb194039432,0xd3243141e4e3280c89a3,0x3e4a6080c94c50f9245d,0x3ca0c5019418a1f26304,0xdc13461b237cc0e46628,0xb8468c3706f182e0da30,0x1b23280e19a30dc2b461,0x864c10d0c98a00db3040,0xd495ca1d92b942e3387,0x1a31c0c351574860f709,0x3eef3287cc3030dc5212,0x9d2501d334d861e69b14,0x53458b9e769973c6182e,0xd68b1754ef32ea9da65d,0x4d186e7d0501ce3bdd39,0xc501d218a03a1304074,0x1860662194074a3280e8,0x30c0ccc638198cc30f31,0x61879a23ae7341860668,0xa4e733b49ce6468b9cc8],#[0xee02617c404c26382995,0x83b4d2dc759a51b0334b,0x980dadf101b598a1a696,0x303e1bee036b7d406d6f,0x607c130c0f8a6381f10c,0x3a1c0d074381cb05e0b9,0x743920d0a7041614e069,0xe875341d0e731401ced3,0xe330401c4d3743a9a2,0x1c2608738e28e871982,0x3acc5007418200e5314,0x6f98a00ec30401cc628,0x62496b8c4d2d71888650,0xc48d064890d70b124119,0x8962ae91198606236fc2,0x123410e248242c490465,0x2d30c0c42d084891a107,0x6462808bcc5011834d92,0xb0c5011a18a023131404,0x2b410f4618c0c5231818,0x231406866280d00c303a,0x66080eb8c501a2182034,0xc6501d68c607ac18c0f5,0x3420e6b19407603181eb,0x6939d1cd173a39a10136,0x6381a3da707473420e8e,0xcb0291c550d266840520,0x8e0a6e68b94dce58248d,0xc14e0d2729c1a107371,0x1819c629093798e066f3,0x7034918e0a9168b95226,0xe0a9468b95286181a4cc],#[0xc0d2c6381a55a1074a18,0xa000280000342029730,0x98025600f6005f0021c0,0x8091c03fc01c900c8005,0x1b300c9c05d402b5013e,0x8e02290105c07a803990,0xa059d02b20148409b404,0xcea0643030d817a40b8,0xdd40e860717037081aac,0x5820d40ff407d003d101,0x498023b4119408a0043,0xa3f05050275013300968,0xadd055c82a5414e80,0x817520b8805ad82cac16,0x32c018d60c47060682f5,0xd1035cc1a780d04066a0,0xd0743039181c160dd406,0xfd107c983d2c1e2a0ec,0x1bc10ae083c841382016,0x42326116b08a0844402,0x849ac248c122108ff047,0x9b684ce4260012cd094a,0x650a1704fd8279213a10,0x615680a9585390294e14,0x2d28165b0b11857bc2b6,0xeac2ee417430b7f85b04,0x5862303080181a0bf105,0xcca865a8328c190a0c6,0xa780d208682c33ba19b7,0x8a1b880da206c10354c1,0x4392c1c5c0e1506fa437,0x76303aa41d1e0e778730],#[0x5e879c43c601def0edd8,0xf0fc987d743e701eef0f,0x209a1029080543fee1fb,0x37e2180109b8840c41a8,0xc452422611119887e44,0x88ec446f82331117888b,0x23c0915c485e241411f1,0x26128389384499424a61,0x625e512cb895dc4a8625,0x4e4426ea1358899804c3,0x19c505c27e113d089d68,0xd8a42c51ee28d814528a,0x15350a89853e429a414a,0xb63158e8abc455822a94,0x222c5216058af50573e2,0x5ade2d35167d8b31859,0xba005c822e0016ef0b6b,0xda0bdd45eb62f12175f0,0x218518c18060802fff17,0x31ba18bb8c4e061f230d,0x57e32ab19350c89c63c4,0x506752336a19978cbdc6,0x8d29c68e234431a0d0cf,0xac28d5a46a6a350f1a71,0xb91b400d9046c0435c51,0x8375e1b9f8dc306dde36,0x712438511c050df846f2,0x68072c4391f1c768e2c8,0x40ea1c749e3a071ce68e,0x1dc58ed38760e3ae51d5,0xca11e3f0f15078163bb9,0x1e3d501e8c8f3e879903],#[0xc7cea3e481f008f6e87b,0xfe907ee23f381f760fac,0x3a90144802e3ffb1fe68,0xf209f10414818e409020,0x420a20ea106e48316416,0x586429e213b10928844a,0x2887084342218e90bfc8,0x911e888a2441b21fb90f,0x2d2915c48a6e44f7225d,0x82232f118ec8c2c45d22,0xe473c238e11be08d7a46,0x906647ea23d711e6c8ed,0x63492904903245f121dc,0xa92904942449d024d212,0x25a492c1095b84aba253,0xc34260412f74976a4b89,0xdc4d33267c132cc98ec4,0x9c5c4df626df936849a,0x3c9c9e024ebe27441398,0xb93fb89f724f8527a89,0x1288114328a122505828,0x521f28fb946e4a2fa514,0x5c052c7295394a08a484,0xfca71a5365299794bf0a,0x95160a858540929f194e,0xa9895424a9c854bc2a44,0x8f2b2915870ab9c55722,0x576c2b9b95be8ad7e56,0xb06458122bf815f08af1,0x4e8b1f058c82c4d16180,0xe96818b392599a2cb516,0x2d9196b94b5685a742d1],#[0xc402e0696f8cb73c5b63,0x8a5d052e70172b8b90c5,0xbcc05e242eef1763cba,0x7d98be685efb2f5f97a7,0x32180bcbfe05fcd2fce9,0x13097983fcc1a460a230,0x620130e898674c2e4615,0x5ca62b231429897cc458,0xacc7426369319d18c3cc,0x1931cc9146465320d98f,0x2dd1963ccace653a3285,0xb6334699964cc4465e83,0x8679d33a819c1ccdbc66,0xd1c668b0343c1a0bccfc,0x84cd39c699034b21a47c,0x89aa54d4d26a4a35159a,0x35ee9ae5cd6a46b1b356,0xd1a36719b2acd8de6c1f,0x506de736cc9b5ccda866,0x8de626ee037469b948dc,0xc260e092700237df1bde,0xe99c6bce2d07121386a9,0xc39421c938e45071f738,0x73dc39c71cd04e60872b,0x9b074b13a499d124e824,0x98ebb0758f3aa29d41ce,0x1dc8cedbe76ab3b321d8,0xc339e070f00277ad3bb9,0x763ca19e430f19c788d3,0x7a383d069e744f35a79,0xf6647af63d679eaa4f4d,0x130f8227bc83dc11ed4c],#[0x1f4d0fa0e7cc43e401f,0x3f349f8bcfbf87db33eb,0xf893fa49fc70fdb07ea0,0x74808240171ffb0ff907,0x902fc81344082a037901,0xa2d04c2822940f52069,0xc9a0d99064c830741682,0xe422ea111d081c83d541,0x8561429621411097c848,0xdbe86984321217c50b48,0x81102687c043bba1c950,0xa2601126c88f5445da21,0x56ea2a1d148c8a0544e0,0x1245e8a2e5516ce8b2a4,0xa8d1e466ba322918a28c,0x1cb28e0d46e0235e11ab,0xec51f028f51478223acd,0x6a429120c2901c47fd23,0x48d9a46ad22fa9137487,0x271492e24951244491e5,0x4292f2496824ac925149,0x527f493c649c724d4526,0x52f5291c946f4a1f2509,0xc2a55712a7c951a4a722,0x44af8a576d2b6a95a64a,0x96904b37a59652c84962,0xe7097104b67a5ae52d4a,0x992f3c97914bb925d452,0x2609d2ffe97de4bdda5e,0xc50a622d30ea985f4c1a,0x694c9da642d31d498bc4,0xc99cb4cd826691331899],#[0x34b09a3d4d10a680533c,0xc3135b29aaf4d49269ad,0x226ec137129b534d98a6,0x4e3ea719538549bf34de,0xd394e88273c5399a9c9c,0x329df14edea76713aca9,0x53d8c9e914f35a79093c,0x7e013e949f2f4f8327b9,0x327fc13f969fbc4fd6a,0xf50662825140b8a02e50,0xa16050a5284bd4224a0d,0x414a1ed50e528681430e,0xd4514a2705127a88794,0x28ce94640a305516da8b,0x211a8fe54796a3a651b9,0xf15262a924948e0a43c5,0x6a56d52a8294dd4a1aa4,0x4beaa5db52e32968d4b0,0xa154ce2a65d53122983d,0xaa9ba54d9ea6b3534ca9,0x53d1a9e014ec8a72f538,0x83e54112a0254fd6a7cd,0x9ca8b35441aa19950b4a,0xd525aa9145480aa37551,0xa6ed5342a97e54b22a51,0x2faa8fd543ea9f754eaa,0xe5555aaa5d5504aa7355,0xab35558b2ac1d55c0aab,0x798abb755d0aae2d56da,0xa15880ac3156092afb55,0xab38d59b6acab56422b1,0x6c6ab59d5a90ad34567c],#[0x1356f82b75d5b88adad5,0x2ae8857322b9355c74ae,0x5e60af0f577f2bb795d6,0xf655f68af8a57b9abd85,0x62c1d960c0b0395805ab,0x587eac39d617eb09c584,0x1a658c02c5696268b113,0xf0b23f590aac7b1638ab,0x165eeb2d4595aaca7964,0xcead66f6b35d599dacc8,0xead02167f0b3e259e12,0xd5a562d22568c6b4405a,0xb5275a82ad3f569d6b4c,0xb88b59e5ac52d5ad6a8c,0x216c54b6145afcad7656,0x2da6d6d02b6795b2ead9,0xb93adc156dc6b6d05b5b,0xa25bb92dd716ea8b7455,0x4b7fb5bf72df216f6ab7,0x7148b8895c2d2e119706,0x53d7244b9045c71ae2ed,0xaae6f57344b9825cb1ae,0x5d5a2ea5574c0ba2c5cf,0xbc85dcc2ed617662baee,0x74bc865e2faf0e17802b,0x57a74bd085e752f34d79,0xf7417b60bd835eb22f55,0x3caf9797c8abe275f002,0x15f74afb057d3cbe855f,0xbf745fae2fd217e4ebf0,0x5cc00a5ff32ff1d7f48,0xfd8152c0976042b01818],#[0xb05b18278c1186073b02,0x107b07b9839ec1b460ca,0xae6147309b9849cc22e6,0xcc318617e30b99858cc2,0x875cc38561b530d49865,0x241889cc41e61fbb0f5d,0xb3141d89e6c4d9625e31,0x62c9315d58ac8c553629,0x63f6310b17dd8b9cc5ae,0xdcc6d2635731a1d8cc0c,0xd8ed4c74f639a31c418d,0x200d8fcec7ce63d5b1e3,0x3f3219d90a0c8386411b,0x86493323e991a8c8a764,0xc9e064e1b266592f2c95,0x4caca48651ab287993e6,0x3995e6cace6552b2a159,0x32e1196dccb53659b32c,0x629330a197eecbd465df,0x2667633351995acc906,0xecda266bb335199a50cd,0x9c98ce27670ab37b99b9,0xb819d80cea2673c33991,0x33ce19e52cf0e6779b3,0x67fab3f1d9f2ccf7067a,0xd6684eb4191a09ad01c,0x26d17968a4b4479a20ed,0xda460d21068fab4701a3,0x4c69a5b4d2ad69433496,0xf734ee5a728d36a69a63,0x26a4cb51cda878d41f69,0xd5496a9bb5489a9fad4c],#[0xc54d5f76aea35695aaf2,0x99acfcd65b6b28b58d1a,0x35cd1ae44d6ff6b67b5a,0xbc8b5e11aed8d7546ba1,0xfe6bf2b5f31af7ed79e6,0x2d8626c27b60ddb030d7,0xb1bed8c26c55b6221b0f,0x665b2dcd94c6c97b640d,0x8367d9b3bed9c26cd436,0x6d41369a5b4a0da2c6d0,0xb146d7ab6b69b56ada99,0xb2dbb76dc836da9b66ed,0x5b8acdc3d6e0bb6fd1b7,0x73d5b99edcc06e5c3722,0xce3762dbacadd396e8c3,0x86f1eb7845bbdeddd26e,0xdede6f63b7ac1bd50de7,0xf00df596f9fb7c91be04,0xa1c012dfe46fd637e7db,0xb8229c0e8e06c7026380,0x8138381c1a6e0b77050,0xb770c7385d9c28ce1227,0x8e252711138815c3b0e1,0xc65ee300716938a85c4d,0xf2dc758e38971b938d31,0x4b9211c88ae40471f938,0x72ab394a1ca0ce4ea726,0x5ec72e8396c5cb36e575,0xf2e662732d398d1cc20e,0x9cdace6b6735439a45cc,0x9e45ced6e739738a39bc,0x25ba0a9d012e7e873de3],#[0x57484ba375d14ee87174,0xe9a374c1ba5a5d29ee93,0x46aea1a74fcba761d36e,0x85d57cea98753cba95dd,0x3acb9d644eb0d757bbab,0x5e6baea5d72ceb7e75a7,0x44761bbb089d81cebe97,0xaecbd76483b1d1d8c0ec,0xdac0ed467690bb435d9d,0x7eddbc0edb876d3bb615,0xe3b989dc98ee2077043b,0x7779bbb6ddd88eea5773,0xf8f77bd3bd69de7aef20,0x2af00377f73bf51df5ce,0x9e0f4f05f781cbc07de0,0xc52de256f0ed785ebc26,0x11bc7ede3ccf1b678c5b,0xd7946bc9b1e4a2f24579,0xf35b79973cbdde5a4f2a,0x7f0f3df79e73ce8de6ee,0x9e8daf4547a1ebd061e,0x3d431e9e4f4cc7a51bd2,0xad43d625ead6f5437a94,0x4a7b15bd841ebccf5cc7,0x8f6c07b543d9f9ecaaf6,0xee94f7277b8e3dbd1eda,0xfbdefbcf7c37bd13ddfd,0x2be145f044f8137c03bd,0x7c74be335f14af87a7c3,0x9557ca03e47df200f8f8,0xd0f9c87cdcbe6a9f2f2f,0x1f4f6fa5e7d213e82df3],#[0xec0df5aefac37d523ea5,0xbb3ed95f698fb337d86b,0x37e0abefa9f788fb9e7d,0xfcc57e4b3f219f8d2fc4,0xb80fd777ea7bf4b1f9f2,0x11fc74fe2a7f0d3f795f,0xbfaadfd1efe607f2c3f9,0xf933fc69fe1cfefb7f6f,0xc87fcebfdd9fea2ff2e7,0x5001680043ffc9ffd4ff,0x1d300ba803cc017e008,0x5f202a5013b8083c03c6,0x8406ba0329018c80c240,0x8129c08c2040f01ee80e,0x33f818540b82055f0280,0xfd03d381d940dca06b30,0x209110458821dc109207,0x14660a0b04f6826a4130,0xd14163a0abb0551829cc,0xb82f4c177e0bab05b182,0x647831dc188e0c2505f,0xde906ca835ac1a520d01,0xba0eb50747839c41ca60,0x420960fc307ad83c5c1d,0x47fc233211450877842a,0x9684b5c24de123b090e8,0xf09df84e8426e6133d09,0x14a70a4b851a4285e13d,0xb8a15730a938531c296e,0xc2d8a16790b1d858442,0x85efc2f3e17650ba385c,0xca1863ec313a18650c06],#[0x5b0d17867dc335a19750,0x61b650d9486bd435321a,0x394e1c630e0a86f3c374,0x7a43b521d730e898731c,0x187a543cba1e230f0987,0xfba87d5c3e521efb0f6,0x133106b8824440521fd9,0x422241110a8875c42ce2,0xc47062343118b88b4445,0x919c488e240f11ff88f1,0xf28963c4a9e250512578,0x7138b89ae44ce2261d12,0x283114108a02c4f26275,0x22228eb14568a27450b2,0x245392298714b38a4bc5,0x8abac55862a6d151e8a8,0x5ff8aeec571a2b7115a3,0xfd165e8b23c58ca2c351,0xe2ddf16cf8b5945a5e2c,0x5e9e2edd17608ba145c6,0x2c460fa302f17ec8be6c,0x28c6ec62f6314518708c,0x19668ca3c64c2320918f,0x3f919e88ce0c66ae331d,0x3234e51a4e8d1ac68363,0xc6bbe35911abb8d53c6a,0xdc6c6daa36a91b288d82,0x1e8dfc46f8637811bac8,0x91c798e2e4710a38631c,0x3a6b1d058e68c72c6392,0x63a3b051d5b8ea7c750a,0xe478423bdf1dd68ed847],#[0x8f4d47a263cef1e578f1,0xf418f9447c323da91ec8,0x6d1f9a8fc647d7e3ea11,0x6408b2014900647f963f,0x83da41af20a190414816,0xbec85a242a52133908e4,0xf9108c879a438721a090,0x22a09148489c644a5223,0x6ad2325918148b824581,0x8a47f123ce91cfc8e1e4,0xc92f6492524589223c90,0x2a2494c24a0524f69264,0xfc92ecc96ee4b1125509,0xd269a9339c99364c5525,0x4efb2757938b49ba64d8,0xfde4fa727c293d449e56,0x2ca1ae508d2814940449,0x9473ca35651752897944,0x98394ab4a4b2523328f4,0x412a0994f44a73e53632,0x255712a869531ca8e254,0xad6e56852b2995834ab7,0xf8caf3e57812bb195c24,0x596274b06258192c0495,0x2d2a9678cb35e595f2c7,0xc3f2dfa96e54b67e5ac7,0xca5d812eab973ccb8fa5,0x4be2e5ec32f3d978ccbb,0x821cc0ee60112fe297df,0xf49864cc2b2610330509,0x731b198c6cc58e623f30,0x64a7324b9917cc82a63b],#[0xc1265f332cf9948cc9aa,0xcccf06672933659997cc,0x9a524d1fe68bf343299f,0x5979ab3cd4d269e134ce,0xdb36409afe4d7666b673,0xe6e3536f69b684daa66c,0xdf6a6f4937729ba5cdcd,0x44ce1d270b738379c08c,0x49c954e42e71ad38af9c,0x3a1a9cf44e7367355397,0x6533afd9d614ea2e74a1,0x1a77b93bb29dc24ed467,0xcf2c2791f3c749e21cf0,0xec9cf5767a673d069e67,0x9a9f30cf88e7be33dc49,0xe9fabcfc4e7db53e,0x80402407034050040c,0xc130010c120188060003,0xa000f094c19104790c13,0x110410a4c4314c2c0c2d,0x5a4540c492241050c45,0xb98551019100879041c,0x60981207800468340141,0x10a018258321542c058a,0xe101be0c8330145a2a49,0x91e00d054080d840548a,0x81284a16426270562107,0x30f09b0743218c841289,0x900821220f81e46a0744,0x4254783408068843184c,0x84b4061b0ac2f81c2306,0x78c74154805cc907687],#[0x11b028302b2348862c8b,0xa2ec4405467083609f07,0xb0dc6e281f091c12300a,0x52b86d090c61e1340a02,0x8d0a0b04a0521612e19,0xa08180883792a88525c0,0x8178b080cb32ac00a2c2,0x41b46715c470e8643496,0x922068443592f85e0b45,0x45d121345685608e21c8,0x2f4ab1ac552f4887108,0x4589d0c5ca44d1943c32,0x1885d0be5672e1d09a10,0xc83668c4bca036682c21,0x473fa22a6c301888b073,0x7179ada79ce49a24511c,0x56136cba5b65a53b7802,0x263d9d3c07524e2ebcb5,0x36ffd11da3715888aa94,0xd185262d3ac554ba5a6d,0x50c0deb4443e0e2b088e,0xd26868d57408cb110abf,0x90aeb96263a40265c95a,0xb80f12a3876b56bb1a2e,0x4ad138c9dc4455961d3c,0x694ac6808af7dca84c89,0xeced650939c448bfa3bc,0x5a311f45274e25396279,0xe01ad1d34f1208a84d2e,0x1700d41fdff0cb42c02,0xc8300b806a0feff865c6,0x2b2ecb162a795acddc36],#[0x4e43443c6d4bca2d09fa,0x115edbd4623eb4529753,0x63654e440bf52b949539,0x457ce6d7a211ad4ce9d5,0x3c7828b44eef738cda,0x3a1459e1d62195390f5f,0x212261a49b89c86af85f,0x16d28109116d793ac010,0x686ae9b65c50a234ebc9,0x6d149871f35961060add,0x3163888062ff08284303,0x914944294e587e7b2b40,0x899888e7c44141d06368,0xbb69f482662235a34514,0xe5cd65d76ca8f04cc446,0x5dbcb9aca9d3cb9acb94,0xb39b6930986a71694b0a,0x7d04eb43489eeb4984c3,0xbb813ad0c1a65cd65576,0x4b130cd13b948c96209f,0x870e3e6b2fbce28b1a08,0x585f773be7110875cb45,0x88a44eb4556587d53856,0xa026568867ba9d1157a5,0xda13f87362ad338bafd3,0x8115488d884fed2aa326,0xa85cec08365a14c4eb17,0xa01a2cb3ec90187a6ded,0x106cf7170cb077725695,0x2ac1acf7114068e5d620,0xe4f4481504a04245c3d3,0xed41ec91490f82fdb533],#[0xc251a4c555ab1516db51,0x5fe00500d985a707ac9,0x7452161cbe27fc00296d,0xb670d30ff4282d9e8a97,0x17f8015b4cc1a7dff014,0xc062bb1fb385309d1fb3,0x2d953c3f244a575a6d29,0x12161732fc416cb45e45,0xe88111dcbc00a5b3330c,0x7c5292e8810f2c9c5292,0x8810e2f1e2403cc4088c,0xcabc957640d22f1e2579,0x30c63bece98afabf2cd5,0x5620dd3a685791ee20b9,0xf9df7b14ed7e888809,0xf4cab0477dc483433b1,0xe29e0e9888553cef8b77,0xacb8cd7e8da42b0477c4,0xdee5c4a814b7dca6eb4a,0xc5245217fb441dab9eba,0x81168900d3c01a26c447,0x2d7441e68bffdffc100,0x43697b7f0abf431b0d51,0x30003437728259ba3e64,0x57dbfcc5dcf55a63f997,0x11009343dbf907584534,0x24e4fff621433663be20,0x286b98fc7fff8e181201,0x7c05973517cce09e09c4,0x607db502e21aa30e5d79,0x6381882943f5300d94be,0x2f84800c2f75c694ca47],#[0xf48cc04444bf8348a8ce,0x8f789dca4030111ef13b,0x2a010001c47d6b42bc24,0xd2e26b04f4f817bf5871,0xd28000004d0fdfdd5183,0xcdd523452e26bdffe7f5,0x468a5c4d6fffa14217de,0x9fd750030492c3fd9baa,0x7aad9b3e534fc1c8906a,0x5b3cff641609a95decdd,0xf5e0eab5a92bbd929ed5,0x94a4fef64f057aada76,0xc6bc1d56b5254fea1682,0x86cdff9ff5d000409264,0xc818cdc19e21668ec5d8,0x91600d0e9fad7cadba02,0xfe8a9000300013683f2b,0x1590011141f086266cff,0x525d76a6528033dbfab3,0x9b6472b422cc62393d6b,0xea16d3d698c4727ad680,0x4274b6a267450f835dde,0x2563d899480087874b3a,0x308170036ede2393d6b5,0xff960050a2e0fdecdd51,0xba6311c9eb5a0261f9ff,0x85168fad57700c1009,0x9a07d63d2e800927fc8e,0xfe3802011697ff728182,0xda6fc10378388111137,0x202d6ff5e09f0000b885,0xe0111d224d1779ff9201],#[0xfcf244cfe1b228c4b447,0x767d6614275a3078552c,0x37f858691ba3e49d3626,0x92242443bc254cdbb291,0xfefc808516ae56f1165f,0x10011372598fe22c73,0x980a8029115ffcbba810,0xedff2b6e88a0633663ec,0x809dbc60e09c2600c8d4,0x312239a757a440989114,0x57a68e312225ff6aa68e,0xf0a2db2783a5055b75db,0xdd9126c35cde908ad9d,0xb6bf4c65e800040040,0xfe40410171ff3fff2a08,0xbbf7ff9010405a7fedff,0x369cc123fd9400,0x69642336d7ffffea0010,0x99a4d10c6d4f5eb9417e,0xfe90500012d3f3ff20f9,0xcbf91fdfe7208008ca7a,0x5f7bea2448da9feb8351,0x9cc4291047e8281110fb,0xfd2594a5e18054d627f8,0xb4d3ca12e0b84c744d7,0xca52fe6869eed41f15ee,0xfd634b6060a0044597b2,0x4d1dcb832dd1f3221b25,0xfc800a012bbf01e19624,0x110ff872c28080440ff9,0xb376035331727d583081,0xb6e54f644a680ebef3cb],#[0xb756e4f906a633452693,0xf98ccce0020009d1fe57,0x81bfb904a2c9f59606b5,0x1b0bf4ff9409a0030081,0x428567fffa0599080000,0x4ead61f2e4e1204cd6ec,0x35cfffffb3c74002012,0x33e03272fffc33120000,0xa497cce09e050c4286cb,0x5cf9540821767f514a06,0x8888aaffa55f5ca0accd,0xe54021036625f1dc2484,0x1b0f671b140acbdbc386,0xa2036665fdf16a252498,0x7279281b0be957c43284,0x4703434c304117d2af8c,0x3eb9a43201044163fe7d,0x181b15a3cbe762010442,0x40c99150d981deda907a,0xbb96b4c0740082006da6,0x2fcb829033c290e8b021,0x9a925c3f14904f001101,0xffd4051016ce08fc7fd4,0xf1e55c44d37de90a5155,0xff14340498ba1ca1494a,0xffc08010c0049b3823f1,0x49db5fd2e62018009387,0x590a8699d7fc08400c00,0x3f173c20001105ffc2fd,0x7fe6014002687e87005c,0xcb4cb20001a5f6e3005b,0xfffd9402000602006eaf],#[0x9bf1821ad7ef48000939,0xec80600009e9fff72f5b,0x1004934de8b02110cfe3,0xfeffa404145bbf33fc10,0x22404edd324588ce6455,0x408022d67fc524490011,0x77724c593eb2c0d51ff8,0x348ffff75f080080012,0xb1fb8422347fe8509011,0x8f8a8d5e09e0010c4286,0x3f3ff20e118b6ae35ae9,0x164ff9fe0000000135,0xea020100100a47ffe800,0xe808080000284ff9f075,0x81953fafe04e665ebe3f,0x946686fdb4100cc1fcea,0x4cd2f371902f3f972d0,0x7c1b76c894fa7a28f4,0x609ae1ef5ce364300dc3,0x9f04d6011ed91fcbdbb,0xcf9c73048008f6c8fe5f,0xa58bfc94e70a159112b5,0xe900088c5a27dabf5c88,0x60ff9114b37eb92949b0,0x66f7fe0d2c0850eb44fb,0x3043fdca40ce1f815b80,0xfe2f2c308204447eec13,0xa889f8008a2fb28410be,0xa6b6015357be104c2b84,0x9ff1d958308111dffee5,0x77648324baf52b47021c,0x885f4f088083f16cc043],#[0x525e20993dfedb01004a,0x9664f1e6c9526ffc8514,0x35153c0ca99ae038a4fa,0x54f95323217fab26d6c8,0x8b27d6581b173ff64a8c,0xa1a1f4ffdc704d0ce412,0xe20155374bca9ba184fd,0x8e3fd2a8982c0265d84,0x2a812088801b173c4fa1,0x70fff3551040812677fd,0xa6817411fd3ee81a99a2,0x463f44100967fce9d761,0x701a1b0f0ad872285b3c,0x84fe9880a9be83397902,0x9aab1ce510a8ff250514,0xf05100979c7dfad15491,0x1127b9e40aa2a5fffd50,0x533c78f2aca00e692cff,0xd15619aeb83137faa8a2,0xbe250042da1b2a455f14,0x522af2e89300b587cfcb,0xbe4df5e6d64021036e7f,0x36677cbbda924ac881b3,0xc206c2fa9157e7849810,0x2c0ae0c65f522af2e113,0xf703026214d3f74027a0,0x10fcff7898a821a67f13,0xf9a270c0d74cdf1c4c54,0x25473ddf8ac9cbff401d,0xeffeb04000004e5ce3be,0x93f8fff55840100993fc,0x9f4cb854cd7e77a10405],#[0xff420002b58f1ae64a90,0xaa67f13e0e1626214d3f,0x275536200f974e21,0x2c082426b9fe67c7eb08,0xb9e27960421135d73ca7,0x78a4a18abc9ea428292e,0xb889aaadd95397621352,0xfaf27ad5a926a805d3cb,0xc81380169de35c4ca471,0xfff8d70b0482013430f1,0xc57d420245ecd00c056b,0xdc44d3562f4e5d884d2b,0xfd793d6ad495562e9e5,0x7207e4435afde9000124,0x869fe11a26869ef2feeb,0x602227fffaf201824955,0x100180009ac1f17bf1c0,0xa7ffff900c00497d0ffd,0x2c0d63fffd7900c10096,0x3f4c8044286724c593eb,0x7902701a1ac37de0a14b,0x4204217f9948195bebb9,0x60697c5250aae6592c3e,0xfec911863341262c9fd8,0x413988d31fcc2204cd9f,0x4030158d7132023c07cf,0xbe06d2483bfb9604f7b3,0x38cd1bf702289114a9e2,0x858c0f196067ec3ce55c,0x49a9fa6e210ccaed4c86,0x1c673ff93e300802,0x1b63fdbf005c1d00010],#[0x6069cfffca1d00010000,0x1cfe4bc05343f7f76440,0x34407fff6400d15a0ba9,0x112910a255f45dc72495,0x5d4c1fe9780a55bfe824,0x1fef96661c6697d87508,0x7d6cd466f90e6326d9eb,0x7f612d332197bd6a5155,0x580a82ea7647d2f014c6,0xcaf0f1c2543673feff20,0xf721c9bdf86d095aa066,0x9bff2946f199f4a37ca4,0x2ad500d128ea37f25261,0x3f1fd71210c1289766fe,0x62006b5fff1f80110094,0xff9c2008676fc7fc5600,0x3597ff86c0008400d45f,0x40802637c3f8ca320200,0x98b3f4bc05357fe176f1,0x10d13fd800c9248ff8ba,0xa07e92f014eefe01d224,0x5243f2984219b7e1753,0x990ecc84c851bceff4bc,0x882db35ffffe0100000,0x2941136d7f1722e1dd0b,0x2089ad29e9f6fca458,0x15000524c0ffb7ed2b5,0x6f2e09e01c0416a9fcff,0xc8b01800034aca3c4847,0x4b5ffff7b802892507ff,0xf3c04400b77fca510000,0x908e3fea0242249473ff],#[0xfffeb2ee002024c59478,0x82006a39fff970061162,0xfea000a012b3ff948b0d,0xc9250619ffb8899e7,0xc6c1a8cbf1b06a30ffaa,0x5841845910fffb889987,0xd0d3ff4001900957dffe,0xfebcc008804b97ba9f01,0xff301900933ff5c01230,0x4500903faf30022012e7,0x6492a67a71e4024af15f,0xfdde994081d113ff5000,0x7ffb97dac8400000d80,0x85856c364ffd00054025,0xd5dba8850b1fe19a74e6,0x340c52fffebae0082492,0x6c22082989f769a32411,0xa05c2d7e7089c899d4e5,0xa99f9e1e6b434303c28,0xf8e4de022406aeff9bcc,0x844d39c3e7ac08081a7b,0x1faf411f054b5e568aea,0x637f948809987f5f4489,0x26d8cfc3f06cad84e013,0x49b19f97f5db9002202,0x20024e5fe3f03ff29440,0x609272ff1f81ff1801,0xde0104e695fe3f1bfc4a,0x350fc6ff0a44d492f0e0,0x101003637faf80002011,0xff0a4602674f3ffae000,0x1b138fffc00402006a6],#[0x171913279ffd70000808,0x5c4cf7e7ac0997912023,0xf1bfd60010249805f4ca,0xd7fbf97dac8400000d83,0x42013eb8700d3297134,0x428c20b68fc4c7e2400,0x6a5a2418a114d16ce7f0,0x154c3c200121136bbee4,0x673a2f0088c20b5f7fff,0x934c44b2714a4ba2044,0x43769fe50819a5fb20a0,0xadfe1b1032d3ffe04c20,0x587e7d7fd8c9a924440d,0x420660f6fcbb21000003,0xbffc71f2100012c3fe4b,0xff1cbfd092c8400000dd,0xf7e0ac5ad884458488dc,0x806c9f64a5d1b0001172,0x2291cbf2945cc000022,0x40001399fd9215d4d800,0xdb6c000dabfecfebf802,0x3c840004c2fdb1be3d7a,0xf06e7952c000d8befffc,0xfaff3e2128040d641fdf,0xbe1e15824e218408b0fc,0x3f7b780032f7fb00032c,0xdeb60a485afb7ec98103,0x3a066947426cfdc60221,0xcc400400226d6ff85fa0,0xf96a9252498089cfffe8,0x3fff9a88080080044dc4,0x78b2525c42b1a922233],#[0x69561a6b5fa977ab6069,0x41c6355a218d95ebe17e,0xa24915fa403227e7fe,0x2144b3eeab9100865fe,0xa33f11b4d8cfdbc00108,0x76326448c36107f7fc20,0xff2ff39080a320fcfcfe,0x8f1201c4510224fce0bf,0xb979050c50514408b17,0x800002767dbe12a91034,0xadedb000368f8fad7f00,0xf8f6000012f3a6d8df1e,0xd5c3e617ae0840df3ff9,0xe50b206ccc640c99ed94,0x39c4f08239797fd08314,0xa2733ff2ad36f2900d5,0xe020924a67ede0000041,0xa63cffcc5d90344ffc77,0x1f0fd8cb1d7ec3cc5c81,0x24911ff9eacc84044d4d,0xc9ebfd008924a1fff642,0x10a193ffff97340d1304,0x10a1acce96d051627ffb,0x24e7cd20196bc1bc8143,0xfed3fb325ac7ffc01401,0x9dfdd7f0cc96c06cb6ce,0x60af754f8c890d60d96d,0x108024e60af754e9a869,0x22050c886b1e7e7ef188,0x67560f93a064337faf6d,0x964202006eec3fde080,0xdcb22a224587e9fefe01],#[0x3eefb609008793bd42c1,0x1db104ffc02200001443,0x62c1e5d886a160e45404,0xa7d1d7525a9028c8b692,0x20fa7c4d69f1fb6c0c67,0x419827f2710d754b49a3,0x4200026c8f87e6465ae6,0x1580010801babfaf6506,0x958018801a53ffefdb86,0xfa0180ae3f7091199bff,0xd02d6e4955993c60d01e,0x1f98819bbe156361aea4,0x2727acd48e9f8fc1363e,0x6c0d507f4d48e9f8fc13,0xd6db7cb8ccc91b472338,0x8880fc315efca920a435,0xa9ee4605183c29f2c408,0x2801a339fd48bbfa79a9,0x5c50bbb608004567e0b0,0x1aaa459e7e2a400d44c,0xa4928f041548b30fa7b8,0xcff3aa1080b57f1e2048,0x856ff99dbe80403221b0,0xf07d02402087f7ec4020,0x6d5c05bf7fc89e8e09a6,0xcdc4996d9ded2f59790e,0x1bc932db3bda5eb2e0a1,0xbceff98043c3c0001080,0x435b27ebc93b7c030446,0x8000dc1fde53604ff6e5,0x1b23627ebb310658fc20,0x357646e0d923bf9e7a06],#[0x7f0836e5b4e21adf9e7a,0x7e7106f8f9938300863f,0x34870ff3503008037c,0xcf4ce8c8d75e9963f0b0,0xbf5570488001ba23bfdc,0xa7a49b07d3e006bca7dc,0xd71ef5cb581c84000da1,0x13032e11c7e0270c0,0x372fffc0ffa00,0x8186c8d89de7ffa7ebb2,0x46af991abbfb88a7e79e,0xd4bfd7a942024278f3cf,0x8c800d8dfa5987d3dc00,0xbff27a181aa3deb95a01,0x275fe31a94a00965a7c0,0x6e7ff96ffd980800089b,0x1ad75ff8ffc70410002,0xd7b90017df97d9808088,0x6d8ed4bcbfe02000226,0xcdb9ffcf25f0c9c0440,0xde19afafcfc122faa,0x3737fa65b7fe0c400000,0x6d06cd3531ffca316d83,0x920d92d31ffce175506,0x1ff6b510092b1ff7b090,0x51b0f3ebec4004004dab,0xf6200200006c40fbc199,0xfffec40000004d6df7f5,0xddef97f200000026d42,0x60377f2fe400000000da,0x74d11dfcbf8100000003,0xe2e1398543804265c901],#[0xa1cbffd38e229274d24f,0xcc6ef3820047fe484ac2,0xb74ce8c5fa5933214be9,0xcdd95311e19b0ce4f654,0x78e44d5954d7e9e0cce2,0xe584501c4e2388285fd2,0xc512029df96d11d9a0df,0x3275aa18abf0c7bd0d7b,0xd3c0899c771a0619b078,0xbc06680ebc94a4cc98c3,0x1a8c9cbf01a113fed6e2,0xdec9084cdd5c068563c0,0x64d14bc9de930b26855d,0xe652279ff272a206495d,0x7a893420750c63f510e3,0x2260750c7b9c873c443e,0xf79ae851f3ac73c7e9c0,0x11b7ce2088d3e864446d,0xd1c2594688032c397c25,0x692903313e000211df2c,0xc4157948a4d0678b0d7f,0xb0bc907af2415113450f,0xac7adf11539fc78c8a67,0xde59e143f31f122c6143,0x41af64635ed78a08dcd7,0x17820cf86712f05e0839,0xa0c95e1cc4c3e32808dc,0x5905e2c90542a7962a4e,0x4450fa8b8ad6043672d0,0xca4c49e988527c272e2,0xa92f852d982034c7c0ce,0x42e586f138237274d810],#[0x71274970d403440b161d,0xf78d448fc8b192a10962,0xa45dfc10448797498908,0x3859598ed092b31d010b,0xd24f6d514cb0caf35869,0x5f0e2265afe49de18044,0x920e54a5fda3e18044d1,0x85a299f20bf6514cff48,0x45c0cd31902f83334178,0x380d0999fc1991bf20bf,0xb5f7c41d7ad76f299a9f,0xde6a4678f55daf35a91a,0xfc2ee8335922b2451cbe,0xaa193dbccb09998cf828,0xc337714aea8887f493d8,0x7a622d7faa8fb12269a7,0x471d991de8f9f431543f,0x6cb346637e20ac6c1c1d,0x93f6ecada66acf831f7a,0xdb609be842c9bf71cc91,0x2f40d32ef88d7be01525,0xf9b5b8b4031a69f6a836,0x70fa9244543673f3187,0x7655382235f1383b1b07,0x99de8f9f405821e9f08c,0xc0ff6685154357913c19,0x187efb131f05f173a10,0x61ddf6f6a8417a366a20,0xf175081d0d0f80760660,0x1c7b756e02cd50ed0c8e,0x327bc1054187064cc383,0xfd068bafe7a05257b7d0],#[0x88ab4d17bec107efb041,0x505ed5044ff38b9420ac,0x89d1c1d6a50c92db05ed,0x6f7c27220d4a9f8331d,0x640f8fcfe6031344380d,0x5b80b3754b968668fdc1,0x6d97953226adf4c91edd,0x71e15e0d9ab2e0e387cc,0xd9e2c3154349c0068ec8,0x3d3f828d568547fb2213,0x257e90c756fa6394304b,0xfe153a12b88f63aefa43,0xa98908b7c62260147064,0xf5ed622ef4a31d62383e,0xe0b0d0e3b410f5ed6228,0xd3f0b19646a1e3b410a1,0xd41992dc08605c298662,0x408ada75ec53ef40d35f,0xe38d12f8c86be3218f5c,0xd9232fb2e0cbe9bcc884,0x347c8f1c7858b4258717,0x4b43f85e4f2985a3c71a,0x6497378d100785eecac,0xc302755c435fff380262,0x793280501fe545832c7c,0x8844e9b31ce1431fe087,0x9958a1fe986442a0dfc2,0x24e8567fda4e849e0686,0xb09e9c8cfa7a50c4ff4a,0x86d7cc464252f04e71e,0x6781a1cfc84afe4f5098,0x1bd7d0b047df33a10812],#[0x89505033f7b7e4c4140d,0xa1f882af2934a8cd9ff,0x9334fd655c4683a1d792,0x13af8c86be321f76e851,0x20199be8325066b0ef5e,0x2a2a1338f82c2668aff9,0xe6ec9a67cfc8a504cd0e,0x80b4544424397c94cf55,0xe98fa9fb8226647f75b0,0x3f53c7226593d1954691,0xc04257cc0640eb587503,0x7bc84043b7fa40c88fce,0x2085f610212fc2125a9d,0x31e38a8d569a283a1d79,0xbdf6c4313307cbee0658,0x29094f900184ef94a12c,0x237f47a8ca01deb17bb2,0x824227f775259a3fb4b3,0x43f6efc01a147350e1c9,0x82f79a506bae0448c3a7,0x9306b3d43aa501e8f1e0,0x8f4fe0a243f890600cf1,0xcb56f4a03289e43afd21,0xe442be7222d53c12c,0x8edffe9045021839c24,0x180ebd7507e66990877b,0xf7410dbdb3e35fd1034,0x390893fffb4200123741,0x4243de81f142d9d8a2df,0x796099fbcf8464d766c0,0x21104f0a425e711a7bd6,0xd5f20111ab7b20d9fdc4],#[0xcf8e1f066300d38e8403,0x2e54468c84fa7a2c3468,0x747a6aa7c81508dff850,0xf996400001b23cba3c08,0x6b07e2e00d0b01487,0xd87042268cf8f8d87040,0x9111b7e29c29220698f8,0x605c29866c767f6dc000,0xfe140081a11d1f220428,0xde9900d6d1071e18f3f2,0x1a0d31b7ef0002684f5,0x4a03434bc80684b7026f,0x3e440876ff0046427dfc,0xb1022f36be9846667af2,0xc72836f3120f3e08c63e,0xb7150cdb89f3191b935e,0x26e73b48c91338c889ed,0x681e7244332241788554,0x257f7b30656fc9b18262,0x8d1945ed0b12175e1a04,0x6560b7f249481a1be5e,0x9894518b1462c41f4f32,0xc640d2e24a6be3190334,0x2a600068dee6b8247dfa,0x1040ca1f8e3000666fa7,0xa71b29c425ff1825ef,0x9f0402115fa55421fd11,0x2115e5212105d182a11,0xf5d1102112d0e8a1f21,0xa124c4a227c40839e29,0xcd0d5b20e7e09125e2f4,0x1d7f924a099ab5fc6000],#[0x21d5fd140342c9fd005,0xe961c18741b3557d4e00,0x2545ed3e91606674d113,0x8093416db153b804cbc6,0x42dba12f9095173b1726,0x1963d70191752fa8bb7,0x42424e3f67e40214ba76,0xfe06032d65e54c8bdd70,0x9e466e042f3c8cdc0854,0x82105f6020e4f34e0292,0xbeae837b9a440a4c7ccb,0x41b1ccc502931913c19,0x1e30ae0f1b3170423317,0x4263c1622551c275624d,0x1993a0b19f17241cc84,0x662e9c292b23397fd8c0,0xa2df8a8601a19bb61682,0x7388d46462b74edb4001,0x22dbfea30210b57f0094,0x3f4aa10933f6b62d8ea1,0x8abe19d456d6c44dad8f,0xb2090a5e1b08cb3fed48,0x5e8241d5fdc264a31fc3,0xa22eee31161c92741215,0x8e31000488ec258c7e86,0x4b70ca5e65479a09593e,0xdbca05c665ff95ad4002,0x8a356893fd8c40012273,0x43d2a2d7e066890a27e4,0x8d0452707a8121578c43,0x58819cb8fb525881a17d,0x13257e12a58819f3fa62],#[0x399c477e7e8300a4be9c,0x54f462d8d04495e62052,0x2658389128c5ffb40408,0x69132b1a321d224ee788,0xce5cf04ba68005702bce,0xb58c801a1cc8fba4c856,0xd4909b87dda2437bf,0xcc76eac01d4068703f9,0xd2ae4c9a22848888ae,0xb026d01a1d3ffb784040,0xfdd372e4819f7e321dba,0x2427e0cc6dcbcba9e0cc,0x661490000889a8e327fb,0x48d55366843fcb04bcf,0x9a7eaf6b00246fcfd089,0x231e9ba760ce1ff41881,0xde1a174fe73d54ae7413,0x4121b9db8646fd94ba9,0x690d15eb4f06655f3f43,0x3e8102334a1c3ff45c70,0x7097d2500069db8c951b,0xe237d650b9e383103345,0xa50b6feeee904060222d,0x810e47919e741446f29,0xc4c5f2b0810ccc5d6db,0x397ea1026557d5d5b081,0xc568454071ff6ab0a814,0x5d640e1575e29623203b,0x5e117c379b1752c2945c,0x223388c5e15d1c2711a8,0x20e41630e41633388ce,0xd28338125b9c1994e047],#[0x42a655f2351319a5078c,0x2e7268af591a7deb1d73,0x515b30b1c3f980684934,0x4a8143557f38f146f909,0x7fe190460fa10323bf91,0xcc6447207ae072b1421a,0xe335127e321edc545167,0x963b7f4b1e28ee0c9645,0x4ef065ca98e9279061a7,0xca07f19109c392a10a4e,0x46243bbf34d284aa74d0,0xc489792e12a171fc1a90,0x28689cfda8142680bc52,0x2758f1623aff852c46de,0xf2f27631035a203f48c6,0x342c9a1009793a5532d0,0xd2e8491cfda48d6ff136,0xac48ccec5bfa80d0cec5,0xfcbc0bc0486805e0a787,0x493569f445255c4228f3,0x2f6412a1ad13381f8410,0x8c200f0bdd9399687a7c,0xa107a715a11e8bf31d8f,0xb115f322f1434487ed40,0xcb099e77426a7c9480d0,0xf318284ffe0d58804269,0xbbbf91828eb7d08ca1fb,0xd498c2f3a2008bc45046,0x684cb0efd592285e744d,0x5f24a92688d451b5f072,0x7881123ff4e625819ca9,0xb33fa4913877a6b6b19d],#[0x19d4f20d466fd37d2402,0xb868664ca0ebff805792,0x4fd7b046cced8c397c08,0x560046707919f4f4a193,0xe099848503f0222a7ffd,0xd0454f368d2cbb7f90f1,0x6b9f9085dbf02042cf91,0x40d65ffe008d560020,0x51260a206baffe01998c,0x2120d9d9805091ffdf1e,0xefc06a067778b412129f,0x8e7670b08f3315a1193f,0xe8576645be21147bac21,0x2983c4d08a49185fd246,0xee4c6101e8802e7ccc10,0x9175fac917d81080f455,0x6552a49f60f851a2da59,0x232a7ffe361648cef79,0x6672fc3ca080cd5fe58,0x80108967dd046ce90fa6,0xfd102042d3e4102135e0,0xe603477d7e687f708d1c,0xc2ffc033890ddf5db2ef,0xe31a75f8c76f92a50810,0x126b460642275f8c69d7,0xa9a66dc654d336e32867,0x30148d9a4319134cdb8c,0x655c4c48c96e79b32efe,0xc8777e1640a03f0c0226,0x11925056b486be321af8,0x918e9d635601021dbfc0,0xc4c81fef144ca86023bd],#[0x10e3f9894f1d4648e5f8,0x64964828c306648b0cfd,0x68d05869d707e672ee92,0xa7043b5fe88a5869d775,0x8668701a0db0d2e50ccc,0x6dde09475ec8cad42af2,0x48b0fbcd2832e51e7cc6,0xc243eeb56e60c681f824,0xc8975d2f09488e551907,0x33af812226b2634fcbac,0x68c95c234644ff484301,0x1236ba60aefc3c898b8c,0x6262450fc30089995713,0xa9f9031a027911cf190f,0x4aa123e90320b83a1010,0x3ac524d09df36e9969ba,0x28dff884e1935513d5e0,0xcc0ac7800044920e9c42,0x4031a35f180a2ac36bfe,0xe13e70330d450fabf7a1,0x4cdb8c8642c899f04217,0x7ecb0f1889088c156c84,0x4244445a3c0a198b2180,0x74b30d00fd9e5fd81295,0x528ebfe9248244127f32,0x52f8631de88e0f5940a4,0xa6489edf220655bdf894,0xf7372106a286df24633e,0x8abcdc85270ff40342c3,0x70664af524640d3d98dc,0xc3f96322f7c072833354,0xc8834fcdf60659e40508],#[0xd7758640fda9b9619b5c,0x3e1cb902cc40b463ccd1,0x3626f02638e10c39b99e,0x6fa2c72c66579250844d,0x8d85031a13e526f32902,0xe38251b03d08f3317f6f,0xd7b231c5c8ebc10322d,0xc49dd3dc18209a31c0ca,0x8f8f04c05e2186388619,0x57021e200c83f7f4654,0xc061f8c05232fc08a450,0x78df018cf237bf128c37,0x5177624840e441c88bfa,0xfc7992d70634a7da90e6,0x9c12b4bc31932992590b,0x3269b16b9f4084be22bc,0xdfee588e808becf72a04,0x177285df8d630fd231a8,0x8527b9b832161263f502,0xce4b7f20602189af8c0e,0xbcf440a042d7e1e3c140,0x1a278379a2f8897c0508,0xd3dcbc3800200d2dc,0x33069dade658b6be0c1,0x7a6f89330003617f0008,0x88a0d1206ff58466ff49,0x62406f08af088bfa78df,0x141d158bcb67086008f2,0x9a20b19b6f1b0a440be0,0xd994035065063c312de3,0xa292144c7fc4c8dd00d3,0x6204616336dacb0cce4a],#[0xc1199fb61137688020fd,0x58ddec1c593d99338175,0x5ba195f996e837254191,0xea043e3c10400acdfee8,0xab01a176ef51509939ea,0xd9963f0463000000064f,0x2c3e1a0db0e96648b755,0x435a6fe0c8436dc7ea04,0x1d58f7a8ca6453d77c90,0x5d37a5855bbb7b30436,0x31a5799ff88681a0ab8,0xb40372022bbf0cc71fa,0xcade430257a59969e92a,0x25e6a2a847f1019a1d89,0x8e7b09c721b866af4b32,0x8413e43f415448d86e68,0x4a1091e4c46e051eaf86,0xe0c104d12835ec8c6af2,0xf81148d4e0433892bc3e,0xc8ebc23193c4680a0335,0xd018081444a0d7b231c5,0xc3f180a460ce2437edf,0x200c88e43dad03218cf2,0xb5b4107220e442e39afd,0x2fc882420bf3120d3f18,0x9404d46f93fa0531d0e,0xfe0c0c04cedffb7fe104,0xff82501336bf830e84ef,0xfae6a468e4bd295121bb,0x4077e4c7648ac914735f,0x470f20433731f9fe2283,0xb818e66c79cb199002dc],#[0xc9a51cbf7a374c2f8e0e,0xac903380000039b5a2c3,0x264cc5d47c903377f837,0x7843e7d20e12163e15a,0x9141f0460185e7c78108,0x1939c0cc477c48dbef88,0x18756a749247dd0a75c8,0x9a1a31c8991dfc895142,0x8c736e3d248f0feeca44,0x218ef8891edf2060c3ee,0xa87e40c8ac9c126ba132,0x64671420d3db0d366267,0x283d7043e7ec915b6fe2,0xd09ad9e230a153f88323,0xfcf87025428d826b06ad,0x84074c907cf870001850,0x2c095460038943074c40,0x851e947272a8bae82a8e,0x109a39c0a0f7a241ef44,0x87c7fc7888854ed2f0f5,0xc16aa81a427f24ca3440,0x44338a1069ede6191133,0x87cfd922baeff0651221,0x644cff90379666707ae0,0x1096f2410be4c0c841e0,0x5d0551abee455080e988,0xb8da32a1d0f5d0551807,0xa929215b55a790433d7f,0x3d7930033f7a795326ba,0x6ae7fee68d9ad83920f8,0x563f9157076751d73c44,0x844d436d6251f7fb0132],#[0x36982006021e227fb6ba,0xc51e8c8994027beb0046,0x2321d0dbe40c1f381ae8,0x7bc1440708a4849eadf1,0x487ae5543212193c318c,0x303c218712f45f34cf38,0x9225f7e310513fc90da0,0xbc1318e250fbd898f67f,0xe81419f960977fe00117,0x1436ffc0022fdc80a8dd,0x115bdac1d033524fb291,0x5fe204600222361de6b4,0xd9ef128a0f9ccc14293d,0x5e4ac9842d3e86444086,0x48bc8871f8244572e20f,0x8cbf8909ae2920e9c197,0xa796b56067ce18b2c945,0x301a15bfc15320df6a24,0x10aaf34135975a8d9f8b,0x510a7bc12da0637aa9bc,0xafc51195d97107a27ee5,0x16d0303c4a837cb681db,0x8af3412bf1650c85581,0x433f7bfc4802a27ee551,0x8fc714c956f8d89947f2,0x55fc887dfa444653cc23,0x20e36467848f5f1a8868,0x64cd290c85b70664c722,0x74ec4d03cfd248a5b706,0x45693376e1850edd3f55,0xc871e06e8642d90d88ac,0xc79fa00047c77789a10],#[0xfc4802aae326e32d3d32,0x1f37a26328bd0a833f7b,0x1f7cd36630a1a3647262,0x28a3f7cd3662000088b2,0x1437da1fb43a65383fbe,0x1aa9c219236167e6f4c0,0xa57f2c4cd6f360f930a,0xabe8875f83b0f9626800,0xcd0b43899181f468b070,0x9a3f88632377fc3daba8,0xee61424f06448f194599,0x74cc6b0a38943b7920a1,0x9b9d3bb24273f49e484c,0x7e00ff2c4cedf1e9c109,0x7b985095f98d1933db15,0xe72806500ff8a64b1c18,0xf1f9c9119431f44465c,0x9195c31a1d9f9a4ae209,0x5f1385e85431f961233f,0xcfe94a666b3930020297,0x244698d9197fd2811973,0x9dbef3c119bbebb65e7d,0xa1a507917e801090da83,0x889412da0637fc52210,0xbe801104af7cd3662000,0xdfa0a208edfab2322ffd,0x1ff629957fefd051048,0xb0be3812336538e0c0cc,0xd3f070151b5c5f2002a1,0xdc809081a90c76bfe990,0x14c70e8c62a42c65bffe,0x2354c8c7e90444740cdf],#[0x4004a3215f210ffd488,0xc531ef9f02c11f7fe6ea,0x22a0dbe6f60b2c7a46df,0x65ff4086651a0d3a466f,0xc209237b5eefe447b364,0x4c89ed869b3133effd07,0x5b9be24465f922236dfc,0x78f4600671e06448b0f4,0xecfe2001240e1cc25270,0xf04f4466d3b543d85d1f,0x18cb2fcc7ded7ca996b1,0x3c4467aad7f329b307d1,0xebe2232bb81770358fc9,0x884988487d4100c6b055,0x404d499f0c889999ff8,0x23bf7e82542d7b791066,0x2bae1ac7da080d33ae2a,0x8303513eef7a04d41a2,0xd5d59a7a443575f3ec72,0xdadc22a915d59e723021,0xfb67000312264d6e7518,0xc6a187cbf3200c8d1af4,0x4b81e149cbe8a8104879,0x6266eb481f7a3dacb0d5,0x6be11134b53ca1976cd6,0xb91da16da7010a173821,0xa08067d3f1632d968e74,0xd0d4091be58ff302049d,0xcc9a60d4ad1f9664cb1f,0x80021456c86442c6a54b,0xf6189448d2c3f008de60,0x1dffa5950a8796b1548],#[0xb874f0a16ce8c82e4353,0x6211d7e9218023c5441a,0x15fece146110112877e5,0x220067a4326df208052f,0x915fde198010034a67c3,0xff32b100481ffd0f0100,0x1112f570f86318511b,0xa527ec22a1a5ead5c4e3,0x8537d600542c3f485426,0x6cda2dbe2931e2f9b0c,0xf360872f844f57cbe240,0x2ead59d181025bb8004d,0x9f149ae010b642c8f032,0x70e089de2008008ae12c,0x200101108e933bd0286d,0x85d55cc7108faf05bf9,0x6019163f3b8118dc9e48,0x1a33e19100331e611d79,0x839acd4087afef0cc100,0x10a05dfed853c01a3ddd,0xc031e0517c033022c780,0x3377f60800cc38843ef,0xdbffc01064021f3e1910,0x6c5cc01881b76f3c522,0xbbebb7997e2a68efaed9,0x100872f114c997f81011,0x6c4ffc460021f583c300,0xa04457db936ff40a069b,0x197c00402201dd2fc100,0x3010a8cbe002010d2f15,0x86e1bc72711850e2d9f2,0xd3b9e441a961fd0e0a63],#[0xf6c91081ab4ee79106a5,0x836fea0d92223457f27d,0xebf244586ae28423bd02,0xb0121b7fef3ef9450254,0x40d0dfa7c2103303d17c,0xfe0d80523477f27fb654,0xf0840ce2c9e689c0866a,0xefe4fbed95103517b7e9,0x201ab3dabf8360148d25,0xf6c0381a5bd8461f87c0,0xb77ea783101036417b67,0x386f1c9c46143c17]]
def g63H7 := limbs80 #[#[0x331c0704260101030a01,0xf000201081b120e0015,0x34360a040a01162703,0x2e021b5e0f060c530101,0x3b350201c95206070001,0x2c0a0443c10c0204003b,0xf0c4d9d8f0e05e30011,0x11122b133d0c8602131c,0x5a5402dd0007157a1201,0x1d023b02650269010647,0x9531f44006085a000552,0x2681730ad62f650d5b,0x29d97952aa7b71d67e00,0xa7a9c16bc942099dd248,0x55cafc92804e62e4000f,0xace39de1da19b88d8000,0x81d6f2820f957fe39a96,0xdbbb60c06a5a7acfb62,0x3da04bdf0b0003c53f8,0x180bff58c001ba8bd1f2,0xb9630d3469035cd70024,0x8b1000181481e540d,0x96ab68bc6ba2718dd6f4,0x4b680000af80e92e,0x500024cdcfaf03a26c00,0x48cdd00ce86c94dec669,0x7a4d5794d9257fb9c3,0x42a98cd7fa6799d80b0,0x6a474d1a075263767484,0xfe2dc5bb807042c6c439,0x8220f801acd327c842a5,0x9a145c888521c327050d],#[0x40ba5e5551beb02d2ee,0x675965e6d928d6670877,0x1872552c508c64e0fc4e,0x5bf9309d61026bd4631b,0x972433646611bc656a13,0x83ad651434e8599e2d05,0x4e96932afbc3c8ac0829,0x3543f6af60b7e5d710b8,0x22aa878c9a1c75ed9acf,0x48833856d1a4b4a842e3,0x7505a74aac95d8d7dabf,0x40003253c404da72d79e,0x51c4486ebd0128f60295,0xc848500008e5c02911c1,0x35b70a000f92a84bcdf2,0x62dd0296b462e44066fd,0x44f42b7717bcadf9357,0xc46177fb3c400052c000,0x167a4609c41d5eb3,0xc573c34186b9cfb04900,0x96c8faed4ac068281ee9,0x6df8eea12cce2e2351ff,0x392849e553d23a961,0x296d52e8690003e9771a,0x1e2ce9d8026d4c59db0a,0xe25e8a532195991a17eb,0x758639325dab265f9921,0xb5fc9921d08368f558a8,0x2234d71a3cecdd4a9,0xc871822b3aa877b521f6,0xb4cf5b5a27f91967f3be,0x65d58ed9b23b5420e9ea],#[0x5600069bf06b2328c155,0x44d59de56234d079b9a4,0x46777c72fc56d4911477,0xb68caa6077109e615643,0xd3442f37494d35b224e8,0x3245dd60d0955d2879dc,0xa8000d020720148a524d,0x8c0007dd4000e31604f8,0x460001564d4e00000013,0x4c469b11a428180d2d0e,0x7bc8000000d61d2768d1,0x4000e6d9ba5d57d0d97c,0xfee59c612ca7435b8c29,0xce0008a23890a8247ae1,0x90629e0066175ca498b4,0xd0b6914d4daeed414f7c,0xe1e003227f3923778dc1,0x2488873283aad26f1960,0x2fb74bd6a44ccbb7540e,0x3b85c35a0cd0002c5f51,0x526481a87ecb27cb2e2a,0x159932f0c0c4fa11e9,0x3e5808b1d5c78]]
def g63D8 := limbs80 #[#[0x100100c8100c01008010,0x508104c81010c1010810,0x8801058c105881050c10,0x90810900108c8108c010,0xcc81098c109801090c10,0xc4200c020d0c10d0810,0x4c42010c201042010020,0x54c205442050c2050420,0x8c02058c205842055020,0x90c2090420900208c420,0x980209502094c2094420,0xd0c20d0420cc42098c20,0x58c215802150c2110c21,0xd0c2198c219802190c21,0x10830104301003008430,0x4c8304c4304c03048430,0x5443050c305083050430,0x58830584305503054830,0x8c4308c0308843059030,0x9083090430900308c830,0x98030950309483094430,0xd0430c84309883098430,0x4c43110831d0c30d0830,0x5883150c31508314c831,0xd083198031908318c831,0x54c3250c324c832d0c31,0x98032950325843255032,0x8440d5032d4c32d0c32,0x4c440484400c8400c440,0x5884058440504404c840,0x8c8408c4408844058c40,0xc844098c4090c4090840],#[0x4c8410c841cc840cc440,0x980418c84158c4158841,0x5844214c42cc84198c41,0xd4c4298c429804258c42,0x98043588435844350c43,0x4c85010c50108500c850,0x8c85058c505885054850,0xd0850cc85098c5094c50,0x10c51108510c851d0c50,0x8c85158c51588514c851,0xd0c51d0851cc85198c51,0x54c53d0c5294c5210c52,0x10d10109100c91058853,0x4c9104c5104851018d10,0x8811050d105091050510,0xc851090d10909108c910,0xd0910d0510cc910cc510,0xc520d8d10d8910d0d10,0x4852018d2010d2010520,0x50920505204c9204c520,0x905208c5208852050d20,0xd0520cc920cc52090d20,0xd8d20d8520d0d20d0920,0x1912118d211812110d21,0x50921505214c9214c521,0x5512154d215492150d21,0x595215912158d2158121,0x981219512194d2190d21,0xcc921cc5219912198d21,0xd8121d0d21d0921d0521,0xc53008530d9121d8d21,0x10d3010930105300c930],#[0x88530509305053048530,0xc853090d309093090530,0xd0930d0530cc930cc530,0x109310c931d8930d8530,0x19131189311813110d31,0x55131549315093150531,0x951319493190d3190931,0xd0931d0531cc931cc531,0x14d3210d32d8931d8131,0x19532191321853218132,0x90d32551325493250932,0xd0932cc9329513294d32,0xd8532d8132d5132d4932,0xc9400c54008540d9132,0x4c9404c5404854018d40,0xc85408c9408c54088540,0xd8940d8540cc940cc540,0x18d41181410c941d8d40,0xd0941cc9418c9414c941,0x18142d8d41d8941d0d41,0x18143d8d42d854218d42,0x18d500c950d8943d8543,0x8c9504c9504c55048550,0xd8550cc950cc550c8550,0x18d5218152d8d50d8950,0x18153d8d52d8552d4d52,0x18d5418154d8953d8553,0x8210d8d54d8954d8554,0x10a10102100ca100c210,0x1921018e1018a1010e10,0x4ca104c6104861048210,0x54a1050e1050a1050610],#[0x58e1058a105521054e10,0x8c210882105961059210,0x90e1090a10902108ca10,0x98a109521094e1094a10,0xcc610c86109921098e10,0xd0e10d0a10d0610cca10,0xc6200c220d8e10d8a10,0x1862010e201062010220,0x4c620486201922018e20,0x50e2050a20506204ca20,0x586205522054e2054a20,0x8c220886205922058e20,0x90e2090620902208c620,0x986209522094e2094620,0xcca20cc6209922098e20,0xd8620d0e20d0a20d0620,0x4ca2110e21d9220d8e20,0x58e2158a2150e2150a21,0xcca2198e219822190e21,0xc63008630d0e21d0a21,0x10a3010630102300ca30,0x50a30506304863010e30,0x58a30586305523054a30,0x90a30906309023088630,0x982309523094a3094630,0xcc230c863098a3098630,0x10a310ca31d0a30d0630,0x90a3158a3150a3110e31,0xd0a31cca319823190e31,0x95232586325523210e32,0xc64008640d523298232,0x4864010e4010a400ca40],#[0x58a40586404ca404c640,0x8ca408c6408864058e40,0xcca40cc640c864098e40,0x58a414ca410ca41d0640,0x98e41982418ca4158e41,0x9824258e4258642cca41,0x9824358a435864398e42,0x4c650486500ca50d0e43,0xcc650c86508ca504ca50,0x58a514ca510ca51cca50,0x98e51982518ca5158e51,0x9825258e5258652cca51,0x9825358a535865398e52,0x9825458e5458a5458654,0x10f1010b100cb1098e54,0x58b1050f1050b104cb10,0x90f1090b108cb1058f10,0xd0f10d0b10ccb1098f10,0x4c72010f20107200c720,0x58f205872050f2050720,0x98f2090f20907208c720,0x10f21d0f20d0720cc720,0x54f2150f21507214c721,0x94f2190f2158f2155321,0xcc72198f219832195321,0x1073008730d0f21d0721,0x4cb304c7304873010b30,0x5873050f3050b3050730,0x8cb308c7308873058b30,0xd0730c873090b3090730,0x4cb3110b31d0f30d0b30,0x54b3150f3150b3150731],#[0x5933158b315833155331,0x9533194b3190b318cb31,0xd0b31d073198b3198331,0x54b3250f3250b32d0f31,0x59332587325833255332,0x99332987329833295332,0xd5332d4b32d0f32d0b32,0x487400cb400c74008740,0x58b40587404cb404c740,0x8cb408c7408874058f40,0xccb40cc740c874098f40,0x50f4150b414cb410cb41,0x983418cb4158f4158b41,0x5874214f42ccb4198f41,0xd4f4298f429834258f42,0x9834358b435874314f43,0x4cb5010f5010b500cb50,0x98f508cb5058f5058b50,0xcb51d0f50d0b50ccb50,0x54b514cb5110f5110b51,0x94f518cb5158f5158b51,0xd0f51d0b51ccb5198f51,0xd0f5298f525535210f52,0xe9ecee5f1f98f5458f54,0xf7fbf5f6f777b7d7e7f3,0xfbfd7dfefb7bbbdbebf3,0xf7fffefeff3f7fafbfb,0xb0ca3dd85b20e0749376,0xdd89004ecb201762b45b,0x82c40029710001bb15e1,0x5ca6002cabb000d59400,0x2dab281705880b52e20],#[0x2802f58c0152e2009776,0x98c0c52e2061576005ab,0x52e2019576031ab2818f,0x115720454b881c65d403,0x8cba804d994026aca0,0x100cadc40658e0031576,0x994066aca033e6301a0b,0x82c4069776018dba80cd,0x99576035b3281ad5940d,0x4db32826d594137ac60,0xb00865d4046cca021576,0xdd8076cca03c16201cab,0x2aec07b66503e0b101e5,0x2b665014abb028d99414,0x21b32810f98c082aec0,0xb020d994107ac6081776,0x5d81532ea0ab665054ab,0x94ec5d9572048bb90145,0xfb7652d61b116ab1c0b5,0x2fdbb297f0d88bf5ce05,0x296cf18cb658e05b1676,0xd8cc05ce06014762d9bb,0x58e05c1676301bb2980f,0x8ae702c4cba984b9c0c2,0x2c5fb19630d88b152e25,0xb16265d4b16eca58b465,0xdd4b76eca5bb4652dcb3,0x78c65e2e702f0a3b16e6,0x96762f1bb2978d194bc,0x305bb2982d194c186c46,0x1164a5c4b25ce0591676,0x9d8b232ea5934652ca1b],#[0x5ce05e94762e5a329725,0x1c36230cb3b17ad194bd,0x2cd4b896659d8c368ca6,0x817459d8b368ca59bf63,0x194be28ec5d34652e963,0x68ca623c63310b3b17cd,0x315722d0b3b18865d4c4,0x5e20b12dea5c56f2ae46,0x8b0d05898652e2c32f76,0x98986c2c4c36a7161b4b,0x52e2c3bd635c14b8ae18,0x499755c94b8ae4f98d87,0x64a0b12f2b1c17952e2c,0x1af4b1c17a82c4c92e70,0x1c17c7ac6c9ae7064df3,0x5ce0b8997565573832ab,0xd96765c4abb2e265d571,0x5eca3b2f66dd57b56e2b,0xb31055d9885ce0c41776,0x9c1732cecca1576650b3,0x2cecb995765cccbaae6b,0x52e70628bbb2fa51d97d,0x658abb32c59d98a2aecc,0xb2fe51d97f56e2bf9676,0x9d98c2aecc62e70630bb,0x86c4c7c36260a0b12ea5,0xa457166253833065d58f,0x5f96382fc59d9742aecb,0xb31655d98b2eecbf1476,0x9d9972aeccb997565cb3,0x2aecc69776600a3b3005,0x195725d9eb1aec59d98d],#[0x641fb1b205dc98336eac,0xb30251d9812ae4cc9572,0x591772cecc71576638bb,0x52e31cbb64644cbaaeee,0xc99758e5d32472e59239,0x8f1f31c78b1c23c2aed1,0xb4786dd63c74c91e3964,0x5da4174c920b964904bb,0x74c922b964915eb1c8a5,0xd19758e94b8c7455da45,0x918abb4845dda3d2aed1,0xb47c55da3b52e31d9576,0x5da4732eb23957690cbb,0x4ae40b1572910bb94805,0x1a57208cabb02cf58c16,0x612b903055d8237cc61,0xa02e75d0174ae4129975,0x5841b58e00d957605cf3,0x2eec0dbe6306d3b90371,0x69576090cba849158424,0x70abb03255d82d7ac61,0x84c5dd81c4ee40e4561,0x5d82e32ea17157609a2b,0x2aec1445610a22b083c5,0xebe6307563803a55d81a,0xbcabb04ef58c272eec0,0xb03ef98c1f2aec179975,0xdc4222aec14bd630a4bb,0x2aec151776080ab88585,0x5b86432e3b0996b1c0cb,0x3463b09a2b9c0d176c86,0x98eb9c0c776c868b864],#[0x190c77ec663a57231e3b,0x3ce8639d7431ddb218ee,0x63b64331c3219859d8c7,0x349e319a4b9c0d228ec6,0xb1a465d4d276c8693864,0xd90d570c86ac761354b3,0x4ae4642e70320b3b1aae,0x9ae7034ca3b19c59d8c8,0x334b3b1ae65d4d72cec6,0x219ae190cd78c666ac70,0x9c0d628ec669b75335db,0x76c86b3864359fb19acb,0x4ae7036163819e59d8d6,0x340b3b19295c8c95ce06,0xb1b265d4d92cec6a1476,0x5c99a2ae26d9571328b3,0x7cc6d7a5726bdeb1b349,0x125726c4cbab3895c99c,0x6b973835d1585a258e0d,0xa33675d19b5ce0cdc561,0xdc9a32ceccd957666cf3,0x5ce0d8177668ca3b3469,0xd16766c0abb36065d5b0,0x67573833a59d9ba2aecd,0xb34a9dc9a52cecce9576,0x5d9b25ce0d91776694a3,0x2aecde19756f0b3b3645,0xa15766d173836859d9bc,0x6dccbab3f15859f2cecd,0x834879d1b73ae8dbc761,0x9c1bb36ead23e6369163,0x5ce0deac70699eb1b76b],#[0xf157667973833cb1c1a8,0x6ccbbb34e51d9a72cecc,0xb37c65d5be2cecd99576,0xdd9a928ecd496766f8ab,0x7ac6d016766d4abb36a5,0xc3f636e0bb8b5855c5a0,0x6a8ab8b8065d5c02ae2d,0xb36c55d9b62eecd51476,0xd91b932ead0b964684b3,0x3ce9241d749212b9490e,0x5ac7092cabb490d59648,0x940bbb496d5964b7cc72,0x1ca855da5032eb283565,0x5ca492aed2a3565951eb,0x2aed289776930abb4929,0x52572928abb4aa65d655,0x934abb494d9964a7ac72,0x2ca45dda4d6ccb26ac70,0x996567cc72b1576949b3,0x2ee3279576958cbacacd,0x699750e50b987255c653,0xe10b9870b9c03842e62,0xb07065d4383ce81c1d74,0x5883c8ac21e2c700f0ab,0x2eec1e15760f11b98790,0xb4162158abb093158449,0x12ccba8965dd83e2aec2,0x98811584402aec1d1576,0x5844e5ce02717761011b,0x2aec2b997515cabb09d1,0x821731422b08a1158443,0xfcdba87e5dc8462aec2],#[0xb07665d43b2aec261776,0xdd84182c420ac70104ab,0x2aec27a17313e0b109e5,0x223731120b108855d858,0x11cabb0a30588512eec2,0xb0b265d4592eec211771,0xdd84546e622ac70114ab,0x8ec27d2e703e8abb0a45,0xd38643e91399f50d88fa,0x3e8f3a1f475d0fa76c87,0x220059d8fa32ea7d3765,0x1d9006eca803b64401c3,0x70c881c36240cb3b2005,0x3967640dbb2a06ed9103,0x41ddb220ee191078ec28,0x21f6e190fb2cec83b765,0xd94fb3ce87d9d743eddb,0x76c8843864420b3b1f6d,0xea2733f4b3b210dd9508,0x428b3b20851d9012cec7,0x21f855c90c2cec851975,0xd94fc68ca7e3b643f1c3,0x70c88496763f0cba9f8d,0x4b765425a32a12ed9109,0x3f91399fcb9c0fe2cec8,0x2a0459d8fe32ea7f3465,0x9d90568ca829476409a3,0x2ae286967642da32a165,0x33465418b3b1fed194ff,0x774cbaba289cdd12cec8,0xa39c89cdce5ce0e72273,0x5d9ce32eae71e74738eb],#[0x2eecea9576755039baa5,0x79d7473cabb3cc55d9dc,0x759039bac55d9d23ce8e,0xb3d065d5e82aecef1776,0xdc9da2aecf02273780ab,0x32eae81e74790eba3c85,0xb957674ccbaba6b9c1d3,0x7a4abb3be89cddf2eece,0xb3c25dd9d840e6ec1576,0x1cdd932eaf2977176cab,0x5ce1331576788bbb3b28,0x31e74998eba4cc85ce66,0x9a56384d255da6632eb3,0xb4ec55da712eed349576,0x5da6742e73399759c8ab,0x2aed3a2e709d0bbb4d85,0x597729bcabb4ee65d677,0x9a0cbacd085ce6836eb3,0xb4ea5dda6d58e1369576,0x5d6792ee33815769e0ab,0x44e637a1731bd7380de6,0x945611c8abb0ded5946f,0x1c8abb0e4d5947282c43,0xb0f2d594798ac23c9776,0x5d87f6aca3fc1621fcab,0x8ac23995761c1ab28e05,0xd17761cdab28e6f98c73,0x1e9ab28f515847a5ce03,0xb100d594807ac6401576,0x1cc7572c63ab9621d4ab,0x6cca38b5651c4bb90ec7,0xa41621d16380e855d871],#[0x1d1b328e8d594747cc63,0x28f6d5947b82c43d9776,0x594817ac64095761edb3,0x3ae23e1576205b32902d,0xc1d711f4bb88ee79cc7c,0x1f8ab88fc5dc8782ee23,0x9a6b0d89355ce09a9572,0x1d9392cec9aa2734d50b,0x2cec9e43624f0b3b2725,0xd16764d9fb1a6c59d93f,0x500b3b27af18d3d28ec9,0xb26eb9c1372ae4a11676,0x9d93e28ec9dbc634ecb3,0x2ae2a19676505fb1a825,0x21571510ab927055c538,0x7e90b9bf4b9c1fa2ae4a,0xb3fe55d9ff2aecfd2273,0x5d9fb2aed049576814bb,0x2aed051576818bbb4005,0x11e73831cb1c18e58a0c,0x7f17383f8d1d6022ee50,0xb41655da072eed009576,0xdc6033ce6fe9d717f4ab,0x2ee5021771810eb8bfc5,0xe2e70a70ab941055c608,0xa7cabb53889ce9c42e74,0xb55255daa52eed4f9576,0x9c2a62eed501576a74ab,0x2ee5511576aa8abb54cb,0x39776a8563854255da9e,0xa90bb8d4655daab2aed5,0x955055c6a82ee5521771],#[0x98c9782c44b9576250ab,0x2aec4dc16226cbbb12ef,0xf9576254abb13cf58c9e,0x258c39930d58c982aec4,0x913465c89c2aec501576,0x9d95828ecac1572274bb,0x78c6ac96765723b0ab85,0xf9676575fb1aba51d959,0x568b3b2acfd8d562ae4a,0xb2bc59d95b78c6ad9476,0x5c9572ae2ab9571580b3,0x2aed601572584ab8ac25,0x9576b20abb58c5ddac3,0xb09aaa58855dac92aed6,0x958e5dcac52aed651576,0x50c329086193554b1cab,0x90861acb430ca5218652,0xacb430d652186b250c35,0xd653986b25cc3590e61,0xa06b25d03590e81acb73,0x994307ac6184b740d653,0x7cc618ab710c4abb060d,0xa3d630d0bbb062d99431,0xddf3186e55d8346cca1,0x806655d83732ea1bb665,0x1d0337ee019bc700cca3,0x7ae01b16700d9fba066f,0xebe740d9eba06cf9c036,0x3a11b99d081cce892c06,0x1de6dd4e83ee8741c74,0x5c8f278c67027723825b,0x4ae47a2772389fb19e49],#[0xbc633855b89c265d4f4,0x38dfb19e6a5c4f336ea7,0x89b8adc4e552e27aab71,0x1d8e42cec6e15763714b,0x2cec7615763b0bbb1c85,0x316763d8abb1ec65d4f6,0x3b4abb1da5dd8e628ec7,0x81d259c0de7ac66f1676,0xdd0e938e874af703a563,0x2ee27494703a4dba9d27,0x816703c1fb19e05dc8e9,0x39cb381f055c8f02ae27,0xb1dc55d8ee2eec739476,0x5d4f176c878b96437cb3,0x36eae1be6370d5b8b866,0x62b71711eb1b96a5c5cb,0x714abb384a5c5c252e2e,0xb39a65d5cd2aece41776,0xdca582ce0e5147071cab,0x7ac731a57298df31cb09,0xb99759912b94c89dca59,0x978bbb4b4adc65a2aed2,0xb4b655da6532eb329576,0x9c26228e12e957697cbb,0x2ae4311576980bbb4b85,0xe3a64171cb20b8f98c5c,0x181cb20c05dd85c36ea2,0xb0b465d45a2aec303a64,0x5d8612eec2eab71174ab,0x2eec2f147017cabb0c65,0xa1572444abb0c865d464,0x438cbaa3c89cd1e40e68],#[0xb23a59d90e32ea872273,0x5c50f44ec8ebe76474b3,0x2cec87997543d139a1ea,0xf9676461139a3051d915,0x469139a3451d9162cec8,0xb22059c12132ea891676,0x5c51b28ec8b9676464b3,0x2ae4f8967646d139a36a,0x919757a9b32bd4d595ea,0x7ad4b8bd6d995f26acaf,0x2bda55d9eb32eaf5b665,0x5d9ef6ccaf797767b5b3,0x28e0f715767cdb32be65,0x9c74a05b32be0d995ec,0xa291b9cf855ca883ee94,0xacf66dd67b32eb452173,0xdda7b7eed3dd3759ee83,0x2aed3d19759e90b9cf48,0x2a173a14bbb4faadc67d,0xa18bbb4fe55da8b2aed4,0xad1851c2822aed432173,0x5da8742e7439776a00cb,0x56e2419576208ab910e5,0x49576218bbb106f98c83,0x214a3810855d8897ac64,0x911059c0882ee4429470,0x5c5456ceaa31572518ab,0x2ceca49476520b3b28aa,0x69d7352cf3829659d94a,0x51ceb929879c14c2ce0a,0x929c59c14e2ae4a39670,0x5da0d52e3069572848ab],#[0x2aed089776839f31c1c5,0x8147083cabb428f58e14,0x84cb384265dca1028e10,0x2d58d596ac2ae5599572,0x596ad56e3569576ab1b3,0x6acb591776ab5b32d5ad,0xab565ad4abb564d996b2,0xab8e3855c55dab56ccb5,0x955e71c2af28e1581f73,0x9c2b42ee5589470ac4fb,0x82c4521576284ab95685,0x3c16229cbbb148f98ca4,0x288abb152f58ca92aec5,0x8946d550a52aec551576,0xdc8a62aec55957628d4b,0x2ae51535542a0ab91505,0x49776899f31c4c55da25,0x89cabb458f58e2c2aed1,0x84565dca2828e1141470,0xddace2aed6595728acb3,0x2aed661576b54abb5a45,0x69873b3dab1d9e55dad6,0xb4cabb5ae55dacd52e36,0x88d655cad42ee5689972,0xdd8666cca3314701a4ab,0x34ea3619751b1b328d85,0x415761b4bbb0ce55d86c,0x490abb0dc55d86a2eec3,0x2a6455c5246eca923465,0xd95253ce8929d74495bb,0x2ce099b7654cda32a66d,0x420734a1bb2a5cd1952e],#[0x4a5a32a5e89cd2f68ca9,0xb244d1952244e6982073,0x9d9232cec95b4654acb3,0x2cec9694764a8b3b2585,0x316764c5139a6295c931,0x49da32a68dd952668ca9,0xb3ea51c1f62ae2fc3765,0x5d9f94ae4fc95767dcbb,0x2ae34a9b75a44c3ad225,0x69a75a58cbad2c51c292,0xa691b9d1e85ce9846e74,0xb52069d69932eb4ca173,0x5da9b42e74d9576a50bb,0x2ae2469a75a5ccbad2e5,0x795762292b911451c08b,0x238bb891851c08c2aec4,0x82a255c54f2ae2471670,0x9c1522ae2a81670540b3,0x28e10a957185cab8aa45,0xc1670860bb8c2c51c216,0xad8a3856e55c6b92ae30,0x857055dabb2aed5b2572,0x5c6ba2ce15d1771ae0a3,0x7cc65715762b1eb19585,0x19670594ab8ac455d8ae,0x598b382cc55c5632ce0b,0x845c51c22d2ae3179571,0x5c6302ce11817718b8a3,0x6aa96d1576b6cabb5b05,0x8957224cab89266dced9,0x249ca19225dc89128e04,0x8aa671c0902ee2491470],#[0x5c9542ce0aa157254cab,0x2ae30d9571554b382aa5,0xc9772864a3843255ca1b,0x870bb8c3451c21a76870,0x857a55cabf2ae35f9e70,0xdc6be28e15f1772af4a3,0x2ae2b3b5542c1aa99605,0x495725a0b382d055c967,0x8ccab8c6655c5692ce0b,0x84645dca3128e1189572,0x5c56a6ea71917718c8a3,0x2ae4b616705b0ab92d45,0x596705acab8ada59c16d,0x5b8b382dc55c96b2ae2b,0x946e55c6372ae4b71571,0x1c2352ee51a14708d0ab,0x2ee31b14708d8bb8c6a5,0xc15718e0b384705dca36,0xab95ba5dcadc2ae51,0x1817358c0b64e6004e63,0x5880c9ac400b27302e73,0x64e601ce6300e6b10073,0x8cc320466b181d35880e,0x1279902338c8119a640,0x981ec1cc0764e6024e63,0x1c00964e60a4e6305193,0x9c8604cd430266218133,0x4cf730266398133d0c09,0x2ef8989773dd00998e80,0x1977cd04bbe2825df331,0xd0cbbe4865df1432ef82,0xda825aed312d783816bc],#[0xab1732d67b196b318cb5,0x2d98b997f318cbf66e65,0x916d74c8b6da825b7070,0x1d8b666e45b4f622daf9,0x62e4604f62302e991813,0x1594230a7b19713d88b8,0x30aca1984c5c8c29ec46,0x896ec5c4b162e6614c63,0x5c4bc98ec5bd7752dd9b,0x98c65931713058b9978c,0xeb3732e59b8972c5ccb2,0x30e631986c5ccbd62e25,0x198b350cc5988662b173,0xdc4ba62e459cf4331672,0x62e45f31712f99b9174c,0x7ce635bd8b8adec5c8c4,0x5e3898af0c9cd6f62e6b,0x1af1c90d78e286bc7331,0x58d8662e2c373635e383,0x64e6c3317361a731b0d3,0x3734161b998b0dc4c586,0x61b8b1b0dcd0d86e086c,0x8ae1c9cd86e2e6c37263,0x5c58762e4b84d625c18b,0x62e4b9317261e6b130ec,0xcf0705e5939ae4c5cd72,0x5e66b1af3318d79e6e0b,0x9af2c1cd799ec6bcce63,0xcc59266e6bcb2735e58b,0x62e6c94e6364a631b25b,0xd73705eb8382f4c9cd92,0x5eaf992f574c97ade62b],#[0xb2f4cdc97a9ec4bd4d62,0x58993be64c9dd3264e7b,0xb284cab17264e7b13273,0xad9436558b932b3d8995,0x5c5939b2ac5cd9598c6c,0x8af7b1c57bca64b8b171,0x1d57bce64bdb3715ef7b,0x9eecbdcc765eebbaaf75,0x9b171653399310c5c588,0x5f5939ae6c5cd7398c6b,0x8b14cdcd7d60e6beb371,0x18d9664e6c531736298b,0x9ac6bfb2736598b9b2d3,0x631736319b9afec1cd7f,0x5d58b9aeb398d7564e6c,0x9b053d8d8298c6c13273,0x90d829a86c1337360983,0x98e6c14e5360a6a9b053,0x7cc6363e6aa3053dcd82,0x6626b1b30c9cd8f62e6c,0x1b30c9cd9862e6cc4e63,0x9cd989ae6cc4f4366262,0x66e2bf59435d18b92e93,0x5b17262d8b8b16cdc97e,0x6359b9300c5c997b686c,0x9307358d7662e4bb3172,0x5c9999ec6c831726419b,0x66e6c0b0736059b9302c,0xbb2736398b9b1cc5c98e,0x611939aeec5cd7762e4b,0x930acdcd8460e6c23372,0x98e3a66e6c2b0736159b],#[0x9a871fcc438fe731c8d3,0xb4d6105a7a1c7f390e3f,0x618b884735842362e20,0x84b6d042562e20c4d61,0x58c25b08612b1710966b,0x9e6215cd310ad93984b3,0xbcf430ae6218573d042b,0x726b085b35841b64e60,0x9839358c1cb6860e4d61,0x9cc289ac217327309983,0x988610ce70086638042c,0xcf43086721843350c21,0x86639843394c219aa61,0xa0433dcc219ce610cd73,0x5d02198e810ce540866a,0x9aea10cf7408673a0433,0x7b3710758b88353dd421,0x818b8852cdc41f62e21,0x1996c5c42a60e6103371,0x18cd166e665cf6332e63,0x98ec664f613318b99a33,0x44c633227b09aac5ccd2,0x35d8b99a73d8cce62e66,0x19b4c5ccd798c66bd943,0xdccda98e66d4e4336a6a,0x62e66c4c633619b999f3,0xd4d616698b89a8cdc4d0,0x6718b8b5f3585af62e2c,0x9b39398d9c62e2ce4d61,0x585b1b682d8b2736718b,0x9ac6d8d8436c58b8b633,0x14d63689939b62c5cdb1],#[0x6b99b9b44c1cda29cc6d,0x8b36c9cdae62e6d74e63,0x1c9a39ac2d1ef3168f69,0x9eecd1cc7668f3b93479,0xece636766b0b75bcc5b0,0x6966b0b4ac9cd9d62e6c,0x9b4ac1cda59ac6d2db43,0x585bc64e6d931736c99b,0x9cc6de4c636f2ca1b793,0xa31736d1939b78c5cdbc,0x67d8b9b3f398d9f64e6d,0x1b57350dab9886d5b273,0x94dab9aa6d5cf436ae72,0x62e6dbce546ae6aa3573,0xfce636fe6b1b7ec9cdb7,0x699839b4cc9cdbf62e6d,0x9b7ac5cdbd9cc6deb373,0xdc5a7b286cf317167993,0x62e2df5b436cd8b8b66c,0x64d636818b8b6acdc5a9,0x6e18b8b713d91ac66e2d,0x9b54cdc5aa98c8dc4f63,0x5cdb662e2db33736a983,0x64e6d0b173685939b6cc,0xb3736b5839b5acdc5ad,0x9526b0c96c9cdc162e6e,0x1c9d350e4e9ac7264d61,0xdc64d9ce7274d7393a72,0x9ac4254d6112b89087ac,0xcb1710e66b0873c4844a,0x136da089ac5c8399ac41,0x109b61084d62e226cd61],#[0x5d8389a4229b1721366b,0xdac21e73700f3838078c,0xe65620f373087935843c,0xf2fb987971cc3cccc41,0xb0793dd83c62ec1e4c76,0x5d84962e424ed611259b,0x62ec2b656215a6b08acc,0xd317212d9b907d35883e,0x1026b0880c5d83a62e41,0x909ccdc8409ac4205b42,0x58857b2842bcd6115d8b,0xb2c82bd94315d8b90af3,0x34d621198b90a0c5d857,0x11a6b208ccdc8469cc42,0x808d31c0469aca234e64,0x108469c64234d3211a73,0x9e84234e4211a6a108d3,0x34c7211a72908d354846,0x11a7b908d39c8469ae42,0xa08d354c469e86234d43,0x5d04698e8234e5411a6a,0x9aea234f7411a73a08d3,0xfb1721527310a93dd446,0xed8b8876c5c44c66e21,0x88b0c5c44f66e220b176,0xdc44462ec2c59641618b,0x9ac823b37111d8b88a2c,0x3cc7011e6b288f399047,0x11e6a988f3d0c479a862,0xa08f31d0479ca823cd54,0xdc84266e22131711567b,0x66e22433721159b888ac],#[0x1cc764027b0a00cdc848,0x4218b91f73d850762e48,0x9218c5c9049ec480cf62,0x9090c9a84864f3243261,0x9c86864f724326392193,0x8f12179d8b8a0ac5c4fc,0x776da0bbac5c5d19ac2e,0x13bb6109dd62e2eecd61,0x885e39842f1b1727766b,0x9e82f1cc4178e790bc73,0xacd617567a13c73109e3,0x75663b3ab7dcdd5b8e6e,0xbacc5c9cf9ac2f34f76,0xdc9d69ac4eb5b4275a6b,0x62e4f04d617a18b93bcc,0xd4e4276a6a13b53109da,0x76a7293b53549da9e84e,0x8ba0c5c9e49ca8ed4d54,0x5c5e962e2efb17174d8b,0x9aa8edb1717859b8bb0c,0x4b1717898b8ba8c5c5e5,0x9c67bb4d3358669e0e13,0x94d5358a6a9ac33b3172,0x58a6c62e533b1729c99b,0x9ac53bd9429dd8b94e93,0x7cd329beca1ceec5ca77,0x9be7214df350a6f9c653,0x8cd7350e6f9ce537cd72,0x5c67566e336b1719cd9b,0x66e3374f439c26a1ce0c,0x94d611caca08e4cdca6e,0x1ca7318e5358c72b4863],#[0xb0e56dd07264e6393073,0x98c79b4863cb1721e67b,0x9ac23fd9411fd9398f33,0x9b2731c18b90e1690870,0x202ca0901358473b2823,0x11017cc880ba64404d61,0xc87562e4404d62202d2,0xb6643ada321d6c990eb6,0xb4e321da6990ed30c876,0x1da7390ed35c8769e643,0x88e8c5c4719ce63b4d73,0x5cd3598c69ab1711ed9b,0x9ec69ccc634e67b0a72c,0xe4c764e59b9a72c5cd39,0x4fd8b9a79318d3c62e49,0x926cc5cd3f98c69fcf61,0xcc93aba649d4f614e98b,0x98ec9d33724ea7b12757,0x4f615018b9a7ac5c93d,0x5098b92813d8940ba64a,0x928538c9429a64a14c32,0x1cd429ee4a14c7250a79,0x66e29db1714de7b9a853,0xb1734f98b8a7d31d93b,0x7feda0bfec5cdfa62e2a,0x1bff358dffb086ffcd61,0x1d1ff66e6ffb1737fe73,0x62e702b1728167bb3ff6,0x4d8438266b0c136d0609,0x8018b93f6c5ce099cc70,0x940174ca009ac3005b41,0xdca009ac5005842802f9],#[0x9eed005874802c21c00c,0x55b418298b9c0cc5ca06,0x82ac2141574ca0a9ac30,0x941960ca0c62e5054d62,0xca02b665065a32832c9,0x9e65014e3280a6994053,0xd8438059b8c02c5c5fc,0x81e7bb40351d601b0e90,0x8c16c5ce07b08703b171,0x98e9f9ac74fcd61a7d8b,0x9cc752b172a967bb53f3,0x54d61a818b953b3586a9,0xaaa6b155574caaa9ac35,0x954534caa29865513172,0xdc6a162e34f4f32a8a71,0x9e864ccc432658b8d4ec,0xc31735627b1ab1318d58,0x572631ab931d95866e6a,0x12b37cc959ba64acb173,0x4c95d98ecacb3725667b,0x9864afb1725767b12bb7,0xfcf3257e7192bf34c95f,0x57e639abf3dc95f98e4a,0xb2b4cdc55a62e2ab4f73,0x5c55e62e6adb17156e63,0x62e71133738798b9c3cc,0x1b37287ef9943f74ca1f,0x8818b8c3ac5ca23ba651,0x8c48c5ce2162e310b371,0x1c0319e87624c43b118b,0x9cc66ecd633766319bac,0xeb2733758b99bb3d8cdd],#[0x3766909bb3990dd98c86,0x91bb3d04dd9e626ecd31,0x10cdd9e846ecf3237669,0x9ce66ecd733767a19bb3,0x433733a18399d13d8ce8,0x3be7b19df318cef9ec87,0x19ef3190ef64e677b173,0x9ccf762e67bcf633de6b,0x60e0704f643de6b21eec,0x64723836a09c1bcc4e0,0x382fb19c1718ce0cee47,0x19e5718cf264e0794c76,0x58ce2b68671307038afb,0x66e671307338a7b19c53,0xa59433d19381e96190e2,0x3d18b99e9398cf498c67,0x81e6c1c0e1b6c87a3273,0xdcce360e671b07038d93,0x62e67acc633d59381eac,0x2cf633958381cac9ccf5,0x3719381b8cdcce560e67,0xb1b96d90dcb2866e3171,0x1d8e466e272307039193,0xb6867631713b19381d8c,0xb32703d993b1d96190ec,0x3998381ccc9d8f662e27,0x81bcc9d8ed64e076b076,0x190de9ec66f4d6337993,0x9a426f327637a7321bd3,0x832703c27b21d2c1c0e9,0x3e19381f13190f09ec67,0x29f13594f89ec87c4d64],#[0xdcce760e673b07039e7b,0x64e077307639ec321cec,0xfb2763b99399dcc5ccee,0x3a99399bec5ccdf64e06,0x81e2cdccea60e6753070,0x9c0f964e678b1733c593,0x60e075b2733e58b99f2c,0x4cd327259b99d6c1cceb,0x711938396c1c1c39e64e,0x9b99398dcc60e6e23070,0x50dc69886e34f7071993,0x98e8e34f4371a721b8d3,0xb27072183838b3dd1c6,0x9867a0cc33cc6619a633,0x84c6c1c2589e8730cc43,0x58e59b6872cb07096593,0x64e12bb270991839cb33,0x2b3719698384b4c5c657,0x97d8384b6c5c66564e13,0x84c0c1ce5c60e12e3270,0x1c05c9c64314d3218993,0x60e02ece631699380c0c,0xfcc7017e7318c6c9c061,0x17e7a18bf350c5f9ee02,0xa22c1c05e9ee82fcc74,0xd891198c488df324467b,0x9e8288cc644458b92233,0x8cc4244679922330c911,0x44673922335c9119e848,0x92413d8920be64904c43,0x1c1149ec48e4f644818b,0xb6848a5f32452e99228c],#[0xa58644519b92293d8914,0x47593821cc9c11e60ec8,0x8a1ec9c10fbeca8edd54,0x9c11f62e28c32704618b,0x60ec8b30704598b8a3ec,0xcf61449938224c9c11a,0x4426aa243394d219eca9,0xa26c9c11364e08db270,0x9c1ea9e64f8cc327c67b,0x9e83443372a059383dec,0xe30709f27a1511310a88,0x9f26b14f96d0a7cba653,0x951574ca8a64e1453372,0x5ca8a9ac5455942a2af9,0xbee13ddc709ed8384f6c,0xddc749eef2a4f775527b,0x9e99384f4c9c284bee93,0x850acdc67d60e13eb171,0x5c68b64e145b171a1593,0x60e1413270a198384fec,0x14d54a0a7b850531c282,0xa267ba50531d2829ca94,0x8500cdca7e60e13f3270,0xdca8360e141b372a0183,0x9c6443cd3221e61910ec,0x3307020d9381053cc887,0x51a69928d30c94664e04,0x928d35c9469e64a34e32,0x5c5459ce6a34d7351a73,0x98eca454755219b8a90c,0x931715298b9a92c5c549,0x84a71942534ca1298650],#[0x956734cab3986559cf32,0x5c6ac64e1564f32ace71,0x64e1593371ab583855ac,0x54f4329662194ac5c6b2,0x8aa71945534ca2a98651,0x18d73d0ed09887684f32,0x9c0699ae034cc701a67a,0x9e8634cd431a67b80d33,0x4ce541a66aa0d3354c69,0x1a673a0d335d06998e83,0x80cd3dd4699aea34cf74,0xdc46860e034337119983,0x62e2924f61492630a48c,0x24d714926322493d8924,0x4ca621a493d09249ce29,0x824b3d913262e2994f61,0x1c1339ec899cc644cd93,0x9c8699cc434ce7b82673,0x9cc744ce72a267355133,0x489838252c9c12f9ee89,0x8a5ac9c12d62e2913270,0x10df862e29332704998b,0x9886fb4e707da6b83ed3,0xb4e547da6aa3ed390df6,0x7d19383e939d1f69ae8f,0x8d22c5c5f764e0fbb171,0x9c29864e14b4d54a499b,0x66e3473070a3983851ec,0x9b070a4d9b8d20c1c290,0x53e73991735cc8b66e34,0x842b35c2159ce2a7cd71,0x5c5629ce70acd7385673],#[0x9ae448ce7358a6b9ac53,0x9ce7154e6b8aa739c891,0x5526382a939c9539ae4a,0x95793dc95498e4aa4f70,0x9c9679ae4b3cd7159d8b,0x9ce4b54d725aa6b8ad53,0x7743203bb99007d0c803,0x2d7b2196bd50cb5ee640,0x197fddd0b5eee65af473,0xdd0b6ea845b76432ffaa,0xee645c75322e3aa1181d,0xbf4742dfb99185d4c8c2,0x5c3a90ae1dcc586eee85,0x92e5dc8587ea42c3f721,0xcc989e864c4f7325cba1,0xec86bcf5435e7a382f3d,0x977745e7bb9af3d1cd79,0x5ebb992f5d90d92ea86c,0x1327ddd17aec86bd7542,0x4c995ee64be75325f3aa,0xee86b8f5435c7b9932bd,0x8f6545c7aaa2e3d58d71,0x5efab2ae3d99171eac8b,0xa2f7d5517bec86bdf443,0x1d17becc8bdf5645efb2,0xe886c475655efbba2f7d,0x47654623aaa311d90d88,0x653ab2b11d99188eac8c,0x1b29d58d94ee86ca7543,0x19194eca8ca7554653bb,0xeec8ca7664653ab2329d,0xa7565653b3a329d5d194],#[0x97b3b329d5d994eecac,0x1997d5d02deaa816f731,0x8859aea42cd764332faa,0xea42ce76216bfa90b5fd,0x8f7316c7a90b63dcc59c,0x68baa1b45d10da2ee64d,0x1b5dd50daeee86d17643,0x505a3ee62d1f54366fb2,0xeac8d1f55468fb29b47d,0xd77416ebaa0b75ddd5a3,0x6ebab1b75dd0dbaea86d,0x2375d591baeca8dd7554,0x5d9baece8dd75746ebb3,0xee86d5f4436afb31b79d,0x6f521137a90873d4844a,0xf3a38079d59038ee422,0x879d5043cea621e7670,0x5083cea641e75610f3ba,0xeac41e75520f3ba1079d,0xe75530f3ba1879d50c3c,0xf3aaa079ddcc3ceae61,0xa079d9903ceac81e7654,0xdd03cece81e75740f3a3,0xeeea1e75750f3ab2879d,0x4f542127bbb079d5d83c,0x15baa08add59049eac42,0x28add59056eaa82b7561,0x58857eac22bf5620ebab,0xe8e423774211ba2108dd,0x3777211bb3908dd5c846,0x11fab10b1d9d046e8e82,0x888fd9c447eae223f471],#[0x1cd00ece823f47411fbb,0xeee8807574403b39a01d,0xaf670757a383abd485dd,0x757a39babd549d5ea82e,0xa3abd5d1d5eaa8eaf673,0x5d9d5eeeaeaf575757bb,0xea6534f5319a7bbb3abd,0x4f5739a7aa1cd3d50a69,0x1cbbba4d3d5d269eee73,0x98e5dcc472ece0397470,0x4c539eae44076731cba3,0xee649cf5324e7b98a73d,0xcf6734e7ab9a73d1cd39,0x4ffb99279d4c93ceee69,0x83ffddc53be8e29df731,0xcc5ffea62fff6707ffa3,0xe8e6fff7327ffa993ffd,0x2f7737ffb39bffd5cdff,0x807b98c13dcca05ea650,0x9d3fdcc69feee300f471,0xdcd58e8e6ac7673a7fa3,0xe8e70f7772567a392b3d,0xef77287fa3943fddce1e,0x377aa09bbdcc4ddea626,0x19bbd10cddeae26ef741,0x54cddee866ef643377aa,0xeec66ef463377b299bbd,0xef673377ab99bbd1ccdd,0x377b2a1bbd550ddeee66,0xa1bbd1d0ddeec86ef464,0x5d4ddeee86ef674377ab,0xec867475433a3bba9bbd],#[0x7f6433bfaa19dfd10cef,0x3dfb989efd4c4f7ee867,0x19efd18cf7ec867bf543,0xdc0e0e8e07077643dfbb,0xe8c8797764383a319c1d,0xa776338ba319c5dd90f2,0x3dbb319c9d18ce4e8c67,0x81bdd18ce6ecc67b7463,0xd8cdeeae26f767037bab,0xe8c86f765437baaa1bdd,0xf767437baba1bddd90de,0x3e3b381f1d5c0f8eaea6,0x8a23d50511eec87c7554,0x5d111eae488f552447ab,0xee85447442a23abaa23d,0x27571493bb8291d1c148,0x1800001d5d524eae89,0x56007c80196004b000c8,0x3f600e20031800ad002,0x2005a40153004e401198,0x1f00075801bc00682018,0x802610091a0230008440,0xbe002db80afe02a180a0,0x80de6035c80cee031780,0x1400fdc03d700ee6039b,0x49b011de0459010e204,0xfc0520813f804dd812ec,0x171805a60160a0561814,0x981932062b0184c05eb0,0x6e101afe06a401a16066,0xe076701d38072681c160,0xfec07de01ef407a401e1],#[0x221e086682108081b81,0xf023b408d60230808a8,0x96d8255a093c0248a09,0x1409e98272609aa0262c,0x29f60a61829140a23028,0xf02bba0ad782ade0a9b8,0xb8602da00b4702c9c0b0,0x60c1502fd80bcd02ea00,0x29e0c83831880c4b830b,0x834c60d0e033a40cca03,0xcb036ac0d8b835b80d4c,0xe58838c40e0e037aa0d,0xd20ed183ad20e93039d4,0x3dee0f5983cf00f1d83b,0x983fde0fdb83ee80f9f0,0x9c041d01052840d8101,0x6111f0440810e28430e1,0x66e1180845a41151044d,0x8482811ee0474a11b504,0x95049d61254048f01221,0x130204ba812ce04ad012,0x2e136d84d4c133584c6a,0x503213ea04f0613a504e,0xf85282147d8515c142b0,0x55e854c815110539414b,0x215f20574415ab856161,0xa66167985974163b0586,0x85c5616f185b4c16b505,0xb785e68177805d5c173a,0x18318604617f605f5e17,0x1e18a386224186b06134,0x651619268641a18ec063],#[0xe8675219ab0660c19660,0xa9f869e41a500689819f,0x21b2886c001ae206aee1,0xf7c1bb886e4a1b6c06d1,0x71d81c4f070c81c0886,0x6073a01cc6072981c90,0x1d838757c1d40874961d,0x7c1dfe877781dc707696,0x7a341e6c0793e1e36078,0x987bfa1edd07b001ea40,0xf9b07de01f5a87ce01f1,0xa200d07fac1fd287ed81,0x26c207e081922048080a,0x8845620f00834020b408,0xbc0865a216f8854c2134,0x223f0887021fc0876621,0xd422d008aa8228e089a4,0x8e14236508d20232088b,0x10902823e388f2223a98,0x4ac0921624678912c243,0xc2516093f024df093142,0x7002597895f42559894c,0x89960262e0980e25dc09,0xf289b5c26bc89aa2267f,0x275909d00272809c3e26,0x7a27c809ec2279109dce,0xa17628410a08c280109f,0x58a35e28bf0a274287b0,0x97a8a56629350a44228f,0x629fe8a77229b90a6622,0xa562a700a9342a348a85,0x8ac8c2afa0ab4e2ab50a],#[0xc08ae882b7e8ad762b3f,0x2c258b0162bec8af5e2b,0xdc2c988b1ea2c5c8b116,0xb4b42d108b3d22cd20b2,0xd8b70a2d9f8b5ee2d548,0xe470b8a62e108b7e02dd,0x82ebb0ba6c2e7c8b99c2,0xd442f2f8bc462ef10bb5,0x8bf822fba0be6a2f770b,0x928c1bc30488c0ac300b,0x31248c40230e28c2f230,0x31a20c5ea315e0c516,0xc916321d8c7d631dc0c7,0x50caf0329f8c9fe32678,0x34d8ccac33090cbc832d,0x233bb0ce8833848cda43,0x12c342c8d03c33f28cf6,0x8d33834ad0d246346f8d,0x7e0d56c35328d42c34ef,0x36188d7d235cc0d68a35,0x4836a50da2a365d8d8cc,0xdd84373b8dc6c36ef8db,0x60df7e37c28deb6378c0,0x86e8e13e382e8e03a37f,0x638e28e30638a50e2303,0x5ea39600e50a39220e40,0x8e7b839cb8e6ba39968e,0x940e9d03a4e8e8ba3a11,0x3b098ebc03acd8eabc3a,0x843b860ed883b438eca0,0xf06c3bfa8ef623bbf8ee,0xe0f2683c7c8f1663c3b8],#[0xd360f46e3cfa8f3863cb,0xc3db60f6543d790f5643,0x9883e3c8f8703dfa8f75,0x8fbe43edd0face3e888f,0xa18fdee3f618fd0c3f1e,0x40208ffe43fdc8ff083f,0x1e40a710228406d90138,0x548412f1042a40ed903,0xe9076241bb1066a41771,0x2761093e42341086e41f,0xe430290b8c42b990a524,0xf2a439f10de6435310c9,0x9117844311102243e910,0xf01134044b19126e4484,0x45771155845349144444,0x4e45f41175245b81166a,0x19ea465f11928462f918,0x991bb846d591ade46991,0x77a91d86474691ca0470,0xc47f111f5447b611e564,0x22848681212c482e1204,0x1243c48f11233248a912,0xbc926784980125844938,0x4a309284249f41275e49,0x1e4aa612a204a6a92932,0x2d144b2212c164aeb92b,0x512f184baa92e184b689,0xc6d1313c4c2a9300a4be,0x24ce91332a4cae132464,0x62e4d6a1351e4d231343,0x1384c4df11373a4dad13,0xd013ace4e8b139944e38],#[0x4f5c13cd64f1c13be24e,0x144fe593f224fa013dde,0x4220506b94136502d940,0x21446450f19433850a91,0x1c51466a517614536513,0x25257948e25218147ac5,0xbea52e194b2252a3949f,0x94dc2535214cd2531a14,0x114f9c53ca94eb4538e,0x54851518c543f1507054,0xa2550d153b854c59528a,0x56a65588155925542154,0xe158dc5613157b055cd9,0x6d895ae45695959ce564,0x6576215cfe572015c005,0x4a57eb15f2857a995e1,0x16272587616148583116,0x53964ba59089639e58c4,0x59e0966e65995165ca59,0x265a6e9693a5a2996800,0x6c545af116b325aa716a,0x116e725b7c96d705b3c1,0xc4f970b25c0916f925bc,0xa5cdc172ca5c95171c65,0x5f85d57174f85d20973f,0x178345de69770a5d9c97,0x9b17a005e65179365e31,0x5f0f17be45ed917aea5e,0xa25f8717d985f4e97cba,0x8092600497f8c5fc197e,0xd98276607f9817c603f9,0x13f9847e60fe9837a60b],#[0xc61bc1867a617f985786,0x99c62429887e61fa1876,0x98bf462d718ac2628b98,0xa798e26636818d1e6322,0x64309902863f118f2463,0x5064bb9927e647a99154,0x956a653a9945a64f8193,0x99976c65bc99674657d1,0x6889999266409987665f,0x4671499bda66d199ab46,0xf1867a599e04675e19ce,0x1a16268339a03e67eb19,0x101a39e68c49a280687d,0x69959a5d2694c9a4bc69,0x266a241a7f269d89a6f0,0xab766ab51aa2c6a689a9,0x61ad9e6b449ac866afe9,0xc041af866bc09ae7e6b8,0x86c7e9b19e6c479b0946,0x4986d039b3806cc71b28,0x9b6be6d8e1b5a86d489b,0x5e9b8ee6e189b7ce6dd0,0x6ee29bb026ea81ba066e,0x206f639bd3a6f289bc1c,0xc0546fee9bf246fab1be,0xc1c29670819c16e70381,0x1579c4e071159c3c670c,0xa71d19c6cc71949c5da7,0x97c72441c898720c1c7d,0x1cb8472be1ca64727a9c,0x819cd80733d9cc7072ff,0x73fe1cf6e73bd9ce7c73],#[0x4e747c1d16c743e9d074,0xd43474f19d34c74b29d2,0xf1d5d6755a9d50675289,0x6081d77e75c09d6a0758,0x476839d98e76461d8a27,0xca677071db8276bf1da8,0x1dec477951dde077519d,0x5d9e0c478081dfa877ce,0x78fd1e35278af1e22278,0x6e797d9e574793e9e45c,0xe86c79f89e75679b89e6,0xd9ea927a801e9747a431,0xb691ed067b1e1ebd47ac,0xc7bf09ef347bad9ee587,0x1d67c5b9f10c7c271f02,0x9f3c47cca9f2a27c8f1f,0x8e9f5a67d469f4a47d0c,0x7e011f7a07dcc9f6ce7d,0x447e6a9f9307e301f864,0xfc027ee29fb167ea89fa,0xc9fe607f751fd3a7f279,0x4aa00b880081ff8a7fb,0xa80d3202ba808ea01b48,0x5d88150204b68109203b,0x2080881dda06d68194a0,0xb620a3e826a209148228,0x8340a0c8282fa20b5e82,0xb683cfa0ebc8386a0d7a,0x11fe8459a10ce841120f,0xb2143e84e62131884a72,0x5c82167a858121572853,0xa866aa1914861b217ca8],#[0xc6086fc21b7286b6a1a3,0x21e42876da1d40873221,0x31a204087f221f3c87ad,0x88aaa221a8868a213488,0xf489242242a88efa2348,0x2704899ba25f88964224,0x3a29168a252280489df2,0xaed22b328aa7a2a0e8a6,0x68b65a2cfc8b2422c288,0x7e8bf922f448baca2e3,0x232cc8c8ea319e8c4623,0x62a34fc8d1aa33e08cdb,0x8df4237368da6236068d,0x928e7f2397c8e3c2385c,0x3cd08f0c23b948ebea3a,0x523ef88f9a23dfc8f5a2,0x6aa411c9026240128fe,0x90e8a431890aaa422a9,0x5fe915ea45109124a441,0xa47f091dd246fa919fa4,0xada4a149261a48fc921a,0x934424c6c92f3a4b2e92,0x1493df24ed8938e24db0,0x5252946ca5148942d250,0x7a548094faa535094b7a,0x5d7256d89595a55b4954,0xe96642591c9620a57fa9,0xc2a96e925b2896aba5a1,0x25e6a9774a5d4c973025,0x402606e97fca5f5097b4,0x98c52628e98812618a98,0xc09947a6494990526394],#[0x685699eda670c999a265,0xfa6a949a7da69709a3ea,0xb6026cf69b1aa6bea9ac,0x9be8a6f2e9bb1a6e2a9,0x2729c73271229c27a701,0xa74f09d15a73a89cc1a7,0xf42774a9db0a761c9d62,0x9e82279709e38278489d,0x529ef9a7b889ec427aa6,0x7e3a9f6e27d389f3227c,0x4280749ff3a7f589fad2,0xe8a831ea09aa81c2a04,0xea16fa8548a12e28426a,0x8c6a2092878aa1b92864,0x28af6a2a0a89f8a25d28,0x6f28d40a32fa8c20a2dc,0xa3de28f04a3a228e16a3,0x5aa47629130a425a9012,0x9490a4fea937ca4bba92,0xaa96dca593295bea54b2,0x67329942a627a980ca5d,0x8a6f7a9b5ea6b529a54a,0xe76a77da9d80a73ba9c6,0xaa0b0a80429f76a7bc29,0xe7aa2f2a895aa1c2a84b,0xa97baa568a93caa442a8,0xbeaa06aa784a9bbaa666,0xab28aaa62a9f8aa562a8,0x52ad4aab30aac36aaeca,0xbfa2af8cabc0aae74ab7,0x2ac93ab1b0ac43ab07ca,0x52cad29ab42aacdd2b2d],#[0x2b740adacab62ead6aab,0x7bab96aae362b854adf4,0xaefeabb82aebd2ba6cae,0x6af982bdc6af4aabc9a,0xc148b029ac02aafedabf,0xcac39ab0b9ac25eb074a,0x1a12c5eeb154ac4c2b10,0xb233ac832b1f22c722b,0xbaeb2c4aca78b279ac96,0x2cddab3512ccbab30cac,0x35ad028b3e62ceeeb39a,0xb4c92d290b47dad15cb4,0x14b55fad4e4b5132d3ba,0xd828b5e42d70cb5a3ad6,0x42da66b676ad940b62da,0x764adcf6b7162dbbab6c,0x8b808adf8eb7b9ade42b,0x378b8b1ae20eb8562e0b,0xae5c8b94d2e4beb900ae,0x412e85ab9f02e708b99c,0xbad4aeaceba8fae9a2ba,0xabb622ecfabb1caebe2,0xefbcbbd52eeeabba6aee,0xcaf1f0bc5a2f0c8bc10a,0xd212f3f4bcda2f2f4bc9,0xbdbe2f67abd73af520b,0xa20be65af8eebe112f79,0xafcb6bf0a2fb74beb1af,0xebaff22bfa22fdf6bf58,0xc08330172c0353003cbf,0x62c12d303fcc0d6302ac,0x824c1db306b8c184b05],#[0x7b0ab8c280b0962c22cb,0x38a30d78c331b0c10c2d,0x8c416b0fc8c3ce30eb0c,0x2fcc4a331204c45e310e,0xb1522c52431400c4ddb1,0xfcb1756c5b1b163ec56c,0xc67db197cc63d3186ec5,0xd2c706b1b92c6c131a7e,0x1f5ac7a7b1deac758b1c,0xb2180c83fb208cc7ff3,0x907b238ec8c4b2288c88,0xec98fb25e2c955b24b6c,0x8c0ca12327c6c9d1b26b,0xb2ae6ca95329ceca5332,0x8932d88cb3c32c3ecae5,0xcc2eb300acbda32eb2cb,0x20ccd9b32cacc873315e,0x361ecd6db3530cd2a334,0x3b3858cdf9b3748cdad3,0xee0b3afcce91b39a6ce4,0x2cf7033d36cf1eb3beac,0x8ccfff33f72cfbab3e5,0xb42ced091b41a2d044b4,0x7234540d12bb4408d0d5,0xd1f734756d1b434652d1,0x94d280b4976d235b485a,0x4d04d31f34bccd2c9b4a,0x1b4f8cd3b334e42d3653,0x498b51d4d451b50c8d41,0x2d524b5416d4e6b5304d,0x7b8d5c9b5678d57ab554,0x35a68d66e3590ad61a35],#[0x72b5d1ad713b5bccd6c8,0xd80b35fa0d7bdb5e4ad7,0x3ad8a2b61f6d859b60b6,0x65f4d94eb648ad8f5363,0x936882d9f7b6738d9a63,0xad4b6ac6da8eb69acda4,0xadb7836d32db2336beed,0x110dc1cb6fc2dbc7b6e6,0xb7338dcac3721cdc6b37,0x9f375d8dd4f37474dcf5,0xde36b7842ddea3770cdd,0xb2dec637aa6de87b797c,0x7ddcdf4d37caedf0e37b,0xe380c8e00537f4adfa7b,0x1023835ae0b0b821ae05,0xee1af38614e15c384bee,0xa0ae24eb88a6e201b875,0x38c9ce2f8b8b30e2a638,0xe438f0ce3a138dcce354,0xe46739114e42539014e3,0x2ce4ecb9330e4aab9220,0x9696e57ab9556e530b94,0x2b9908e619b97a4e5c03,0x6ed39b20e6adb9a16e66,0xae78fb9daee74539c84e,0x15ce831ba01ee7dd39ed,0xba3dae8ccba2a2e87cba,0xb3ba640e96a3a508e91b,0xea453a888e9fdba762e9,0x9ceac03aa8cea88ba99e,0xadf0eb5b3acc8eb0dbab,0xcbaff4ebd8baedeeb96b],#[0xcb33b238ec663b0fcec1,0x6ed3e3b45eecfb3b35ce,0x82aede5bb708ed963b59,0x3ba76ee773b948ee2ebb,0x5bbbcd2ef0fbbbaaeec4,0xf0013bf66efb13be14ef,0xef0a1bc1fef05dbc0ba,0xc56af130bc42ef0e5bc3,0x7bc806f1da3c68ef17eb,0x2cebca98f2803c96cf22,0xaf3783cd4ef323bcbfcf,0x114f420bcfcaf3cc3ce9,0x3d36af4b6bd252f4663d,0xaf3d618f558bd49af501,0xf63c3d872f5fd3d758f5,0x92f6c5bda9af681bd974,0xdddaf7513dca0f70b3db,0x3e04af7e6bdef8f793b,0x8d3be2d2f88cbe198f84,0xcf96ebe534f926be3f0f,0x852f9f1be722f9aebe63,0x3ea42fa76be954fa2f3e,0x20bec00fae5beb22faae,0xfba7bee32fb64bed08fb,0x74fc2d3f02cfbe73ef0c,0xf402fcd23f29efc7f3f1,0x6bf69efd7b3f54afd2bb,0xe6bbf908fe213f806fdd,0xefefebfb78feb9bfa52f,0xeeeff9a3fdf2ff513fc9,0xc019f0039c0038ffe5bf,0x44c045f00ed402f90091],#[0x1d6c06b7018dc058f01,0xdf028bc0975022f40807,0xd830334c0c2d02e040a,0x94100903db40ec703894,0x4e0412c904834116b042,0x1057f4153d052cc142d0,0x9470624c17e905d1416b,0x41bfb06cd41a83067541,0xd9c1eab0782c1d67072b,0x87542135081d4200507,0xe70910423cd08d24229f,0x273d09a3c260d095c424,0x2c29c10a43c287b09f94,0xb1ac2bdd0ad242ac70a9,0x50bb9c2e2d0b66c2d2b0,0x1ef0c4b430ab0c0342f8,0x434670cf3c33390ca5c3,0xe5c36f50d93c35af0d3f,0xe664391f0e28c38150d,0xa70efbc3b510eafc3a23,0x3f2d0fa243de90f5343c,0x8c41b31040c406d0ff34,0x13dc445f10ef44301109,0xb11f3c471f1199c45971,0xb6512af44a05124ec488,0xc4d9f134944c9f130744,0xec4fbd13ccc4eaf1388,0x14b4c52391468c50f514,0xbf154d45497150b45383,0x57fd15df456f7159ac55,0x145a4d1664c59151622c,0x744c5ca5170dc5b9716c],#[0x317dec5ef71797c5dc51,0x2591873c61471829c600,0x464e1190b463a318c2c6,0x34674f19a7c6603195f,0x1aa0469f91a56468b91a,0xa71b4246c551aefc6b25,0x70791bed46f131b94c6d,0x8c73531caac71f31c48c,0xd8cc75a31d46c74791cf,0x91e23c780b1ddb476d71,0xb011ea5c7a2d1e66c790,0xc7ccd1f18c7bd31edd47,0xd5c7edb1f9347df11f57,0x2066c810d2019c7fd51f,0xf20dd482f720a2c821b,0x8677217448537212c484,0x5c88932203c878f21bfc,0x2c0c8a8922864899b224,0x1233ec8c5d22f448b6f2,0xff323d9c8ed5238ec8da,0xc9235246cc91392424c8,0x52c94b52506c937924b5,0x25ed4970f259ac95cf25,0xe1268ac99892636c984f,0x9d8d273849c4f26ee49a,0x4a05927f0c9f1d2795c,0x8e84a2f128924a199284,0x529a44a5c7293fca4592,0xa3f2a644a8f52a0b4a76,0x4acad2b04cab6f2ab7ca,0xf2caf492b9c4add32b53,0x2c794b1572c34cb04d2b],#[0x992d04cb38b2cbccb269,0xb7152d9ccb5df2d4d4b4,0x1cb9732e3b4b8532defc,0xf20cbbf12ecfcba912e8,0x92fb1cbe472f6bcbd152,0x1ab30404c06d2ff9cbf5,0x4c40d30d94c2c13090cc,0xd24c697317c4c539312c,0x325ccc8f3321dcc7dd31,0x8b32f84cb4b32ac4ca07,0xcf05339accdcf334d4cc,0xa4d147342acd00b33e14,0x51ecd3cb34cbcd287347,0xb35b9cd647356ccd51f3,0xa4736674d9093614cd7a,0xcdc9b3708cdb7f36b9cd,0xc4df6f37b0cde01374d,0x38b84e24338664e0df38,0x1539594e4bd3903ce383,0xe86b39ef4e70f39a3ce6,0xcead53a8bce9a73a41c,0xb764ed553b2f4ec193ae,0x13bf3cef553bbbcee6d3,0x25d3c7acf16b3c354f04,0x4f4ed3d13cf3a73cc1cf,0xf84f75d3dac4f6273d64,0x3e9b4f9c33e4fcf8933d,0x7d3f3b4fc313ee7cfb03,0xfff13fda4fec53f854fd,0x2502914073d0121401ac,0x15ed04ef4120503d740d,0xd41d9d06ff41a1506094],#[0xa23426dd0931422b507f,0xd0c7d42f650b4142b1d0,0xedd0f17439950dc74342,0x4488d1189443cd104943,0x2f4528d13fd44d6512a9,0x17b945c5516894575d15,0xcd1a674670d191f46185,0x752d1cb946fcd1b6946b,0xb47f1d1f25479e51ddb4,0x2f14891521a948425206,0x5258749395243d48e552,0x375283b49e2526d7498a,0x4ac652a754a7bd29694a,0xe14b52d2ca94b0bd2b9f,0x30534bef52f0d4b9cd2d,0xfd32ab4c85d318b4c3e5,0xd73535474d28533f74cc,0xd4dffd37674dbdd36554,0xaf14e9d539cf4e4fd389,0x53d394f23d3c154edb53,0x1353fa74fc0d3e7d4f77,0x50a8541eb505a540d750,0xb351465448750fa5435b,0x482751e5547015194545,0x854a87527754951522dd,0x37bd4d455322d4bcf52c,0x9541d54fe753cf54e875,0x38954b8d525354705510,0xd560b555bd54c5550b55,0x50d58a755fe5574955a9,0x56f0d5b1356a2559e556,0xe3579555dc1574755c5f],#[0x615558305601d57e2d5e,0x5d641d58d7562ad587cd,0x9e6d66cd5988d658f593,0x35a7f569735a36d68375,0xd5b5b2b56bef5acdd6a9,0x56fe35bce56e9f5b8156,0xc1d72695c73571315c23,0x5d65575035d19d73bd5c,0x895df9d77635daf5761f,0x7aff5e90d79a55e44578,0x57d495f27d7c055ede5,0x1857fc55fc5d7e675f7,0xd60c3d826f606d581036,0x627615cd84f76116d83a,0x588b962045876561b1d8,0xec58b2362a4d89fb6259,0x638a58d99633d58c4162,0x47642ad900f63dbd8edf,0x939d64c1d926f6478591,0x55962b655b594cb6508d,0x65f598cd6607d976565b,0x3670a59b9566b059a1d6,0xfb767c359e7b6769d9d0,0x5a20d6860da0f3681959,0x4bda48f68fa5a34168a6,0x69e35a6ff6999da5c969,0xe76a93da9956a375a82d,0xad616b2ddac216ae0daa,0x45afdb6bccdae996b7e5,0xcce5b2976c76db1336c2,0x36d6b5b5096d1b5b3d96,0x9056e11db7b56dbfdb66],#[0xdbb5f6eb25ba336e66db,0xad5be216f58dbc9f6f01,0x7051dc0ab6ffedbf4d6f,0x1f71195c3a970b8dc22b,0xc78771bddc65b71715c5,0xcdca1972605c8d172065,0x3545cc9572fcdcb3772a,0x17408dcf7973acdce0f7,0x35d74a6dd1e3745a5d0d,0xdd5f37557dd4bf74ff5d,0x41dd85f75f15d72375a3,0x76d8ddacd768ddd9af76,0x4d77715dd39772d5dc01,0xe09b78015df6d77b85de,0x5e2ed7897de1d37849d,0x96f5e53d7928de41178e,0xf79e9de73d79b0de63b7,0x9dd7a59de8ef7a21de81,0x5ebb57acf5eac37a93de,0x9c5edfb7b5b5ecdd7b11,0x7c105efcf7bd65eeed7b,0x9b7c86df1ad7c485f0af,0xf4037ce8df3437cc1df2,0x4df5b37d51df4d97d1bd,0xdecdf73b7db55f6697d8,0xb7e655f90b7e275f81d7,0xbdf7ed3dfae57e9adfa0,0xdfdab7f52dfcd97f1adf,0xfcdff8b7fc05fe6f7f84,0x806a6014f80346005f7f,0xc180d9e02d3808ee01f3,0x5238131e047b8107e03],#[0xa606d38194605c5815ee,0x21b6081381efe077181c,0x58276e099f8249e08d78,0xbd182dee0b2182a560a2,0xe0d8d834760ca7830c60,0xf6e0f6583ba60e7f8380,0x845f61119842f6105383,0x5b84bee12a3848fe11db,0x156d85436146f84fa613,0x86173785b86165f857a6,0x646e18c98618e17db85e,0xf8696e1a2d8671e19738,0xc6b86fc61ba386cee1ac,0x61e218771e1d59873a61,0x1ce201387e0e1ef787a4,0x88a2621f7885be20df88,0x778905e239f88cde22e3,0x267b8982e25718934624,0x9e287389fd6276789be6,0xab1e2a6f8a7e629618a3,0x78b0be2bdb8ae4e2b138,0xe518b79e2d938b3fe2cb,0x62fc98bda62f078ba8e2,0x55e31078c356307f8c06,0x8cb0e32518c7f631ab8c,0x438d00e339d8cd263319,0x35c58d57634ef8d25634,0x7637598db6636798d8a6,0xe56e38f98e1be38258df,0x58ebd63ab18e8de39bb8,0xcb38f18e3be98ee363b3,0x63e118f6e63d618f4363],#[0x15e3fe58fdde3eeb8f9d,0x907ce4185904c640d790,0x9390d3e430390a76424b,0x45379131644659100e43,0x646d79197645f991696,0x23b6487d920ae47c191d,0x3929e64a119266649459,0xc89930c64bd792d8e4ae,0xe4dfd9363e4d39933564,0xe4f9f93ca64ec59397,0x946f6513d94306506b94,0x5994bce52a7949565207,0x54bb951d6541b94ede53,0xbe56019570e556f95446,0x5fc6579395cf656df959,0x99652658ed9629e58459,0xb0b96b265a75967fe599,0xe5c679705e5baf96d5e5,0x7f65d9f9754e5d15972b,0x97e6e5f2997b4e5e6597,0x3985e660f5981de6003,0x635398ba66285988f662,0x46649d9914e63f998eae,0x995e660b996e66541993,0x199f4e677f99c5666a39,0x9d79a616690f9a2ce683,0x66b4f9abb66a919a8b66,0x5666ceb9b1be6c019aee,0x4008300e030066dc79b,0x8a802084805800283412,0x2487000311c840f22038,0x120e0984a25070703099],#[0x40cb0b0c8ac08b68646c,0xb4543c258c2e80b042c8,0x90b4244a071448200718,0xc1f0a821284022866251,0x1622d801581416170a14,0x86186911888441a9140,0x98c82562c141d0f86c96,0x1c3c0b4632a9428a585c,0xb0884789158de922086d,0x8658c51a30860d429871,0xf0f890cd92211231c641,0x4691617a5a264d2b4644,0xa1c25dac81a0be5e9017,0xdac09a37fb5f835e1126,0xf5e070975344690e1c25,0xfc42014b4261be5a152c,0x7e4682fa42eb648d0984,0xafae0bc26213029820ff,0x634962a7fd2603a01330,0xbc25c10005e07eebe092,0x489fffc9ae58049bffff,0xff4980e804a5ff939760,0x22601fbaf824588a9357,0x8485a6a12d7fe4892920,0xa9357ff659708012c7fd,0xe20002edf1fbaf824588,0xaffcc4a74122ffffef09,0x1622a4d5ffca92e02025,0x784780080bc7c7eebe09,0x86311f7e595d0997ffff,0x1ee0973c799d01994696,0xf7d09ea000bd6e331f0b],#[0xc7eebe091602549e79ff,0x68fffbdac1201ad49a33,0x200a022c7ae0a5102a,0x6a565b08983f3f226500,0x1a5cfcc3a94209a3f1fc,0x324ddfcd73fa6ca1124d,0x122c04a9426b9f837520,0x6b04806b526a9f2bdd7c,0x6fb3f7470e1612f5ffef,0x4d3f79ffcda5c0002064,0x12a4edfcd73fa6ca112,0x1201ad49a3e3f75f048b,0xfe7a1b02200c57ffbdac,0x1f8abc1b69281271fbcf,0x49bbe3f75f048b012a4e,0x440190fffbdac1201ad,0x4827a930ffcfbf34278,0xf538d4b0115387ffef6b,0xffda72540280345fff7c,0x4d9fff49d592493e4ffc,0x140188fffded60900d6a,0xff4912b24976ff372600,0xbc3fee9011013c4d739f,0x201ad49b7fe7c9620200,0xe4908080321fffbdac1,0xbdac1201ad49b7ff3ff9,0x3f6824980080402a0fff,0x6a4d9fff2d52029267bf,0x70104062bffded60900d,0xd9fff2d5210926dfe7a4,0x80c47ffded60900d6a4,0x60900d6a4db7f9c24e02],#[0xf274108d80589ebffded,0x3ffd348d02080cd7fffe,0x7d9bbfe77810001893ff,0x1a6ed9fff9de0004061,0xa39bdad80ad838f906aa,0x8a48506c3cd79e6f80a,0x25d7dc358c2aaf87d0b4,0x7b0b7161287da58e2d40,0xa705cbfef62950088fdc,0x98aa84404ebffe6ba1d6,0xebcdc7b0b716133547da,0x987fffaf32a34040623,0x90be3c02f9fd2c05cb05,0x87d0b409a8506c3f5267,0x9679df29a31000316fd,0x530a090983f3efbd81a6,0x38f99d29c2069635cfeb,0xa943bf817144503009f,0x3c726b8b08262f87642c,0x106c1eb6343cd0491fe3,0xdc584dcf5685a00119,0xfdbc9d612cbb7d1fb8f6,0x77f27269100040144379,0xf98d5a1680046441b8,0x147e3e8fdc70600dc585,0x20c1137d9fba8c38584c,0x934284550009cdfeae7d,0xc8e1367ec68795091bf,0x800350a0db38ebec7b00,0x3f50931100659e30fa16,0xfff8e4d7168412cefff9,0x6b2e35685a00119106e1],#[0x255f61f42d0006a141b,0xcbe0ca817b5bfd6dfa49,0xfdcf4c0111530cefff3b,0x6c119e38b42e0c409d3d,0xc0454eaf5685a0011910,0x9760c140194e33d4e352,0xa1680046441b4ccffff7,0x87a598008049052cebd5,0xb19e7eb805080260fffd,0x102830af58da00119106,0xc2e29102619fcfffd909,0xead0b40023220da3f8e2,0xfffff1c2ec8204019e75,0x327beba9db408529a7f9,0x64709a3fc8a90071a41,0x26c3104064bc75f63d80,0xf1e63b0a622fbffff35c,0x6338ebec7b000c8e1369,0x64709b4fbfa9528808,0xf24d2880862bc75f63d8,0x26a9fed4803cac132d3b,0xb14271d7d8f600191c,0x2080d77fffef06a8211b,0x40405c7d7fffcd72a186,0xcc3c8800171f7fff9879,0x15f5c1780d42134fbfff,0x50d7280953bfc701e048,0x495ff9396da04adfcfe,0xbba635360354eff1c07a,0x1c84b4eabd318b44d21e,0x6f8600953545f51bfc70,0x1246dfe1ab2d0a136ba0],#[0x1cc4968a0973bfe2cb14,0x51213e77f8a4b0a1247f,0x406651a9d318c3efb2a8,0xd31f0b583304d9f35235,0x201347f8e6e5b2012d78,0xfef44542127767af0ccb,0x2c28266ecf58e5649287,0xbb3d6ba90149aa7fdcab,0x849c3ff602e58284b54,0xbfd81a6097bb072b0369,0x6a0bd3f5a9850484c5a7,0x13d7ff9c56a46a94c020,0xc25974fc2fc2e288a060,0x28080400520379ff793a,0x14521ffc7fd9e393,0x1ec94209abd63dfc9001,0xf751870b0980fffa5cfc,0xd7e94258000002a26fb3,0xfd9f2946801010052df8,0xebf9a1422a8004e1ffc7,0x3fecf1a88a02010014b7,0xe7dfffb2030008990ffe,0xeee654830040800a57fd,0xf8d7da922c000828a43f,0x53efb7fe7797c19502fd,0x18afff38cf538d4b011,0x9450bfdcfff964a854,0x32000113019f3f0b80c0,0xd3ffac9804100654ffeb,0x802fd39fae014200987,0x844100144e3cfffd92c1,0xdffe16490210065be7eb],#[0x7d7e02888020028a37fb,0x11315cabf17300b0268f,0xc08200ccbecfffae3800,0xff549160130bb67ffd71,0x5de7ffef58410061bc7c,0xab5286f3fd4a0000289c,0xf1c02cb409dbf1bbf180,0xbdf8ddf8c055a95bf1bb,0x2da04c4eb00a7e2a06a6,0xf934925a04cdfafc6869,0xbecfc49260200000a439,0xbafefbf3b84994080267,0xa600029853e798ec2988,0xffd91c1010189fe9ffec,0x4fa3ff924e02000647d3,0xc02c50a3efc93301004c,0x80535ffffbc1aa0846,0x329affbecfc2853008,0x3288f8d6bcfc28c3000,0x2014f7fc2d67ea068000,0x14f7fc2e59fa81a0200,0x4519fe172cfe45a04000,0x5a973fc2d67f22d00200,0x100a5bf1bbf9925,0x29f038311af7f177eb14,0xb37f3ecf008000d13ac0,0x9efc6efe64956a59bffe,0x4ae7feaefffd9e000101,0x286fe2efd62800200001,0x280ff8197ff55040002,0x521ff13ffd02840000,0x2290ffe177f8dd804000],#[0x5307ff034d7e37080000,0x60c00d511f90e9fcc28b,0x3cc28b52f7fa9f4d6fa3,0xc013978c8998152721ae,0x34d49013864fa5bf34d4,0xc7af5288153379fc0deb,0x9bfd644d22404013d781,0x508c0260fe348565b089,0x97acd35300509fd7d60d,0xe06f59a6a4809c38c9f4,0x9e3acd5291202889e3cf,0x34d4c0135f6ee7d28c0f,0x1bd669a920268fcfa5bf,0x12df7ee6dac80edff8,0x2df9a6a60098beb05696,0xf9ffc0deb34d4901367d,0x9e9a11152df6e6fd2c80,0x9ff538d4b0115327bfb,0x40179dffffba7b06a803,0xf40b008009d6ff373815,0xffff643d914200c37afc,0x80c67bfbce806214a61f,0x44202fbffff37486c310,0xcf384e51080c2dfe7a59,0x805027f88cb42c96d3,0xb5000004d1ffae98088a,0x73ff05a40040268e7fe0,0xa8825cfc0d86b28c8134,0xef125041001377baf965,0x8021327e37a4ba104adf,0x7fc23c0040bf7b81d525,0x623ae5d749068146fff8],#[0x64f1d40d50199469b38c,0xc8a24dd9f9ed57189102,0x941c840504debceb1408,0xbbe47810101927e9c7b4,0xf1c24149aa11aeffff7c,0x367fe60e05c65500a9c1,0x80c9437f96382675a841,0xf00020341e7d33626756,0x3480550bfff6f3c87bf0,0x3068909347afcc1c0ba3,0xbe1ff8b804000ca2d673,0xff9173302e94093effef,0xc7a5622c0080000539f9,0x75c5498048000294faff,0xd1fdc0b88a5495337f7c,0x519fcfb540f182204,0x1c454d9bff6caf050090,0xffc4e0c0017771b502b1,0xff9c772b14a760069f7c,0x9fbe3cccc98440001497,0x116a6ae0b7b58ca6a6a1,0xf3ff6e15005c1e16e42b,0x7f617d24c040100a577d,0x8054ab4d3efb0cc4b37f,0x1ff91c0420311fde5d7a,0x80c47d56baf52912ad2,0x4246c02c4fa397f92701,0xe7234084064bffff7887,0xdc2ded4b40a69affef97,0x79fae5981f03408200a5,0x40149385bdae25911a9,0x800a439fae5985f1681],#[0x401484ff5fe0fae11002,0x1437f89ebded6220000,0xa23e73fdfd3e050890,0x2158ff3f55f971ec0248,0x93e21d94b4026453fb5a,0xa9102600b3930f50604d,0x7e87472a80953e94eb87,0x61e3a12e4f88747b0128,0x5f3e94eb878f04a01672,0x35a104cbff266c3b50a0,0x71a303c89256ffe4f9b2,0x1ba830272fc1dd684124,0x75c3752204e9ffc01f26,0xf3fd9b0cc8c62edf9f4a,0x440603eeb146c410a4db,0x4c3750604ebff37b23c5,0x4a75c3752204edff803e,0x805ed3dfe7d284111f9f,0x3a50880d56ffcdce6b58,0xf0167261ba8302867ad2,0x8c9f4a75c375220501e7,0x184f8b59ccc1204849e3,0x52d0826dff9b9e2e2a00,0xe4c3750604fdffc9f366,0xa53ae1ba910274ffe02c,0xb009cdef37e960086fcf,0xc74041134ee3fd43a140,0xfe7ffde3ac8a80032ed3,0xdbff6e08e6002480414a,0x800305c63f2460642009,0x14a760069e7dffcf1a05,0x8430000014c7ffdfb918],#[0xe9596c104e58c7ff054a,0xb3fafcd354214099bea4,0x10278f3f81be61ea0c09,0x48131347193e92f987a9,0xfdff2e94207cf1d66ba4,0x4ad2a082599cf76a5854,0x93ff81be61ea0c098bf3,0x5801dbf3e90fe1ea4409,0xf9f9f1e069825bf7fdba,0x2a68f1ffcc1c282425cc,0xe20a64b5ff895618100,0xff9aea6c31080c77c75f,0x1953c767952a9018dff,0x246c02c50aa67764d2a9,0xe1862101a6ffffde2954,0x70e94040627d7fffc6b8,0xe0a00000a173dffff7,0x7bf1c3597090264fbfe3,0x4bb0412b6ff885978209,0x9bb7ff525890256ff7a,0x3328d4e1af5aeba4834,0x66f78c6820499e3a81aa,0x2c804e1febf987cb2502,0xce8e5c804a9e7efe8549,0x4e1e7cf1d9a4a9287ff,0x9918c5c3ffc6281cb018,0x9628d882149f7e7fb361,0xe7feec8f02080329e3ae,0xe3f50a48002002503f3f,0x94777d63d33ea50826ef,0x290ff1ef1184a000104,0x9d3fcfcf1cc463400808],#[0x2424ede3fecc5965000,0x678b8104019c5ace6609,0x4148002002503f3fe7df,0xe2220c010200296fe3f9,0x1591400200128cfcfcfd,0xfff50e8502c0268ff1ef,0x7dffcfff8e2481040190,0x44097be3f42970002022,0xf99f7000808c36c8f108,0xf7fe9fccf260104019d3,0xbe7c7e48c0c840136f,0x3d788808b6ffe7898042,0xfdfb50b14a76006a17ff,0x7ef153240200800a607f,0x7ffbfe71ec84404613c6,0xe0410061bf38508b0097,0xf9da0240049b77dffcf4,0x5924cee1f2288999a77d,0xe1f238999a12ffbe2b68,0x4ddcfdefdf14230624de,0x8209bb5e3cf1f8ad884a,0xefcf520164b8bf9d2b2d,0x12e2d66ba4480a2272e7,0xfced24844c5fccae5848,0x264fcf8f03410254f3e0,0xc509a04b1ffcc5c0a0d0,0x7e956181002a6a8ffcfe,0x67fcfbeea49a0480335e,0x45fbe3f5a2c0008004a0,0x91c101030b7fcf0e0011,0xffd92701200c6ffdbfe7,0x50b7fecdc002045f7fea],#[0x292ffffde2954246c02c,0x315fc678fd4853008080,0x4942ffe7ffc7224008a,0x808029cfd6bbe3024009,0x10014d79fcb977c60680,0x1280e7f2e5df58b408,0x92a5b25cfd6bbeb14803,0xf1c5800020805258c7eb,0xc3800100000a9bfc7c63,0x7eb92a5b2589febfc5f1,0xac7e31c000000805458c,0x97fdf58901611337f89d,0xe3e38be38b00040000a6,0xa13fdff9a80220024ddf,0x539cfedff9814200800,0x397f3f957ee87b008040,0x96c933fdff43d1048009,0xbfafa1e8001b266f73a0,0x181e4492f7f7104a0c95,0xeebd79d64ae45126ec2c,0x109abfc7dd628d108526,0x8e680817c1fbc80b2bc1,0xd5f8c15aca312aff96fc,0xa9100daa3c8d27591804,0xdf96680817c61f7002b2,0xc1f70332a9100db7ff94,0x17cff1d6733068909363,0x2f600132ff94ff166240,0xfde44caf044258fba2c,0x74041135d3784e624017,0xff6f3ac3410063df71ac,0xbff6caf2124024142fe7],#[0x1a71f7cffc72a1005cb,0x4c020028ce3e460529d8,0x7c38829935631ffd2654,0x1ff72d5f42412f7f7f61,0x200a39eadc0cccce806c,0xfb0cc4b77f8116e8a228,0xbd5b819999d00d969a6e,0x9d00d9690ffcb28840bd,0xf24250401433d5b81999,0x3fdcb5e40c12d7fe9485,0xb25cdeadc0cccce806c5,0xe4088a0802818f7072d0,0x7fd6011502002725fe32,0x9b3cff63022901004e9e,0x6651a9c31d79e4d140a0,0x9c18c48262fd7fd03540,0xefc0cb11154093e7f939,0xd25507596b3a001467f7,0x899269feef194d0c59b,0xed64a364993fbfeeba95,0xfd4f9a594081001422c7,0x54c1f7f0bf8b3cb844c5,0xcc521124e984bf032a80,0xaa2cd67a8413767f0b7c,0xfeb7ae8e006010509eff,0x3b7fd6f5d5810200276e,0x800192f9853e4443a015,0x4844942ffbf1ff3dabc0,0x80000298fcff8439b331,0xa83fbfe87357c200,0x2424d1e57d83d5e60080,0xa60100000528b59cce90],#[0xfcd134080019af6b83de,0x6607f114a0094dbff8fb,0xa534c81e3052098b,0xd104983ef9a75e0a020,0x1fe21d4252b7ffc7f50c,0x35027fff44e2800178f8,0x2a6f5fef5e858a53b00,0x47fcf5f507ccc9808000,0x298d50462607f142b253,0xd7d20480137b85a11d0a,0x6727fff5b81000305983,0xdbbf591d7180004100a3,0x200291becfdd5772c25,0x2040051993e4fed3004,0x38d4b01153a76b93fda4,0xf7392a048032debffcf5,0xfe7b0f9c0c02265ffd7c,0x288f81fd60500264c1f,0x13262ff7cc3fb0501020,0xce34c120963e179d6052,0xa44fdff92c5200ba0f,0x499307afa93e264c0408,0xf5e8508272f1ec0ff385,0xd5a040800a73fcfd7483,0xbcf315264d9c75d7483f,0x64f7d281020028eac7b0,0x99fa3800000100a7b3d6,0xcf4c101000005383fd7f,0xff10e825d80589cbff4c,0xdcf34820800000555fff,0xd607fc01221235afeb6b,0x284fc75f7c0a02904c8],#[0x54df8eb8ebfe050c000,0x62fc75d666bc7b010000,0x4ee7fedf036a11140c94,0x8bd8b42094bcc790e682,0x41367fef7596b3064993,0x671a413a7f0061716715,0x5d4234c224f193e9481d,0xfeeba95089926ef7dfe7,0x183f700750bcd413b73f,0x17ef79f163f6b251b24f,0xa7cee0bafcf9fd526240,0x2903aba63482701e199b,0x643f70075449cd413a7d,0x7454106249c5da734100,0xb82d9c5ec584124de2ee,0xeba63482681e5e6e9f3,0x3f700751273504d9f4a4,0x9a0957e7e3da39a80060,0x7979ba7cee0b57511aca,0x41367d2903ae98d209a0,0x988800180fdc01d449cd,0x2501be2ce32a097666fe,0x25610c49b3e90face348,0x3eeb27621293375ebceb,0x5083f79d42f3504b5fe,0xe5b82d5e6319d4c50000,0x4b475d31a41302fbcdd3,0x1407ee8751273504c9f,0x10429307e318bd314000,0xe6ac31000329fdfde63b,0x5d7a425000828dfefcfd,0x3cefff47230002f1e7f0],#[0x7d7fdebc0c0a53b00350,0x8e7f2726651140000150,0x41323afffbc97d4002f5,0xd671a41327f037c59c65,0xbee75128668258c9f487,0x51952f47ef3a85e6a096,0x7da45020027af038f5ea,0x685e666e9f2dc1745f5c,0x866826cfa5a3aba63482,0x875449cd41357da1d512,0x3f1a83da6281001407ee,0x953fc67f15b340400a9c,0xa8999a099bf3f668420a,0xf3d4e8d4b0115397d803,0x9fff675cf60c480325ff,0x1417d803aa26668269,0x666825afe7f055f64259,0xabfa04210013971c0ea2,0x29afb007544ccd04dde2,0x28e8e7f1446254450200,0xd04c9d0fd79038280000,0x2431000331d7dcea250c,0x43a8999a0997fffe35cd,0x26d66bfd3950000c575a,0x46a0e6d18fc11d595014,0xd7188582496dfe01a208,0x3fdfbf032c4450324f11,0x9377ed5d4b6a598300a3,0x22649bbfff9d7508d308,0x6b251b24d9feffbaea54,0x74b2808080284fff163f,0x57d644aba79204fdfd77],#[0x57faeaae8e002420511e,0xaffd644abb2c0404014f,0xffd9333dabc2020335ff,0xfffd935dfd30202033bf,0x294179d6488851449b7f,0x194fff9fb0ba593b104,0x9350b2fff67fe689a101,0xf77d2704040674b987f9,0x77ffa2704080beffffd2,0x775ff7af0b14a76006a0,0xfdf5d599a4c020020150,0x4060ab1dafa4082026c,0x2000053bbcefff5b84,0x1005084d9a3f2a39af0c,0x71a97c84184d612975cf,0x29b0458f97a9440a9a5a,0x2c0454e4f6f82a482000,0x4a84040cb75fff3d4e35,0xc14020200a57ffbb8fce,0x7671a40304c1fff82ade,0x200a8775ff2582040bc7,0x481387efc8ab6264c020,0x80802a4ff3f5ca3bd7a2,0x100519e7eb94556f5680,0x549faac552fa5010,0xa9b37f8f1c717d1c0008,0x28458261532d8b1aca81,0xf814200100a13f1f93f0,0x8e3d8040040294fc7e0a,0xf81b5088aa04a13f59e0,0xc59bdd65ace8125cfff6,0x15140231361feef194d0],#[0x7c58fdac946c9333fed7,0xa9811aecff9fd5268081,0x9bb9d15041847d390525,0xb9ff8bb9cd040185cff,0x50101859ff8f68e6a203,0xc7cce902424bbf337f4c,0x8080cb7f798ec41424b1,0x49002051bfd9ffbcd586,0xa86068824d1fecdb8bc8,0x3fffa3950202f9ffc63f,0x6bfdf3c60529d801a759,0xd635f15e4ca88900100a,0x1444c3c7f7c3f2fa880b,0xe7ecd0892250e3d524ba,0x92fff3d4e8d4b01153b7,0x1134cffbf3ae7b068081,0x24a00a03ffcf65cce060,0x81602009cbfdecc3fb21,0xe312a2240401487c9afe,0x73207048008051d1af8a,0x89463dc5768592d9d7f,0x3a049fbe71f9036a1115,0x80b3064a1be7dc1d65c9,0xd0166600d4edf3ed74b6,0xe9e787f5b084019af999,0x67f451eaca80953899ff,0x1aa13fa28d2f1406493b,0x81820c40f9951a02ccc0,0x7bc2100627ffa79f5dce,0x18951c04a9c7ffa79e17,0x32a34059980353f67f45,0xfff4f3c3dd784000335f],#[0xd4f9fc31a5e280c926dc,0x6000c57cca8d0166600,0x6240039bcfff4f3ebfa6,0x95e10101a07ccbcaf005,0x6bca80253ee7ffa4fd2f,0x46a7d400149ebe8f5d14,0xc2ca8d4b33006a88f5d1,0xdd367d7e1e101019ef03,0xa74f3ae178b2d1049c7f,0xd505f47ae8a35c7004,0x200067bd785951a9666,0xd00212719ff749fefe0f,0x3405998035467f6d52c6,0x786f02000643f9f5f32a,0xbcb1e050d1269ffe9e7d,0x99bfe5ae550d125efdf,0xc0080033cbcfaf351236,0xac48007375e7eeff0bf3,0x6425913034f0f99795e2,0xe1e65010100525e3af26,0xd746a95960113c7e7f49,0x72fcfe93ef1400993679,0x6a80f5d147a358002a,0x913034fdebc2ca8d4b33,0x70f0808194e3af266425,0x4fbc500264f3fee9b3ef,0x599d4b33006a781f1eba,0xf5e4cc84b226069dbd78,0xd1eba4fb88a040800a3b,0x3006a8cfedaee0b80a44,0x4c0d387f3e07cca8d4b3,0x810200284febc9990964],#[0x2f5d0643035cfedae8c5,0x34a97ae832181a5a11,0x6c134de7f9e7dee74008,0x99810001981f6eabea24,0xf9e01000189bcffbf77e,0xfbf998001019de7eeffb,0xff7f3c0002031379ef27,0x13ff5b5088ab24cbcfdd,0x2e49d024b4f1c658080d,0x4e9ffada9660c92e7feb,0x20026ef91feb4980400,0xe8a4320104e9f8faeccc,0x4e4f1c61040679f8fa,0xc8000276f99faa99900,0xf368e30910344fc7d7d1,0x804fdf338f0a66002013,0x1e13034cfd62ab859800,0x33af4160800009fd9b47,0x74fe7558930400004fdf,0xa02a52f5bac70bc80002,0xc7cd2602009c3ffc3a88,0xa35f2f8a3590304e1af9,0x8009d3f9f7a16602009b,0xc17a1209e35f3ef12410,0x5b19304200270d7c3a55,0xb7fef2070c800027cfc7,0x9bb7bf3e047001009d,0x11000013f7ef3e063001,0x7c0c0800009bb7fede01,0x3a7dfa1352c55926efde,0x98324e9d2fd08b927409,0xca02010014675fa5b405],#[0x5d1c005020a1a3bcc7fa,0xbc2eac040200288ef31f,0xf39faa58090000511de7,0xef31f5f080120000a236,0x2dde7cfe7f95e1010198,0x13bbcfdff2fc3c202032,0x288aae63fd0181000005,0x449a3bcc7d622c080000,0x481909b074bcf6baf143,0xd9673236099df2ae752c,0xfbad71808200009e3f7f,0x478007adea64f10b51d,0x404014836f1c4a00a69c,0x808028e8aae738f9940,0x502040051155cf7ce818,0xc581020028e8aae73fc4,0x7f8f732360962ab98eb8,0x1477fe1f32360923b,0xe646c1376ff1ce8e0104,0x7844240000288e1e7f0e,0xdf7c60240000276dfea6,0xedbdbf7c44200040286f,0x4224edfbef8c04000804,0x9724e81274fbf032c445,0xef75b40598324e9f7075,0x27ff3ff2fe2134100633,0x191ffcffcaee7454106,0x400191ffcfee57734d04,0xc5400191ffcfee5ee34d,0x469a020323ff9ff95f90,0x5f9534040667ffbfc87e,0xf8178b2c41269ffcfcc9],#[0xffdfe4bf8a98800194eb,0x4ffe7fe5784d31000323,0x52be3d7ff8fcbea000c,0x89fb3af80790489010,0x9534040ce71f18354acb,0xf904c480323ff9ecc97b,0x464d140800a573fdfe4b,0xffee70e95000653fba83,0x3ff7008a80000289be3f,0x687bf3818500000508b4,0x81bebfcfe7f0ce8080c5,0xa57c7dffcfe1e50101,0x993177d57df11cca0202,0xb42e054c4beabef8ef4c,0xc7681808080294aafbe3,0xd57df1de993268f955f7,0x57df1d88a040800a2a97,0x18aaf3c470c9e91337d,0x20028ddf9ff33a66f024,0x1001467f15f7c466b009,0xd58ca9938afbe380f840,0xb54212c0c27cd7a3e557,0xe23a2e020080538a303f,0x4640e0200805211f8afb,0x99e2384b0309c3f15f7c,0x607bfdac0800002828c2,0x84787dfffbf784040608,0x209abb1dfc59e2402002,0xf59516127633facf1240,0xc77f17c41248009e3e2f,0xa1b183ee28d50c2027e,0x68013f623f9275890010],#[0xc50000050d8c1e75c168,0xf1e69200009db1dfc585,0x802807d8f29c40d1a96b,0x404014463d1fc5e64480,0x1cf328498a3c7f07a162,0xe8fe2f92281001407efb,0x63e7d6c571408009e31,0x27e19bff95c12400014,0x201430cd3ffa8a4004,0x54000013e7b073fe0612,0xfeb0a000009d866fff14,0x43fa39a44808028cf773,0xaed0feed0b120200a4bb,0xa2bb43fbb1245020028c,0x4018aed4f5e193140800,0x800a477e3fff33d835,0xd946ada271da1ff09513,0x8ffee74d8621018e6bfa,0x3bf1ffdcce186210195f,0x2821af7f30b5000004f,0xd5b32fd0d7bf985a4004,0xcfd30c44df009d55fb16,0xe7ffa61889be01347fef,0x4f9ffe986226f804c5f,0x59282ff07e7e986226f8,0x6b24d1ff3fbbd361112b,0x895ac9357f9ffe986225,0xc44ad64a03fe7ffa618,0x30c44ad649cbfb3fbbd3,0xad30c44ad64a1bfffbbd,0xb5a618895ac93d7e7fd5,0xfbbd30c44ad649dbfffa],#[0x67f7e0b0c44ad649e3ff,0x649a3ff5a618895ac937,0x440f59264faf5a618ead,0x75babb2f841274fff4d8,0xa43fefbdcba69f24c0b,0xaa24ce2ff5da08b90420,0x2f5baf0f8c92b2f4233,0x1040bd7fbef72e9a7c93,0xe956bcbf024bb7bcf43d,0x511ff7dee5d34f92605,0x893d7fe96ae44d48210,0xa69f24c9f006eb75787c,0x4ff11968592e5fefbdcb,0xd17faf4c0720840142fe,0x9387fb7fc4568208009,0x3be04963fca38d30c77c,0xfd3611df024d1fefe986,0x9d3e7c69863be04993f6,0x8c9307fb7fc456800200,0x1885e324e43fdfd30c67,0xbfa618cf19258ff6fd20,0xa347adbf4c319e324e9f,0xeb268e409bde1d225b99,0x7fc88ac9db0827293df1,0x9697fc4e72614604c52,0x39b06604bdfc6e727344,0x95ded8a44b7334efe37,0x19e5d18925af9dbaee00,0x24a5f3dc01f10094a3f,0x7eefb9dc80ae7afe037a,0x6a1abe445d535140270,0x1387ffdeb4a06a94c02],#[0x9d10b260e35e5713db40,0xb35d22405113b667f15e,0x983cfcc989dc31009d16,0x90804d83feb37a6d508,0x3c26c48280509f12b89e,0xfeb03e373094027c9f90,0x8bfccc96d02105505fc9,0xe7fffdf7049848210673,0xfcffffbee09bb1100647,0x10430a73f350f40040c4,0x924c8410831b7fcd9484,0x4c2adfc937a2200c6aff,0x2010814afe63dc465a16,0x100551e38fff414610,0x200a83c74bfe550580e4,0x28ed6be6b31e281a800,0x1051defe6bbf140d4021,0x20029cefe6bbf245a840,0xb6e4a95af9aefc916a08,0x164a0000805293ffde4d,0xdaef252dc226e8f0b5ff,0x8a4ff911593b6104e83f,0x34089906fff593828889,0xf7e488322260e7f7e4a5,0x8f9aff8b25080209eb7a,0x33bffdff8f3a4000018e,0x4a27ffff76f3b3c80000,0x92804204f93ffde4db6e,0xc79d200000cf47aff9c5,0x879d9e400001a17ffe67,0xe2c94100000a5739fffe,0xfe6aa80040051d1e16bf],#[0xff3554080413b6bad78f,0xfbba1b9404020a2befc7,0xfba1bb2000400541fbf1,0xdab964c21b92d63d6bc7,0xb1d311cfdab583410dc9,0x474612555ffbebbee2e4,0xbf88c4c70924b18fae1,0xd882698b59ae42344c4d,0x5beab895e804955ea140,0x20f24a4a9fd5e0bc4c49,0xffcc94031082a7cdffc,0xe6fffff6886ec41019ce,0x90195bfb1d0f4120303,0xf711968592fab7d8c37a,0xfffff68d0ec410195fc9,0xff0fff0c94100000a06,0x943fc3ffc32500004028,0x9d4719258fe0dd77404,0x2491fedc0d8c492947f0,0x6abd112124a9ebdc05f0,0x840d3747f9754e414933,0xb0208040296fda81aa53,0x99a11d3544b1f7f85c48,0x40634e1fec38441018e,0xb88cb42c985387f26e11,0xffcbf2c324410195fcc7,0xb313a812104200a47f7f,0xd6627914841080296fe6,0x47efff2c94104004fdfc,0x868f5febcb2500040143,0x28afbf1fe9f540812002,0x1477e3fcb8dd0201200],#[0x409307e563cce3250082,0xdf935151278df98e6c44,0xd017f37110a4ede0af52,0xcf8b1ea96c80a2276fad,0x4b0ffe1f3cdcf1004019,0xfe6fa5258af52df931e2,0xc3e79ed260080335ba02,0x7fbe7a9c6a5808a9c1ff,0xe727af3b4e590004014d,0x2802807e6c5a7430011a,0xca00200a1be65f374040,0xd920020643fc7ff2739e,0x928000201449ff3bfe43,0xf3d3918000c47fa7e7c1,0xfffcf52a86ec02c4e2f8,0x4fff7c769b6188000d77,0xa575e93cf58a108020a4,0x149fa3f38e8af440a893,0x3840d427ea1f208ea722,0x8888126aff38ad281aa5,0xfedf7ac25976c8fe6315,0xff0fdfdd3100401a01bc,0xfe1f5facf100401adcf7,0x3667f88714e2244eb9ef,0x20a9d3e3d64e29c70499,0x84324fdf9c1ff3d3004,0xc6a5808aa03af7aa1c2d,0x72c800200a4bfce2b1a9,0x2e80800200a43af7ace1,0x4d7b3cb6062f5fcfe1bd,0xfe64dfeed88040c0fe6,0x879fc1e4055810004015],#[0x71e6a3bd2a90800200a9,0x86fbf1e2bbea5c324d1e,0x54cdf8f15df52a000802,0x400002a2588cb9fea51,0x98000d747ce1f5b4b25,0x10001ad9fdffe598fcbb,0x8052bfffe11e33ece5,0x92950daf38ebf27eaa80,0x4852789e79e74abe1c1,0x4029efbf9f22f1ba,0xa1000028ce3cf9178dd9,0xbe01fa1260fcc91fac64,0x7da5ac12b7093278ed2e,0xb8d0934458f5ea51952f,0x2d609523093476975bc1,0xfce0ff9da68420a9dbed,0x454ddf602d6095e1266,0xb58880325fff3d4e352c,0xb58246309349fffb3da7,0xf80f9ba0211001437d80,0x8802fdc70b5825784973,0x16b048c61269927cfdb1,0xff93fc87b24440196fb0,0xfa0fd78325040000291b,0x8497bed2d60952309347,0xe2322d7034efbdac1231,0x42052ee111937981a4ab,0x4a0932575e0e3eb45080,0xaf3a82e4509364e56244,0xe5f3098688b1a002ddab,0xb46d37d9fbaace1612f0,0x8a2146dcec27db07488a],#[0x45180446cef817db7048,0xbfc7121c704999a77b68,0x9e3af8fe16a112049bb3,0xa2bf9c67a9c6a5808a,0x902260ebe3f85b2c8208,0xb708880311ff3f97c1e0,0xb89ffdc729c88b0d3ffa,0x6488803227ffeb6c6200,0x820800a67f7ff7ffc2b,0x4a9460499bf9c83f4b29,0x7e952a08200286fd793f,0xe7a5a4a00008053dfaf2,0xf7887412ec02c4fd1f3d,0xaebfa555100000a1bfff,0xbf5d79c25d02509397df,0x6fd79af09764100000a5,0x521f967bf315a0200028,0x4c1f51ebe32265400100,0x7b10c93d46bf8cc3b204,0xda5c8008196fcb70be30,0xe67a1b888031b3feffcc,0x6e17c60ee4812759ff7f,0xacffbff3342791100659,0x2be62fc7b05680400014,0xc17cc1fd662b4100000a,0x8050bcbeffe7cef88000,0x80c17cc9ff315a0000,0x1020104ebcbeffe7cef8,0x8697a5fbcd5083f75ea3,0x477c7605205356023e9a,0x35955cc7f932a0008029,0xccf779f3fff54b900103],#[0x4acf779f3fffa86e2200,0x9ba7798eba9061041001,0xa24b8feab8608b0a9190,0x2ae040001477fee90a59,0xf06342966893e5576fdd,0xefdd7ca59a24c1fefd67,0xd57fc2355c0004027aeb,0x50dfbe5d4620002013,0x274aafea46ab8800,0x15c08000276fdd7a8c44,0xe38fc60662053541fbcf,0x1258f3fdf9132c004013,0x344004013e77efc1e881,0xbf384588200274ff7e6c,0x27cff7e0ed42092a7f,0x200009d3fdf98418882,0x3c571000009aabfef057,0xddfbcf15c4000026aaff,0x2013557f9e2b8000804,0x51840408286fde78ae00,0x857dd427434e1f967beb,0x4bc9991a80ec69f3ea38,0x9f99d7265400100535f3,0xa0a39e7183da4089a2ab,0xa0a3fdebb4333ba84e86,0x541fcf34bc9991a80ec6,0x41573f33ea5868400100,0x3a7fdea3886677509d0d,0x14d7e9793323501d8d,0xd0d45573f33ad6115041,0xa16f5f9f03b432a37509,0x40053ae3955333038821],#[0x9a24e55cfeebaa418410,0x766892a7f1f38bf9d29d,0xf52ad00800029af3ff48,0x7649947232136af9936f,0x446bce79f3b34497df4a,0x28af983faad568200001,0x1496b9efad461040000,0xa2be62fc72d5680002,0x100525ae7beb51840001,0xe249b97fdfbe2244ca90,0x34688c9372fefdf113b2,0x9b0d090100525fefdf11,0xf7c44ecb89272ff7ef88,0xdf1138455020028ecbfb,0x477ef888306b024c5fef,0xa3bf7c44c20c281001,0xa1006039fbe234e59248,0x96d9464a5aeffe610f64,0x5feea3403c0294f860c3,0x73f7c46822e50040292c,0x4f9fbe234c0728020144,0x4028258f7f22b500000,0x6c94b42fd2c7bf915a40,0x1cff9d2400013830e5b1,0xcae73f2255000401460c,0xa52b439f8374619274ff,0x1425739f9b0d0800200,0x818126cae73f23150410,0xd8410400501e873f06d,0xfc72740200009e3e73f3,0xe553ff73a0800004e553,0x804edda8ff3a0800004],#[0x3be002030553ff73a000,0xac99520200a57afb3fff,0x4a342404014c7beabef8,0xa22a81001487beabef8e,0x830a0400531efaafbe2a,0x5924800a23fd579e2394,0x8300800a4bfc57df110b,0xb2a2c535aff15f7c701b,0x3f6d529060693d25e0f1,0xe35feea36d180529ea30,0xafbe22245ca0080539ff,0xef888503940100a631f8,0xc29d98ae458d270c7e2b,0x11e1f7ffeeef88001828,0xc14e3c3efffdddf40406,0x292faf397bcad710a000,0xa9717d6371f2e4a00080,0xfa72310062b577ba4cce,0xb56aef749943aa607217,0x589cdfe9e480a9980291,0x82002a28de3f3c82a88,0x400529fadf5803cca22,0x20028cf5b3fc2c4f8c41,0x200a2ba3e2b1a3cc50,0x4014f6ba1b9fcf3eaa,0x200a304fa1e7f3ae3d90,0xa71140751fc4dba3e920,0x712228efe71c7486f052,0x840105213afb4b4440b,0xb712227afaf2bcbfc716,0xde440621368d35fa58e0,0x94e03f391309af3d2e03],#[0x7e46afb4b1c10f911433,0x4871afd21bc14a9d1140,0x14850d7da5a2205b8911,0x89717e70fe238a108000,0x3e8391b1352fb4b9a0f7,0x89782f5e040192876974,0xe0f220b2625c70b9a4af,0x52fb0173495f1316bfea,0x99b168fd62bf7230593,0xa54e22747ae8c3942d4,0x35328910400534bed2e6,0xda5cc148f113563d7e27,0xe021cc7484820800a697,0x5d1f19fb78a0400501ff,0x7f513e3431041001507f,0x3fe78d2a80080292f2b4,0x27a95b2000802aed75a3,0x9bba3d440cdb37d68eff,0x47fd84f87aa00a74751d,0xb21ff613e1e920200a31,0x13768ebfbf9bc10e7113,0xc16f889cbaf2c705b891,0x22043dd8a487d7f7d29b,0x5c42820905255307e055,0xa4a08200292faf3970ff,0x9f5510400518bf387fcb,0x1ec820800a7b5d0dcff9,0xd1ea2066d827d0f3fe57,0x2747d2810013cb4a8fdd,0x79c97c40582d83528ffa,0x1081533e610888a78a0d,0x1497d795f71531c5820],#[0x24d917e7b8e238a10082,0xc20949af3d601a2f1b00,0x727d78500449ec93f016,0x40a11316bebf83c91089,0xc4fc5ce844b43fe64fee,0xffde21d04bb00b13d747,0xa3ebe4f20aa216276ff,0x49743cfd71e6aa20800a,0xb7d0f3f5c743d9041001,0x28a8fe2691e1ec8513,0x9882daa3f89a4787a502,0xe52aa34c46927fd88905,0xeab1140088288d69ff11,0xeb2d680010014979b29f,0x50f610a894286e5ecc9f,0x5f1b8c5c5a8200a01f55,0x555f1b8c1c0d41005055,0x28af993fd56b4104004f,0x50dff173fd5708a08200,0xa2be64ff956b400100,0x8286ff8b1fd556228002,0x4fd37f138c708100,0xb8000804e55fd6231881,0x98c708000805055ff4c6,0xabfce3971000009db7fe,0x13f6ff9c70e1100000a0,0x800a1a61fd7588c0024,0xc41001307aaf7af2d700,0xaeb846208009cabfaeb5,0x3d57fcb5ae002009bb7f,0x20a5a7f85b588c00401,0x14a72659ff231c101],#[0x3885357cc9fe84630804,0x2c5a8200a2aab8f718b9,0x98606a08028c555f03f3,0x47494100000a4aabe275,0x8e1c104000029af993fe,0x46b4000100a7bfe2e7fc,0x1c10000402a2f98bf1c1,0x846670a26eff8bdf3d23,0xefc23a2e504014225f7b,0xa112fbdc232b8029a2b,0x920a22befc232072820,0xc8280311fa2937fd7c10,0xa0008028df747fff93bf,0x800200a3bfc2d56ff367,0xd041001407e18bc7ebe0,0x10410014b7f85aa9ffb3,0x5000241447e18bc7e23c,0x6dff80200c344849ff9c,0x3fe77a08200275d1fffe,0x18bf7d462820800a1355,0x284d56ff277a0008027e,0x10051c317ef738a00080,0x100511ff8afbe3168b94,0xb0039a68af3c46290394,0x1de5c28a68df31fafcb7,0x5e65df9db88a00281442,0xa63f2cc79ee308088050,0x497b3247cd2eb4000100,0xd93ae63cc05c61008201,0x4029d7f13e74017a450,0x80555f3247cf7461000,0x35eff8bdf4313a382000],#[0x200209fdf4a7705deb12,0xe31200004ed0627f7c46,0x3eb5e5c4000027c5cefb,0x88f3bad7862400009eb3,0x146cf7fe57f73c30001,0x813f0f3e97d1c22000,0x31020804fd17f9b788c0,0x16bae000201420f1e6de,0x7a2d71881040278f59fd,0x502fd3e224517ad0d7bc,0x805159fd37d18800080,0xc0b123561ff4df470800,0xff7114120829c7f55c8b,0x7f71843000284e4c0609,0xfd2f2d040000290fcba7,0xdf4bc30840000a4be669,0xfaeec5082000015275e9,0xd774704100000a8be661,0x830e33cd4d8d7bfe2f0f,0xa531f8f1a798659a627,0x13d7fa2900dffe282002,0x18ce0c523ffc2c000,0x840000a1746fffcdf7f1,0xaf4100000a5aa4aef5ae,0xe9100019cfff35423f11,0x8a0001028d3267f7efcf,0x23f8490402868a45f91f,0xd737d00004028ce0c18f,0xac8fbe804100a03f54a7,0x3f58d7a000080511fea5,0xf33c7c100004029af354,0x896b18a0f3525a87f0c5],#[0x9f3f2a41be3f8c000082,0xc375c60f71fe320000,0x200009f577fce6ffe400,0xe040001427fa5aad7bf0,0x8408000288f8f5bbe46b,0x7f0001009d3e38bd7b8f,0xd63f8c00040278f5bfd2,0xfb55ef8c400040278e65,0xf8f5bf433f8800004f9,0x138717ad2f18c4000028,0x820a73f6ab1fe220000,0x1437f254086fe3e280,0x14e70421ef8fc250,0x623ff402cfc2df400,0x10000520beeff0bffc1,0xfa41000663d099fa357a,0xe820000140f21fe79f73,0xdf3ce2000321e80fe217,0xc7e1040000281e43fefd,0xc605fa000080519e26ab,0xf9b3cffce0020331e82f,0x6abf7184000100a2790d,0x9c303df7b5884004d9e2,0x3e50330303df7b5e0200,0x98855940d6c0177f909a,0xe4bb76800d6fcdff7625,0x7f909aba1406d7b0561f,0xfef89518d41980dac017,0x2b39fa4d0f0801adf9b,0xf20128c7970188000a94,0x421070ffa4d2f480d97f,0x683def213566881bdfff],#[0xfcdb30931a83440defe8,0x8422e7f69277a40687cc,0xf921ccb8157320029dff,0xafb16fc37d0201b6ffeb,0x7d8b7e1be8400707ce5c,0xec5bf0df4080687ce565,0x5f62df86fa1001a9c3eb,0x683dfe426a98018dce1f,0xffb51964ea20140d8e7b,0xe654985144406d7fff7f,0x40d100200aa7ff9ffffd,0xab10028d87fbf8ae10b0,0xa93a880301c5a0f7f909,0x386ec05f7ffe7ffe6d8c,0xdb78684c20234bfa6d7c,0x4cb89845080094cf7ff4,0x36fc34261011a6ffe57f,0x96c4c2080800958e7fe5,0xb6366420094b7ff32fe9,0x65c6cc840129affefb4c,0x589d80812541fff55c1a,0xe244c0409294fef06992,0x20d0311580a13ecffd32,0xf48342c115809c3f82fd,0xf8afc83603c0560286ff,0x7883e7f48340c4560280,0xcc280f8afd20d03b0dc2,0xd86e1387c57e90681d80,0x3603b0dc28afd7e90681,0x16c737aaf015e1e2bf48,0x3bf035e2c0fe9b34e5af,0x802ce7395d9ca0343fad],#[0xd2c1584cce57ef001a5,0xd2fff6fdfe2476122b2,0x1940cedfbfc48eca8ac0,0xeca8d2018d802efce577,0xfff5d0ea8f82db7ffe21,0x43fd5cf613aa03a93cf,0x2535fd2d8f169582a425,0xd57f4b7b11695a0a98,0x707ffccd82b3cfe3cc64,0xdffeaf9cc310f6545600,0x60948d26fed7dd519818,0x6400d97fdb1e2d20682a,0x36bbfff9b05679fc5cc,0xab7ff21ffe621c0ea226,0xb3f19921ba3a8714c100,0x8950dab268672bf1b006,0x6ca71a8f4b8b2352086,0x8bcff33683973f8f31a4,0x7f5cff9c930ea9620e03,0xf3af056b321a0868946f,0xce7b9b41ee7e5771a206,0xb5efffb30d59511601a9,0xdee5fbfc42e70460a06,0x2281e7fcf8807a411540,0x810a0abe37b89129d4a,0x823440361ff493c58a55,0x2002a40343ef9cf881cc,0x48228301c5ffdfff8967,0x495d9c1435b97eff100f,0x805048005439fcda0f7f,0x914480dc7fbfd442a10,0x88c00373cbffb9cc03d],#[0x41037bfe7dffff9958c0,0x2adf3cb7f9fa617a413,0xaef1cfce215080049820,0x8ff9fb41efe92bb38021,0xfeffffd9958c8220c00d,0x65fa41b2ec352010563f,0xffa497bb4be08339ffd4,0x32fd20d5d82d0082a596,0xff492dbb4bd041b4ffea,0xf9265938222301c1fb2d,0x84664114600e2f773f3f,0xb3801118007179cff679,0x1c114440eacdffff984c,0x88c40737efa4bf3f9846,0xc00e0b37fdfdf2659300,0xd2ee7fff982659c8220,0xf940d0dbffc42f4411d4,0x47100d89005dfe40b1,0x988046140dcdbffc4b8c,0x20d0311ca0281abfbe25,0xe90685a08e501457ebbd,0xfafd20d80ec0721437fd,0x4b5fafd20d03b01c84f5,0x73603d4ddff7a69cc23d,0xc403d048ec069bfef482,0x82b0ff256fe800d4dbff,0xc9005dfe4ad7c280dae4,0xb9b7ff89538822d001bd,0x809f6fef895318228501,0x47280a2bfade9b40c472,0xf01a80a4bfade9b42d0,0xd03b01ea6cccbf03e9b4],#[0x23e9b40ec07a9ebf5fa6,0xd3f1bd36c9b01c850cbe,0xe909fbfef4db2611c84d,0x380e909e3eb1f4da3088,0x2b8c11430361f9fd368c,0xce7ed4cf0801a45bffc4,0xfcc4b3400450801d920a,0xe215e208a601b1fff14f,0xacf3ed4cf0801a1a7f3,0xa7fb312cd10450801d12,0x9260c3411042407a7ff9,0x98c00410c01cdfefe8f3,0x24c608211038bfdff660,0xb3f533525c804dafed98,0x54ce0fd7e298b4b9009c,0x7b5001ad802cffc835b8,0xf95aec280d890565ff2b,0xacbfe56eea0991200b3d,0x6fef44a31c1141407360,0x9bfdfa810a8c825820a5,0xf7ffeffbe2518ec50486,0xd24d5ffe247641154006,0x3ff20d7a1664bd2f9596,0x802cffcad750a06b600b,0x676fff10f6546880644,0xa8f00badfdf10f1d460a,0x972e4b0801423fffd76e,0xffaa43ab5340338b8cfe,0x15ff87e2d2b054849d57,0x6fbfac3f1695a0a9825,0x97fff2482bbffa995820,0x7fffc882bbffa9970426],#[0xfd1fecc43d4822820074,0xe0c8245f6d7291014eff,0xff653e2d20682a6094e4,0xc2ffca7c5a548a982505,0xffe48015dffc132b0801,0xf800012afac2344114ef,0x2c7fcc43d4a8a0801ccf,0x79ae2c89090431291fff,0x48481f5b01220caebf7d,0x83d4b10120385f3fe000,0x64b1043128dfff67ce49,0xb24b0042adbffebab92,0x440600d87ff889242747,0xb1d440440debfecc1b65,0xf885ce08c140cefed8c1,0x88a3bf596693048985ff,0xa024fd0571a5b3f06a92,0x15400e67f7e973f07924,0x4d3209c7df39f1023a41,0xf854a44a511537eb2c4a,0x44a75288a4bae733c6a6,0xffc7ab41666abe005ee2,0xa2954900aa87ffe00497,0x823440339f3e3f89209f,0xd659a4c12261ff3e217c,0x17eff100f48228301bef,0xc4492123e164948000ab,0xbfecc5c641108806c3ff,0xb5dfda8c5938220140e2,0x1b1ffcfe600f42228901,0x2001b5fde65498045110,0x1341033bff9958c008a],#[0x3002688034bfffe985e8,0x9964c0260081a9e7f32e,0x83df9cad470029ad9e77,0xd9958c8220a006d7fff6,0xb7f6cca9382200c06d7f,0xfe8580940f816130508a,0x4879df2689d404180e87,0x24bffc9a72a02a006c78,0xd024bffef39545100cc,0x585990497f7ef2754414,0x230100ccc709b7207b,0xce6801180806679ff9cd,0x18e121bf58970d323cff,0x4006e6384dbf51975099,0x4006e7fbb9ff9c690450,0x130809a5737f9c690450,0xed0d901343dbfe9b6dda,0x9570c9a08a87a7f94db6,0x261a4d04575f1f68f90c,0x73210451d88fb47c864b,0xb45732104529d7769b45,0x9446104804654debb069,0xa7c0b5b859a6ff1f77ec,0x33040288080057b0c709,0x2880800565f8ffd9315,0xcad42693e47fecf53304,0x6f6e4ac34c831c26d769,0xfe71a004504006e63848,0x73ff38d00228200372e7,0xfcafe9b65c0420202299,0x9a79fd36adf846101351,0x842621f69b7bf0aa1098],#[0xe0880301c07da6defc2a,0x5024a299fff3bfc93164,0x28c01a8ffff1d4922194,0x451000dcffcf30af002,0x8a2206d7fff3fd932ce0,0x228880e03fff308c300,0x8125148fff99f7c9964c,0x82801baffffea4910ca2,0x400e2fffe7f249967208,0xeeffe121fecc9ce5405,0xfe79048f7cc9c9d40418,0xff9b3ff39a00460800d8,0xb044709b59036ed7343f,0x7f4b3753304028804000,0xb3ff39a41141001cafff,0x1c269f02abeb999fbcfa,0xf367fe734008c1001b51,0x73fe9fcd03022406a7ff,0x7e7fc930a04440ccf9f8,0x1cffff270281180320f,0xcfcb0f9cdf8696002c07,0xe597f9f64e54001806a7,0x1d165fd3ee09d4000606,0xdfefed9bfd61a4110410,0x9bffdf3d61a41101401b,0xfefefbf3ac3482202803,0xf8f6fe73400884101c5f,0xedfce6801101401c1e7f,0x9cd00220280373fe7ff3,0xfce48551680dcffe7dbf,0xce485404500e0fe59177,0x39215006806e7f2c377f],#[0xb213b38081a9fcb0ddff,0x909dc6020353dff683df,0xf4dbf09de80032b41efd,0x5ffd36fc277c0018d97f,0x9d97ff4dbf09df000636,0x6e7ecbffa6df84ef4001,0x383fdb05672fa62d7030,0xb1fc0bfff10ac091140c,0xffffb60aee1f4cb5c0c1,0x1c9ff3d108e2091660d6,0x7fcfa1a0e125f4cb1c8a,0xffe7f65985741209286c,0xae63f5852052256d8299,0xf0d17b2ed32ce4a1aeff,0x75fcfe615d049650d0f3,0x9052b9c9249c75b42f3e,0xd850c863e4964ccca3c0,0xf74c800d4f7fbcc1240d,0x9ba64006a7607ff60279,0x7d8e420393387ff6027d,0x835bffecec3a7e4241e,0x20d8ecbffa6d33b4f00,0x4036b3b0f3fa6d33b4f8,0xb01235bfff1098128140,0xd6048d0ffec1077bf32e,0xd50831b9ffd82b397e65,0x62830a91fda0e597732,0xda3222361fc7dfab9264,0xc6028687cfed5c39ce4,0x9bc73da18257fef306c5,0xd07092ee65c6418ddff7,0xc9f9df3985b4128191f6],#[0xab48657f4863dcedd10b,0x4b46011363ebf48634fe,0x84001457bf3dffd21a66,0x226ebfaf2bf821063064,0x2cdf9cffca413cc968c0,0x7997f41121183242000a,0x8fe432918154c24555fd,0x4523001530915871f33,0x1076cac80914f7338fe4,0x84534eb21a298fc7fd82,0x1074eb21a28cfffd7060,0x20ed9590122a0fc7fd82,0x6002a0c05567ffeb8304,0x551402a8bff3f7a42298,0x420cd67fe78f8908a460,0x41543ffff9290696e75,0x133451ecffc109861d2c,0x2a87ffff2520d14fea8,0x6a53ecffc1083b452c02,0xaa4be421ffa08a658a81,0x42c4843ff4114daa60c,0xffd7c75ac40251a05000,0xaffe798471088d141aad,0x58fffcd982388488460d,0xfcae4f9c485410243441,0xe80e3e24a340908042b6,0xd4bfe970910c30551cf1,0xe7c832a100c13c477e86,0xe07c8e9708120208551b,0x5df3493b1ca0359efe2,0xcec1597269bf5e0034b0,0xe50323f9fc48c92c5620],#[0xe4b1a4031b005df34dec,0x793933d1900343f9fc4a,0xd26fa183bee33032b056,0x1a1fcfe21392815800d0,0x6880d2c15df3919e8c80,0x258830019da0f7a69bdc,0x872e9bea340036becc27,0xff984e40ca800199fdab,0xffeae499018a0c2a267f,0xff683de9a6f68d101c41,0x20d9769bb6759a42673d,0x57bf3df7e982de4b1e8,0xfd795cc6880cb8321a01,0xfff3bd1211d5c3020a23,0x191efd3019dee9920c47,0x60a867fff995a4b2a04,0x9b424bfe484ee4135544,0x471088d020d9f7967674,0x28c105200205927fe798,0xed088361febf8379a101,0x822308839bd82bbde132,0x265da1106d62fffc42b0,0x8c08246110717b0577bc,0x78465a92021c9cff9f10,0x60ab412a40439b6d070f,0x90ae8f0008757f3cfcf6,0x2901a90106f7da1a0f73,0x1240da8004363fffa986,0x290291284d82a9f7fb66,0xa119748421aec7ce2fac,0xcc2ba0952021cded173f,0x92482856d8289f357fa7],#[0xc9ce42b3fa10693f8fd9,0xfcc1348b52020dafef6a,0xf3049036a0010defe3ff,0x565fd3775a800da3dfe,0xec0167fa49ad61406f7b,0xc7bfef504716c50501c5,0xd0f5fff12324b154006,0xa0033bd802cff4dd7614,0xd8c140687bfff12b92c6,0xad1445cc1265ff7c4ac2,0x8d6fffd4d8574d82edf,0x44503ffb05773e4cbaa1,0x9089f3e57c72c799f249,0x48449507eff58f4cf925,0xe89a329fea5201cd15a5,0x8a22e609308490fa73be,0x60aee7c99754211a6fd6,0x1ada0f73d375621146b,0x414163ff7d984e4b1050,0x32d44251b3eefbcde3ba,0x24c80c506151b41c3d99,0xcf4dda88408d97efff57,0x83628630010dafff6ae1,0xe60d240c6808343ffef1,0xffe6139032a000333fff,0x946effbcde39e504143f,0x18544fb68387b3265d10,0x11472bf7ffab59901882,0xaff37ffed5073fd37552,0xce7b683dcf4dd544228e,0xc7dffb30d24b10a20d2f,0x1a1ffe4b186c5b100886],#[0x501ad26f3fce72580b00,0xdd868d09bcef9cc2d802,0x31820033bedf1c268ceb,0x630400677fff3ffb610,0x25a88404defffe7ff6c2,0x992d54809ad97ff4d533,0x1e64b552026b65ffd347,0x54664b510809c597ff4d,0x8a8e640e8a427165ffd3,0xa8e520745213a8feb9fd,0xa640d40653738feb9fd8,0x3992d454a6d1fddffb51,0xc82402000558fecff36a,0x2010002b2fe3cf1fca20,0x54266bf8f3c7f0810641,0x8daa1a677f1c26afd0f5,0x840c504006b7f1c26af9,0xf2d840c504006a7dff2d,0xfef32a4a18800086e7df,0x7fff995a40c410106d1f,0xffda0e7f21bab100a1b4,0x1fffd995a4b104041adf,0xb47ffdb32a4b6200021b,0x2075ac40251a05000140,0x74b24ca281251457ffee,0x798471088d0106e3fffc,0x128c105100040b067fe,0x495141944f1fff885f91,0x4710910a20dc7fffe296,0xcd1c4251620dccffcd98,0xcd594941221c9fd26fe7,0xadbaad33bffe7bb06f3f],#[0x4804000ae7ffc709a33,0xd10265bfce78fe102081,0x800158fdfc7cd3a5d7,0x569aeff39e3f94410209,0x1034d4bffc709b1a56af,0x30102b17dfc7a78d2f46,0x2190efd0cb97fd2e0144,0x40830ba7fe7fc9287040,0x12022815edffffcd2071,0xc4196fe2f2ed40e9708,0xb682221adb3fe7f34968,0x40c400041b5b3f90ff04,0x42588000835bff9ffda8,0x6c211104101d5ffcffed,0x200041bdf3fe1fbff6ff,0x20dcffdfbff6ff6c206,0x835bf7fedfe98103100,0x20d6ffff6ff6c258800,0x84031bfffdbfdb096200,0xccf1c2018d82bbdf99e3,0xe59c9f19200cec15def,0xbefd21a664b3c2833b57,0x9ef3e5213cc967850667,0x2209f3bd201c35188827,0xc4246941a4ef41070d46,0x997cf904cbefff9e611,0x2bb8790c5ae500e47cae,0xace166dd0f088393fd58,0x6e3e5704817cfa265500,0x8ff9f5683dee90cb1ea8,0xdffff9ecc11930542a0d,0xe7d5083da736e970821c],#[0xf3ec8265d086a1041c1f,0xe72f902912b6c14affff,0xeb41fee90cb3d50d257b,0xbf9fcc23260a8541b1e7,0x6dbffd3c91447b8265fe,0xdcf3f5083f4e6d9dc208,0x5efe7eff098ba1b50820,0xf3394f7d825ff679001a,0x70262fea7a1ac9292004,0x28e9764c1ffc4f38b349,0x5ffe1d9707164f93ffb2,0xfeb00065ff0cbac151c1,0x6ec1fc25f889452129e7,0x159426502bfe73b3a0a9,0x51d69044d9f33f985bd9,0xa91751d693260fe7e975,0xb20b68c17fecfde0b17e,0x77f67fa4b1757fc3bc91,0x293abfe1dda8d905d4c1,0xc1001a0fe14f9112ca0,0xcb24a480142fffc4bd68,0x65ff0cbaa151bafea7a1,0x479b9cecf05969ffac01,0xa082388f370fda8d305e,0xd4608837ac159c39ecca,0xbed46a0035a3fcc310e6,0x6ad9400400055b3f30c4,0x74289c0309ff1fff8904,0xce18b540463bbff8fbf6,0x166084a0c2a7795a0e1e,0x7ba144228ed78a8f8f93,0x631041b1f3f1f5a0e1ce],#[0xa47fcc9fff260e68,0x44231d2fffc11ab01882,0x861553c2b41c3d9c317,0x1479ba83f8f934598212,0x93fe7d5a0e1a73dd0a21,0xfc7a89044cd94004082a,0x94e9ff64acc16a8069cb,0xa0541497bf127ec62800,0x8000a5bfebe8730a3804,0xc151cefff917b15f6484,0xd585471491c234ce650a,0xb518280c8a48e11a6732,0xd3bb2c28119adece7e1f,0xd2ecb4508c6f7ff9c8f4,0x810266955bffce47a6,0x3f9db2c180f99f2b1265,0xf0122379eace0d2f8086,0x3dbea2d7c8bac1047975,0x6df514cf22eb02473490,0xef80dabc968c00ce69c3,0xe036fc968c00a737e7a1,0xb7e4b460066c7df9e87b,0xbc968c00a757e7a1ef81,0x2071a54e2bf3d0f7c06d,0x34b37bfce7fa7be08b5f,0x2cac71fc87be096be40e,0x8cf99feae8208a6e5640,0xc92ca77bb01b13ff5aa9,0x82a653e67fae4041067a,0x22d58a26f7ba434ef9ea,0x2d18511d5dcf7efa34f3,0x13368af7e6dfbe8d8d32],#[0x21561f129e6b490ca460,0x6dfea7cec6ca61800a82,0xfa9f2b43652302a89215,0xf7b210da5f3aa0466cb9,0x7be03687fd50266879ff,0xdd80da0ffaa04cd6b9ff,0xe434ef9d5023353cfffb,0x404ca2e2a05aa55cffbd,0x994da9824a94c7c81fab,0x86576503254dfc81fae0,0x7d6a304006a3fc852029,0xd608c10039b9bffecf7e,0x3d608d100d4f1fd3e205,0x40280011056bfcff9f10,0xa688292fff1ffd68801e,0xa20838dff5f5b94a3804,0x150f7ff9dffe7302f488,0x7fcfffe1007801220024,0xfffe7b3017b0440120dc,0x8ef7e20fe61280094ebf,0x1057bff8ffc61d0a25c1,0xdc7f2b927f10dd020048,0xd0f927e23c8048411055,0xfff3df9dd8228280cc47,0x3fef1e9a76738a04535b,0xfde3d2a767a128014dcf,0x7893280428d20932b1e7,0x80996f1161020a23c63c,0xffa209e76868101385fe,0xa218e7684c0009c9e67b,0x2291c320904593ccdbff,0x6904432ac8f8b0e3e920],#[0x24865691ff0f9e365238,0xa6ba3fe1e3d04b291c32,0x2a1f7fff48563cf86808,0x2b68d5fc134e62240043,0xe66bfc88e7900a201000,0xffff9d308eb0463006b3,0x4905759bcfbbaad4214b,0x298a4fa1d4bfea600884,0x81fbeadfcfb014220105,0xb13fe4bcf00028005005,0xf6bf3f428800086cbf94,0x5607fc33d7800cef3ffc,0x1534426682cfb804eb0,0x6b3ff7ea0d592024080,0x2a01489056179e19ebc0,0x5e00335fe363c502f24a,0xcf9468006d60aeb39cf9,0x910000543fff7b570b39,0xab8005255aebfc11ab01,0x25df001a4e44d790cbc0,0xf259c8106e70fdbb01bf,0x4bbca0c4ffe7a1d6e95b,0xa67f77c4181cceb79b7e,0x75ba699fddf10631d6e9,0x3dfa65209e6459fa0d2c,0x2b172fffc40f58234c33,0xfdaf0ff8401e00490048,0x341c0f95e902f9e8258f,0x50a837b6ae150f218b1c,0xa77ffbffffe58c15cc1,0x8351fbe74c54814895b6,0x50a836b47961d218b386],#[0x47b826dfebf9fc615cc1,0x328ee01056dffe9c2914,0x84106cbffff80430a00b,0x806b7bf9f3fe4c5d0da,0x800cacce5cde48b7fdbc,0x308066670fde48b7f9fc,0xf350066670fde48b7fdd,0xda9a803933dfbc854f3e,0xf0506a7b339d3790a9e7,0xc0106b667a66f21b6fa7,0xe82373e67bf790db7da7,0x2889c7ff600b03df0cba,0x51d69044e9de960aa8eb,0xdeecfde8918cfffae493,0xa982c9dd9fed24614484,0x1ad802c0ff865d5a08d,0xc4707fcb3fe625f6a305,0x418544da0e165f0cb510,0x420472bf7f1f262cc109,0xaa7fffed07030e7ba14,0x529fb3f9109984510402,0x8e57ffe08d580c410000,0x148f0da0e17670cba218,0x39dfff22f62bec909000,0x39399ed9092af22d1911,0x353d0f6c844bf22d5c01,0x9c9ccf4f092fc8b5711,0xcdfcf43db21b7e45a320,0xcff4f6c904af901c4e09,0xff4f6c9095f22e2649a9,0xff3d3e9234c80e21c4e0,0xdb3448e645c6b1373ff1],#[0xf77e73f6a30400671ff3,0xbffe881eb0460a06e7fc,0x51003c805000220b173c,0x9100120a8bfdf1ffd2,0x22009073bffffe90803c,0x9020ad7ffffecb180bd8,0x2a8ffc7c93fa21ba0400,0x6fe5724fe11e40242088,0x1f31a42291c34806022c,0xccf201440200055de3fe,0x8eb044030395fcc78eb,0x680480590563fcfcf2c6,0x6692e04c13f1eabc61ca,0x7fe19e3940663ffef341,0x13073f167fbd02fac016,0x1adfff897ad01240066,0x3940671200bbe78678e5,0xcda89241a560aee739f2,0x312fb51b00318ff98621,0x89046ad940a0002a5ffc,0xdce73e51a20379ff1fff,0x580c8800028dffcdd683,0xa2cc1094185497ffe08d,0xda739f28d101c2dfc7c9,0x99b2814082ade7fdd683,0xb34af10f2d5fe3d44910,0xfdf516fc96794069727,0x70fdf516fc977d0313e7,0xce54b404cbc0a30040aa,0x27bebe06df92cf0a18cf,0x4430a7af80d33fb3c886,0x9167d4333d7c0699fd9e],#[0x5d6089241a9ef6fa3699,0xf881eb04698313fd3e20,0xfff3980bd2223041bdff,0x803c00920090543dffe7,0x53ce9df04321febf1ff0,0x8da674ee4086a67bdfd1,0xa611d6089d065666defe,0xd12ac4265db51308323,0x537dce38f01651f90189,0xc2a37fb0004dbdecba85,0x5046a3ff80b493514a41,0xeb18151b5823daf74dc6,0x518b1c0821cd802d97d9,0xa319b02086e7bb7f93a2,0xd6980b01ca07bb7f93c4,0xb06967c264a3157c5c,0xff3c4b812342080db7d1,0x2d24d4529070a89ffff3,0x5b0f2cf598151b0ffe0,0xeff2789542c7022038b0,0xe02d3f9018a6894aff3f,0x802925fecba255359c71,0xbfdfee0043f343070a7d,0xefcb3fe621e58e04406d,0xfecf109812340500777f,0xb28f103521a255bfcf79,0xc9decba80a4e2799e400,0xd3f801aa6894cfcd8209,0x727f65d10a4d37e39002,0x1ae2d2009054d150d82a,0x251ae2d282cc9525fd25,0xf00028d25090d0dc3e55],#[0xad97de4ca2042386ed,0xf76b3f0cbf09868ffffd,0x71215b400c1c2a68fbfd,0x856d0184530ac0ff18cc,0xd003070a8af9e1c331c4,0xa0060e1561fd7cc71215,0x24de2ebe638cc71002b,0x22d1c9c373a6071fcb8c,0x99226c38401538542004,0x9c38508f0a840122aaff,0x9844ff2e30209baff5c8,0x8883307d6cb285e70dce,0x311044907d6cb290fab9,0x5cd1107483eb4d149757,0xae68883307d69a282ffd,0xddcbfff10b962c00a1a6,0xc7c7f63c408c24580841,0x333cff4f881e24584506,0x27993f7680ffecfb3810,0x5c08613ff502e0538200,0xecfb1c080cad01ef7ecf,0xbaecfeb800199ff680ff,0x7891d856508313fed47,0xb3ee0130f123248e6106,0x8acfe32ddc4111f844ae,0x181ff680ffecfb38101,0xbf67ae04323c4ae48e60,0xff67da3020647f9280f7,0x31887248f4a0b8ffb407,0xd4185fdffe621e58e620,0xd3249989a4955f9fd9e3,0x12d284933451dfe7e12],#[0x55e777f94700069bfcfc,0x428878247308353fff7b,0x8fcabc16754220271ffc,0x6af4093cd67fd97ef008,0xafcbf678f5062f566fd9,0x75c7096900493345224a,0xe494eabd090a0000a73c,0x65ffe621e091cc10ca7f,0xd8ecf7d5fa87f9678506,0x661c975fd43fcb3c020,0x10667bebfa87f9678506,0x60409c7b75fd41fe59e0,0x11d560409ebd2eb011d5,0xbfa867f67d417ccd2eb0,0x5fbafea19fd9f505f7ee,0x78850fffe2172c590a18,0xc5835902135fab0fcc9d,0x227c40f122e94188fcb3,0xc2458c10d559f765bb14,0x22f247088035bff36201,0x6de720307129d9febffe,0xeffd975c14d772b98f01,0x8e14529070a8db3bb001,0xcfcba6eb802351fbf014,0x2ff967ad60146a7ec11,0x9fecf128d86c0841add8,0x3fb3c4a2491c0841b9ff,0x7efcdb85b61611938ffe,0x820361fa2123859f6112,0x8006a7ff7ffe22e048d0,0x6894cffcffcf12ac91c0,0x829ac8f8f01651f9018a],#[0xe150b67ec007bff65d5,0x54031a0ffe0291c28a52,0xc923845067600bfe59eb,0x796381101b9ff9fcfe21,0xc40d5344a977e59ff310,0xecbaa513595ef9002ca3,0x2d324998a14f9360afcf,0x116942499a2a6fea51ae,0xde26860c5437fdfd4b3c,0x3f32a9011c6fc7cf7002,0x8100416ccff9f080579f,0x37fff52c3a8228250814,0xa323fe004b9a8a4a3514,0x894f7aef28b9a8bcb0a8,0x575ffeb3124cba6754a2,0xfd471110417029020000,0x950498144808800aebff,0x47e006a9a2541ffe6b1f,0xe7f65d5289a6fc720059,0xc5a40124cd152df9b057,0x2de26860c53a79e3a967,0xfcbc9954808df7fbff00,0xf048e0410deffe7e8057,0x6801838550ff859ff310,0x183855a7f43198e242b,0x385497cd8e198e242b68,0xc2ae3ebde63890ae8018,0x75f173198e20057400c1,0x984d5d0a9c2a50028b11,0xa9c2a500011687fad08,0x28014581feb42261365d,0x581feb91309b2da11e15],#[0xf8984d5b4a0f0a940004,0x97ffe2172c58014349e7,0xff3e2046122c0420eaff,0xd6021f514a41a8a47ef8,0x2bb593f52b84089e35c1,0xe558ad70a9481a88a53f,0xd66249bf41ae800a8c5f,0xf3fe7c40f122c228355f,0xa8ffe021f59520d44d3f,0x68fde7f3f897491a1141,0x1f994002110219001081,0x29b6fd9e3310cc7fff8,0x35b047b6ecfe330019d8,0xdc0285802d97d9f638a0,0xd08406bbe884cd0967,0xbecfb38a0343ff3c4b81,0xa6d27d9e3310d6c016c,0x87ff9887940e5101a120,0x99241539a7d9e3ac1a5f,0xcd14c9208f92fd9e3ac1,0x10035dfd6e2c25a40124,0x86e7fffec11fb77dca3,0xe0c1a81fee98878201ca,0x88839b9387c67d43fcb1,0x306972722e3a750ff2c7,0xc441b9c3e3a750ff2c78,0x641433386e3a7507f963,0x20162841c17ffe217281,0x3c402c250687fe3a201c,0x795f8682901154ff9f10,0xafc3414808aaa3ea4a1a,0x65ecd280cf73f5250d3c],#[0xeecbf2700195f33c5df3,0x7fd8cc3a2c833be67365,0xdff6324d45906673f49f,0x3e5099c59f7009c73f6f,0xaf99e2ef9b2f714a066a,0x89e7edfbfe9cc1a8a60c,0x9334529f3db1c6d32499,0xd0001567cf6f606d284,0x51641aaf1c198a392671,0x54220271fb7ce61d3c13,0xda40124cd14f63317d27,0x66c434000551f3e7b638,0xe20d4124365fb198a392,0xff2ce860c8e7c97cfce9,0x117851c1041542e17d86,0xf0a38441487ff00480b5,0x28e0820a83ff81a96a22,0x88a813c7ff0352d404bc,0xea22a0509ffd5a97327a,0xbea3b209d3ff216a5cc9,0xa97327a8ec827ea4a972,0x72fdff4b950a0861a6a4,0x7df39fa0720840590717,0xc63f493c5835902140f6,0xcfbe73f43c48514c1a2f,0xf9f6becb908804344152,0xcbf7ee81c24200921c6f,0xf6fdfea8cc3a238343dd,0xfdbf7faa3306a0f06b5f,0xff6fdfea3983514c1a57,0x4501f6c78929924cc4fb,0xa83c1b0fd8f125284933],#[0x499a28dffb7cf66a3c41,0x6a0d86cbfc7ec7892942,0x50430d6ff92f9f9a8f10,0x6a0f07166fcbf7fa972b,0x4530695367df39f50390,0x86882addff7ce7d43e0d,0x361bcfe47ef759721100,0x106753ee5fbfd40e41a8,0xd0419c6c8cfe7bfe96f4,0x81c446d1b233f9effa5b,0xb1020af7f7f867942632,0x9b8fff5e850912d0100b,0xa9fcfcb1c1243cd5d6d0,0xffaf4284986100bb6132,0x3f38e09ab86afe120d47,0xff7e7cbbf49a11184835,0xebce7e93008211020a67,0x7e7185356943fa1086c3,0xfcfcb1853d3a5e425a6a,0x411c5fa9abaf4b1f0189,0x804b3187bf5882e1f768,0x7ff913b5904b4018bb00,0xe643f10d5a1f6a4828f2,0xfd620bddbe8411c9ccfc,0x5a232f00804ae7f1870,0x65b64828e67ff913d640,0x180808ad7f399bf10d5a,0x404e17c7f3bd6896c076,0x2299f9b70fd4d5a1da78,0x1145671c4d6822e29588,0x419efc7c7135a65c1ac4,0x4000aa73f581357b6f6e],#[0x36dd49fe3d69308128,0x5689ffff399d49a12b2,0x39f742cd4c2406db8922,0xdb42671c1357a0f6d0d3,0xa11184006c71c1305edb,0x88c200363ffbf3e5ff49,0x90969a1ffdf9fbe7a4d0,0xbb420a97ff38c29ab4cf,0xaff9063b16bd48930e25,0x342564006b7fc709ab86,0x9420005589ffff399e9,0x5e910286ea4ff58f4984,0x3358814e7f5ea614031,0x503082379f75ea612036,0x8bb6cd2320f7e67c436a,0xd25367445a946f5f3e35,0xf167f75cb4024d5f85bc,0x8024e59fb75cb604972b,0x7cb870049aa3f19e5b61,0x82248beeb948c9457617,0x7f7f10d0a5030823795f,0x26affafdcf2d1c012659,0x942905399ebf80db0c01,0x28344a47f1167cbf30da,0xa8d026b3fbfbf5724c96,0x1a046a7ffbe1ab8bfcd7,0x480a37bf7c3564e7cd7b,0x1008d6ff3ff6e983630c,0x2d824a067fefcc1b6062,0xd4a14828dd2ff96eb80c,0x2c50624ebefcffc3d986,0x7cabac6028ef7ffab599],#[0x2aeb1a29bdfd967683da,0xb10804687fd9676839ff,0x86c7624051b5fbd986ac,0x9416c12523fffffa4a9,0x5342018411cec73f6ad7,0x54d0806104717b79c789,0xcca9a1002128e8b7df62,0x644480a36bffe27af39,0x54e1110402363ff6f32b,0x654d080120a3833ff7e6,0xf0d758c06363fffef0f6,0x9c2441008d6ffbf683db,0x3ef2e9ecb2145afdecca,0xf24bde4d201805292bbb,0x10940f110cc1915278f0,0x26422c908124b03fc4a8,0x192190095b7ff1e8b1b7,0x140a8db7ff87a4f79328,0x1922454727fbd8c124c8,0xc62544c0f9b9fef660a2,0xf6ad64a4161c9e7fb262,0x5fcad642619699288fef,0x1143dfef36fcc3d04507,0xd2c70c5af7fbc5ef12dc,0x9c6124c8060146c1ffa4,0xce7308c322240a37a7f3,0xffec98b1895130bffe9f,0xf3d7fc9779382d193aff,0x29411b05dfa4d2c70c5,0x659a22a7fffccd9824e1,0xb2130cb4c945edf68bde,0xf349ca11a08d478ebf1e],#[0x3f4986487250bffa7e19,0xd348380500492bad78f1,0xe930c90e4a33f1c702fb,0x4d088c200371f5af1e27,0x9056f7a6e7ffde1fbe7a,0x82b7fa6b605e71c2487,0x40cb3921954de71c1357,0x96e90c69a0ff2753824b,0x2440a50094ee0ff1e967,0xaebd2d64119cdfd85da5,0x2efd268446120deffea6,0x955ef704e04dae6fcf9f,0x980410881054bdcdb38f,0x357a0dbde998fd6273f4,0x824b52f4114caa6f38e1,0xf49a11184006ebe72753,0x9e75d4e04c8fff2f3e5f,0x4aae1d66e8136379c7ca,0xc2e1c4879114afe6f38f,0x2a1128b9115c63fd0581,0xc8c146abf19a131c489,0x10009299f4c977cffe4d,0x60004a1bfd0bf4f9040a,0x5f9b5a3258ebe7e48028,0xbd7cfc982c889396bc75,0x246b26180482492c0d6,0xe48c9011009497f1c38f,0x243fc13b41151b0f33d9,0xf7fcee84c32439289ef0,0xff2ff5834254210da47a,0xe7fd62284ad0136be7db,0x599d60d095a026d4fbfb],#[0x1bfd2684a8421a9fdffe,0x3cf49a1158008d8faf3e,0x6ff49a1158008d6fffe1,0x97fac1a11508436bfff8,0xff60d0958008d8ffedff,0x3d83425600237a7dfdf3,0xa934254820393faffe73,0x628456002373e0f3e1bf,0x4d08ac0046e79ffc37fa,0x9201929815afffe13c7a,0x216a9046e3943ca2a27e,0xd5208dc9f9fcf6c3ff49,0x211a93f3f9ed87fe9242,0x42323f381cbeb157f6fc,0x3a08d0e1f7d62afedf8,0x52740c2c697e71e254e5,0x882d3010322542fefa89,0xe6549864818c57e33b99,0xd07bfa1275380c687fed,0x14cddf6976f7590a2b7e,0x1a8e0ebeb4830881e920,0x8ccebffa6d330d3b001,0x11b1d7ff4d3cc34ec0,0x60023738ffca54f30d3b,0x1252bff357ff4da661a7,0x92a28fa78c16c2237c,0x8d67d9efe0b611123a,0x18051a5fe19e6131940e,0x1f7d024687f39c6124e8,0x72cdf4091a581ffac06e,0x6e1f4f20c7070ffd603,0x6180028ab7cfec3a7e21],#[0xa78044d87ea37ad36c07,0x81624687f61e7ea6da1d,0xa0740a1634bf33b10db2,0xfcc36a18583352fefe21,0xbc936b3114c607e659f2,0x7ef86ac9efebd3244677,0xbfcffdbcc1b186440c69,0x7fffcb2cc36a50090636,0x707fbd8c124c80102c6c,0x6bfb9fef6608c3244454,0x970458f5bbcdbf307491,0x38400912373dfef17bc4,0xef324d1163fffe66a609,0x9f349ca006246cf6fb45,0xa6927400858d4fcfa7e1,0x930100442254bff25fdf,0xfc930c0206311e1cbb9f,0xf0e7f2694022b1adff4d,0xdea8b7f6fa1406e74fef,0xef545bfb7f50323f381c,0xc3f44aae10142007070b,0x1cdfdfc4bb8407100caf,0xffb0fda0e1fd213d2c11,0xe67be739955e814808de,0x7fefa65de21811199fff,0xed070fe909e818008e0c,0x87fb7c13699a17100a37,0xa0e0fbf04da60c622014,0xe2fcebffa241e7697c51,0xf7e6affe89079da5e028,0x251f6f826d307a90494a,0x6bb3df826d3346a4125],#[0x2806d7f8674c26f40530,0x6bd140ff22c121b909fd,0xbfe88381e3d084e93c8,0xe7d10707f3e848e20dbd,0x45a20dcfb48b10437b1,0xd0d0734ffbe9b9c9e7b8,0x1d5fff9fd238841b4c1f,0x99f9e94db52b70fb6431,0x7099bd609732df818373,0x87edac117bb7e1106e7e,0x7a536c436dbb4f222731,0xed886db769e40137be7e,0xe9ab4c38d6908a17f399,0xc634d5a61c6b484511f5,0xdfb6a445a52d3c2a0e87,0x3d084e93c86bd144fff3,0xf722c2437b1e7e419e1e,0xdfd9ee7be7bc117001b1,0x97f2b29116927efa0da8,0xf402b8cbf8b98c8237bf,0x259f2fc61a7a0085138b,0xc0f0a54257431184a47f,0x818d091205d0c445290c,0x7f3a93249d0904344a9b,0x79b47912feb863408dc6,0xbe7c98738622808dcffe,0xf08f316109904a41ffcd,0x1b456ca010151298ea7c,0x658c34f4010a2371c7e7,0xbf44bbc006140d4ffff9,0xf44ef484d180d7a2995f,0x8df8209b20d7a292fe3c],#[0xf7a98bbc01402470a217,0xc14f82241236bffff9db,0x65de20c088d8f93ffdec,0xe607e0124223331b7efa,0xf662abc0010211c1ef9c,0xecc05f8222211a9ffff0,0x5fbf936f400842353ffd,0xcc69c56a480c2944f3fb,0x9b7f7ddf7a0881234dfa,0x10f9ef9ee011d001c1fd,0x604db90dfe123627ff86,0x8aa043964458bfecd9f0,0xd2dd2139def742638420,0x408af6e67e1b9fd80dc8,0x6f3c71331a4268c30815,0x91b9be72c61378002060,0x593a7e7f8587f37a0082,0xb1e99b95a51a80420890,0x90734da437c3511c4ff9,0xb9b85825fdbf8806a05f,0xf685825fdbed001b1f9c,0x20fdf80977a03a81a9c3,0xadf3ffbe94bbc4302233,0x157fff73bf3d70419001,0xfce79bd0125c3ed908c7,0x537a0245b769e006777c,0x406db769e00538be7e7a,0x61a5d004289c5fce67b8,0x4ae8688c2523f32cf97e,0x4890904344a433133424,0xfdfc1c31a28d87ffc992,0x1cb0c45011b1fbf7d683],#[0x974010a2373ff9bf9f26,0xba1a230948ffff965986,0xaba1888a5283e5610912,0x1212086894e4d42ac213,0xfe0e18d1475bfe393459,0xd88a02373bfce6a1075e,0x14200737ffdee1c930e5,0x5a23a28defca7a256f00,0x8cb4474501df3e209b46,0xf6d180d5e8a5be7c4136,0x26da046af45358f3d13b,0x9b465a23a27c8fcf44ee,0xf8826d19688e8a5bf7e0,0xcf8975c007100d37e27c,0xbfdea62eb8028048defc,0xffffdea603f822412343,0xdfbe73995564029011c1,0xbf302bc888c04687fff,0x2513bfdf4cbae20c088d,0x84723ffae200e0092008,0x8d0ffff87b3155700040,0x2108daf6602fc11110,0x40204aa7d3edfdfc9b5d,0x1406c3e7ccbad5695201,0x523ffcf9f3bf3ab008a,0x81507ea23c136c430232,0x32a8e6c2af826d896384,0x6dfe3899e36d186102e4,0xf8e247a1b681d82a4865,0xe5dfe436e6ae668a6ab9,0xaaf826d89481890ca95b,0x7cf9df9eb008c20035d9],#[0xce984d70014c01c1ffe,0xb1af379f7f04b822e6ff,0x71e1cbe7e25500102412,0xc35f39d2810044004a6a,0xe7fe1afcf5c1042206b3,0xffce1afcf5804180a373,0xf8cdc77e1bc8048d8f3,0xf19b8efc3790208e2f27,0x3371df86f201234bc9c2,0xe3371df86f20411a9c3e,0x97f7f12c98130031a1c3,0xd2fccf895340310811b5,0x5158f7e67c4b3804c888,0x59f911309b6aa1d5ae00,0xce61a1edee3bdf7e0013,0x158386daee3bdf7e044c,0x3fc4c272554a6ad70001,0xa43605adaa8479e80ca3,0xa4be3816b6aa5079e80c,0x28ee3935b40a5079e128,0xc6a3e3816b6aa11e784a,0x8dafcbfbf881c302c80,0x5288a57e67c403d00b14,0x50802a497235173aa522,0x1612233d8f124dbe8a5,0x2ce0160911bdf99f10be,0x6500b1451c9ffe3c87f1,0x1178008256bf2fce7881,0xa0011c2ff9112b5aa857,0x22333987af5771df86f,0x2550f7d7b8efc37d,0x126ebff895ad542b88bc],#[0x3833270dcc86077ba7e0,0x33270f4c86077ba7e041,0xb9c36990e3bdd3f00935,0xe70f990c237ba7e04136,0x26b8102c100210008966,0xc40e181640635dfff881,0xb4c00094100096ee5fdf,0x162811ceff9fe4c46040,0x84104b367df99f1023a0,0x6fffc54988c081640010,0x543efccf885f00b0911a,0x83fc1534f2bc41b52002,0x8ff054d3cafc36a4004a,0xa91c2f597f86f081234d,0x91991c2f597f86f08411,0x10823423d7acbfc37840,0xda9011508f5eb2ff0de,0xda9011507f8290d3ced7,0x9e450d87f8290d3ced70,0x4010a77334f3f5121e76,0x4010a43ed6078261da2b,0x6802148706f7d0130e9f,0x74010a43f0b1d0130e1d,0x22d78664383ef704c3b6,0xcc8b1c86363affe890f3,0xc6051155539abffa243,0x214801559a8adcd1d243,0x801561f8fb5f8d870c02,0xa4bdd677be86c3183214,0x2a51479f104c3b665002,0xa98f67be809870ea500,0x548251bdf404c3a7940],#[0xe0aa9b67bf04c3b454a0,0x154b6b22731d0130e588,0x8a0d9644e63c130ed4bc,0x488d4ff3f8738a136d03,0xa2a5e7bfdf98475223,0xa2aa9c785779f9b0850,0xdd633e869ee3ea614420,0xc9cfce3020d1e57df400,0x9cfce281068f267b6801,0xf2b8273f4e0821b0002b,0xc500980cf7fa1106e17a,0x71c43476ff08420d8f7f,0x95e9ad32f6bb00948e7e,0xd795ceb4cbdaec02515d,0x6733f6a6afedb2444d57,0xdffa980f30d3c208373e,0xc09a3c99eda41adff33,0x5cfd3a04324000ac7bfe,0x29a3b7f270832df520f1,0xcfd3844324000b07bfeb,0x3b7390d02359d2e6e705,0xd1db9c13409b13fc721a,0x7448476b6d02913fd610,0x9ae8908afb681487f3a5,0xfe951e6458f4046e3db9,0xca54799163e026d7f3af,0xe4870c022c1408b075fc,0x1832c16022b8f9eb7331,0xafa619487fd6e66b3243,0x8ed69865393b99ae8908,0x6d00800138d9ccc46890,0x6822b1fefffdec52b],#[0x50221bcf1c757de9364b,0x4124ba7e6fdec509b68,0xff3a9b3723210128b40a,0x3ec4cf36c02400422b8f,0x24753812010422c4f8ed,0x1d961004162627f34e26,0x26002571d687a609cef2,0x20a9a7ea2ce6e7e43a04,0x52de33bd6900c761841,0x88298f6e66ba61ca3d51,0x244663f0ba574c39656a,0x639226675ffd34f322c7,0x110885154e3ff29a7991,0xa0515078fee663e1c210,0x514e7ff73359c3108642,0x514f673311a61cb2a60,0xa4619853b99ae98728e6,0xd028264aa6fdec6136d0,0x122a8ffffe6f721010a,0x424561d3ed899e6d8048,0x5e627f2789891d4e0480,0x957d6223d3a043008001,0xe7fca11d3206a58a6fbe,0xef38c7a7a18a1001cd7c,0xcadb4020004d8ff3fbf7,0x64b0006822a9fffffbd4,0xdb40e020de78e3aeb593,0x17ae4b70458ffc38d184,0xd63cd842800022bb5eef,0x530a2100022c29c7864e,0xda8004368287d0db3d73,0x110012583e7fe1a31e9e],#[0x68a53f89fc44a0f4e082,0x68a53f9d99b8f48069e5,0x409294eccdc7908069e5,0xf49466bf40b5b50056bf,0xfd78a1a525f5fb03b667,0xad430523e1daff7ea0e9,0xfe3c226a3f2035e941c3,0x86028a27c3b5f77c2274,0x7c54a03fc7aefd24070e,0x1cf8208a424520ed488e,0x88e7c104529120c1da91,0x9804f98b29c89060ed4,0x4c027cc595167664c64,0x877f8824f9ff9d90a632,0x550e98fa209474180baa,0x617550eff200450d1617,0x93c2ef611bfffc0132d1,0x34bb0babe33bcf5cd0ca,0x5330eec2eaf8cef3d734,0xc29907672eaf8cef3d78,0x1c80a71672eafa2779eb,0x82128d87732c99f327b5,0xbf8908a3a29009d523bf,0x91dfc484529d0629d523,0x6dbabfe48942741804ea,0x60edd5ff1019427c2a90,0x8c1b6eadfe203296f214,0x58d0e4716a34874dde42,0x64278d0e2a075006874d,0x54343a6491a1c8e2d478,0x9f638f24074a91a1e607,0xa497bdc5ce3c801349bb],#[0xbe740b2a496bafe740b2,0x499bdcd8e3a0045c9abe,0x3c201b4cdce3f1e0100b,0xacdad2fa580e99bdc5ce,0x9a4d55dcdbbea0126272,0xf2c009a51dcfa87c2c90,0x37fab00be3218c29c74e,0x1d3bac009a503cf2be7c,0x3cc45ea401b4f1e3037,0x3577e09fd88126260f18,0x77b02c5df802dfc40931,0xfddf78cb6c0baee7f965,0x1306755ea11b2809a63,0xad41b2809a33a81ad6d5,0x82a91cdf0a4321406755,0x6427295dcf4a50c84c9e,0x3d0d0ea54de2a91cdc78,0xd9203a50ed7408db8d77,0xa96cef11d9043a54ef11,0xc568172c9977fbe3525d,0x499a6f11d0028b9352eb,0x11e020da54ef11e0100b,0x4941d2c7fd2587a244ef,0x4fe57fd90f44918ceafe,0xa4d262fa6ed6a9052627,0x63a775829a4e19ddcc2c,0x27961a6c6540516a5f28,0x516b5fa1431d3bac14d,0xd2f11ecba4972ca6c654,0x44bcf02c74a02445b581,0xd41c030e9ea07e314b63,0x66f507001e9a33ff349b],#[0x42e887f2290ea64cfff2,0x621ea505d10fe7048753,0x48a8af5aca7a25c1bf86,0xf5aa008e9eba5baf67a2,0x91b2ea002db477fd0926,0x60ad16fd450ea5e77c82,0xf608a8d42b45bf5510ea,0x3d08bb921151af30f48d,0x162d9a0dfdaa27a921f,0x380243a86dc4797a3567,0x2380243a70affc4937a8,0x693f91c3a932bffc2cde,0x39887a92b49fce0a7529,0x6d2c8ce3cf5d3a23c1be,0x323328fd7db1a2417fd8,0xffa4dda5888874eac3e8,0x4617f89cd6c02145b057,0x1d93ba6399b45eb8d0ea,0x4e9bf6343a91a6feb275,0x462a12ac6983cf5802ca,0x1613cd481dd613cce5fa,0xc633457a18cb1fca81db,0xede7dc51952874b6c836,0x652720bec89d5c991516,0x2e6d7ed80f24c5f62069,0xf405d281362f7ed00959,0x5deab9002e9409ab07aa,0xb4a04d5dea06b5b4a04c,0x2c6250a50272ef503185,0x13521f6bc8d0da9690fe,0x343484c5d4fe2d728528,0x729ea50a50272ea7daf2],#[0x1e489f7e306800f25a9f,0x5eb9c7688792978fc761,0x83452b254e3f23b49e49,0xda4af5ef830cac94bd7f,0x6fad54e1c1252fe92510,0x1b07c0e2ea3b12082d28,0x4436a158651913746e05,0x286e499c678facabf260,0xbde44dea18146b9e0fe6,0xb49b3fcd55985886d319,0x3101d1267fe6ac70a820,0x8498bf8e3884118d3be7,0x417dabaa580806b697cc,0xa43999d2bf2fb80a6b46,0x80ca44f37f593724653b,0x442fcbc024118d13f858,0x99844c81fac43726ec66,0x47693725cfef18340b6c,0x4321383efbf2c142c71e,0x8b9728642721c748b1aa,0x379e1c4378e1d2f79d1c,0xed740933414fd8942253,0x2c697578ad2e81337578,0x60020b4a0b7fd0230e09,0xe4780082d284fe86ec74,0x5ed7f811a0524cffa1b2,0x404aca039fee0158422,0xf06094ac9fbff4356f83,0x80d7901224cdc3fe86cb,0xa24aff023805927b5f22,0x9ff90cc9cc8d2388ec2b,0x60895587c4f2191ac8d7],#[0x4b7578ee60893b3e456a,0x4067cfe886af0741001d,0x354cfe7e50d878e8221d,0xfe8844a61479017e1406,0xfa187c668792879fd0cb,0xd5ffe82d623a8003c9c3,0x20b350fe865e456001e4,0xd19b51218d65f90078e4,0x17a433f41989793d3dc6,0x902bd219fa0ccf9307ff,0x6eafd64cc8fb9ebe90cc,0x285336ffd0d5be6812b2,0x20b49e80fef52ca456da,0xdea8b04cd3fa1a323aa0,0x40cfffa21a239b500e9e,0xd19c148b8d284ff692ca,0x3a945254f3b54965223e,0x52966777c24b294b32be,0xe2fc18965220ebdc5496,0x788ba91075cd888a252,0x3d18b68b8cf12c363dd7,0xdd707c43a3cc3d8c4b29,0x1a888a252e57e6928548,0xacd8f758d472ea40feeb,0xe612594b8f4eaa2319d3,0x7a20233cf9c43a28f328,0x45c96beabe790448af6,0xee6f1f022e4adee2d63e,0xfae811fac9b34465169d,0xa693469767fae8127767,0x394b659b0718e48e3a80,0x447dd5ff04464f5bf49a],#[0x1d26acce58a2daab75f0,0xf248fcc5af887924bf7,0x859652d9cb35af9337f1,0x1b3c164514b672cd7c1e,0xb3448d9fac44555bce71,0x92e7f3819904495ff810,0xfc2ba23cffeb9f182007,0xe90448d9e97f48224ecf,0x8b9256b5f008b927767f,0xed8be4772e812e6f5f00,0x832d27ced17c8ea4ba04,0xe715b7c98bf8e8695d46,0xcbb505ce2b6de4d5da82,0xade543a5b32c780a2329,0xe4bdfc25025d22e7f844,0x4f012af24affd8b80a45,0xaf972e4a437fcb97244e,0x2e5c8d35fcb9723efc99,0xb25affd9b8149ab260ff,0xffec8cabe2a9c1e001ba,0x298973f02e31c934c4cb,0xa4f0beba0489fae31c91,0x6240ba4e9e93c2fae812,0x7426398d06e9623c9da3,0xf92d44793a56c493593c,0x4278dedf240e82c29e26,0xbdbe49df9a4c0de55e4c,0x83d3669b1bdbe4941631,0x610f427d2944793a52e4,0xe2745e5fd4396f8b4741,0x7208e264115f34e30e45,0x2467e12812e922be69c4],#[0x99afe5cb91d05afe5cb9,0x1da9a999f3680f6a6a66,0x4c4a9fdbc2f9269897de,0xda08380b36d3bf13e489,0x722f13336ca4c059b69c,0xe91e2b9178942bf48f85,0x156b248fb9ac0d56b250,0xdcfe52e0350879367303,0x964715ffca98f20a564d,0x21e489f2f443c9135efa,0x20b34adeb443c9035f4a,0x11d31a6a659a3bcb3564,0x3f26df24278fdd3532cd,0xe5e66f33878edd6651f7,0x9acccf98b63b3599a32d,0xb804792abf66f3245b1d,0x1c0be92d02acd3bfe3cb,0xc8e416671fa91fb43c91,0xca399f2df4c194734072,0xcca3f53abe21d490e591,0x99b21eb2b29e682fc651,0x3c0d7d288792992dfca7,0x21e491e3c4adeb443c98,0xd10f246af84791a7cbc8,0x6bbc945fcd5912cceb57,0xc8d30b58bbc903ee6060,0x49ff297f443c9235fc23,0x3c9116b63eb334389a68,0xec57e5ca744b1fa95fc4,0x3211581ec6679729c4c5,0x2f8b4a62b087930f96b7,0x1020b354cb9811852b26],#[0x226712c21a49a5fa5534,0xc7f8a13389610d24e1ff,0x2230faaf226616c29593,0xd1404689e08f0447d878,0x3d7c785c45011a6be32e,0x2b8e1a333171af8a023,0x5eec319242f7b1f87992,0x7ddfb2ac54792e4dbe45,0x879232b88c34eec659ac,0x4b28e2b78d0f23895d46,0x90fec209b0956350ade3,0xd8fa08cf9e31f28b0dc6,0x1479357b9af76e22495a,0xf3b820b33cf1f77db2ae,0x447dac7cee5a84b8985f,0x499b1d77378913c3fb8f,0x40323945a173a06bf11c,0x20b8d592e6b2b3d4692e,0x712e4ef27651c39f4675,0x271bad389a3d64138ed6,0xb65704d7f98e254c7ac8,0xcaca6d1d2e403239151a,0x64b9a]]
def g63H8 := limbs80 #[#[0x10600e420501c4a00,0xc0300008090a0240c,0x70121001000060902038,0x10040409120140a650e0,0x6080080c330a80000030,0x784c080202854020,0x42a140681c00040387c0,0x4c190080828020602,0x9681a00078040e0400,0x10e88c0007048042404,0x420d0380c22170300010,0x5c060c03804261b038f8,0x90141a1a000081e01000,0x41a0583c050084c12020,0x400020080600070083a0,0x820010080416020000c0,0x804165d00000200a0c03,0x1800000803854020226,0x2110801606110140802,0x1a0504085500a070000c,0xc040206800000400098,0x40a11098541e03028,0x1480002040000012030,0x25e0000c140000804061,0xc0a070b8349e23000b48,0x80c220203818000b0007,0x2814240a1c87810180c,0x6030d0164b0581c0452,0x3a010001c3415180043a,0x18e2060607c42070e010,0x3028142301834140f048,0x5058040a020002558040],#[0xa492802c0803128b8161,0xce2012503c0e020c0000,0xb402760502408000383,0x181434701f00404a000,0x21e800020d010044e0d,0x1007298c000040701800,0x40001020ac1a020094c,0x281886260a8440a18078,0x5059b41e07e4814382f0,0x813038000c4a01838480,0x1c26058200c1b020140,0x828001106818502c1031,0x81806033a004082203,0x22028142e0b1403c1434,0x60111a6400010095c16,0x940c1d068b5001145078,0x3c0c272d8280a08128,0x10800400360a87c16050,0xe0d038505c000f00c0a0,0x434760e800043c940004,0x82c08351d0dc1e081900,0x82a22180080e0102,0x1038293001108140e35,0x1411038001c060083816,0x9c040203810660b0482c,0x9104e36b69a3e0b82761,0x248cf77ba91c036d7e76,0x28ae614b086460002dc8,0x718a2fc765bfe115bc3d,0x935400000000000c,0xc296a1e2482e60000000,0xdd6e1cbb710000587eac],#[0xabd0000b1eeab58000a,0x5a3d16bc0000f7dcb09,0x4c900000000b7be42,0xfdf3e2f32a499050be40,0x6942cdc4338ed5789fc6,0xc07adb800072391f33d5,0x54de4344217d29b800c4,0x600675fdc515fe8fbc4f,0xc965c46c6c88b7de1,0x992772d88c1c47405a20,0xf0fdd38cf56d1e8ab0a4,0x73799b50859f6dda1985,0x96b78d9fe851a306789d,0x2400045db7f4dbf89021,0xa58037800076a395869a,0x9c96dbf5c77f6b3a223d,0x715f7e5234fae53263e1,0xdec8bb44959ac5000025,0xbecc0000da596b300007,0x32f6c243e26b3bfa65b,0x10b200005de96eba00,0xbc0065124f45d460b350,0x8800000000000399cc94,0xc4ab9dcd38754d9d51f9,0x15ac6165aff04e9109c2,0xc2e63b8159afc000245a,0xe8da32aaaec2eba20a70,0xec0b144e9eae5365cc23,0x28a0858c2825bb5cb8d4,0x8900000000253d6b4c07,0x8000624a6d653e44a345,0x740001bd0d4ce0001e24],#[0x115fc0002955000047,0x929ade2800008fe0,0x842afe3cbb52bb880000,0xd9a00000007894ebff48,0x83291280729400000008,0x2a5678000000000029dd,0x76fd0e73a17582534391,0x1c151e693,0x15d6e70460d40000000,0x99a3e400006759f39a00,0x688caa80000342080009,0x1791b00000e9d540f817,0x67e070030190001f2,0x7a03a97b364fd5f8fb70,0x700003cdb3944f6a0000,0x5ce000000000000000a7,0x764100018f8471500007,0x1112e6be00000000000,0x1ee9e39000000,0xf3097a8589db29a81be0,0x323ab000000018420863,0xa12000320ed4a3b1c00b,0x11b73ed73cac88e024ab,0x1535200000001c46887a,0x1878f2a30c16a0000168,0x90e7749a61a537900006,0x540007ba55126f4448b3,0xb0b9197c3fe68da34bfe,0x7bc00001f88c2cb68dfd,0x8c71e67c11748be63f08,0x2a800000002ba3bb62ca,0xefa8ed5cff3f09e31aea],#[0x30106b0ace4d13305c71,0xef00000593a9c8000127,0xa6ece4926b08cc600005,0xa91070000501400026ce,0xdc1800042ffee25d4,0x98b5dc9c00037c600000,0x92d800000797284cc91a,0xad9ac7bf3b5aec3a66f2,0xfd1ad5322a1310c27c6,0x4a7f42dca13f8c94568,0x1dd70f5c80a9a4c48f,0x15dcfa980001e8580000,0xec00013a9896950f9424,0x2b4b6100000ef0000115,0x4ca8d10ace800005796d,0xb2c496157900aa128000,0xfb4826800040d940065e,0xa241dac7c2ec3d880004,0x73855000029084c6c995,0xa00c03c0000000320681,0xdb0ed2425ecd7158226a,0xef2dc3a00017015a04,0xbea0002cbae31f000000,0x6f67ec7d8dac0000000d,0xe7844ed62a2ffd8ed7c1,0x1c2b8c6aba8000535f43,0x3ae50001cbf8f8f544cb,0xfc7f31471bebd367a7b5,0x9a095e01a8fca9ab5fdc,0xe42a0002c695e7ef,0xb6a0e60a3edeb74128cc,0xae8c6d3ae9123b6f3e9c],#[0x8000ef3dfec8b86a48b3,0x1b939a4a0002aa7,0x56437e1d5662be735000,0x31e19d8b3c3fc3e1b9ad,0x34000633be12a0002b97,0x638aeac508a8835f232a,0x80008cf000026079688e,0xa000000000000596809b,0xb05cdb000002d4568,0x1ec400000,0x8e57dc33a4a720000000,0xebc36d68000e5be19,0x6812000000015a40b3c0,0x2c319c52920f58b85bf,0x57546fc000559b6df800,0x70b107ea000129a4695f,0x2e9f1ccaf662706b831,0x1bcec0000000c8a800,0x34c0902620d000045170,0x1ddce3ac00008639197,0x170d484cbf0000000000,0xe38e47b343534a7d1699,0xd000076ac43299e5280e,0x86e0001bbff9d900000c,0x37a9049c0002eeee783d,0xbde8a0f0d3b4ba0000,0x7e24d7c000749c000000,0xc35aec5bf80800000009,0x19dbce10a9618daef5cf,0x11e000206b3f444b8459,0x557051e00009,0xb1c826aef5ec08000bac],#[0x2dcb81549180000001bc,0x4e8000158c25f980001,0xea5158bd268e1f60316b,0x2f06a85a974f18,0x5773ced97cfa37a3f850,0xe67648c648e8f93bc000,0x88c0003c2b80000000d9,0xa49948bcfabc0004e4a9,0x8a919975089cd49f466b,0x27ff280000635c6e906e,0x119bd2402bf5f9bef5f9,0xdb4c9c5980001b71bde4,0x785aec5ef01601fb485e,0x80008cc800038cf20fbf,0x40fd39e4de8cc29,0x1d268000000082a600,0x8000000112fece0fa130,0xa78ca9fe02e,0xd7e00016be8000aa3e00,0xb5d43dbaa12631a70f38,0x780007b8b6809e5bfc0f,0x335986a7888483d6a7bb,0x26b10000f52c81952371,0xd400041166c280000000,0x7e043daf67a00016a,0x1ad19b460,0xdc000005479540024000,0xa2df934e1700003a5791,0x18759396c8ea06280008,0xbbc8c318500014452eb7,0x154a7987923df3cf0f,0xbb668499ededeeb965b0],#[0x2d41800000000001e73,0x921abc40ca8000000000,0xff8f3f7da75ab2baed05,0x2aef0d68c9a2b96e3559,0xe5347267e80000853b7b,0xb97baa39b142939170a7,0x1460800090eea19646b,0xe15960daf47df200,0x95bcae9fea9800000000,0x2f93700000dbe00010e7,0xab7474b872f00013d,0xaf39f0d862c27b1be090,0xcc90200008e93d704256,0x828a23ac51745f0001b8,0x466b00008466e1c05fe4,0xce48f0e29f1aaa672b0f,0x4ba800035890000e6,0x9a280000d97a1a40,0x7800057e3ac38b73cde6,0x3abd353b377ee5,0x31a300000000000302c0,0x81f7480ddc8800000000,0xdde000076ad9f1b5eb0c,0xc5499b90ee1bf027ac66,0x200006fde00018fc8c26,0x1682041b702bdbecca,0xccef4b79759c1bb2910,0x715ab3f17e8d0949a9ea,0x1955400008d3879a76,0x550a8480920bb7089ce0,0xf2e060ae20f243e18000,0x5e4f0efa0149c77bdcd9],#[0x8b451f7e3dbc2339c5bc,0x3429d4151b3f2c64b18e,0xc8b2b4c0001963b45bc4,0x56dada63fb200005,0xc6497ca9bd6ed50000,0x9d800002943e43000000,0xa2c88b99df363ede,0xf000033aa00003ca2c9f,0x157b6c8fa07827e89fae,0x5017db92f99a745acf69,0x9fb92641655dc9dd0a7e,0x1bb45b6b6af85e0fef,0x76726f8400027be8e520,0x1f3d2c011454ecbd83e3,0x217ce8000a2b3d5,0xdec4bbe00002afca7840,0x307b920bd9ccad7165e9,0xf44000000000003cd5bd,0x61838b68e24a639fa8,0x237ea3b68ac2acf4d3a,0x6f8812c0af9f03fc9e00,0x9577cbf954db82b45ec6,0x1233ae18ca60808f1e,0x16adc0001ad8a52800,0xca868f164f7a305eb7d0,0xbee86a1bc1b18000338e,0x592d4bd27080000ab6b0,0xd20028f2b6eaabcf3498,0x19343d109fe16ca4d14b,0xe016c506c1c7a10fc040,0x3d7153e657d0801626df,0x39eac87ccad7a4bc9a],#[0xc6c7fa25427a06b86800,0x57523b2aec1a8dc0000e,0x1d0f2cc334a8e2dc000,0x8ae3da400059b0192efe,0xa287ab8067d406da21bf,0x2c97b36321c80001ee9,0x9f400000002556c62c00,0x9e90692a00000000000b,0x8c0001d27f4afe13ec2a,0x548b2e224743b44bcf93,0x462cadc6731156227256,0xda8306aafe924c149dfa,0x57351704532c7f6b0e02,0x78ff94f1a7780002944f,0x88f60c1e4fcde0001cb4,0xd0584772a262694b7ed8,0x544400000000c64642b5,0xf49f90edea683e366e,0x1b1625b98000d1a000,0x64082100e32c000179c0,0xbb58870075cc367f590b,0x40e2a727ba8000bc7ff4,0xbdf5ee752f47d480,0x400000000c9b40000000,0x620003a30b83b048406,0x467fbc329c7c0007e5cc,0x1c023bee42fa8c2f0000,0xbed2528939c0001eb,0x2a9b838d374143f78ed0,0x6d56bfe8a00019a47471,0x3d20ce603416518052d0,0x80002a2054fc0006f33d],#[0x56c4c800076efa1d0c59,0x93a8086887e3a8000018,0xf94b0001943ff8d00007,0xaf99f0000c0507007213,0x2c1564b2126ad10d060f,0x6b72cfa5244f833d,0x2b738000000108bfac7,0xdb1c0131635813a00,0x3e55bf880001b5b00000,0xa070980000001eb826b5,0x696966b6af1f35cd87f8,0xa52452873943f56cbf0f,0x1f8459b7f68de7da0782,0xde652442835f6289e999,0x696d1e8630c8d1f8c6eb,0x63af535caa0b79b81c62,0x91a00010d8b26fdaa7f2,0x59e2a84772000003442c,0x61c7377a7c9b049dd6b2,0x855761b625a8ebaf8bb4,0x20f3239400072200,0x18f90b38ed84f07ec11,0x87b6dabe1e3472743a00,0x6757c2190623f528c155,0xd05e669f1b1,0x958708000049c2bd6800,0x4ea7000000020f317a40,0x1aeb00000793f932d95e,0xe04d9000000400001e6,0x51a69732d5a12129a7e6,0x81aef5d45e68ff489a75,0x9e6000000048c08edc1e],#[0xe4bba1146c638ccee865,0xc966a7a10942e0000ded,0xc8190b641055cb703d6c,0x518bffb0d606037cc75c,0x6e32eff6133fd48920c1,0x72e28728f1869a60749e,0x4ebaa3e0e9708dee6b20,0x4300b2d4a06dfcec822b,0x706cd79258f13889e002,0x9a32c62f8d9d3d5595b2,0x7fc1c62584659c3c13dd,0x75fcd340002426000116,0x26e55072834555138252,0xa82d73f7c0b4b2d43799,0xcd87c61393f910235885,0xeb57b7f5463e47577adf,0x3c588eb2ab4c81c3a7d7,0x1b06c87689d82da86692,0x3cae0f920001628f8f54,0xb1b8dbb0a1f713926466,0x4f78f0ced00d1d853f51,0x80006cb00ba4d71d1f4a,0x649b4bd528db000024f2,0x7020001faad8c6f86dd3,0x167420f6c334da1f6ee9,0x59dcf09a04db7874c000,0xce3fc700000f54cfba0f,0xaaadd609b818e7c569f5,0x14ae22218f4b400021c7,0x7f72603203000000013d,0x800056457a10000207af,0x66158831a133baa96ad4],#[0x3df8c049adb45d6e621f,0x40ee1684000141af846a,0xada536119cbfc7d9d6d,0xb16dd3468d18644a5bae,0x4f8ee1c40006554b,0xf0426a633b1e96ada3f,0xcfbbae252b666e9dd115,0x4900772adc43522c3be4,0xe00002f77012d8a879f5,0xfa430a50ede8dc0000bc,0xd4ee949665c1900c375c,0x7f23186aa39db7c20253,0xd026f1da994edad49158,0x5336501db62a03b487da,0x51a311d02b52dd483dff,0x89a609296ce4fd7291fc,0x830d19e3335542121774,0xe0083301ae3868d056b9,0x203b2e8f674637653caa,0x5939e729e5e85c90b747,0xd8ee72e80e3dd9dc3f26,0xd2873afb9e635d369c32,0x451933fff5bf2c881ba4,0x692f97130e8f15088373,0x70e78c90b9712e6149a8,0x140d99028f24afebf792,0x4544c3c41aa6391f5d5a,0x4c02c23a35f6dca2b075,0x3cffcbbf89426d0be0a2,0x2ced9de1b9534c26d793,0x74372f89fbd2cbd251e0,0xc3baf5411323e8399328],#[0x14adac045feec03a50eb,0xa3c628503779117fa631,0x9de4a0e791a8ccbace44,0x30bada20b5699aa3db42,0xe2cf8985328b7055779f,0x3f7bab6d425e7de6b3fb,0xe306d136cdbe27950216,0x55578e33584088296605,0xe92a50f0000095873780,0xff67bb7aeb9cae55896a,0xacb87600000018e8e60f,0x2be50e444bf0713eb4f8,0x2b8815142f5b613ec8a9,0x8da8294cb2a1d1f244ca,0x2caf0000c14364deb057,0x9e077baabe28b1cd95bd,0x27c70000ab6176,0x3fdb00000002dc4c7d60,0x3a9ee00000000946c000,0xdee0003dfc8000166e4b,0x255809f32a0895700002,0x778762db4f141cd01e27,0x6ca85ada1a8000851773,0x313190cc000367afec63,0x32b4e0000566600118f0,0xf39a230a2e318,0x528db756dc256ed0,0x826000027007c4c000,0x115b7b6a0000502800,0x212ccc1c00011e2c58d0,0x1962d6a2200011d94000,0x98bc6d40000000655062],#[0xa983e929c63400000006,0x9a6ec800000000000fc9,0x3f811d2114a1eceb32a4,0x1576445c0000df64d7c0,0x5000076fb0000e6ca965,0xdfe0f1207e404ecd37a7,0xabe80000165000000000,0xc40000000217369d4610,0xc100001350cc0affbf3b,0xaea06023c967123b33,0x21acba720ef0e1518000,0x8325dfa72f7b88000194,0x3e9c00003,0xc0000601c000000005a9,0xe040003435800014621e,0xd6709c3b22e93b378f15,0x3e0f00009cd00b00443,0x3a1c4937478000e43200,0x9715528e00000006ea62,0x353580002a1de29ee74,0x65000005eab371a29400,0xd3b526c3cb92e2aa3fd2,0x858e0614e0d57cb49623,0x5dc23a6e41885,0xd9b60000000000053580,0xaaa69927ac2edac0a3e5,0x2740001b0380003ba2dc,0x518a00010bce23345aaf,0xec6e699d500008a425fc,0xe32f7befe04db7000036,0x331934be92f0386111fc,0x8dd39942883f786122ed],#[0x871000002a9eea3af,0xea82b78e15b1e480,0x677a0000276a522,0xc5e0002e592396173000,0xccdf59c17543791c315b,0x4b0f58000000126ad7ea,0xf2e644c0000000a6e470,0x3cd68da5356749b39b9e,0xda3c438236f358624000,0xf9b4e29707f051d50143,0xd48638b200fc380d3cf9,0xc1529c505007aa93ed40,0x15a6fdb250c2f74089d5,0x2610001e5f7d7d493d9,0x535563020000000,0x1985c00028012ad200,0x4e44608c4d20,0x10e29d1ed0d6a0002929,0x15cd393312710000cd,0xa9a29a3800052090,0x67a5a8000e42507a8000,0xd32f0605e77f3a00019b,0x6c0300004a640002e7b0,0x3e759eb5b01c000,0xdf02c4b74f0000000000,0x401b07b400039ec79123,0x7f4fbbd57f926446ef22,0x2e980f12e3bb03af9da8,0x44a6732249740000f21d,0x382deb3b000001858000,0x2a396664741a33f50,0x2431d8f943dc00079660],#[0x3e88a9d01165b7798d2f,0x17d220a93cd53cfbb1d3,0xb93b7c8592ad9bb52855,0xc28ae86600000e035166,0xdd42c2c000000024585c,0xd30e26b7dd779966,0x93bb8beb3707c2f88663,0x64c970ff84a91757af3f,0xe54e3daff22835ed530c,0xef8a0d7b9b0bc458a52a,0x1f52c4e72599e824d4c6,0xa512000137ef00800000,0x6000012f9ffcad642e34,0x12200008a876c07cb3ca,0x7c9e2]]
def g63D9 := limbs80 #[#[0x104400c8310c02108010,0x4811014c521445010c42,0x50d42505404c9314c121,0x886208415454d5254550,0x9424390a41902328c630,0xcc321c83109525394a51,0xd4750d0f42d0740ccb31,0xf7efefadebe7f54d4f52,0x650016503fffbf7efdfb,0x64b0564b036538065382,0x65b4165b47643c4643c6,0x65440654476444464442,0x6008d600826518165183,0x640856408a630896308e,0x64105641026508165086,0x65cc165cc26584165846,0x654c0654c26514165142,0x65d4165d426520165203,0x63011630116201260002,0x6339063393623aa20392,0x627516276a2076920753,0x63752637516375063753,0x6005263b1163b1162b13,0x613d2630516305161052,0x6379161793633d0633d3,0x61b53637926379163790,0x300e9300d263b5163b51,0x61451620d1610d2600ea,0x618126082b3081362453,0x4119162bd161bd162811,0x431916219a4219161199,0x6251361512631916319a],#[0x618db418d36351063513,0x638d8438d1628d8428d1,0x63c9162c9161c92638d1,0x53291622955229263c91,0x62613616126329163296,0x63d9162d936361063613,0x630926009554d9263d91,0x63410634106041263091,0x627d2607d36341263411,0x63b9260b92637d1637d1,0x62125311126011263b91,0x324a7314906049263111,0x31852608536249f3249d,0x32c1260c116385162867,0x621d2601d162c1f32c1d,0x4255060552631d1631d1,0x635506355b435536255b,0x63911639116291260913,0x43cd162cd942cd260cd2,0x632d1622d263cd163cd9,0x62a1260a15542d2632d1,0x62dd552dd263a1163a11,0x6015263dd163dd653dd1,0x604d2631613215161152,0x654d4654e3324d3614d0,0x638a3328916189260897,0x612126021161c5260c51,0x61590605926321163211,0x61952609536359063593,0x61d1260d126395163951,0x633165331263d1163d11,0x53693616906069263311],#[0x61a5260a536369063697,0x53e1263a5163a5453a51,0x6025554e1263e1163e15,0x605d9432516225161252,0x6199260993625d3615d0,0x61d5260d5b4399162991,0x54355533516235162d51,0x60a93626d3616d0606d5,0x62e5753a9162a9161a92,0x63713627136171060711,0x62ad161ad260ad363710,0x63e9162e9263ad163ad1,0x3002e2002c2001263e91,0x3202e4002c4002e3002c,0x4202f3202e3202d3202c,0x4302f4202e4202d4202c,0x213af4302e4302d4302c,0x413af313ad313af213ad,0x323ad323ac323af413ad,0x423ad423ac423af323ae,0x433ad433ac433af423ae,0x3076e2076c2076f433ae,0x2176e4076c4076e3076c,0x4176f3176d3176f2176d,0x3276d3276c3276f4176d,0x4276d4276c4276f3276e,0x6276e5276d5276f4276e,0x4376f6276e6276d6276c,0x5376f4376e4376d4376c,0x6376d6376c6376e5376d,0x6476e5476d5476f6376e,0x6576f6476e6476d6476c],#[0x32b2d32b2c32b2f6576d,0x42b2d42b2c42b2f32b2e,0x43b2d43b2c43b2f42b2e,0x4006e3006c3006f43b2e,0x3106d3106c3106e4006c,0x4106d4106c4106f3106e,0x4306e5106d5106f4106e,0x5306f4306e4306d4306c,0x213ee5406d5406e5306d,0x313ed313ec313ee213ed,0x413ed413ec413ef313ee,0x423ef323ed323ef413ee,0x433ed433ec433ef423ed,0x407ae307ac307af433ee,0x317ae217ad217ae407ac,0x417af317ae317ad317ac,0x517af417ae417ad417ac,0x617ad617ac617ae517ad,0x427af327ad327af617ae,0x437ac437ad527af427ad,0x537ad537af437ae437ad,0x637ae637ad637ac637ae,0x647ac647ae547ad547af,0x657ad657af647ae647ad,0x31b6e31b6d31b6c31b6f,0x41b6e41b6d41b6c41b6f,0x43b6e43b6d43b6c43b6f,0x210ee400ec400ee300ef,0x310ef210ee210ed210ec,0x410ed410ec410ee310ed,0x610ee510ed510ef410ee,0x420ee320ed320ee610ed],#[0x520ef420ee420ed420ec,0x430ee620ed620ee520ed,0x540ed540ed530ef430ed,0x2146d650ee640ed640ee,0x3146f2146e2146d2146c,0x4146d4146c4146f3146c,0x4246f3246c3246f4146e,0x4346f4246e4246d4246c,0x2182e4082c4082e4346c,0x3182f2182e2182d2182c,0x4182d4182c4182f3182c,0x6182e5182d5182f4182e,0x4282f3282c3282e6182d,0x5282f4282e4282d4282c,0x4382e6282d6282e5282d,0x5482d5482e5382e4382c,0x21bed6582e6482d6482e,0x31bef21bee21bed21bec,0x41bed41bec41bee31bed,0x42bee32bed32bef41bee,0x43bef42bee42bed42bec,0x211ad211ac211af43bed,0x311ad311ac311af211ae,0x321ad321ac321af311ae,0x2152d2152c2152f321ae,0x3152d3152c3152f2152e,0x3252d3252c3252f3152e,0x218ed218ec218ef3252e,0x318ed318ec318ef218ee,0x328ed328ec328ef318ee,0x21cad21cac21caf328ee,0x31cad31cac31caf21cae],#[0x32cad32cac32caf31cae,0x322ad322ac322af32cae,0x432af422ac422af322ae,0x3162f2162d2162f432ac,0x3262d3262c3262f3162d,0x319ef219ed219ef3262e,0x329ed329ec329ef319ed,0x32dad32dac32daf329ee,0x43daf42dac42daf32dae,0x430ad430ac430af43dac,0x6042d6042c6042f430ae,0x4142f3142d3142f6042e,0x4242f3242d3242f4142d,0x4342c4342d5242f4242d,0x5342d5342f4342e4342d,0x6342e6342d6342c6342e,0x6442c6442e5442d5442f,0x6542d6542f6442e6442d,0x427ed427ef327ed327ef,0x437ee437ed437ec437ef,0x41bad41baf31bad31baf,0x43bae43bad43bac43baf,0x54bad54bae53bad53baf,0x4212c4212e3212d3212e,0x4312d4312f4212e4212d,0x414af314af604ac604af,0x424af324ac324af414ad,0x524af424ae424ad424ac,0x434af624ac624ae524ad,0x544ad544ae534ae434ac,0x3286f654af644ac644ae,0x4286d4286c4286f3286c],#[0x60c2e4386c4386f4286e,0x32c2f41c2d41c2e60c2d,0x42c2d42c2c42c2e32c2d,0x62c2e52c2d52c2f42c2e,0x53c2f43c2d43c2e62c2d,0x64c2d64c2e54c2d54c2d,0x321ed321ec321ed65c2e,0x3256d3256c3256f321ee,0x3292d3292c3292f3256e,0x32ced32cec32cef3292e,0x322ed322ec322ef32cee,0x432ef422ec422ef322ee,0x3266d3266c3266f432ec,0x32a2d32a2c32a2f3266e,0x32ded32dec32def32a2e,0x43def42dec42def32dee,0x5316f4316d4316f43dec,0x5416d5416c5416f5316d,0x614ef604ec604ef5416e,0x424ed424ef324ef614ec,0x434ec434ef524ed524ef,0x544ec544ee534ec534ee,0x644ec644ef544ee544ed,0x438ac438af654ec654ef,0x548ac548ae538ac538ae,0x60c6d60c6f548ae548ad,0x42c6d42c6e61c6d61c6e,0x43c6d43c6f52c6d52c6f,0x54c6c54c6f53c6d53c6f,0x64c6d64c6f54c6e54c6d,0x5322c5322e65c6d65c6e,0x4332f53d2c53d2f52d2f],#[0x5326f43e2c43e2f4332c,0x3400cc00680002c53d6f,0x3002cc02680204019c01,0x4004d4046c0404039803,0x4406e80680060405a805,0x5008e80880081807b007,0x500aec0a840a1c09b409,0x780d000c8c0c280bac0b,0x940f180ebc0e400de40d,0x14126c11bc110c10640f,0xa815fc154c149813ec13,0xd019f4190c1850178816,0x8c1db41d101c641b941a,0x6c21c020ec202c1f4c1e,0xb025d424cc240c232022,0x30299828ec2844277426,0x2d302c442b842ad42a,0xcc30d430082f6c2edc2e,0x8834f433fc3368329431,0x5838a037ec3734368435,0xd83bdc3b403aac3a2439,0x5c3fb03efc3e543d643c,0x30437842cc4214413040,0x50478c46bc45fc453044,0xfc4b484a7449d0492c48,0x7c4ecc4e2c4d504cbc4b,0x7852a451e0511c50544f,0x38564c559c54f0545453,0xd05a34599c58c8580057,0x485da85cfc5c505b805a,0xc8612060745fdc5f045e,0xb864dc6404635c62a061],#[0x9869006808675466a465,0x5c6c946be06b2c6a8469,0xd470406f486eb46e246d,0xe073ec7330727471d070,0xa477c476f87658759474,0x407b6c7a6c79cc793878,0xfc7f507ea47dd07d007c,0x8340828c819880cc7f,0xf087148668858c84b484,0x448b788a80899888cc87,0x408fa08ef88e088d188c,0xc9308927491e4911090,0x8975896b495d8950494,0x109b209a70997098b498,0x209f7c9ed89de09d049c,0xf8a32ca230a170a0c0a0,0xd8a738a6a8a5b4a4c4a3,0xacaac0a9cca918a878a7,0xc8aed0adf4ad28ac34ab,0xd0b2e0b1fcb118b05caf,0xfcb72cb6a0b5a4b4acb3,0xb0bb10ba78b9a0b8c0b7,0xe8bf40be94bd98bca0bb,0x60c2bcc218c178c0d0bf,0xa4c6dcc5e8c4f4c428c3,0xd0cb0cca54c98cc898c7,0xa8cee0ce14cd4ccc94cb,0x28d32cd230d178d074cf,0xdcd7e0d714d618d51cd4,0x14dc5cdb64daa0d9a4d8,0x2ce03cdf70dea8dddcdd,0xb8e4c8e3d4e308e218e1],#[0xc4e9c8e8c4e7c0e6bce5,0x40ef18ee04ecf0ebc8ea,0xb8f3e0f2f0f200f13cf0,0x84f89cf788f66cf590f4,0x10fcfcfc08fb40fa74f9,0x1d022d01390010ff20fe,0xa106c105e104dd040503,0x250b590a910981089907,0xed0f290e650db90cf10c,0xc912fd1235116910a10f,0x117311651155d149113,0xbd1bc91b1919f118fd18,0x1d20551f811e7d1d811c,0x1d244d237d22b121e921,0x112849279126d9260125,0xe12c1d2b712aa929dd29,0xb52ff12f292e5d2da52c,0x9133c532fd3231316930,0x15383537453651358534,0xd93cb13bbd3ab539e539,0x15410540053f413e7d3d,0x61459944a543b542ed42,0xc549ad48f94835475546,0x7d4e594d594c914bc54a,0x51536952695145505d4f,0xa957b556c55611553154,0x3d5c415b795a6d596d58,0x7560b15fb55f055e095d,0x9964cd64056339627161,0xe56901681d6729664565,0x796d956ca16bad6ac969,0x11722d712570416f5d6e],#[0xc176dd75e974f573e173,0x357b517a6d798978a577,0x717f757eb17e0d7d017c,0x69847183658261815580,0xcd890988218739865185,0x318d498c618b798a9189,0x71918990a18fb98ef58e,0x9595ad94c59411935992,0x319a6199799891977d96,0xa99ec19dd99cf19c099b,0x15a33da26da199a0b19f,0x8da7a5a6bda5d5a4eda4,0xedac3dab31aa5da975a8,0x91b085af9daeb1ada1ac,0xf9b515b431b34db241b1,0x2db949b865b7a1b6ddb5,0x61bd7dbcb9bbf5bb11ba,0x69c1a5c10dc029bf45be,0x31c569c4a9c3e9c329c2,0x9dc9a9c8e1c819c725c6,0x99cdd9cd19cc59cb91ca,0x81d1b9d0edd021cf59ce,0x6dd5a9d4e1d415d349d2,0x75d981d8b9d7f5d731d6,0xe1ddeddcf9dc31db69da,0xa9e1e9e129e069dfa9de,0x99e5d1e509e43de371e2,0xe9e9f1e8f9e831e765e6,0xddeee5edd9ecd9ebe1ea,0x9f341f275f1b5f0d5ef,0x65f785f6a5f5d9f4d1f4,0xcdfbc5faedfa15f93df8],#[0x620075ff89fe85fda5fc,0x1a053a045a0362027201,0x160942087607ae06e206,0xee0dea0ce60bf60b0e0a,0x6a12a611c610e60fe60e,0x5e169615ca1502142613,0xe61af61a1e190a182a17,0x921f961eb61dca1cd21b,0xf624162342227e217a20,0xd2280a274e268a25c224,0xc62bfe2b322a66299e28,0x9e2fd62f0a2e422d8a2c,0xde340233223246316a30,0x12382e374a366635a234,0x563c523b663aa239f639,0xe6410e40123f163e1a3d,0x9645ae44c643ca42e241,0xd24a1e4962487e477e46,0xa64ea24d9e4cb64bca4a,0x2531a5232516e50aa4f,0x125742568e55d254ea54,0x965bbe5ae659ea58ee58,0x3a60565f725e765d925c,0x36647263c662f2621e61,0xb268ee68426732664e65,0xda6d126c466b7a6ab269,0x2e7166709e6fa26ed66d,0x56758a748e73c672fa72,0xfe7a127926781a775276,0x967eca7e027d027c0e7a,0x5a8386827e8176806e7f,0xc687ce86d68602852e84],#[0xb28cba8bb28ab689be88,0x42916690528f5a8eaa8d,0x22962a95329426932692,0xd29aea9a0a9926981e97,0x469f929e9a9da29cba9b,0x1ea436a32ea246a132a0,0x6ea966a83ea72ea616a5,0xeeae06ad02ac16ab62aa,0x86b2aab1bab0c2afdaae,0xfab716b632b54eb45eb3,0xaebbd2baaeb9b6b906b7,0x5ac0aabfb2bea2bd92bc,0xc6c4eac40ec332c23ac1,0x2ec962c89ac7bec6e2c5,0x101eccd2cbf2cb26ca,0xc15151905080426000c,0x222a041a10090e19120a,0x3c20344c285849021431,0x1d24b2222cb470b8642c,0x9444de1e247d2868412d,0x6c5cc4d48cc03854a480,0xbc905088cca074d06078,0x88839c6445c7191084a8,0x2220fe0888b8ae222f2b,0x709107de888b91c441fa,0xf20883c68222e3c2445e,0x591445e7411171e8220f,0x722631f80910746c8a34,0x7f1244dfa49117f40225,0xf7491175d2445fd4910,0x8baf0222faac883f0b22,0x41d12368d046d107bc08],#[0x1185e11446be48abef24,0x3a356918ddf120e07844,0x9900170e8d98468b3088,0x5cffaadbc106df9d1f5,0x7bf5660045857756700,0xe3630644174fd6d0c049,0xe7b00dbe7c61904567ff,0x8456b8d6d0c04927e7f5,0x797f518300831bbaafc7,0x61818b6eea6a3061430a,0x17c0bdd18700065771f4,0x61c40bece2ff46180118,0x61fff3b12644165d6374,0x5f3eb3208a8397acc801,0x980005a7ffb1b5990017,0xb7df9ef5670005d7ff41,0xe0199105c677f5660045,0xf601b7cf0b3208aefcf8,0xcff380330000c0f9fe3e,0x67000657ea682cc0a5d7,0xff059801175ccefcbbc1,0x16ded4d059c10bef33,0x670facc8015df9e7c199,0x7480bf1048339f599045,0x217acc8016ee802fc412,0x26000185ffd06600016d,0xfee1f066400b6f3ff351,0x1fa08f7fcf1b126400ba,0xcc0002fa7d6640057a40,0xfe1c35126000191e77a0,0x264116df9e7c19904597,0x5e1fe2701293fff1b1],#[0x1fe4e8941fffafe10661,0x415dffe9e60893008312,0xb7d6159c00171843fc9d,0xb41620012adf85660045,0xe41145ffccd8dc882cdf,0xf89c04a6af1f200557e3,0x4733ffece70661005f67,0xfece2c498041828f8294,0xd670005d493fc9d4155f,0x30805d673acc008b2e89,0xe9e24893220c2f9edc83,0x5990459781cacc8016df,0x20c2fe3722be22ca7b9,0xb805fa0b6fffeccec48c,0x45cdbcfebaf401f7ef1,0xfafc33080567eccfac60,0x904547f9cc6c93220baf,0x44171edf66400a8e4fd9,0x4ddeb19002dbfddf6246,0x1c6cd0cc7eefeb190458,0x2005467d23bacc800c02,0x62617f59904586feb3,0x3f818641175771d81864,0xc24b6fc7f40c3b05875,0xbf17f030c80171d4fd03,0x99001599f48ec2cc8830,0x99045857e166400b2fb5,0x3ebba971864006565f85,0x8c3208bafc7fc619002c,0x5067d23bacc822f3887f,0xb2fb1264115d8bbff88,0xb8ee30c800c2cbfacc80],#[0xed0d0092762effe20aab,0x5a79010372fc7a02ada5,0x5067d23bacc8017b7f37,0xb2bb624c8016d8bbff88,0x45b8c3200322bbd66400,0xe3d4553c736a52012abb,0x5e79e4d8c1900181d6f7,0x224c882f339e66566400,0x16dd9cacc80165ffed79,0x861c618402ea07e56641,0xc8830b3bf0668a4ffff,0xb1b8ff0ca955ffece2c6,0x27186400b4939c619045,0x820977fc3b8f900165d,0x4114dbc7c8014affb94d,0xfe73ccc8c32003037e3e,0xc923064418d3bf0668a6,0x80169ec7f8654a6ffe13,0xc12fc8c3208b83e7230c,0x6400b6fffcf9d8919105,0x473e7cfac641161b97ac,0xff237b32002d1afcc761,0xc80154feb5690420826d,0x231f4595f6cc822ab76c,0xb7fff667620191061183,0xd71ec03efde24c033c85,0x8b8fd99f503208b9b79f,0xff06641151f5f8eeb320,0xd664005fa390efe0126f,0x30afc761664005f19973,0xffc80546fefc9c033200,0x212b49822234612e3b5c],#[0xd7e3bacc80174c460827,0xf80493fefef833200587,0x8e4fde7acc8016e8e43b,0x664005ebfcad7c7de404,0xf3c7332b320030bdc380,0x2c3ffd8ff20cc800bc,0xe77e56641165fde79599,0x82fbfff430c2cc882f3f,0xc2cc822cbfff4e300cc8,0xc7c800b17bc7dec0309c,0x4effda0b080012effe1d,0x3237e3e4114d7c7c801,0x66400621fcf1ccc0b320,0xbcf02cc8016dff63f600,0xfe149ff3bf02cc822dbf,0x22cb33eb19002cbc6e01,0x1f96f8bbc907d99f58c8,0xcd8aeffffc670053220c,0xffcf7c153208b8f89703,0x175fff9ef82a6400baf,0x7d0cc800b8ff391bd990,0x5578dc03fc293ffdfd,0xd8acf7db3208a8f7db32,0x9b7bfc75ec038f89703c,0xb44977fffd99e163208b,0xe34ccacc822f18f11803,0x41181ffec7f906641171,0x357f30c28bfde9e49126,0x5ef4f7b00c3cf5f7b00c,0x3cf5f7910f7275b7b00e,0x8bcfffe539c199045c3,0x1abf9d84e7ff99c58932],#[0x9002fbfd91cccacc8018,0x5f09224c801812b9e419,0xc29bfffb33b123208bce,0x2f8fe67c6b685713e364,0x532005f7fce46ea9900,0xf9e86a826400c4fffabd,0x9045e7fa48dd53208c2f,0x6a82641189ff7febe829,0x2006113e3770a0f9fce6,0xfde373e400597665b123,0x1041346f1fbc16200132,0xa4ffa7c82289ef7169a,0xfde266cc800bcfdd3e40,0x30d35fec40222001389f,0xcc801599ff93cc124c88,0xc882f37e1b3208acfd86,0x5bbd75ec036fff9d2c48,0x86ef0871123a758c822c,0x2bac21485514de10e226,0x198abfe8aeb0852157fa,0xbbb0433147fff725dd80,0xcb7f159e10802effedf4,0x840177fddfc52784200,0xf349e10802effbbf9acf,0xe00422ef03cf80108bb7,0x8c3f85efc30844dec367,0xc373600043270d8f8010,0x200859ff0ddd80010bbb,0x3de0b9b00021a7f86eec,0x61127fffecfd278c308a,0xf67fb2c6108559f6cf18,0x37ffbb3bd9630842cffe],#[0x20462b7e491f48501013,0xeecf0840157fffd2df36,0x55fde52784200bbffdfb,0x10802cffefef7b3c2100,0xfedb3cf80108b3f7e49e,0x1011a3c9ecfc208455ff,0xf63e00422d7f714ce010,0x10042aedbfcd80010b16,0x1fa7fbb0002157f4bf76,0x2028466f6d3e6c00086,0xf5413020284675ffa0d3,0x2153e7d5b102028834bf,0x57dd80198a3fa8eeb085,0xbe4f7a4000021327ffe7,0xc228f7ffddba4f186115,0x2c610861efffbb6d9e30,0xecf658c210c29fef76fb,0x7e4ebd2100101345bfee,0x195bffe757cd88118bd,0x10071ffb7fdbbaecf084,0x784200cb79feefe293c2,0xb24f08401b7d3fddfcf6,0x7a9e7c00845dfdf7fdbb,0x8c9ed767e104228dfff,0xc7c00845efef13380408,0x3ff6a896a18459fff3ae,0xa0098bcffda6adaa6113,0x87531e80204697eee367,0x9ec3a2cf40102363ff3d,0x10b99eeea63d004c6257,0xdd84010a3feef5fcd800,0x21a7fafeec20084dff4f],#[0xd010106c7fbde8f9b000,0x401a02020dcffe3cd6a0,0x726e3cf40450cafe6e6b,0x3ff3d42d167a02020de8,0x228667cc9ebfdfa84216,0xf03042026513d6e367a0,0x667e657dcd1118a9df28,0x404c0f47f2eb0f00046,0xd70f000404c0ff85ef00,0x323abe6cbde0008cc8ff,0x8d004ccce7e2b31a0081,0xf2b3c210056f7c7bf159,0x4200a3ffca4f0840167f,0x7ff693c210055ffed678,0xd9f80108abc79f002114,0x422afbd7bf04211279e,0x47ff6e6c0008557b63e0,0xdd80010a3ffdbbb00021,0x8147ff973600042cffed,0xa9ba9216051fea6ea485,0x8c5fff8d4f7480722cff,0xb2961005ef9bcec41014,0xbfcfdedb2961006177ec,0x10069fe7ff4594b08030,0x5021167feffd7ce5b296,0x7f789d8a00202346939a,0x6940845dfd2f74b84225,0x76802c020468ffff9a9e,0xb5fc0d4170408c4ff5e,0x6f7480102cff5bcd2004,0x205df6b7ba4808157ed,0xffcd41d0902affa9e690],#[0x214464bffcd51d090287,0x9f9fe388a448eb9cb814,0x9618445bfa4e5861125f,0x5dfbfa4a5840156f7b3,0xd494b0802cf4fe929610,0x8451dbda4a5840177f7,0x51b5f674a0422af6c694,0x58d28108b3eb6ce95084,0x848147f7d49c90902a5f,0x3cfecf910a449fff24e4,0xf1a4008165fdcf201489,0x102cf6bdce900205ddbf,0xdf38d20040c3b5fe7480,0xc0b3ff7fab9a9216055e,0xabce900e459fd5335242,0xdf2739620002919bfff1,0x2c3089bbffdd272c3089,0x2eddd252c200c3efcf27,0x8034b7f9fbdd252c200d,0x92961006dfe7af5494b0,0x9b1a5021157f5ffd7ee6,0xe970844dfd7674a04228,0xffff3558d28108c3fa6c,0x899fc2f3aa00b00811b3,0xe35804a5e7ffe5147d30,0x99f0fd4c6b0081191f80,0xc0252fbf6704c6b00811,0xefdea9392120603f531a,0x148a3efbd92724240bbd,0xaebb1e4029147b5d9f20,0x40c9ffc0ff4111600c46,0xd24040abffeeb5f8d200],#[0x1b7dafce9202055ff5b9,0x880386ffbdea71a4008,0x41d0902f7f90bf085058,0xf27d4c6b022862cbffdc,0x63f3f586098d604401b9,0x114326fccfebb5af8481,0xa740b4288c8fd7d46358,0xc451f9bbde388a454d1f,0x292c60051193aac6bc0b,0xfbfe6a40c60051199ffc,0x40b00c468ff3b3af02f0,0x7ca2102c026655c97c98,0x59f9f6ca5840153ffd,0x94b0802affefe7db2961,0xffdf9d6ca5840177fbcd,0xdd28108b0abcd28108b3,0xbe55ee970844dfff6cbb,0x2059fffe0b3cd28108c,0xf777ba48081477dde690,0x480102efbbbdd20040ab,0xd0ba86ea085a157becf3,0xfba001a147fe357dd000,0xefbf1d9c30802eeffdfb,0xc200bbdffef938610055,0x7b6ce1840167befcf270,0x65faddf6d94308430f7f,0x8010c3fdbbe8b286108,0xfebfba1002157ffb4dcd,0x861fffd3774380428fe,0x7505c210c3ff9abe6840,0xfff9551748428ff63fef,0x2020d03f1e7502020c1d],#[0x2704240c87ffb3826750,0xeef9ece0848177ef77c7,0x2059ffbd4f3c001030fd,0xbdf060409bfbfafcf800,0xeffcebf1e0008187fff5,0x2a920518fffdc4950902,0xfd4cea04401839fff9ab,0x42847f9e6367502200d2,0x3fa1e680028612f74101,0x8284cfe7f0d41501141a,0xe85040141b35ffbbfc29,0xff85ee200044c4f90b9e,0x4dfff1ae1c4000899d9f,0x84015b3fdf3662a0444c,0x75938610061fffdcece1,0x59ffddde4e1840167ff5,0xa1862157ff775b386100,0x861dbad9430842cedf2c,0xba1002187ffd56e68400,0xfff16ee8500859fedc5f,0x1a051ffc54f9a10021a7,0x77eb2704240b3bf3b382,0x2065ffdf679e000817,0xe77be0408147fb59dcf8,0x167ff3ddc78002061fff,0xd5ee80028597579a002a,0x342affe957dd000d0b9,0xc7670c200bbffa77f740,0xfbefe72c9c308034fbef,0x40177df5e7938610061f,0xcb28610861f7f796ce18,0x2185bae5b28610865bae],#[0xee840085dfff69b9a100,0xfffe9bba1c02147fbda7,0x842187ff8a3e68400869,0xaa2e90851fdc7fdeea0b,0x47ea97deb842147bfff2,0x9c109030fd567bd70c42,0xef75cb2704240cbdd71d,0x4040bbfffd4f3c00102,0xfd6f7c181026ff7b5b9f,0x30ffe15b8f00040dbff,0x5255240ab8fffcc49509,0x1fd527bd709028f3fff3,0x14304ffbd4073a80600d,0xdc52f7400143052f3400,0x82850f79f61a00a808a0,0xdff144142875fdbbfc2b,0xff0808ee200541ab8fef,0x2a01a0d0a5e7ac0a84cf,0xf9d9c3080294f79e4866,0xabff7ff938610051fff,0xce1840147fefef270c20,0x55dfed94308428ffdff6,0xdcd08010abbf8b286188,0x6fedeffba1002157fffe,0x8400859fffdb77438042,0x77e72704240b3ff3fbe6,0x3c00102cefdece086813,0xfb7bfcf8202055ffbfcf,0x8167fff7bdf020409b,0xb2f74101424ffcfff1e0,0xece1521186fe3cd00150,0x5211745be4e152116450],#[0x945b6ce152116459e4e1,0xb2854086149baca15021,0xdb295650a810dbfed96f,0x142065419eca15021a7f,0xb672e4e05081a58cbb38,0x65ff6df7d9c0a102cff,0x4fee15211258ed938142,0x1d21107bff6e1d210f7b,0x1373f7ee1d21107bdf6e,0xffa87408497bfbea1502,0x2126f6d7d43a0428dcf,0xedbfb81420517bdfea1d,0x68408b7b6f4e0d08155,0x55efddb834204dbdfff7,0xcdc2a42265f0eee15211,0x908997e79b8548450bf7,0x5bbaea1502172bdb770e,0x810cbfe9defba8540858,0xeea1502177fd2f95750a,0x8181ecbbb83420585b9,0xddc0a102affa7f2e6e05,0x61eed9b814205dff4ff7,0xe4e152114634ece15211,0x5211463de4e15211563f,0x97bfaca15021563f6ce1,0x942a0432d8ffb2854085,0x5963deca1502176c6d5,0x6e4e0508195edbb38142,0x42061b5ff6702840ab63,0x3ffec40ac81658fd9381,0x67decfff9102b205df7d,0x2b2061f7b3ffec40ac81],#[0xe8000aa2357df4ffd910,0x7faf7f5402a917337cf6,0x2cfbedfbfe801450b3db,0x4d70893ef77effa00514,0xbcfb664d7088bfbcff26,0x226b0851bcff644d6109,0x5d3bfec48ac8145e77b,0x8ac8137fdeceff9122b2,0xe9dfb2645640b33bfecc,0xd7089afbef7620d708a3,0xfbdd8035842cfbef7620,0x5902cebef7600d610b36,0xff76205640c3a7fdd881,0xbb67fdd8815902cffad9,0xa2401aae9ff76205640,0xbfe640ac817bfe2df480,0x61bd9dff7205640b37b3,0xa88d1ffdf4efd9902b20,0xfdd00aa458dfa6de0002,0x7dbb7ff0028a156dfead,0x4004167bbb7ff0028a15,0xcff976ed0010559f5dbb,0xdda0020bbecbb7680082,0x9895dc71dc0508c5ceae,0xb803263779e4388ee00c,0xf3663b80a1181e577523,0x57ffdfafc35ac220adfc,0x11468fffdfdd86b58441,0x53400451adfc9d914d00,0xddafc37a4220b1ff08e4,0x1289bedbf837a4220b3,0x987f93f4025147b7c9fa],#[0xed0010587fefe12f4328,0xabfed53b48041565ff4,0xaa76800830fb7e9da002,0x4182bfdf429e8441773b,0x54064fff2dfdfc21e84,0x62391dc0461954a9f1dc,0xccfa95b91dc046191e7,0x1e625133f3b1763b80a8,0xf2fe9cf1128ab1ffcfd7,0xcc2ffe05f16c000d1907,0xb6000733bfdc322d8001,0xfcfa77c06a2177f811c8,0xf43a8981fae081c05cc1,0xdaee37a4220a87febe98,0xf4425126df71bd211051,0x4161fba7e804a26d6ddb,0xb74ed0010599fdd3b400,0x20bbbdba7690082af7,0xfd7d3ad61104dceee9da,0xdaa12893eba9d6b08828,0x10545f5bb5025136b7ad,0x6d5bb48041567fd6ed00,0x80082efb7adda4020a3f,0xbfdf4a1e8441673bab76,0x4228c96fefa54f4220aa,0x97d7e788944e97c1d607,0x21105153f0de10882e3f,0xfcefadf80020b2aff3bc,0x80828fefef93f0004167,0xfe4fc00105dfdfdeb7e0,0x186178dd80030abfe3,0x5c138fd01441a267c6ec],#[0xa9cf3c0b23f40520ceb,0xfdbb10061574ea758c23,0xffe2fedd88030b3dfede,0x830ff7aa7f3bc21105de,0xadf80020b3d57e0de108,0xfbdbe4fc201059effdef,0x20bbdfef6f5bf0404167,0x4b508830ffc7fc9f800,0xd7fefa52d5220ab1ffbf,0x4062565fe2b9fa02c066,0xd6ec00185aff1703f405,0x6a118585eb76100c2a4f,0x4fdf1a606157ebff7d28,0x66c7f2fedcd1030b19ff,0x90ccbf7caf1bc00048,0x2634052199ffd0963780,0xea9fcef0844153e78fd6,0x6fc00105d57e0de10882,0xfef6793f0004187fe75d,0x4187ffd9d6fc301051,0xdc6ec001861ff8f793f0,0xe80a20c04e376104c2c4,0xc3aeb77fea1484ecdc27,0x6177dfdbdbb76200c2,0xc3784220cbeffc5ddbb1,0xc3d57b9de10882cf54e,0xc20105df7fceeadf8002,0x7f6adf86020abfbdb64f,0xcbfe3f64fc001061f7f,0xadaa441647feec12d422,0x4ea643f40540628ffdd4,0xd80030a9c43a7e80a80c],#[0x21bae756ec00185d6ad,0x35c0c267bf1fb4541a02,0xfd777e68818593ff9bbe,0x2e22976fe805c41ffa3,0x3f5498d0154cd67bb7f4,0x4184f563bc14105cf7e,0xfec7782820ab3d586f05,0x504174df61bc14105d9,0x2c3782820cbffc7c7cef,0x2effe9fb73bc1410593e,0xcf786820a8fde0de0a08,0x413678b2de0a0830be2,0xf6cb786820a37ed9ef0d,0x41a7ffa4af9de0a0830b,0xee7782820b325586f050,0x3649fc1bc141061ffd97,0x5620bdff5e4085014420,0xf63142b1059fdbfec228,0xfffaffb08a15882efedf,0x28dae7feab500151468f,0x440a1856f7e712aa002a,0xbbff59d10286157fd67,0x18a15883269efe628562,0x9efe6285620c3ff967bf,0xff9a7bf18a158832ffe5,0x8ac41769fec62c5620b3,0x67fb19b15882ab3fd845,0x85620b34ff61362b1059,0xff08a158830fbe9ffe62,0xfbd9ffe6285620b3ef67,0x451abefa7fe08a158832,0xa002a28dccdf3dad4005],#[0xbf7dd1028616337e332a,0x47deefdf7440a1859f7d,0x5dba402c1525dba482c1,0xc5fe500580240d5ffefb,0xb059bfffe507426099ef,0xc0b4008198dfbdf6c380,0x5ff605080081a9f88f9e,0x478dffff6c3a03054fc0,0x300c8eb5ed91d604403,0xc8eb02c0647cefae23ac,0xf3de47581501807fb9c9,0xc175eebf06e484c17b,0xde4f9003059fef6793e4,0x5907fff824e84c185ffb,0x400c1766dffff093a130,0x974e920305dffff35d3a,0x13061dbf7fe1074260b0,0x870160b3f7c9ffff083a,0xffdfae1dc182c9bf7bed,0x2c83f7feb871060bbf22,0x1819ba6ffffa61d018,0xb1800606674ff7cf22c6,0x99820581606a7ffed0c8,0x3ffbc987c3e0a9ff909c,0x4cff9d36200022066ff8,0xfe5074260a2b76e920b0,0xcf17f950580240d1dbff,0xc1828dbf7bed870160a9,0xfdf8e20c1432ffdfbe1c,0x74dffff6c3a0305587ef,0x858157bef7e17af85813,0x9f8bd7c2a098ef2f17af],#[0x82cfede3e2f5f0a828b7,0x4f9003059ffede27c801,0x13fff81274260c1ffdfc,0x60b1f8dfe0222c041036,0x7dea9d20060b96a9d240,0x7e2ff010058082070fff,0x582adfffd083a13054f,0xbd5c39830616fdefb61c,0x1f9fd4e3883069fe85ff,0x378dfffd4c3a0305dff8,0xf13af01d132713af01d1,0xaf22fda0816056345efb,0x1ca1828dff794c3e1744,0x3ff7ce0e50c146bfef9c,0x58fe67273b2914a231a3,0xc1ca182cd7bdf1839430,0x51bf7dd0428c1467fee8,0xaa085182cefdf7410a30,0x5dfbaa821460b3ffb7ef,0x29438505ffdf38294385,0xdffdf38]]
def g63H9 := limbs80 #[#[0xc010140b000371c800,0x42f1580400c150f802,0x7c060000101c0913c00,0xf0020983700c0004800,0x5c1c01c1300c00008b5,0x8020e02b0401802401,0x10110081b0980300429,0x281201407010070000d,0x18220000e02c0505011,0x300b010010f00200c04,0xc000b0020440101012,0x1002504420e01300000,0x20330d404004000000a,0x8008030980600c00,0x4260004c0901615804,0x54000f0000182205805,0x12c0004c1406c1712800,0xe804010360740701802,0xb81200403004020e802,0x2b00901c2500c0702001,0x40d1680700c0309024,0xc09030522980000403,0x38e30880e06c02000a0,0x1300010002018cc09439,0x2400064072744c07c00,0x880a060010940a1a444,0xb1bc1e0040109404,0x68401000010600a03018,0x1a8180ac1401c0001c32,0xa0c4000780b04c00,0x342b0000001c3100809,0x701c01c070181000002],#[0xc01004010141100402,0x4c2b0000104c0300416,0x881137c1b0740000c04,0x988e36c0c00c02018eb,0x1585402c0a054110c017,0xb706003008331ec05,0x580b02cb7060300d456,0x38702ecb40ac4b03c3f,0x27c1e02c1403c000001c,0x1a806080001cc0004000,0x2a02c320000b05845,0xb04c1f03c0802403,0x4000782c01c0e00800,0x804078220000014c1c,0xc070d0080f00a01004,0x450080003401c690284f,0x2e170140640d00000,0x14780543c07c0002800,0x1d4030006e0802b0f80b,0xc0a1e845034080200a,0x1b804068000c01100416,0x3cc9a00c090200202c3c,0x4f83b00c0704c0e0cc1c,0x21240383036c2505c04,0x1825000053901d05c4d,0x1c0260b02c07000020d2,0x4c1f1180a1882f09413,0x640b000251380031000,0x27c401500202c4f29802,0x100a090b7084712f01f,0x1b48529801000010280b,0x4050302b1c8021a800],#[0x2c0230ec02014025c955,0xc800018201080c23406,0xa0101d000054841a409,0x1f1310000e1680902c02,0x40936e4030100b00401,0x106c16c310942c33835,0xdc06380500001a02838,0x134e009cd3004260f089,0x258e00780f188010e439,0xbf0401b1380f02c0c,0x3c3d0440a0953529408,0x2184a45b0c41401400,0x230d500d260105800402,0x8d521825094430789e,0x100d00c3d41d300047d,0x1200703401038120b000,0x6a0120380e1b03009809,0x1800584000301c0fc62,0xc4752180500ced0147c,0x5416004b02940240007,0x28171c0000ac0006404,0x5ed60acdb7105500013,0x4c0150373240703574,0xf090000900805814,0x33cbb000000195906c00,0xd04f000021300624896,0x180306400048b445804,0x1171104130559e00000,0xb82010071285361f00b,0xa010013341603d1d,0x6a0043a0001501c00083,0xd048e5013540003d6ab9],#[0xec4000194dada170645d,0xb67212b81d8000000032,0xb492ce117dc000385d78,0xb5c0001d4b1086b17405,0xb6143b0000022d31a668,0x8ea9fd6283020cf12491,0xdb268934ec80002a5464,0x822d2958839181fa56fe,0xe075bebdb96e6c121336,0x9e00002e6245feee1f26,0xb591bc80000ac4b6a73d,0x39d858ac1985b87c55,0x98665b00002c95c00000,0x452521417e00002acca0,0xabce12a9ad5bc5c8fad,0x15c608b14de23e44fe50,0xecf9c000894c1614e934,0xfa808ecae22a7bdd5d7a,0xf051c64c791524c0b71,0x42ba00d0248a001e3f68,0x4a34d04ac53c44b6e465,0xebe1f846988e05a81e72,0x39b9d9d834727ff4b580,0xd1ccadc5f1464db9db1c,0xaea47af98d09f5414049,0x4f46867a0d6a676d6488,0xc700002ee4102a3a85b5,0xc545864c9b2dc684e5a2,0xa040002a3796cab025f6,0xcaed80a9f22eb861efc1,0xcbf9e9400000002aed54,0x79000000002d963e8d45],#[0xec5a2c813f40552d0f2e,0xfe51e7fd6e5009e27774,0x10f1724f6da105,0x80866d150faaad1a4680,0x8fed1bc90b943584a974,0x321c3e29bf3eb8de6ba9,0xeebd8054957cf86df012,0xa1dcb2f64eb6ed3030b0,0xaa6a6898d38606b29ee9,0x290a428a9f5cfa6dca06,0x9131f79495142e5536e6,0x417e158117c8f73c9cc8,0x1e000039829d763e2b9e,0x9be6446ed9b84621cf6d,0xe7710040f444d84aa28a,0x12efa0ab943fd40ac,0x9be0f558520d667d2540,0x3e800000002ce69183ad,0x16b2c2cdbdbc983ad499,0x9bb900b27a9e6eccad00,0x6dd1d0b64f1e91e621a8,0x368dc2de22d11d9ca4,0x36660f4431619b18e940,0x4cb20a7cbd901e2c600c,0xc9811342deb2ba118eae,0xa668a3800016b7a9b278,0xea69110c51b06ec43604,0x11c0001e7d5280043a64,0x348660ef000006,0x9f08b1b9b14aaad26dc0,0x69cd2380b3010dce60b1,0x2461c2bbedb1204e56],#[0x72c1218a654d6b0e2540,0xbc5d981eab44d80818e4,0xcdde99d6572691b22,0x5d8ec01e721c60943940,0x410e340c08a1f95c22a5,0x15366d8df400002e3bd1,0xb42d9dce79cca82dba0a,0x932c8da4f9edffea1630,0xf27e8e217f46dc5e5d34,0xdfad13c4acf29,0x6194233e770c9c283ac0,0x9de4fc0000268747372,0xed898f08a1cd,0x676c99400000001a0700,0xae9aeaa8818a83a29c84,0x6bb6c5800005770edc85,0xea3706c1d4984e8ec,0x358ba16dd040b9ca40,0xd3de45428d0000189900,0x1700000e3c3d234db5f8,0xce000025b280003d7cb1,0x8bc4d489ab38e4d0ff25,0xda5f60eef01edd67ad4,0x10f7e1b440000a36cc,0xbabea18000363fd27840,0x1089c090ed91400008,0xed3edc480,0x4329304c9f869fdec40,0x368842b6647ed2251a,0x62c5ef10512a30140680,0xd9400030d90c76acd301,0x78da873594b06f400034],#[0xaaa2e5f29d400015f498,0xe1a826814ada7d9de734,0x96242ac0001d2d00eb7c,0xb500001e02c0000ab208,0x2b8867de9fe312025,0xba48880002449c00000,0xb9ad8abec3bd5086ab0e,0x597decdd4976195845d8,0xa8d8dc7ab6289d400002,0xa2216206783d776d5ad9,0x671c7262be9e2e7e7109,0x919634d0b73a9ce90ebd,0x757e283ceaf09596681c,0xc2d00000669612275,0xa6f4f18d8769e6300000,0x3680cb800035ee69c5b1,0x95816d000000f7722c0e,0xe6d0f258efe18a3567d2,0xb13ac279537cf88a0382,0x9411aa4476255d2692ea,0x7b2cafc8ac70df4e8792,0x8535ea940a01c189b6ee,0x26a6e658c1d8f2999a,0x8000022ba40002c1980,0x3e115ebd9e9d5031003d,0x782cfb0c1faada494c99,0x2579cc5b265f6875cd,0x5a357c7a472a83cdd700,0x2adaf93ed8ef893ba9,0x8aec0480003007b48b00,0x1080002a08d60bf0ce24,0x828df2c0edfae4a90ca8],#[0x8966ea000004eb8826f2,0xf04edfa4dc800009e9ce,0xaf0000000000002ed754,0x3191d11887fd0bc00031,0xc3000000003222de66a4,0x342740003d91c0002d,0xc41a612cf1182254c940,0xd97941744c0d9778025a,0xcd49dc6dbb00001ccf0e,0x7ddd121653e651b05568,0x1fb82105aa0ca1bd70a0,0x3af64eebc5e849,0x220422e1a440002dbf80,0x12ce99a2e00002a5364,0x8cd5c78955c0a9305965,0xb2c4499675c000229031,0xa0b248b08059a2ad72d1,0xd530c929c700c6ceecaa,0xd2684156e116660058f2,0x61865895ed987462c108,0xf36ad7d17acebc800038,0xc8000019c0449658f958,0x84d4b6d06a5223b54ed6,0x5c3ad1e88781d5755968,0xf91dec84af85689c75b1,0x8f6227a5c2ee5eea5879,0x1f7cc386670000155cae,0xc505cb4082aaef0b86d,0x75d506b297c00038d518,0xd2b061442cb3483e9,0x4b516f5a16800038d640,0xc4f55436ee4a328ab36a],#[0x5f866991d0dca26c31f4,0x2df60e00003df32e87f1,0x75a13a4e7cd2f681a4b5,0x23c00015c5f1377a24d6,0xe8ad457aa318742ea235,0xa3eab3f1b062bfeaef9e,0xe02220caf00ac4681660,0x926d321e45fe5e4642c1,0x22c31276b57cf6f264,0x5464650000000000ce80,0xa2c1b9f8450000341388,0x3708a05d13800021e050,0x2838bb2a558c7a3cb118,0x862db65eaa9a0d0e631c,0x2ffa978a0836b0e6c62a,0x3bb427adbe6d9b480e0d,0x24000104b4566e16342,0x63e8194cf66adff61f79,0x74f18d8185fac3c00012,0x3263aecdc9f77a616e,0x61a944405a910f5c1900,0x2a6587a4310cc5400019,0xb740002d152c5c000024,0xdb79d6809280003689a8,0x2c105201000bae0f20,0x36e97957c00021f0c0,0x9f0000000008f5ccbc80,0x2d85aec0003a2601bc38,0xf5ac65fdc4de0ec823be,0xf740000000300140002a,0x80aa2b2e9e92a842e2a6,0x8bc62a40001aeb01588e],#[0xdde9944d10000342c86,0x341a551c84000004be48,0xfa00000a3fb9d7d891e9,0x8d8cb35cdb18905c7e69,0x3ebdefb1e99561000012,0x52a1d409d9a02526bb5e,0x3399b3329c1aa11deb1a,0x164000257fa11f0434e4,0x2e71016c7936dbe5459a,0x6a752db08cf0a6d24bb9,0xb44d28d503e107261482,0xeb4221180399028259fc,0x12ac4a40003cfdbecc5d,0x3aa90ecc6d5139a8c189,0x5dc4a9dac4fca88ddec4,0xa52158291eb9c8bce358,0x287030c028800005df4e,0xaed8bc1dbb83c946c8e,0x190f680002d2a222cf1,0x20e5dd000029e6423596,0x3b52c0d1e0b2100e9478,0x28ac881aeed7ae953c,0x3af09a50c074e05900,0xf04959f2498d0e7ccbc0,0x1a6d418e1aac7f0c4829,0x4ee2387d20747024bc48,0x39576532682f7d2696,0xac3ac868ee4163898480,0x81e6347cd2ee1c896059,0x4234b68d58cad896b334,0xdc1a3a5d3cea2bcad8f8,0x35787b3e2961177902d2],#[0x3cc293e235c1c3ed0a04,0x9db28171c3590c2d1db8,0xd35cca0d4775e462e785,0xe6c0001413f55215b216,0x9fa1eebcbf0086000020,0xb39c1dd908c64585c878,0xc460672a1fee915eec00,0xcfa922d130b6f6d0b091,0xe52abd127a2ad0449d38,0x40f548864e18a7dd787a,0x5c63522eed527400008,0x1996bdc00036e9000019,0xb400001e516682c00022,0x4335926217425fc00002,0xc489058995a02ddc810e,0xa3ec2bc20f9e5ccd2828,0x3c1a906800002998c9,0x3aad9cb925a2e2b440,0x8baab4916eeaac344900,0xf7923d9441da0991c2b6,0xc5b6009206ce6aa6df2e,0x2eb7c9bff19024,0x35046466ad916da3040,0xbaed3588814243425aa9,0x442c4d28b56670000012,0xbe5d7441c1e520fda536,0xd8ae8ae183ee981168fe,0xba80dc3aad6c2a9df09c,0xc92954ede582805e5575,0xa514d1b16b5ae699c0c9,0xdd4046b5661db8fee674,0x230d1951cdc5b7561545],#[0xd49acdc11ec43a1bbae,0x48e0ed6e64c8dd09,0x9b1c0724697d92800000,0xa8253c28ff4118b1731a,0xe1417b80000aee39e565,0xe4c0003916156680002d,0xa77a5eaea25532c6c76d,0xa594c8bd9f800012b59c,0x971439342f80000a5b9e,0x235d97ac04796ff12e3e,0x3ec5edb4c19ff69202,0xc1e5dde94d000021cec0,0xcc8de93180003d4fa4,0xd7c0000536750a418f89,0xd8c01c59f800b611d5fc,0xf4fae8400000002dab60,0xae2eaa00001c41a05d1c,0xf6c00038974981000028,0xc21d999986d49cb92648,0x9884d9ca91151188442c,0xee350d0000000022a93c,0x7f497bd1507c8e5e3cac,0x6ca473ae41000024ca48,0x8f545311232d9702d15e,0x7306ca7812028460e0e8,0x6a000021ccc0d431093c,0x37b1953d14dd1c000026,0xa204d9ae4d283f4df181,0x675363cacc0003aa5d8,0x400590f0f424c1400035,0xd0d0b4f0300d15407841,0xb1f46e9a3f0a243cfc08],#[0x587d1acd3d16e2554f3e,0xff25f286e1c0002cbc2d,0x4a45a9f6f0edfcf127d9,0xd5d611598dcee9a0a699,0xa1913355021a842c38c8,0x565a34917efc48918d59,0xafa45880001e9f9a113e,0x1834d019e6a0cffcb7e2,0x8346cba5cfb8cc20a0c9,0xd59dbd685ee2f115b0ec,0xd40945c0857e97483a09,0x4fdb7000000de4d50ea,0x82e0614661e079b086e0,0x21e619f4dd8d913993e0,0x5b9c947c444df5f8faa8,0xf6000006edbd1d21b3c9,0x104ae662fce8ad70d2,0x184ebf644ce24fb61c00,0xfbaebf8cb27528606339,0xa9982e190c65512c6cec,0x4d5465a667fc06264615,0xfbe57f04abc94481da31,0xd63c14f4572cf5b98244,0x7ce12c4982eac8800004,0xa9429dcedb764b00cde8,0x1153be9f04ececfd69,0x7551f72944f525b1ee00,0x149e68ec0b14de1db898,0x939ab738e9d29a00003c,0x11d3de94bd06e1f699,0x270438aa955c7d566280,0x47fc6e38feec935a5dd9],#[0x714af32a7ba42d50ab21,0xfd2cb1eab6d5964832fd,0x6d6c5428157604418ef4,0xc269442ed59239c286b6,0x1b4136a95b54b03557b1,0xd745372d49162fc00018,0xaf915c87fb146c12aa5,0x8e4188dcb8c589fcb2be,0xa03988be375e8830d085,0x653e5db02444428dcd4e,0xe205e12119aef2118f6d,0x843d0d98284929a67080,0x2e85c770a495ad86b025,0xff6d2c2cd59d0b51b821,0x2922f7c2c61ac4de439,0xf3498b5a4840b0f5e370,0x1ff1552a21ec94d2371a,0x9ec2330e247ab5ea2030,0x150657254c3951800008,0x657a5c7ddf25ac9561f0,0x5b6a07e4084dc6483bf8,0x82406befd5dc946bc,0x6b599b80001a4e650b00,0x34154619ff917392d6e2,0x4915af845299a6bdc9bc,0x2340001e27541ee6d33e,0xc30d76c0000c2f1d3c84,0x3c7e259e6516859ef4,0xfc8660223cc47210a340,0x3bfadda63ee2edfd9080,0x6d800015d7bc8a400019,0xde65b1fceabd47b8dcf9],#[0xad68a4fdfeb937dab1ba,0x16f57215de84a5ad9925,0x1b0e52d2b688267468b2,0x5a4ae3253391696816da,0x29be1a56724c59a65490,0x5b1898f44dc4304dd16e,0xe186f3fe477e24aa7799,0x88d0e3dc6f3560aa6b19,0x6f21564425b9a7006ac2,0x984ae712e62497b0e25d,0x28c2a7966e2eba85fc7e,0x78854800c7e124483dbc,0x76149e69fe1861a4ace,0xb020254000391a9d74e8,0x10a4d158ffc4c252e3ad,0x32f4a31e928450ae604d,0xa702a62c3c6ed29614da,0x1b1638d91ca429dd5ab8,0xe1e0b18c6696c8e2b7c,0x8266b24caf6e96080e41,0x668ff8dd4916c6930e2,0xc418938e47dea3fde904,0x1bca60c480c9fb78cb29,0x435df111f8fd2f503202,0x6c44bb1bac48a91a431,0x51c062c6d2e8db814b70,0x7c94e72d6bbd07ccc8e1,0x9e9003c8b20412ca7e0a,0x12c1c8d0b52992045bb4,0x1136926ecd29b7d1d029,0xbdca22381bc0001069b0,0xbf622e8cc8196772d3b1],#[0xb544f285c9722f96bb9c,0xefea064864c86066f046,0xf5e61270f0a5d39e6f46,0x504d38ccc6901f32ef6e,0x6f06c969a77e65f6d67a,0x1c80deeaae10f789d902,0xae41b905c7e947211ddc,0x59e98e1a6920437180ca,0x9c2c1b99bee2642138b8,0x7e90e02ea14143308205,0xc1bde82cbae09006cce8,0x3c41ceba78e5f8921b46,0x847221604c61278e5922,0x48f070edf3cc3d501190,0x9925b3a87b78f536a4d2,0x5f18c3ce6ce5d95dd826,0x5bf53b50b4b1e1f8899c,0xcc100064c0c21dde44c9,0xf704610a30a9dbfc71f9,0x7fa0cd35033047eecda2,0x45961ad8dadcc13409aa,0x1312a9a13a127445850c,0x3f8ec7c196f447a07099,0x67c1290d7294be243781,0xbe39a0055e051599144c,0x90aa7959213c66e6e756,0x3f1036c07b8e5316eb98,0x944d220ba018975dc81,0x77c0351ea491dac948ce,0x718504a2d9d2aea673d5,0xceba0264d450a03c4f4e,0xabc4853641a41f71ea2a],#[0x7a766c64c01d0404643a,0xda804d813d849bcc4d7a,0x6d020dee4df468551d62,0xc522eb6c765442c99c4c,0xff43ebc7d91d620f620,0xa5c9e25c4abef48e86d0,0x17f2326c2625061690c8,0xfa693fec10fd31e1591e,0xd791cda60ffa72fef4cd,0x334cbb62a46a7e625234,0xd4f852c8a85da3725f08,0xdbe9143a139d944a5ac1,0xcd022ee4bf9231891168,0x63f9f9dd317a55f0a121,0x8c51dcd510cda5b280f1,0xd0e548551b8a9d2a10ed,0xf7408eec2100332562e,0xaec0002ac7b08241ed7c,0x6fed822d84eeb0a41310,0x2b857198a8ce3a800014,0x99c85346b068c361d8bd,0x41e13296b940000e9652,0x88adeb8693489e2cbdf9,0xd4c679a4e2be364d5f3e,0xe7e64aa95fee7f183850,0x44e6170819d97aa6d908,0x51ee404e543c7ffc9210,0x4bfa2ab9ea7a67909d8e,0xd37a4a7289c5628aa8d2,0xe84c9434e2c48fc09dfd,0x8afe5020e490e78aadf8,0x8b4d26e8c09dcac698e1],#[0x59940af65a515590bd58,0xf980496dde4ce09c57aa,0x18f6d6b533254cd437f9,0x23eb80c01ad24c00435,0x600a5a0c2b7d4a987104,0xcab04ee9646a0c40aa65,0x99a6c9942004e4343269,0xd7270694e0a6580002c,0xaa9424e4eee477e82174,0x4d8e390ae70635d658d,0x93ecbffddf88f1c2c1c6,0x85653b57c384a028370,0x1a3d4c759a40003c4072,0x8a6a40e4ad817d34af2d,0xbf7c7a9a635c9142f54e,0xe4c2e568c76e8a0581ad,0xcbc8b82ee83457748c22,0xb90c6b5ee8e1883e6236,0xe5e91fd2cffc79c80592,0x525c8316a9d043e919d8,0x70ca4828d77a8cdc376c,0x5ae52224a455b1aa0e4e,0x122a0c18401511fe1c70,0x84518c02eada021995ce,0xcf7da24a7352c05ca549,0x6a6c5e414a1d42524d52,0xfe212d4c0c1a23f10479,0xd6606604100de3ba01cc,0x9404332c2088789a33ad,0x85fed5de64506d940a65,0xbcceb2f9209855de43ae,0x8b66b28dfd00f9808900],#[0x5ef56e0c46cc29b4ad4e,0xc54a3b76cc12f4296805,0xd280002c010c204e5cbd,0xafe2d866004dae3db7a1,0xcc4d96b40d083c051b42,0x5041d2261db060ecccac,0x15ce189c17d0c5e97b08,0x46c1c091ae5c0c9243c2,0x34a681902bb46a01fdfe,0x6a862c52d559dc2d25e4,0x2892b4dcfc46c67c4b30,0xcfd1db561b96bc1ae3d2,0xd1e13906bd45643e1cd1,0x5840000a0508a9846640,0x9c522ac017b86221a630,0x3ee2af6807f650b5795e,0x54b2ab9ebb0873ccb9e8,0x69121ec50a8c36917fe8,0x6bf68e753e4c54f5562c,0xddf1c9c560f6a40c129c,0x5d1678ef17c8f21c12e,0x832c56598686876d312c,0x1190ef6002d4c6000025,0xe1b45a02452c7c02d266,0x2a05a7e1fb1097c0003e,0x9e08bbf1fd8000084e3a,0xb9997ead7900ceda1e7e,0x3041fc314e41ba4c3bbd,0xa28c329a8e9da92a31c9,0x92d42718706ac939e894,0x9ab4fddd395dbe126fa9,0xa80d7d90fac000087a61],#[0xe4813875c825904629f2,0xbbf2e5800008ea0e27d1,0x70681cfc17092a7543b9,0xed207925b40b0705ebd,0x5d4e0ca838046790da58,0xcf6664be09021e22650a,0x475e09ea4274580191a8,0x92e93af9190dd1a896dc,0x4bc69bb413727b61cc4c,0x9e400005e2a1a0800019,0xa2cc4c81d24993268c82,0x3e337696cad6083fde,0xa7d3a732e8f24be80,0x22b9aa7efc4fd52b40,0x96b4ab482ec2d81a6e80,0xbf00002a4230aaf5420e,0x6af971dd42f8bec00016,0xe17690497349ccae7639,0x86921ecc718797d545c,0x66a0d2a9a0fd08800099,0x28eaf45291958a5d556c,0x8a1a6bea57fa03529ab2,0x8fb0e8245bd90551a39c,0x3dc00025703d12404252,0x8c400011f4f11e6c051d,0x9c40002896800021dfca,0x185c33fa04947d321d0c,0xa5e9da48872d836c62aa,0xf2d1c158145df38d5981,0xc2f50ce4a60000008814,0xa224ce2ce7929c87488,0x627a224000000036017e],#[0xe0b6099ea382135cd,0xf0fe20712f3a38be2680,0x3d45af4e357e14367c00,0x3630e2310daff2a1ce,0x27e5f7f89a1a20b52400,0x187868f21784971295e8,0x3e8a80c4009a7885a0,0x5166b1400016575cf380,0x5684b7a193453a946c71,0xb7616d4429640fb8dfb5,0xfe1b4225bc23e3aea4a,0xc2be1090430146699add,0x611bd195a40002eaf32,0x64cc218000088b80000a,0x780003d300000164c4d,0xce60a7a04f196300f205,0x4fb09af2cae43dd5fbac,0x1e93b12ae8cce1d470,0x187cac2cc684be4080,0xd21d53ea857cca800000,0x38cdba25ba12e80cc6,0x44a5532c5390bb88fb40,0xef72f2f9fbe16c314fc6,0xb56035f8fce05da463b9,0x3496da000021ce767381,0xf922bcf42fdd52bd1cc1,0x887d01c95cd540c63d2c,0xb940f30910793440fea9,0x471676f0f8c9bb7076c0,0x52fe5116dec4d6ec56e8,0xa546054965ce6e7aa955,0x9b5cda20e1f8f00cb3c2],#[0xe0b4729505283d3c1d24,0xa69d5e5085fe753605f6,0x72962dfc3e70e47adf52,0xaae451fa8fc922b67552,0x9a80000e8ef57b54180d,0xa662e9c4189a33eda308,0x2e8e581af52636381d52,0x49f671d48d01cb3de2cc,0x3904c45a52719571f356,0xa0459ce6f1d8da91abe6,0x3529e3ddc614d72998ae,0x8e02ac8a7c745fc9e205,0x26ed9940887c56a59f4c,0xd1bde0c04e8cdfe21fbe,0x9d066640001a2d45749a,0xe6f853e91ed9699a7e81,0xa0b0627c01e9f5017e45,0x6cf202ac1ead01b997fc,0x1828f3eecd705e29d6f9,0x2f18fa169a46b39d8726,0xad0c7186465aa0e2ca32,0x812dadd276468c20803d,0x56c1cb642da1a5623b32,0x94f08d506fb94e989e75,0x3f576b21d46d7055f65,0x3acde524b8ada8b52bfe,0x38248776e0e4ba74562a,0xf1d8e656cf9ad450d6a5,0x89b2c096c9c5102684ed,0xb086a39a41ddf6565fb1,0xe561ebc40570b14973f1,0x1c396912cb48091477ac],#[0xdd357980848587cdbcc8,0x13d9548c5c4c517df6d2,0x74c9f6d261aac52e166,0x4848aa0dd51e39587825,0x50e4c87045602c2c948c,0xf1ac15ac037a74000018,0x2ce218f1ec2dc53a0302,0x5e1eacc63dc5c3a2105d,0x5cf0f8061e80003d1a72,0x8552717d6e800000f4b0,0x714e19157a440bfde8d5,0xa7563145b37109811788,0x8c4882a9f471c6edeed6,0x687a1a06e2c0000ec374,0x5700e054cb48d545ddb1,0x118931b84000000001,0x3d5c4e569a0dada4c0,0xbd9a74b28b1e25f266c0,0x90a62700002c6b38ec0e,0xd32575045f400021cb96,0xb6824976c14961541a21,0xeb35de2e47b16fa8bd31,0xed3e9b6c0940002dd2c0,0xdd40003cc06c500088d1,0xf29237f81268de98a408,0xe7beeea6e7f2076c23fe,0x764c29000000003839dd,0xe76904e565513b1681c5,0x39e294d5251ce315a7bd,0x69dc5fbc11526fd25785,0xb9e53d55da916bd9a87d,0xa882dd5d34d09ffd4ba2],#[0xe31581684bc654c0003e,0xf3824c3d80360ebeb501,0xaba47761164639b863ca,0x8c86267041027f712889,0xa7c0000000264024c295,0xc6b0e6112ca2dba000c2,0x22aad03c0e98750d99ce,0x175277dc7bfdeac52fbe,0x7a198b32dcc0000e3a34,0x5c0000229d99e5f17d4d,0x7731038855a4a15578ee,0x33ed759ae372d4c5c230,0x9a043f1ac8d83fadf5a5,0x3c2b3cd370141ae02d,0x8caec6c977ac64aed080,0xc6e40002dcf34,0xfc8a137178bcab9d7100,0xdf2513fd0950ed199871,0x39148457e2cec8]]
def g63D10 := limbs80 #[#[0x1102401062108220087f,0x12028020661182601864,0x310a4210ea1282a02868,0x320a8220e6318a6218e4,0x519264196a328aa228e8,0x5292a429685212842166,0x729aa629e8721a8621ea,0x46048006a92a2a82a6a,0x2274450790d015c23035,0xb08d1091f23a46c0c516,0xd519830c5d0b115027c4,0x22a434828fc1e53a26f4,0xe554a5941a714be9351e,0x6ac8d88b015e2b8568ab,0xee9d3b93700db1acb476,0x4042b83301dfabe179c,0x487122c5080c1420304,0x10010800820025001040,0x950012800840042002,0x20070004a80096800968,0x1420048001400090008,0x30010c00430010800480,0x9580095800930012c004,0x12400e001080049800,0x20000a10024000a0004a,0x870010f0010f0010e00,0x28000a00082007000800,0x4b0009000284009000,0x160002dc00258004b8,0x3801c000a4000b000168,0x28c008]]
def g63H10 := limbs80 #[#[0x23c403041800f0000810,0x1c0000a0401404200000,0x81840620681020078102,0x8100003000008001081,0x118446820204303003c,0x384033a1c08104082,0x1a202801e001834a0438,0x22819620ac0800c0c9ad,0x4486180c0850a000001,0xc983000c484060048138,0x40400203880004202020,0x8062888e00206230010,0x20e042840218405820ce,0x3483c08143890e0011,0xc040050404b830410084,0x380040000010081081,0x410a040d10c903c00500,0x2024a90060001d002,0x520800a80001021e1c15,0xb00010c5249728ee6e6e,0x418c00000022e5d07290,0xab9a1b4374000b9e4c25,0xcaaf84adaf1428f80005,0xcd8900030e60003e5ea7,0x370d6e700000007a6,0x9d48af2600c000b910,0x72240,0x0,0x71f0000ab79d78000,0x12a5000026e0002f280,0xf8d10003eea000000078,0x16ffc4f08b0000624e3c],#[0xf0ebdc00000000000001,0xa35ac0000003a45651c9,0xd8708b1000219100036a,0xad302402113939e5a,0x0,0x2b2700007480003ab500,0x83b59200001896ea0acf,0x4558aa7764c0000002,0xf841ea145029e8a00000,0x79738a85a580008665e0,0x4c05d4ca140005c14e50,0xf0000434ad249ae24260,0x698000ed80000d4,0x94e0000000000,0x68810b20001e6c0000,0x2fcbe0cd70fe647b5900,0x12265cd32c9071f5c,0xa70000438a6d40002c76,0x85665a8c85810002dc1f,0xc4886b33333043670195,0x882000111140138006b0,0xb30001b5a3b1c0000002,0x246da512c868300c664,0x552d33e75e5f3b000000,0x6940002d87cae2784104,0xd222d629000019827232,0x365423d8633b8ade6da8,0xb39fb6e5f90001f4fe42,0x7684d9b2940780002863,0xc44ea6dea975ec2b0a09,0x37f069fb6b24f028c06a,0x400eecfb009220000000],#[0xa34a6ecf4000f1240000,0x347100001f73cd782206,0x450e794000668165fcc8,0xed35460a0925c000194d,0x248f582abfb1d8443b6,0xb40d13b000386e19c000,0x1417e0c4c837ba6dd3,0x344fd26fc0006b659750,0x4680001ea40003a76c6,0x7c90000000,0x9a4400032140008474,0xa67cb37000000000000,0x1f110001605154800,0x72966fe8580000000000,0x6c000284c000d4625da4,0x3553000000068d4cd982,0xd32d540e3d0cb4000000,0x4a00015c0f2728460002,0x24e2f,0x24980000000000000,0x3128b26ac2d6c9adc9,0xec000a56c0000002b420,0xc000000394013f145ab5,0xe8294aeace33b81d0790,0xefca1fdae0000c330002,0x5904d6748122d43855c4,0x65748b0f3d58a,0xb2c000f79f27c5518000,0xf0000074689434bb106e,0xac9f8391688eb8893fe2,0xca170438c40001f4c5c5,0x770000000a1aa67f5d5b],#[0x45aa000059d40004be91,0x2254f0e208558800022e,0x7c7c7d000000022b4c57,0x2a21900000003a0016de,0x64792d18000049c27bc4,0xdd2f1c8000c47fe4fab0,0x2f1b74e5b865d30815a0,0xd9799d800002dfb8686a,0x4654a8d0003c923d1cc9,0x34d80003f5dd842eba,0x70b000000038292b20,0x29db414840b513b9cc00,0x4c1b58000e0222d78af,0x3ab4040000000000b6df,0x9f928abf0002f0c00003,0x23fdddd8c1f40,0x2437f9e00000000000,0x3eb1000000000028f10,0xd1e800000001782ae100,0x8147c0500012d14d7,0x4e000000000000000424,0x8385dacf000000000023,0x3a4de09fb18000c7b26c,0x44f034000274b000114a,0x40000638c00000000001,0xcda9c2ee88f0000e77fd,0x9900000b540000000b3e,0x987b7dc7ef61e84b5368,0x417f5c86d61800000011,0x5158000b3180000002c8,0x1848d500010e5000248d,0x17011cb694dbc86a548b],#[0x18810002db5e0ade0d84,0xa842d36e2a000145c67e,0x350003b3071c2a8c9091,0xfa54cdc0002949e6fbd,0xb4b62f6bbf6e62f39c00,0xcaf54579580000001a3a,0x13827da764e8000011a3,0x31f6c6e0000000214c9c,0xc3ddbcc00000022b4000,0x4db380000e45c0000002,0x107d400072fb75100018,0x5197e29000226a0001cc,0xb4ab49329c00060b160b,0x290000000000316a8,0x20b90000000b9cb20100,0x6f57063419dc0e664b20,0x356017fe469dc00,0x40000000000160200000,0x461000011e1a67000217,0x79221da58c0004c616d0,0xa3a3fd1645bd7900f1e9,0xc01baac71b7d8b3535b,0x63670fa0fe00015e2000,0x68c6780005d62332d98f,0xf0838ee6d550000b0802,0x45986ff7386f1c57f852,0xae44a38c5eabe1a2c55f,0x1bf5b9110d4d977c0004,0x1b158b61d85b43c29817,0x2cc775764ab69a657,0xd750765eac49a14253a4,0x1084b592e4f805e00030],#[0x41ec603b878000119c68,0x87f638f443a9926d16f9,0x2f1c500004a28352ee04,0x9a7e4b5500e0000000e6,0x862905000048848d0c56,0x24fae7bb5ab0001,0xb00015ed396362240180,0xf933802aa5ea5723b485,0xc438eb692fcf208e4686,0x7ce41f6c958e31d1073b,0xc249ba3d57a071000031,0x97305c8047c258000334,0x3308000000382e0000,0xe30489bc78f3b0a35e00,0xcb28000c1d446b9c3569,0x6b40000a880000000000,0x2400036ed19c00039eb9,0xb0b40003f0f0000039e3,0x61dce6b6674a9200e,0xe300000000001da20000,0x1000332a0000340ecdba,0x753ee3b233a9d6000153,0x2b000000024de0002d6c,0x19557cfc000fb7222e7,0x5721344da8662300,0x26ce9ef22fc000000,0xf964b2568b085d99e8,0xc0002e4d97e80006ab40,0x10c0000003c6,0x33c0006cb32610000000,0xbe6088954000c5978ecd,0x39d500035a4e2],#[0xeeb7a98000f65300d000,0x4e79210003,0x6478000323b48c00000,0x30e24a965f6159030000,0xd056b000009e35279d70,0x54000d10713782e8000e,0xc000c3300000000000cd,0x24350003aa9e32,0x29b000000002068,0x356311200000,0x244000000000045f800,0x856d9a222b2719058000,0x38533bd040c0002eefa,0x480f0000000060d6c500,0x24098dfa5c,0xa300021b100000008114,0x7dd0c000906c00000029,0xf0662d417c55ba8b,0x8c700001d9d432855,0x6fa690001823e0db4f40,0x94b09670000000e6,0x1af18a147f010ad44000,0x96399b44a00000009c75,0x2c75e63702e0000d3e25,0x22aa75974a6d7f0001f0,0x2c40f5795a7b35920c,0x70e07907fb1a37371ce0,0x9acd872c000758a5413d,0x68900010bd000060672d,0x322c1b4ab3fbf1,0x719cc000c198e46dabc0,0xc6a8458130c00000034f],#[0xf7a7db60001e7d,0xb38000000000000990,0x142f000000027d052000,0x64500000000000000,0x22ae493432b86430a8,0xcbc76c440540003bec0,0x363c000b0f0000245800,0x51f00000000000,0x220400000008af40000,0xaee00000c866eac6f00,0xf464000ad178ea918,0xbbe1e8000fc2593323e4,0xa873e51c863032ef13da,0xe8c40000002854921f98,0x2e27000000000036a3,0x65a483200019150,0x31f3a4d1e835772a4200,0xaf000020070001dde0a5,0x12000169000000000001,0x113d00017]]
def g63D11 (j : Nat) := if j=0 then 0x3f else 0
def g63H11 := limbs80 #[#[0x9000ece00030108331d,0x3b7590010e889db6180b,0xf4400a4ae324c000b2e6,0x7b31d464fe68d6a16b,0x25520cc4d6203d8f4107,0xe2e43887b4003020e800,0xfedf0dbbe5e159fda8ca,0x1480038f0018957697,0x1e05cbdcefdc9d419c00,0xa7bb60114c36800003e9]]
def g63L : Nat → Packing
  | 5 => (41,6,6,1441825,86,9,1024,g63D5)
  | 6 => (432,5,6,4981038,121,13,1158,g63D6)
  | 7 => (2025,4,6,5571529,122,17,1260,g63D7)
  | 8 => (3039,3,6,1966814,90,18,1167,g63D8)
  | 9 => (867,2,6,786491,70,16,1099,g63D9)
  | 10 => (60,1,6,65537,0,11,1036,g63D10)
  | 11 => (1,0,6,65537,0,0,1024,g63D11)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 10 61 5 10 6 0 g63H6
  | 7 => lookupWord 108 467 8 13 9 0 g63H7
  | 8 => lookupWord 506 2503 9 15 11 0 g63H8
  | 9 => lookupWord 759 3299 10 16 12 0 g63H9
  | 10 => lookupWord 216 1283 7 14 10 0 g63H10
  | 11 => lookupWord 15 71 6 10 6 0 g63H11
  | _ => fun _ => none
def g63 : Forest := ⟨63,11,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 41=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 41=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_8 : block g63 6 8 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_104 : block g63 6 104 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_200 : block g63 6 200 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_296 : block g63 6 296 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_392 : block g63 6 392 40=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 432=true := (@block_merge g63 6 0 200 232 (@block_merge g63 6 0 8 192 g63P6_0 (@block_merge g63 6 8 96 96 g63P6_8 g63P6_104)) (@block_merge g63 6 200 96 136 g63P6_200 (@block_merge g63 6 296 96 40 g63P6_296 g63P6_392)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_96 : block g63 7 96 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_109 : block g63 7 109 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_205 : block g63 7 205 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_301 : block g63 7 301 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_397 : block g63 7 397 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_493 : block g63 7 493 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_589 : block g63 7 589 93=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_682 : block g63 7 682 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_778 : block g63 7 778 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_874 : block g63 7 874 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_970 : block g63 7 970 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1066 : block g63 7 1066 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1162 : block g63 7 1162 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1258 : block g63 7 1258 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1354 : block g63 7 1354 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1450 : block g63 7 1450 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1546 : block g63 7 1546 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1642 : block g63 7 1642 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1738 : block g63 7 1738 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1834 : block g63 7 1834 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1930 : block g63 7 1930 95=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 2025=true := (@block_merge g63 7 0 970 1055 (@block_merge g63 7 0 397 573 (@block_merge g63 7 0 109 288 (@block_merge g63 7 0 96 13 g63P7_0 g63P7_96) (@block_merge g63 7 109 96 192 g63P7_109 (@block_merge g63 7 205 96 96 g63P7_205 g63P7_301))) (@block_merge g63 7 397 285 288 (@block_merge g63 7 397 96 189 g63P7_397 (@block_merge g63 7 493 96 93 g63P7_493 g63P7_589)) (@block_merge g63 7 682 96 192 g63P7_682 (@block_merge g63 7 778 96 96 g63P7_778 g63P7_874)))) (@block_merge g63 7 970 480 575 (@block_merge g63 7 970 192 288 (@block_merge g63 7 970 96 96 g63P7_970 g63P7_1066) (@block_merge g63 7 1162 96 192 g63P7_1162 (@block_merge g63 7 1258 96 96 g63P7_1258 g63P7_1354))) (@block_merge g63 7 1450 288 287 (@block_merge g63 7 1450 96 192 g63P7_1450 (@block_merge g63 7 1546 96 96 g63P7_1546 g63P7_1642)) (@block_merge g63 7 1738 96 191 g63P7_1738 (@block_merge g63 7 1834 96 95 g63P7_1834 g63P7_1930)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_8 : block g63 8 8 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_104 : block g63 8 104 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_200 : block g63 8 200 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_296 : block g63 8 296 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_392 : block g63 8 392 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_488 : block g63 8 488 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_584 : block g63 8 584 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_680 : block g63 8 680 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_776 : block g63 8 776 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_872 : block g63 8 872 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_968 : block g63 8 968 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1064 : block g63 8 1064 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1160 : block g63 8 1160 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1256 : block g63 8 1256 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1352 : block g63 8 1352 56=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1408 : block g63 8 1408 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1504 : block g63 8 1504 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1600 : block g63 8 1600 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1696 : block g63 8 1696 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1792 : block g63 8 1792 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1888 : block g63 8 1888 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_1984 : block g63 8 1984 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2080 : block g63 8 2080 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2176 : block g63 8 2176 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2272 : block g63 8 2272 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2368 : block g63 8 2368 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2464 : block g63 8 2464 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2560 : block g63 8 2560 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2656 : block g63 8 2656 42=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2698 : block g63 8 2698 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2794 : block g63 8 2794 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2890 : block g63 8 2890 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_2986 : block g63 8 2986 53=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 3039=true := (@block_merge g63 8 0 1504 1535 (@block_merge g63 8 0 680 824 (@block_merge g63 8 0 296 384 (@block_merge g63 8 0 104 192 (@block_merge g63 8 0 8 96 g63P8_0 g63P8_8) (@block_merge g63 8 104 96 96 g63P8_104 g63P8_200)) (@block_merge g63 8 296 192 192 (@block_merge g63 8 296 96 96 g63P8_296 g63P8_392) (@block_merge g63 8 488 96 96 g63P8_488 g63P8_584))) (@block_merge g63 8 680 384 440 (@block_merge g63 8 680 192 192 (@block_merge g63 8 680 96 96 g63P8_680 g63P8_776) (@block_merge g63 8 872 96 96 g63P8_872 g63P8_968)) (@block_merge g63 8 1064 192 248 (@block_merge g63 8 1064 96 96 g63P8_1064 g63P8_1160) (@block_merge g63 8 1256 96 152 g63P8_1256 (@block_merge g63 8 1352 56 96 g63P8_1352 g63P8_1408))))) (@block_merge g63 8 1504 768 767 (@block_merge g63 8 1504 384 384 (@block_merge g63 8 1504 192 192 (@block_merge g63 8 1504 96 96 g63P8_1504 g63P8_1600) (@block_merge g63 8 1696 96 96 g63P8_1696 g63P8_1792)) (@block_merge g63 8 1888 192 192 (@block_merge g63 8 1888 96 96 g63P8_1888 g63P8_1984) (@block_merge g63 8 2080 96 96 g63P8_2080 g63P8_2176))) (@block_merge g63 8 2272 384 383 (@block_merge g63 8 2272 192 192 (@block_merge g63 8 2272 96 96 g63P8_2272 g63P8_2368) (@block_merge g63 8 2464 96 96 g63P8_2464 g63P8_2560)) (@block_merge g63 8 2656 138 245 (@block_merge g63 8 2656 42 96 g63P8_2656 g63P8_2698) (@block_merge g63 8 2794 96 149 g63P8_2794 (@block_merge g63 8 2890 96 53 g63P8_2890 g63P8_2986))))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_0 : block g63 9 0 38=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_38 : block g63 9 38 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_134 : block g63 9 134 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_230 : block g63 9 230 41=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_271 : block g63 9 271 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_367 : block g63 9 367 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_463 : block g63 9 463 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_559 : block g63 9 559 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_655 : block g63 9 655 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_751 : block g63 9 751 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_847 : block g63 9 847 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B9 : block g63 9 0 867=true := (@block_merge g63 9 0 367 500 (@block_merge g63 9 0 134 233 (@block_merge g63 9 0 38 96 g63P9_0 g63P9_38) (@block_merge g63 9 134 96 137 g63P9_134 (@block_merge g63 9 230 41 96 g63P9_230 g63P9_271))) (@block_merge g63 9 367 288 212 (@block_merge g63 9 367 96 192 g63P9_367 (@block_merge g63 9 463 96 96 g63P9_463 g63P9_559)) (@block_merge g63 9 655 96 116 g63P9_655 (@block_merge g63 9 751 96 20 g63P9_751 g63P9_847))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P10_0 : block g63 10 0 60=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B10 : block g63 10 0 60=true := g63P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P11_0 : block g63 11 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B11 : block g63 11 0 1=true := g63P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact g63B5
  · exact g63B6
  · exact g63B7
  · exact g63B8
  · exact g63B9
  · exact g63B10
  · exact g63B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K2110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullLower : Impossible true graph 11 instanceInputs.toFinset := by
  rw [show graph = targetOf g63 by decide +kernel]
  exact root_index (g:=g63) (top:=11) (i:=0) (before_sound K2110 V2110) g63G g63T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_41932

open PEqualNP.Outside.L_meta_41932 in
theorem PEqualNP.Outside.L_meta_41932 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678368 * 2 ^ 32 + 4209567936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678368 * 2 ^ 32 + 4209567936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
