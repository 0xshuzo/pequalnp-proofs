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



def g63Y : Array (Bits × Bits) := #[((bitLimbs [0x5d373b73aed7feb55,0x7ff7eefbe4fc068ff368]),(bitLimbs [0x110502091ca02c144,0x9b2ae3064d0048f7360])),((bitLimbs [0xff7ccfc6f7daf217ba,0xca82829c5d86d176cb97]),(bitLimbs [0xa45046c4a083f2109c,0x40028a880d04c126c296])),((bitLimbs [0xff6ff8f88974577f67,0x2fbc1762632b7df52c3b]),(bitLimbs [0x5b2b80380924040e22,0x16200062402b3c500c29])),((bitLimbs [0x10fea72f742f8b9c99,0xbb4bfd9fbf53bf0854cc]),(bitLimbs [0x10cfa3435021890001,0xbb48259fbb123b001088])),((bitLimbs [0x35b63b5902913cc07b,0xc5adf1c09addabaaaf31]),(bitLimbs [0x64a42d410a1190c03b,0xc49d51c09acd83a8ad11])),((bitLimbs [0x6805c52fdc52fe6aed,0xf676ff25186fa2317bce]),(bitLimbs [0xc28d050e8cf27eaa47,0x321cdb05106fa2316b4e])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,1,2110,0,8),(0,16,2095,0,8),(0,32,2079,0,8),(2,0,61,0,8),(4,0,59,0,8),(16,0,47,0,8),(32,0,31,0,8),(0,8,2103,0,7),(0,48,4111,0,7),(8,0,55,0,7),(32,1,2078,0,7),(34,0,29,0,7),(0,4,2107,0,6),(1,0,62,0,6),(0,2,2109,0,5),(1,16,46,0,5),(1,32,30,0,5),(2,1,60,0,5),(2,4,57,0,5),(2,8,53,0,5),(2,32,2077,0,5),(4,1,58,0,5),(4,8,51,0,5),(4,16,2091,0,5),(4,32,2075,0,5),(8,1,2102,0,5),(8,32,2071,0,5),(16,1,2094,0,5),(16,8,39,0,5),(18,0,45,0,5),(20,0,43,0,5),(32,4,4123,0,5),(32,8,4119,0,5),(32,16,2063,0,5),(36,0,27,0,5),(40,0,23,0,5),(48,0,15,0,5),(1,8,54,0,4),(1,48,14,0,4),(2,16,13,0,4),(2,48,13,0,4),(4,2,2105,0,4),(4,48,11,0,4),(8,16,7,0,4),(8,48,7,0,4),(18,1,44,0,4),(20,8,35,0,4),(34,1,28,0,4),(34,4,25,0,4),(34,8,21,0,4),(34,16,13,0,4),(36,1,26,0,4),(40,1,22,0,4),(40,16,7,0,4),(48,1,14,0,4),(48,8,7,0,4)]
def g63A : List (List Nat) := [[]]
def g63D5 := limbs80 #[#[0x1c1610cb985cc7358420,0x487916087050d10e6170,0xcc27c1e92d241435c443,0x41007a54a9bba43196d1,0xc]]
def g63D6 := limbs80 #[#[0xa0d710801020d7108010,0x589710c010209710c010,0xa09710c010609710c010,0x211760c810e09710c010,0xe11760c810a11760c810,0xc971100105d43210010,0xe1d628c810211628c810,0x20d614c4200c97190010,0x20d6154420d0d6150420,0x5d074584205cc7358420,0x58521100302117358420,0x5c521100305892110030,0x5cd21100305c92110030,0xe1921100305d52110030,0xe056210030e096110030,0x58870484305847048430,0x60c70484305d87048430,0xdd870484309d07048430,0x5d074484309d07348430,0xe053248430e093148430,0x2015448430e153248430,0x4c96148430e0d5448430,0xd0d61484305896148430,0xe096148430dcd6148430,0x591624843050d6248430,0xe056248430d0d6248430,0xe1173484302117348430,0x2117648430e157348430,0xe157648430e117648430,0xdda614843098a6148430,0x1ce7048430dda6248430,0x60b41484306167448430],#[0x60742484306174148430,0x1cf70484306174348430,0x5cf70484305877048430,0x5db70484305d37048430,0xddb7048430dcf7048430,0x5db73484305937348430,0xdd9214c030ddb7348430,0xe0b764c030e07764c030,0x5d074584305c87258430,0xd0f72584302117258430,0xd0f71588305c47158830,0x61d62884305896188430,0x5c961904302096190430,0x5c96194430e1d6190430,0x60662984305ca6298430,0x5c07058432203764c832,0x20154584325d07458432,0x60b31484409cd6348440,0x2037650c436043250440,0x201710c9102014358443,0x201434851018c7048510,0x604744c910219324c510,0x610764c910210764c910,0x4c87050510a10764c910,0xa087050d106087050d10,0x219738c9106044388110,0x21932cc51021973c8510,0x4ca70d05105d532d0510,0x50f614852018c7048520,0x2014310d2121943d0520,0xd917110d2150d7110d21,0x5cc73181215cc6318121],#[0x9cd43181212013118121,0x20d60181211cd6018121,0x5cd601812150d6018121,0x90d60181215d16018121,0xdcd60181219cd6018121,0xe1d6018121dd16018121,0x2016318d2160c6418d21,0xe1d6318d215d16318d21,0x9d97018d2158d7018d21,0x20d641912158e7018d21,0xa037350921e1d6419121,0xa047050d216047050d21,0x19243981212017395121,0xa036398d216036398d21,0x20173d052120143d0521,0xa1863d812120173d0921,0xe0d64d812121943d8121,0xa0363d81219cf63d8121,0x60670d8d21a0364d8121,0x19571181325c46118132,0x18d32485405cc7348540,0x1d8714c94018c714c940,0x61c3218141211710c941,0x9ca7118143604704c941,0xe1d6218a10e1d320ca10,0x2014348610e1d6318e10,0xe1d310c62059064cca10,0xd0d614862050d6148620,0x604435862050c4358620,0x20d5448630a0f7058a21,0xdda70486301ce7048630,0x1d273486405cc7348640],#[0x1d3714ca4010f714ca40,0x21532586401d53258640,0x10d718ca40e053258640,0xa11710cb10211710cb10,0x6047050f20e19710cb10,0x20143587206187050f20,0xd1de37c3f87d0ee1bc2f,0xbe96d1f97d2de57c9f8f,0xaf55daaf4fa9ed3ba6f4,0xd9db375f2bb56eadb59e,0x7c5f87edcdb6b6b6bad6,0xdb99f2ee5bc7d8f71de3,0xadb56e9dd37a5f3ce76c,0x399f27e3dc778debcd73,0x2f5ce79ceb9cf36e6bcd,0x8073026079812f71ec7d,0xf803985105cc283a1cc7,0x60a01cc3003e617c692c,0x4b37a261421130a0e898,0x1645b130ecd688867624,0x61ac43c1e97b36e32b81,0xad0b732c86b1222ca00f,0x2962e483e1764715eae4,0xb2802d60a956d052eb58,0xde080de90406d965016c,0x5b2ca08d965025ac1013,0x1c45960b6cb283365941,0x50746c20392a401c8b2c,0xca860c654251f0810319,0xc60da1a4ece4d5950d36,0x5772ad48b95740f4bb4b,0xcf019567244b3baee55d],#[0x56c46c23629dd5adfd2c,0xc2370ce55b48f22da8b8,0x2e55cc632adc8b856e47,0x1472b60dc657135c8b82,0x649693b113cc5a25e5ac,0x5c828cae3ab613192725,0x4c083ba5c3e0b281ed99,0xfe6049c308247694113b,0x49330f0f1837847ba8a0,0x6e4497b647cbbd1125de,0x8b862a1dca6e5ad4e32b,0xc364a765f2da32396279,0x7e613539309a4b91ca4e,0x493229e49924e4fc1272,0x2ed9751576b98abd5c85,0x51672b98b26e185deac4,0x4c0ca4618652f0c30d57,0x4e5c6d170c3489861a0c,0x522e63a89751c48b98e0,0x3c93762176398f225d47,0x8227dbb0fbf1d079feec,0xcc1ea76188cc128401d9,0x8e5114cd2e86ff74440c,0x3f308a4b96452bcaa29,0x90f1964858c324126592,0x54731ca2399e4d18cb2c,0xbb1fa5dd8993b0c92579,0xce54ad2eec5e8b76404b,0x9deea5cef742e38ca969,0x4e9a873b434b9d33a1ce,0x6334dbb20a2dd8a136ec,0xca991025cc0812e629b7],#[0x2dd90912ec8496873c36,0x51eec681998243348122,0x965b944b45bb1b23dd8d,0x62948c32524619309f2a,0x4812a4dd8a83d2e529f7,0x3dd8dd16ec7c17982530,0x4272cae8b763947bb1c2,0xb24498597bc12cbd2096,0x25b22c92d33609608d30,0xbaa910e5941ef04b6f48,0x5e6171372eba31955347,0x433317831955523cb2a2,0xc4bd65630d4bdd84662f,0x7a963cb3209e5991210e,0xc8d506e62a0c921503e9,0x6e62f8c9217c4591ab3e,0xc453184c085c40acc5f8,0x8a5d91c02ec8e08ca5f0,0x7874fc3c23220e102b31,0x41c2a7e1e08f329049f8,0x7e1e2059310a9f878564,0xd92e9069f87896441c4a,0xcc9978364ca41b2dd20,0x38b4e49c5a7e1e293f0f,0xca45a7e4e2d3d27169d9,0x421a0590c7009f948b4e,0x732f32a9847f1fcc3f2,0x449d97a317484f8ba428,0x69c4ecbd20ba42847b31,0x4b4f04a5a54252d3a269,0x9a59ecbd20fa5c967c09,0x45131203f97904048480],#[0x243f979240484912a424,0x48d64ba46a765e345131,0xcbc6b265e3597291ac99,0x42423c55211e93878e65,0xd27211e92908f48c847a,0x1828908c49ca47a46523,0x69848c3cda461e68572f,0x484a23242504d2126129,0x4dcee91d27288c939447,0x948eb5c5e90ac464a56a,0xc24b985f6ec2afa61dab,0x5a620c8af0e24180252e,0xc0b2b16459865314edb9,0x560abc8b235e39916547,0x481c01801180c0068002,0x84f04604203803082b02,0x8908007887486805c856,0xb0b70b28a70a00980908,0x8d38cf8cb8c78c38bf8b,0xef8eb8e78e38df8db8d7,0xb9079038ff8fb8f78f38,0x92391f91b91791390f90,0x3f93b93793392f92b927,0xb95795394f94b9479439,0x97396f96b96796395f95,0x8f98b98798397f97b977,0xb9a79a399f99b9979939,0x9c39bf9bb9b79b39af9a,0xdf9db9d79d39cf9cb9c7,0xb9f79f39ef9eb9e79e39,0xa13a0fa0ba07a039ff9f,0x2fa2ba27a23a1fa1ba17],#[0xba47a43a3fa3ba37a33a,0xa63a5fa5ba57a53a4fa4,0x7fa7ba77a73a6fa6ba67,0xba97a93a8fa8ba87a83a,0xab3aafaabaa7aa3a9fa9,0xcfacbac7ac3abfabbab7,0xbae7ae3adfadbad7ad3a,0xb03affafbaf7af3aefae,0x1fb1bb17b13b0fb0bb07,0xbb37b33b2fb2bb27b23b,0xb53b4fb4bb47b43b3fb3,0x6fb6bb67b63b5fb5bb57,0xbb87b83b7fb7bb77b73b,0xba3b9fb9bb97b93b8fb8,0xbfbbbbb7bb3bafbabba7,0xbbd7bd3bcfbcbbc7bc3b,0xbf3befbebbe7be3bdfbd,0xfc0bc07c03bffbfbbf7,0xbc27c23c1fc1bc17c13c,0xc43c3fc3bc37c33c2fc2,0x5fc5bc57c53c4fc4bc47,0xbc77c73c6fc6bc67c63c,0xc93c8fc8bc87c83c7fc7,0xafcabca7ca3c9fc9bc97,0xbcc7cc3cbfcbbcb7cb3c,0xce3cdfcdbcd7cd3ccfcc,0xffcfbcf7cf3cefcebce7,0xee0809406d0bd07d03c,0x5c024c4805004804120,0x808641c44195124a3829,0x36c1c4110004007e8a09,0x3341812115c00130190],#[0x6c072c2074200da0d216,0x823c0c7a4200037431e0,0x23c4400009f44037a89a,0x8ed813c22bc45708b366,0x40002011d]]
def g63H6 := limbs80 #[#[0xb2c00f94224041218703,0x74d9a91549003d7,0x11df5207f0d82e99dc,0x601c1035c4b548e00081,0x96000e780000351a8cc0,0xa65271900054a1f,0x5800d40a000000c3f0a,0xb0e8853321,0x18800]]
def g63D7 := limbs80 #[#[0xc0105c4200416208010,0x41750c8105c43004162,0xc840042650c8105d832,0x100105c4400416210010,0x417510810cc84004175,0xdd532042654c81099442,0x5881010d620407350810,0x4074588101cd6204070,0xd0d62042435881050d62,0x88010dd1620437358810,0x41628c81058a3004273,0x58a4204171900100ca40,0xd0c105d7430413298010,0x81710c0205843008265,0x1c13108161100205d831,0x504201cd41081614c420,0x816154420dc54308161,0x1c16108043584201cd54,0x584201d1610807358420,0x81545842054d6108143,0x5d56108174584205cd61,0x58420951610825358420,0x8274584209cd6108270,0xdd1610837358420d0d61,0x8c420586300837558420,0x81639002010e4008161,0xcc64008273900205c640,0xd0420586510816190420,0x8743580211c14308561,0x5ce6008474980211c163,0x98c21d0e600857498021,0x867498c215d26308570],#[0x9974308663d0c215d743,0x84305cc210c16408430,0xc16110030484400c176,0x588410c1711003058840,0x484305d8420c17610430,0xc074484301cd210c070,0x4c9210c131484301d921,0x48430509210c14148430,0xc15348430549210c143,0x589210c1614843055121,0x48430595210c16448430,0xc175484305d1210c173,0x985210c254484305d921,0x48430991210c26248430,0xc341484309d1210c270,0xdc1210c34348430d0921,0x48430dd1210c37348430,0xc1214c030dd9210c375,0x585410c3764c830dd930,0x58430dc9540c37155030,0xc072584301c1610c042,0x509610c132584301d161,0x58430549610c14358430,0xc16458430589610c154,0x909610c232584305c961,0x58430989610c25258430,0xc342584309d1610c272,0xdd1610c37258430d0d61,0x588301c5620c37558430,0xc1645883050d620c074,0xd0d620c271588305c562,0x59030dc5640c37158830],#[0xc1618843050a210c372,0x5ca210c1648843058a21,0x8c030486300c17688430,0xc1768c43058a300c161,0x486400c042900305da32,0x9003058a400c16190030,0xc34190030c86400c171,0x5c6420c1629083058641,0x98430486600c16194430,0xc1719883098a610c172,0x58b210c161c843055321,0xd0430597210c164c8430,0xc164d043058b410c161,0x58b420c176d04305cb41,0xd08305c7420c164d0830,0xc7764c4315db430c176,0x1c1420c6644c8311c132,0x58831d0d620c54358831,0xcb764c8329c2320c774,0x1c1610cb71550321c154,0x5843250d610c87458432,0xc974584325c1610c954,0x9d1610ca70584325d561,0x58432dc1610cb4358432,0x10265d0c32dd5610cb74,0x9c021101730844059421,0xc4405c8311027308440,0x101710c8405943210242,0x1cd21100704844099432,0x48440585211014148440,0x102634844090d2110163,0xcc52110273484409c121],#[0x4c440dd9211037448440,0x101654c8401c13210141,0xc941103714c84099532,0x5044058d411013250440,0x1003258440cc94110232,0x5cd6110172584404c961,0x884409c9611023258440,0x101658c4405ca2110161,0x4cb3110171908405c632,0xcc4405cb3110141cc440,0x10163cc840ccb3110242,0x4ca60104704c8415db32,0x50c431c1631097358442,0x10d4358443dd94310c70,0x1c16210e72584435c961,0xc910194324404358851,0x44063109105d43244171,0x5d442441731091019442,0x4851018d214417110d10,0x44131485101cd2144070,0x5cd21441434851050521,0x48510d89214424348510,0x440704c510dcd2144363,0x50931441414c5104c931,0x4c910dc931443324c510,0x440764c9101d13244065,0xdd532443744c910dc532,0x50d104c9414407050510,0x44043881101d94344070,0x5c6324434388110d0620,0xc851050f21441738c910,0x44132cc510d8b2144173],#[0x4cb4144171cc9105cb31,0xd05105cb4144143d0510,0x44270d05105d74144173,0x18f4244362d0510ccb41,0xd0d101974344173d0910,0x48343d891010f6244175,0x9d031481740c52019031,0x1052018c41483640c520,0x480704852018d2148173,0xdcd21483614852050d21,0x4c92019132480764c520,0x48063885201d94348070,0x5ce31480648c5205ce21,0xd052018f41482708c520,0x48173d09205cf4148143,0x50c4348543d85201cf61,0x10d219c0434857110d21,0x4844318121d904348676,0x1cc60484641812118c60,0x1812150c604853118121,0x48560181215506048553,0x90c60485731812158c60,0x18121950604865318121,0x48673181219906048663,0xd04604873218121cc460,0x18121d0c604874218121,0x4846418d21d906048763,0x5c0634856318d2155063,0x18d219c0634866418d21,0x4856419121d906348763,0x50531484704c5215cc64,0x505211c132487704c521],#[0x4877350521d0d4148463,0x18d4348773509211cd42,0x50d211d9434847050d21,0x4847654d211c15348663,0x1d95448473551211c154,0x581211cd604877355121,0x487635812190d6048543,0x1c1634877358121d9160,0x59121dc1634876458d21,0x4847359521dcd6448473,0x9c2434846490d21dcd65,0x94d21d0e434867690d21,0x48573951219da5348670,0x18e6048443981219da54,0x9812150e604846498121,0x48743981219ce6048643,0x9c2634846498d21d8260,0xcc5215ce644876398d21,0x48763cc5219c33148463,0x5cf4148543d052118f41,0xd0921d934148670d0521,0x48463d0d219c34248573,0x18f6048676d0d2198f43,0xd812150f6048531d8121,0x48643d81215936048563,0xd936048763d8121cc760,0xd8d219c36348554d8d21,0x48670d91215cf6448764,0x5d0214c064085309cf64,0x85309cc214c27008530,0x4c0640c530d90214c274,0xd90314c2740c5305c831],#[0xc930194324c0640c930,0x4c17510930194424c171,0x5d1214c076485301cd21,0x50930dd1214c27348530,0x4c175d05305ca214c076,0x90b614c072d85300cb61,0x18131188604c44218131,0x4c57218131548604c464,0xd88604c732181319c860,0x549311c1414c67018931,0x4c8611813210c604c870,0x5d0604c9711813219060,0x191329d0614cb6118132,0x4c876551329c0644c971,0x5c7604ca70951329da43,0xd853210f614cb61d8132,0x4ca54d85321d3614c864,0x18c2150374d8532dc361,0xc5409c0215017308540,0x50063485405c43250172,0x4c52150076485401cd21,0x485405cd215013248540,0x5033248540cc52150273,0xdcd215036348540d8521,0x4c5404c931500764c540,0x500714c94018d3250332,0x18e21503714c9401d932,0x885405ca215013288540,0x501728c540cca2150173,0x18f21501738c9405ce31,0xc8540cc72150173c8540,0x50172cc5404cb3150361],#[0x1cf6150072d85400cb61,0xd85408cb6150132d8540,0x50432181415c43250772,0x5cc6050572181414c860,0x181419c8605063218141,0x508754c9411c13250732,0x9c3635097118d425c460,0x181435c86050d7118143,0x50c70d85439c86050e71,0x5c43254270d89431cb61,0x485501cd215406348550,0x54363485505cd2154076,0x1d931540724c550dcd21,0x4c550cc931541324c550,0x540764c950dc93154362,0x5cf21541738c9505c632,0xd85505cb3154132cc550,0x54073d85501cb6154032,0xccb6154232d85504cb61,0x18d525cc605497118152,0x54d72181535c46054d71,0x5c86055171181549c860,0x82105c4635527218154,0x841210c21098c2084171,0x50c32841320ca105c430,0x10210d0c32841630ca10,0x84332102105c44084032,0x588628414310e1018c42,0x18e1058c638426318a10,0x84063482105906484172,0xd8d2084143482104c520,0x486101c1218406348610],#[0x842434861058d2184143,0x1c1318437048610d8d21,0x4c61058931841424c610,0x840434ca10cc93184263,0x1d532840744ca101c532,0x4ca1090d32841644ca10,0x843754ca10dd13284371,0x1d9438407650a101c141,0x58a10551628414358a10,0x841318821010e2084363,0x5c640840438ca10d0620,0xcc61050f218436398e10,0x84143cca101933284362,0x5d33284164cca1058f32,0xcca109d33284264cca10,0x84143d06104cb4184343,0xd8b4184332d06109c341,0xc2209c36284043d8a10,0x882210c2205c43088121,0x48440881430c6204c431,0x102205c4408816110220,0x883311022098c4088173,0x5c4438814310e2098c41,0x186209c0438817610e20,0x8816318e2098c6188161,0x1c121880434862059064,0x48620585218814348620,0x880724c620d0d2188163,0xdd531883314c62050531,0x58620dcd548807355220,0x881545862050d6188043,0xd0d61882545862090d61],#[0x592201cd648836458e20,0x881618862050e2188373,0x5c640881639022098e21,0xcc6205c6638817395220,0x88174cc6205933188143,0xd0f3188341cc62095331,0x4ca215db4388161d0620,0x8847350a211c14288470,0x50d628844358a211c143,0x58a21dc1628874358a21,0x8c161102304ca6088774,0x505218c073486301c121,0x486305d1218c15448630,0x8c374486309c1218c175,0x586408c04258630dd521,0x98230086608c17190230,0x8c2219823010a608c041,0x994328c561d063048730,0x58632994428c57510a31,0x8c974586325c1618c843,0x10e608ca745863295161,0x10a405c4329017198232,0x900734864010d2190273,0x4c92190131486401d121,0x4864058d219016148640,0x902734864098d2190173,0xdcd219033248640cc521,0x4ca4010d32900424c640,0x903714ca401d13290071,0x8c96190132586400c961,0x8ca40cca219013288640,0x90161c86405c63290043],#[0x5cb3190132cc640cc721,0xd06400cb4190341cc640,0x90632d064058f4190132,0xd0d6190c7058e425c432,0x58e52cc9319407058a43,0x9507058a541c16294c70,0x99032c41710cb101c163,0x58b1099132c40704cb10,0xc81720c720d0d62c4043,0x1c143c80704c7209d031,0xd0f205d741c814358720,0xc84704c72199743c8175,0x1c154c847054f211c143,0x487301c121cc07355321,0xcc142487304c921cc131,0x5d121cc1734873050d21,0x58730dd921cc37448730,0xcc2325873050d61cc132,0x50d62cc2725873090961,0x88730dc562cc34358b30,0xcc562d073050f41cc172,0xdc132cc4744cb311c132,0x553311c152cc47050731,0xcc55458b311d162cc772,0xdc964cc77458b31dc162,0xd0731d0660cc44298331,0xcca70d073158b41cc532,0xdc554cc870553321c143,0x593321c164cc95458732,0xd01710cb405c831d0371,0x9cd21d0163487401cd21,0x587400c961d033148740],#[0xd05650cb415ca21d0132,0x59532d06650cb415c432,0x50b41dc532d06654cb41,0xd05718cb411c143d0773,0x8ca60d0532983410ca60,0x58b511c162d0c7058f42,0x8fe3e8f63b8de2f87c43,0xa7a979fe7e9f67b9de6f,0xaf6bbadeb6abeaea9e9f,0xbbeeebb6e7b7edeafebe,0xc5f0fbfafdbf2fbbdef5,0xcbf2ecb727c7f1ec771b,0xd7757cff3ecf73bceb37,0xdf77cdef77ddb6fdb75f,0xed7afeb7abe9f9fe5f7e,0xfbbe7efbbdef3bbee7b7,0x59401ff3fafe7f6fd7f3,0xc380c038602942ca01a8,0x8603c050e0700e180400,0xe1100e180c00c381a01,0x1d2900432b6038608403,0x328e0287508010c95806,0x54c0010c978061d2d014,0xcb10061d615232a94a06,0xea305c3d420f87a7c010,0x6d09575d9d62c9b301e1,0x59542ea2125dd7695b32,0xb3812196602c3ad00587,0x724abaaecb4645e00d0c,0xd81387ba92eeab8ad191,0xb53acbb601e1eed05c3d,0x9a99976f01c36e29565d],#[0x85a323f00386dc8030fb,0x2ac647e54ecafc2dd91f,0x92aeafb26d95f957b23f,0x1219f702c3bf605877d,0x2c3bf806867e92ecafd,0x868312ecaff0161dff,0x30f018061e014abac00,0x6594ee52b29de0086810,0x1c3a2803873b532ca782,0x1873d4070e79ab1cd090,0x50e828021d0460b12060,0x614511cc2898ae73d6c0,0xc289e478413c8908278e,0x8715d32ea2b0e6144e1d,0x829102105201c30aa01,0xd8c1ac28a8378514887,0x3b3c4c806782f0ec6132,0x7cbd2eea6b01e1da405c,0xfd600e1b3000c3e62018,0xfb00043f5e0187eb8070,0x9d89f85371390a6e00a1,0xc330c0d25d962100c3,0x102a5d40864b1012c962,0x1063c3838a985014b702,0x2e1887054350e0886618,0x347b0a0a0f614131ec28,0x717a194c44c0a9865855,0x48c31a68cc634c8cb0aa,0xe2c804dd7ee698962193,0xd56ca9d862193755b2a6,0x62195255b2aa41a864e,0x284327b03654f511009f],#[0x36555156caa0c0d9540,0x310caaaad955528432a9,0x2219583a402b0a975578,0x3b12542c804a8310cad1,0x4804a956ca952fd8d2a6,0x70aa22a1d94755b2a8af,0xd955055b2a9ebc6353d5,0xc3a58ab65558310ca82a,0x805817ae6af862192e0c,0xab216605630c432c02c,0x1ea61643d4a1987a4c7b,0x3d48cf76a911303520b2,0x6b0c5f0f620ba1ea7174,0x7543398ea964b152a5d8,0xeb15e39d5a1887aad7ee,0xd2c7480b50a50f590621,0xae9b0eb5d36dd6b513c3,0x4eaaddabc543b56edb75,0xc20cc3d401981af8330f,0xb0ce73b64310f6006a1e,0xfc3f0f4f1d2029e0cc3d,0x432e1b660dc3d421981a,0x31ec2ed65981da99b0db,0xcbd630918ae411b25c42,0xd52ea13315c82664b884,0x33584270cc308c498610,0x65c388518830a18ee414,0x19860a621081544d0c2a,0x330e17166042e54ba894,0x621c322e400641a870b8,0xec287a59810f4370e190,0x9840c17ae61816604381],#[0x7021a972003525420604,0xe143525c206a48840d4b,0xba06259810e57ee61d8f,0x630ac7b0a1e2edd03c5c,0xcb63318d6c0cc305abe,0x196f5db22debf735ad9d,0x32eabb645d4330eba06a,0x75a4310cbbaed91770c4,0x6bc922197a0c432d4198,0xd7e2dc0afc18865ed7ae,0xae618865f0b302be8621,0xbbc330f71aa5d6e00cc0,0x6e8661f050c43de4ce63,0x100cc3dcabd73b94570f,0xf65981be8330f75aa5d7,0x985b03748f616ff2dc0d,0x606e07110dc0dd01f87b,0xe63c36d81a87c00370f7,0x5c80dc19b0db7335876,0x19eec423361b6f0dc3ee,0x33e088567c090a2c8721,0x54ba8b8bd7317192e22e,0x49862d952ea2eaf5cc5d,0xd6e6313a1cc6294b08c4,0xadcc7f94b08fecd61189,0xfb98dd22621ba42c4373,0x8731ba470437482086e5,0x30c4048988778db98dd1,0xd088765c39581a871944,0xb917b108421d96e443c4,0x7532d52ea6532e1cbd64,0x24c96e049364b9180a9],#[0x48e2dc0928c772264b3,0x392c59812587f0a4716e,0x72287b0a45166048a0cc,0x64b96604970d43914198,0x49c0d4392e198725ca30,0x1185e80230b3024c1660,0x230950846126108c62b9,0x4a92210952e4012a3d85,0x9063b91343f852549708,0x36b9742347b0a4e96e04,0xcb302618f6149b5dba1,0x86e04b50cc090cc5723,0x263c397cc5622fc37023,0x63d852887b0a5386e04d,0xd76c905ae1920b0dc09a,0xae191fd0c43416ab6582,0x2cc0c1aab657f576c8fe,0x1a8783c350f068f6160d,0x76c9012e192022cc0c1c,0xa5d71c0cc0c14ab65809,0x4b8e581987ca4950994a,0x987cac330f950661f2c6,0x3039317a032654bae5c1,0x61b7966b0ef23d85c98b,0xbaf181b86e285901c533,0x85e08b703c112e1b8b54,0x3c30661f852cc0f083f,0xd8f81ec2f105b81e0cb3,0x99f4bb763ee26e87caed,0x63f8330c7b8621cfa5f3,0xc89aa5951364b9224198,0x4f10ec39e4b9763c8370],#[0xa2ebb76408370c78aa59,0x46d7aec8d94e191780b2,0x8386e191954b2a325186,0xa86b1214498641ce302,0x18498642e12c68592619,0x40370e868661d0c2cc0a,0x796605110cc3a2059814,0x60dc31e8a9653d0b7028,0xac56245552ca832f98d0,0x437028e94e051c54b2a2,0x661e2f5eb9c5ecc638c,0x2cc0c68bc868c0310d18,0x18868e4350f1a2fdce34,0xb303238621a490d4347e,0xf5ce4f0c43494198791c,0xc43464bf638c8310d282,0xc6393178ed212f1da410,0xd012a8621a540c4349ab,0x21e582dc0cb01a87954b,0xc0cae5981958350f2c86,0x81914a303218621a332c,0xf9d9c6073b0c4349c19,0xf4838c0e901a87d0c3d,0xeb47680d643d0fa41ba,0x1d38b303a697a034d39c,0x3d4876073a0ec3ea45b8,0xe705fb9ce05b81ea8b30,0x4fe1a869d4310d3986a1,0xa04a10d401421a780c43,0x4296e06850d43d041886,0x832cc0d0e1a87a18310f,0xdebf639bcb3034216606],#[0xf978c73e866067c0c434,0x5af98c4b2e418a018869,0xc2e41b18508014c330c2,0xa5b816357ae6c297e1d8,0x8330ec9122118d2bc131,0x661d840cc3b26be7366,0x5dba378bc736f09108c7,0xbf646f8350ede2add5bc,0x9708f517201ea0d43b7a,0xf9cdee2f403dc3f857a8,0xe41b4ebc63698bd00f7a,0xc636a4310cef92219de3,0x6c8c03850d800c433c4b,0x605b00fc3afe48865fdc,0x4336629816cc350cd80a,0x876789108cf172019e0d,0x6ce14e1d9e284033c1b,0x1dc067b23821987680a3,0x3bb0bf6375d9b02df86a,0x66d45302da94a0df25ec,0x6d212201a40d4336c1a8,0xb130cc36245b81c6c910,0xe2c5981c58330d8a0661,0xc547b0b8c0621f170d43,0x6a32200d40cc362a2981,0xd75d321b6ba643559704,0x2252868587b0a6c86618,0x6891090a0661e1062b94,0xdb55d79a0d4343429818,0x55fbb71ad475e3552ebc,0xc5b8147c7b0bc98f6179,0x370f2e8661e5c0cc323],#[0x382125b0cc3cc0c57298,0x54b2f5a5b81ed950ed32,0x1e80ec952cbda2a597b1,0x9ae06f96607ba2cc0a50,0x2210e32dc09c63d8537d,0x7b81cc3f8538c9708719,0xd853a0370e7096e04e16,0xb0a73aedd0e75cba1c03,0x618dd63c09b8c4803707,0xb8c404a8487192e30e06,0x8587956cb0f2a1961e64,0xcb13b25c62855c2c3ca8,0x6291ec2c5a59818a956,0xc4819818947b0b15966,0x1ccd56cb112a196220cc,0xb9b16607321fc2e665b8,0x6670cc0a425b814807b0,0xec41981ee03303af0660,0x49c91009216605260cc0,0x362ee05235c402461981,0x5f0cc0cdc59819b4b303,0xc61981ee43303b012a03,0x1c3303b286607640cc0e,0xe8c61c0730c300edd750,0x568c200ad084014c30c0,0x49183535a70802b4a100,0x12100a8a4201367e39a6,0xb75d5573043292fd3252,0x683b2868d8150cc10cab,0xd184511a108a2341d946,0xfb04a534e11446942288,0xce1e944941d8afe82529],#[0x6b9d383187a69f6654d8,0xb32b1c630f4e375d69c7,0x101553fdceae7e39d52f,0xccabd48405923287ab12,0x4052edd75b59fe656abf,0x83b2cd30b6924202cc48,0x1678c61ecb34c2d9681,0x8c458eb188e6985b4521,0x3db430875b4c10cb6b45,0x7b91baeb723b5cee419c,0xb870c21ef068b1e0e318,0xee740c1e1a6985c3cd30,0x1632d612c463037cb950,0x16de2e42dbe5c45b92b1,0x310ce08ba96b096edd75,0x62a8b08c4d376189d8e6,0xc54e6218a9ac43154984,0x89faec3151dcc62a2398,0xd3f4846248c30c4ff761,0xa69bb0f481831e9d8e63,0xf52611fea2c23f986187,0xe88e63fd39887fa6b10f,0x21e086648c30ff47731f,0x92b10dc69851f10b043e,0x2d621b9a6ec3721e086e,0x86e63bcbdd86ea1b98dd,0xae146747c08ce8e871de,0x9bb0de8f811bd1b023e9,0x7761be4ac837cfdcc6f6,0xd0e3c4fdcc7892a18df2,0xa1c6330c30fc69851f90,0xc28e47b841c8f1083920],#[0x86200c30c4018e187235,0x636a42006d40c31011d,0x7b41c18e690801cd07,0xe869851ed03063da4a,0x41d4c50032a0e0c74484,0x23a9ae14753dc20ea788,0x8ac96b115833821d4670,0x15af1722b51f0256be5c,0x319d90657bfe00af68bb,0x62b45d8c643c118d2562,0x9397c09272c8124d2100,0x348f812564ee449c91c8,0x9ff00613f200c246c09,0x221608a643c114aef833,0x877c1988ff80311f9006,0xa6182cb06302448c6088,0xda6ed8ea0a0f1d7639e3,0x2020f2069bb646ec73c8,0x48406fc8f81ded0f05bd,0x2c81961a2e72934dce3d,0xa70f2c3421e5897c0cb1,0x860e5a30c1cac6183965,0xd41e7a6286911a0ed221,0xf81d3a5903a74d4cb583,0x10fa7412174e823ae9d2,0x61b4a30c1e9ed387d39a,0x21ea67981d2cf303a498,0x6365638c6c41e6075272,0xec4982198948403131c,0x18598c030a928061461,0x1b251e736163ae6c2cca,0x461ddce6cd24a019a314],#[0xef4a4201e98fb1bda798,0xdee49403dc928079c670,0x3be7880779e0e4d33b9c,0x5fc6100f10ca01ae1840,0xd83ea05b07cc0b607880,0xb11943360f2826c1e304,0x446080678f500e30ca01,0xc5f302f898a01d831403,0xc3ca09f178c13e2fa817,0x2184034a30807306500d,0x830807646500e18ca01c,0xcc5078c8ca01c5194038,0x3bcca1930401b06080c5,0x7799738ed32e71da65c8,0xd07698d1b0331a0a038e,0x6303130ca00de30401c4,0xca039f30c0e6e318188c,0x9394d463829a1a2e5340,0x1819acc703349860a6a6,0x906003ea0c017c418026,0xa08037cc1006f88200e4,0xc3836d387009f70401be,0x7502df66404be0c80969,0xe04349cc0818c3816dd,0x57d9903cf832079a7,0x183f278407249080e34a,0x3049a0e60949e0c1f924,0xe0a98a1c118bba022628,0xc17314382d1474058c10,0x31058504da0e80998a1,0x534c5060c98a0c1469ba,0x994c9d94e993b2993943],#[0x327ec1a64ff734ca60c6,0x7325434e5f6e69abfa0d,0xe0610e9b18219369321a,0xd471cd3a8fb9a6232874,0xb314326707654ccc50e9,0x7254354cc50c9dc1d953,0xdfb049e18219519321aa,0x3f4c95c7f9929030874f,0x8aa1abcdd75575fe64ae,0xf8844a9a0c6acb45cd5e,0xc50ca1b7dd5437dc2254,0x4e054468c0a890785510,0x941296d18252da104a5b,0xd75a69f1074934e094b6,0x10f558c21eaa9931d52d,0xa1eb37f9955e6280ab4c,0xbada66280b28610f580c,0x87a5cc70d4bb49ced76e,0xb4c0c61e9934c2d3233,0xeba7dba574f874ae8d7,0xa574f954ae9f4875d3e1,0x5ae9f4c95d3e592ba7d2,0xf5c8ca1eb430c3568f96,0xab66fbad6c8083ae0650,0x5986186b19a6ed5db41d,0xb2cd70b6698e1acc3043,0x680ce1ece41c1d9d1564,0xc131c359e6086b3e2ec9,0x42d163a88c707609820e,0x99f109b31860ac831c15,0x1bee13667d426ccf984d,0x769c384cd387105a70e1],#[0xad184094c70222186184,0x25906154be142869c204,0x4b20c2c97418912c8312,0x96c18932c831265f0616,0xd0730be5f0624cba0c49,0xa0e61d18a0c2f693985e,0x8a1c2e8bba05c62830e9,0x14387b15740f4c10e191,0x5840c0c50e1c1821c333,0x5061db4dd4358b420611,0x20c3469ba87cd1750f8c,0x4186c62870e4c10e1a18,0x83100c1061b98a0c3f30,0x86b73fa0d6c7ec1ad862,0x117068c22e12e435ba5a,0x8db4d3815cda302b9b4e,0x6b6c630f6e3e5c6dc7cb,0xf6fb75d6df7cb8dbed38,0xee16939dc0d173b80670,0xde26381c186703713498,0xbc65c8778cb50ef19621,0x7723606ee49405dd2f43,0x41943de66985bcc650f,0xbc3387c0e5c87824b50f,0xd8670f6f18e1ade68bb5,0xbbcdc6f469bb5ead376b,0xd31c36148183c39a6ed7,0x6386c30670f858c61f0,0x9a4e788345cf108aa1e2,0x45d0efd8aa1df48d81be,0x30c1dfc6383bf0c1077e,0x3181be1a1098498a0efe],#[0x6303810c6070119c0e10,0x8618b17e43908fd81dbc,0x1c096663822c8c70c589,0x56216e5ac22dbfe1cb13,0x70c2d986185b76b98b72,0x5c85c19c38b6318716cc,0xb10bcd387170c7042e34,0x622dda70e2e98e045d68,0xc45d98e18b730c316f25,0x8b88ab117861862ee4a,0x217263812e5a2c45d18e,0x4165a70e60c720cc18a4,0x82d346105a68bb0b0ed6,0xc6240c18c52d61189a70,0xc4fc7418a8d06315160,0x1fdfee63fbf5cc7f7f3a,0x3fbf5d87f7fba0fefd74,0x6877b98d0d376199feec,0xdcef731b9a6ec3e34dd8,0xba5ac83752e086ea4410,0x74b2006e96b28dd2e641,0xe97a10dd2d421ba5a643,0xd2f431ba5a86374b5486,0xa5aa8374bdcc6e96a98d,0x4bdd06e963a0dd2e541b,0x97ba8dd2f841ba590837,0xd37619e5eec3bcbe146e,0xdee635b4dd87d69bb0d2,0x22046f77b98ded3761ad,0x2b28df26641be970237d,0x1761aa4eec3c49d0c6f9,0x70e350c21c6a69bb0d4d],#[0xdd86c69bb0fcd1761f86,0xbb0e4ee7418dd8e831b4,0x74201dae84034dd88069,0xec403bdd48076ba900ef,0x948076b2100ef76201da,0xb0ec63861b5a6ec36bb5,0x71c1a6ec38345d87069b,0xc3cb45d87919c38e0308,0x864683b0c8e574191a6e,0xe6d3761ccc30c3234dd,0x1eda0ec3db9dd07b31c3,0x40b4dd88130c30f6d376,0x7469bb0e2d1761c4c30c,0xcad376208c70c3a34dd8,0xd5f9003ab4dd87531438,0xab92107579c10eafb811,0x36fc28eadc851d5cf083,0x6d28020da10041bf2008,0xda10841b46088368c090,0xb4e10836942106d18420,0x96b2158d38520da30a41,0x2f842b25a84563ee1cac,0xa10c578c61cad68bb157,0x4e10b068bb15c33862bd,0x9c398f256531e4ac863b,0x176325a2ec6418e18c57,0x2ec2fbc5c85f68c1168d,0x6086019c10c0318717da,0xc117b2c822f5a7043034,0x6432a5f045ecba08bd96,0xc865bc5c8cb68bb19515,0x90cd18c3996d17632e2a],#[0x11803382338f70466395,0x23025d04604b608c0964,0xe45186188a46c09152f8,0x89c8ab21388d81270630,0x118f172230630e4e1861,0x279e6e44d1e210953d42,0x4a345949e693213cd164,0x8b68b91171474250c704,0x38608723cc30445b4dc8,0x55a0e84a9821c9131439,0xf341d09e69ba92ad3742,0xe68a193cd375279a6e84,0x46382248c7044834d0c9,0xc3044f986088d304392,0x8ce046168c096a618228,0x72b21a2d381185a30230,0x7b81341a2ec67c5590cf,0xf50850be5c4a119c09a4,0x4590a87db894c7884294,0x1c0948d1652a1a4c8543,0x3432a1a28654451d0a43,0x302550c608a931c0946d,0xd96058bb240b14648146,0xb24111464821a0ed02c1,0x7681da0ed0441d96088b,0x9033461206683b412d0,0xb2799c365ad08682da7,0x1e463382ca1a2c59418e,0x6c7a3b0d8f34ddb1f414,0xd90a020f2131c3640818,0xb224041e44d376c91a6e,0x6f53186de5a6ed92b4dd],#[0xdf0c70dbd9ae177b31c3,0xbf0ce1f7d1843efad376,0x7f48406fe6b85df8f709,0x14d184e05a6edc034ddb,0x24c705c1b4e1b8a7e407,0xb4b584f631c0f0ed143e,0xd82b29fad3763da0aca7,0xf05653fd0b047fb4dd8f,0x5a0e67cc5dd8f869bb1f,0x479ccfa8bbb1f72c733e,0x82b29ef17743f0c10e7d,0xd3763fa0aca7f34dd8f7,0xa10680b4a01013d41a00,0x4e191373c2226d283405,0xa99230d3863c5cf0878b,0x981469070e8bb95c9189,0x702841e6050773c22327,0xe10f43041a1c7981428f,0xc222ae784419a70c7a39,0x768dd0f051bb9a0d1672,0xe71da160a3b304346ed0,0x8e3847c0c70d0768edde,0xb47860868e1a0ed1c471,0x38f8c50f1a47dce34683,0xd1abb5ce353143c7d1c7,0xa39484047262868d5a0e,0x474ef738e867031cb41d,0x8d8c50d1fb41da3f683b,0x1b34a0e3668c1c6cd083,0x488e31c908f81921a707,0x92d27692cc10d24349da,0x450b0528b421a496831c],#[0x3460a406843464ed739,0x377c3ca71c8694da7052,0xd1c6391a38c7223421a3,0x5a103229860645683b48,0x34e06456940c8ad18191,0x77b9e8a8582d150f059f,0xd376cfd1f039fb4dcf40,0xc10fa09ea1f3b69bb68c,0x91d33c76b9e786287d0c,0x9bb6849080d09a6ed9e3,0x474d11dee7a20ce07426,0xf03a834ddb4769bb688e,0x60b5568bb6a2d176d411,0xb96b0d173d51dae7aaa1,0x87d5a3f0dab4d2135672,0x3ad1e6075972426aeef,0x1b3972426727981d70f7,0xb698dc75d31c8e9a634e,0x4d4dc909a63910f4c69b,0x7d334ddba842c1750e68,0xba769bb74a6087e9a38e,0x748d386e8da70dd5b4dd,0x9d0c50f3847dce7069c3,0x3ab41da713143ce91c73,0x7268c1ce4d0839c9a0ed,0xf31c769e5a7073934a0e,0xd8c50f3d491ca7a4143c,0xdc718e7b683b4ed1c639,0x768c14eed0829dda0ed3,0x8d0869bda7053bb4a0a7,0xd050fb0b4e067c68c0cf,0x4c50d8c8ec209ad18612],#[0x98b9b1930736326486c6,0x317463266e6c64c9cd8c,0x670ec4242018899ba319,0x36058434c2b2f1f63654,0x739b123287610c50cc22,0x28663e28c8c78ce1d897,0x50ccc9a6159949403326,0x2198a48403143287664c,0xb9b0a6286640610ec518,0x8461ddae6c39861d9276,0x8c71e2118e34c2b0e7a,0x919477b9b286b85638f7,0x2316908062da4c8ca341,0x6644610ec5982198b8a3,0x8c318a0d86494030c628,0x19b30c3b26628364e2ae,0xb2c628365cc30ecaa4a0,0x6e8c702c718a0d9830c3,0xde18a19bb3043374ec73,0xd530c1b7aed846e5a50e,0xa2628673a6486eacc50d,0x50c50ce945191d230433,0x9b461dcf31433a869857,0x848403d06283741a0c8e,0x860867a4670ef447d8de,0x8c50cf3bb5cde731433d,0xa4a01ef31c1bd732807b,0x8e31b4cf372698c306f7,0xec63698c50cd3341d9a6,0xa50cd30c219a677b1b4c,0x7191da7631bb6f3726a1,0xa323547a866ae3ec8ee4],#[0x263781a0c6f00ca19ac8,0x10cefb75d5dd3c433bcd,0xa01ad69433527a807846,0x432fee764605a0c6f18c,0x806086500c11ea01833c,0xcd834619b06940304d0,0x1b1683b364d0766bda5,0x362d2806c5a300d8b42,0x6724f500e48ca19c769c,0xaf2b75d5e419403907a8,0x9b37cc0b663280799bae,0x36832866cda50cd9b461,0x67c6500e58ca19ca1940,0xcf9ee119f3c4233f1d63,0xa18eb1b42d27667cd70a,0x3b1d74679a4c8d0b4191,0x70c10ccec51919d41c1b,0x455d19c314033881836,0xf40c1b466187680c500d,0xd06475dff08dfbf611b,0x4c500eb47a01d88ec03b,0xa0a0df24041be08d817c,0x68c336ae4646d5f302da,0x32806d8650cdab4a19b5,0x650cdc0ca19b6723236c,0xca01cd184339832806dc,0x9413e8fa817d1f302fa0,0x186c486500fa8c201f37,0x50f8b45dd3161940628d,0xa031a3143e306087c5cc,0xc362af981c54c5078d18,0x86dd5e305bab461b7468],#[0x1bc3461b7768c36ecd1,0xca113043426628036865,0xc29157484a4ae50bc95,0x2864c3030ac52121431c,0x5cca4a039869b0c30d36,0x38f68b1738d162e40c30,0x7266080e51a30dc8bbdd,0xe5c6501c918a03963140,0x2e9861e5c30c0cb83280,0x6230c0cc46181980c703,0xbcd173978c30f31475ce,0x6cc7052fb49ce616939c,0x1b71d6637dc04b6f8809,0xd7cc06baf880d74c50d3,0xc6181ed5f701aebea035,0xdcb03d998607b731c0f6,0xb49d0df683a1bee582ec,0x69ba1c7068537e0b0a6f,0xd1743a5a0e87318a00e6,0x28e87118200e169ba1d2,0x8200e431401c0608738a,0x401ca62803a8c500739,0xd718825ae30e18a00eb3,0xf0b0f341921e8232c3d2,0x1961f8aba43a6181875b,0x41c3cd04387a090b0f41,0x6489cc3030db42121e68,0x11618a02293140454d3,0xf38314045c62808acc5,0x6686280cd4c50199341,0x1e74c101d018a0336304,0x1d10c607a118c0f3c318],#[0xe8868404ccd083994650,0xd10d083a21a4e744345c,0x495a1014518e068969c1,0x34396092272c0a451543,0x8b68b951714849a5a107,0x1c6181a34c7034618e0a,0x3da1074718e0a8e68b95,0x342029130c0d206381a,0xd003e002a001b800e000,0xf8083007400658058804,0xa80c700b800a9809a808,0x1298114810080ef00d,0x28181016f815e0152014,0x481d601c681b701a5819,0xd821e8212020281f101e,0x5826a825b824c023d022,0xb82bd02a882970282827,0x8830b82fe02ef82dd82c,0x20355034383360328831,0xb83ab839783880373836,0x3040103ef83de03cd03b,0x50452044484348423041,0xc04a8049a04850473046,0xf84ff04ef84e204d084b,0xb054a053c052e851e850,0x105a1058e857e056c055,0xc85f905e705d205c105b,0xd864d063d862e861d860,0xc86a70695067d866b865,0x9070d86fa06e786d106b,0x8759074a87350727071,0xe07b687a487970782077],#[0x18813880787f707e107c,0xe086e8857083f882d882,0x108e308cc88b3889c087,0x589378927091e890d08f,0xe097c097009650950094,0x809d989c809b289a8098,0x8a268a170a0789f489e,0xa8a750a658a500a3e8a3,0x88ada0ac60ab58aa38a8,0xc8b2b0b1c0b0d8af70ae,0xd8b700b630b5a0b4e0b3,0xf8baa8b9f0b930b890b7,0x38bfa8bed8bda0bce8bb,0x38c620c508c390c1c8c1,0x70cc58caf0c988c870c7,0x20d080d028cf00ce38cd,0xb0d6c0d568d3e8d358d2,0x60dd38db48da08d8e0d7,0x88e3b8e248e0f0df68de,0x78e938e858e730e5d8e4,0x90f028ee78ed28eb78ea,0x88f5c0f4c8f408f328f1,0x28fbe0fb28fa00f880f7,0x901290018ff18fe68fd,0x7105f10501038102e902,0x710c610b3909e908b107,0x2111e910c90fe10ea90d,0x21174116411541140913,0x811d511bc91ac1193918,0xb12329218120791fa11e,0xb12a01282126f125a124,0x2930092f092de92c612b],#[0xc135d1345932e1323131,0x993a89399938c137d936,0x8140693eb13d993c713b,0x194729463144c1432941,0xb94c694b614a71496948,0x5950e950194f294e494d,0x59561155715429538152,0x695b495a115979582957,0xe160b95fb95e595d815c,0x51665965596461632161,0x396c316af169b1687167,0xd970f170196ed96e296d,0xc17599748973a172a971,0x517a39793978a977c176,0x197ff17ec97de97c817b,0x11842983418239818981,0xd98a1988998759865185,0x698e698d718c998bb18a,0x194d19389923990a98f,0xe999d198a997b996d196,0xb99f819ec19d999c219a,0x21a4a1a3e9a2e1a1f1a0,0x11ab89a9e9a861a7a9a6,0x41b181b011af61ae51ad,0xf1b689b4f9b409b339b2,0xc1bcc9bba1ba89b909b7,0x9c159c089bfa9bed9bd,0x39c5f9c4e1c429c2d9c2,0xe9cc71cb19c9a1c8a9c7,0x11d159d091cf99cec9cd,0xe1d679d521d451d321d2,0x79dc39db21da09d8d9d7],#[0xa9e271e0c1dfb1de71dd,0xb9e7b1e719e5d9e471e3,0x31ed31eba9eb39e9b9e8,0xb1f301f229f139f029ee,0x21f8d9f7e1f691f541f3,0xc9fe81fcf9fc11fae1fa,0xea03ba02e2020200b9ff,0x42096208220782063204,0x820e3a0d7a0cb20b720a,0x721472133a11f210b20f,0xfa19da18d2177a168215,0x221f521e1a1ce21bea1a,0xaa24a2234a2262216a20,0xf229e228ca27da26c225,0xb230322ed22db22c322a,0x2235223432335a32b231,0xda3ab2398a386a376236,0xa2404a3f0a3dba3cd23b,0x32475245a2441a42f241,0x424ca24ae249ea492248,0x725372529251724fea4e,0x25b2a5a2a5922573a55,0xaa608a5f925e525d3a5c,0x8a65f264f263e2629261,0x2a6c526aca699a688267,0x1a73da72aa71726fca6e,0x4a79ba780a772a761275,0x927f5a7dd27c527b7a7a,0x3284c28332826a819280,0xca8a8a897a88a2878286,0x8291628fa28dda8c728b,0xe296ba962294ca93b292],#[0xb29d029b9a9a82995a97,0xc2a252a132a06a9ef29d,0x12a852a702a5aaa48aa3,0x52addaacf2ab72aa02a9,0x3ab4e2b38ab26ab0d2af,0x1abad2b962b87ab6fab6,0x2ac0aabf3abe1abd62bc,0x6ac792c5d2c46ac33ac2,0xb2cf22cd8acc0acacac9,0xc2d6f2d5cad41ad252d0,0x42dcfadc52dacada22d8,0xdae38ae292e132dfeade,0x22e90ae79ae70ae622e4,0xe2ee9aed52ec42eb72ea,0x12f54af48af2f2f182ef,0x7afb62f9a2f81af76af6,0x63024300f2ff92fe02fc,0xa307bb06cb05e304ab03,0xcb0bcb0af309cb08e308,0xfb119b10bb0f730e5b0c,0x4b1763169b1563143312,0xd31b831ad31a1b196b18,0xe3210320531ebb1e6b1c,0xb325332483238322e321,0xf32a5b290b2773269325,0x7b2e0b2d5b2be32b932a,0x533243313b2f932f1b2e,0x9b366335b334bb340333,0xfb3a3339f3394b389b37,0x733df33c7b3c0b3b9b3a,0x8b43bb431341e3412b3f,0x3347e346fb4633455344],#[0x4b4cab4ba34ad3498b49,0x4350734fa34e8b4da34d,0x1b543353db52f3522b51,0x35a3b588b571b55c355,0xeb5e235d735c9b5b935b,0x636303617b603b5f8b5e,0x8367b366ab65f364eb64,0x636b736a5369b368e368,0xbb70e36f9b6e5b6cfb6c,0x4b755373db7343728b71,0xa37abb7993788377bb76,0x380bb7f4b7ecb7dc37c,0x238543849383f3835382,0xf3892b885b87a386c386,0xdb8d038c238b538a9389,0xab90eb904b8f738e9b8d,0xab94eb943b935b928b91,0xc3996398039763969395,0xf39e439d4b9c839bb39a,0x53a18ba123a0bb9f6b9e,0x83a65ba553a44ba32ba2,0x5bac03ab8baa43a8d3a7,0x3b133b01baf9baeb3ad,0x13b69bb573b41bb2fbb2,0xf3bc7bbbebbadbb95bb8,0x43c0cbbf93beabbdd3bc,0x93c4b3c453c3a3c2f3c2,0xbc87bc793c6fbc6a3c5,0xa3cb43caebca33c963c9,0xbcf33ce63cd8bcca3cb,0x9bd2fbd263d1dbd133d0,0x53d6f3d5fbd51bd443d3],#[0x3bdc33db73da93d9b3d8,0x53e17be0abdf1bde43dd,0xe3e68be5bbe46be37be2,0x7bebfbeb7bea2be933e7,0xa3f08beeb3eda3ecbbec,0x93f70bf583f46bf2f3f1,0xdbfcf3fb9bfab3f9a3f8,0x1bfedbfe9bfe5bfe1bfd,0x5c001bffdbff9bff5bff,0x9c015c011c00dc009c00,0xdc029c025c021c01dc01,0x1c03dc039c035c031c02,0x5c051c04dc049c045c04,0x9c065c061c05dc059c05,0xdc079c075c071c06dc06,0x1c08dc089c085c081c07,0x5c0a1c09dc099c095c09,0x9c0b5c0b1c0adc0a9c0a,0xdc0c9c0c5c0c1c0bdc0b,0x1c0ddc0d9c0d5c0d1c0c,0x5c0f1c0edc0e9c0e5c0e,0x9c105c101c0fdc0f9c0f,0xdc119c115c111c10dc10,0x1c12dc129c125c121c11,0x5c141c13dc139c135c13,0x9c155c151c14dc149c14,0xdc169c165c161c15dc15,0x1c17dc179c175c171c16,0x5c191c18dc189c185c18,0x9c1a5c1a1c19dc199c19,0xdc1b9c1b5c1b1c1adc1a,0x1c1cdc1c9c1c5c1c1c1b],#[0x5c1e1c1ddc1d9c1d5c1d,0x9c1f5c1f1c1edc1e9c1e,0xdc209c205c201c1fdc1f,0x1c21dc219c215c211c20,0x5c231c22dc229c225c22,0x9c245c241c23dc239c23,0xdc259c255c251c24dc24,0x1c26dc269c265c261c25,0x5c281c27dc279c275c27,0x9c295c291c28dc289c28,0xdc2a9c2a5c2a1c29dc29,0x1c2bdc2b9c2b5c2b1c2a,0x5c2d1c2cdc2c9c2c5c2c,0x9c2e5c2e1c2ddc2d9c2d,0xdc2f9c2f5c2f1c2edc2e,0x1c30dc309c305c301c2f,0x5c321c31dc319c315c31,0x9c335c331c32dc329c32,0xdc349c345c341c33dc33,0x1c35dc359c355c351c34,0x5c371c36dc369c365c36,0x9c385c381c37dc379c37,0xdc399c395c391c38dc38,0x1c3adc3a9c3a5c3a1c39,0x5c3c1c3bdc3b9c3b5c3b,0x9c3d5c3d1c3cdc3c9c3c,0xdc3e9c3e5c3e1c3ddc3d,0x1c3fdc3f9c3f5c3f1c3e,0x5c411c40dc409c405c40,0x9c425c421c41dc419c41,0xdc439c435c431c42dc42,0x1c44dc449c445c441c43],#[0x5c461c45dc459c455c45,0x9c475c471c46dc469c46,0xdc489c485c481c47dc47,0x1c49dc499c495c491c48,0x5c4b1c4adc4a9c4a5c4a,0x9c4c5c4c1c4bdc4b9c4b,0xdc4d9c4d5c4d1c4cdc4c,0x1c4edc4e9c4e5c4e1c4d,0x5c501c4fdc4f9c4f5c4f,0x9c515c511c50dc509c50,0xdc529c525c521c51dc51,0x1c53dc539c535c531c52,0x5c551c54dc549c545c54,0x9c565c561c55dc559c55,0xdc579c575c571c56dc56,0x1c58dc589c585c581c57,0x5c5a1c59dc599c595c59,0x9c5b5c5b1c5adc5a9c5a,0xdc5c9c5c5c5c1c5bdc5b,0x1c5ddc5d9c5d5c5d1c5c,0x5c5f1c5edc5e9c5e5c5e,0x9c605c601c5fdc5f9c5f,0xdc619c615c611c60dc60,0x1c62dc629c625c621c61,0x5c641c63dc639c635c63,0x9c655c651c64dc649c64,0xdc669c665c661c65dc65,0x1c67dc679c675c671c66,0x5c691c68dc689c685c68,0x9c6a5c6a1c69dc699c69,0xdc6b9c6b5c6b1c6adc6a,0x1c6cdc6c9c6c5c6c1c6b],#[0x5c6e1c6ddc6d9c6d5c6d,0x9c6f5c6f1c6edc6e9c6e,0xdc709c705c701c6fdc6f,0x1c71dc719c715c711c70,0x5c731c72dc729c725c72,0x9c745c741c73dc739c73,0xdc759c755c751c74dc74,0x1c76dc769c765c761c75,0x5c781c77dc779c775c77,0x9c795c791c78dc789c78,0xdc7a9c7a5c7a1c79dc79,0x1c7bdc7b9c7b5c7b1c7a,0x5c7d1c7cdc7c9c7c5c7c,0x9c7e5c7e1c7ddc7d9c7d,0xdc7f9c7f5c7f1c7edc7e,0x1c80dc809c805c801c7f,0x5c821c81dc819c815c81,0x9c835c831c82dc829c82,0xdc849c845c841c83dc83,0x1c85dc859c855c851c84,0x5c871c86dc869c865c86,0x9c885c881c87dc879c87,0xdc899c895c891c88dc88,0x1c8adc8a9c8a5c8a1c89,0x5c8c1c8bdc8b9c8b5c8b,0x9c8d5c8d1c8cdc8c9c8c,0xdc8e9c8e5c8e1c8ddc8d,0x1c8fdc8f9c8f5c8f1c8e,0x5c911c90dc909c905c90,0x9c925c921c91dc919c91,0xdc939c935c931c92dc92,0x1c94dc949c945c941c93],#[0x5c961c95dc959c955c95,0x9c975c971c96dc969c96,0xdc989c985c981c97dc97,0x1c99dc999c995c991c98,0x5c9b1c9adc9a9c9a5c9a,0x9c9c5c9c1c9bdc9b9c9b,0xdc9d9c9d5c9d1c9cdc9c,0x1c9edc9e9c9e5c9e1c9d,0x5ca01c9fdc9f9c9f5c9f,0x9ca15ca11ca0dca09ca0,0xdca29ca25ca21ca1dca1,0x1ca3dca39ca35ca31ca2,0x5ca51ca4dca49ca45ca4,0x9ca65ca61ca5dca59ca5,0xdca79ca75ca71ca6dca6,0x1ca8dca89ca85ca81ca7,0x5caa1ca9dca99ca95ca9,0x9cab5cab1caadcaa9caa,0xdcac9cac5cac1cabdcab,0x1caddcad9cad5cad1cac,0x5caf1caedcae9cae5cae,0x9cb05cb01cafdcaf9caf,0xdcb19cb15cb11cb0dcb0,0x1cb2dcb29cb25cb21cb1,0x5cb41cb3dcb39cb35cb3,0x9cb55cb51cb4dcb49cb4,0xdcb69cb65cb61cb5dcb5,0x1cb7dcb79cb75cb71cb6,0x5cb91cb8dcb89cb85cb8,0x9cba5cba1cb9dcb99cb9,0xdcbb9cbb5cbb1cbadcba,0x1cbcdcbc9cbc5cbc1cbb],#[0x5cbe1cbddcbd9cbd5cbd,0x9cbf5cbf1cbedcbe9cbe,0xdcc09cc05cc01cbfdcbf,0x1cc1dcc19cc15cc11cc0,0x5cc31cc2dcc29cc25cc2,0x9cc45cc41cc3dcc39cc3,0xdcc59cc55cc51cc4dcc4,0x1cc6dcc69cc65cc61cc5,0x5cc81cc7dcc79cc75cc7,0x9cc95cc91cc8dcc89cc8,0xdcca9cca5cca1cc9dcc9,0x1ccbdccb9ccb5ccb1cca,0x5ccd1cccdccc9ccc5ccc,0x9cce5cce1ccddccd9ccd,0xdccf9ccf5ccf1ccedcce,0x1cd0dcd09cd05cd01ccf,0x5cd21cd1dcd19cd15cd1,0x9cd35cd31cd2dcd29cd2,0xdcd49cd45cd41cd3dcd3,0x1cd5dcd59cd55cd51cd4,0x5cd71cd6dcd69cd65cd6,0x9cd85cd81cd7dcd79cd7,0xdcd99cd95cd91cd8dcd8,0x1cdadcda9cda5cda1cd9,0x5cdc1cdbdcdb9cdb5cdb,0x9cdd5cdd1cdcdcdc9cdc,0xdcde9cde5cde1cdddcdd,0x1cdfdcdf9cdf5cdf1cde,0x5ce11ce0dce09ce05ce0,0x9ce25ce21ce1dce19ce1,0xdce39ce35ce31ce2dce2,0x1ce4dce49ce45ce41ce3],#[0x5ce61ce5dce59ce55ce5,0x9ce75ce71ce6dce69ce6,0xdce89ce85ce81ce7dce7,0x1ce9dce99ce95ce91ce8,0x5ceb1ceadcea9cea5cea,0x9cec5cec1cebdceb9ceb,0xdced9ced5ced1cecdcec,0x1ceedcee9cee5cee1ced,0x5cf01cefdcef9cef5cef,0x9cf15cf11cf0dcf09cf0,0xdcf29cf25cf21cf1dcf1,0x1cf3dcf39cf35cf31cf2,0x5cf51cf4dcf49cf45cf4,0x9cf65cf61cf5dcf59cf5,0xdcf79cf75cf71cf6dcf6,0x1cf8dcf89cf85cf81cf7,0x74fa1cf9dcf99cf95cf9,0x900a0380c010120601a0,0x24898000012e08c00020,0x2989218078181e148260,0x4d000c82c239840805b2,0x4506a2285209824485c2,0x2e022182324990c1286c,0x2d1504b0b84b120e314a,0x2d084041f44a0f094858,0x1d0243b084561100b026,0x3f062248c81c0f42890c,0x211b83283c203420e172,0x6193c0683a1916a0037a,0x11801b03a22d822602b0,0x107098848002842e15a,0x3213c54062020ae160f0],#[0x62910c83e13c8144186e,0x5681a338ae0f0c638108,0x218ca370b45b16a39032,0x390c460584430ca4c050,0xc10825c1a1106f6212d4,0x10570b21ae4095c430e0,0x5196e068a0f02ee1d876,0x2f05a4015c0c3812104a,0x30650888c6520902d8d6,0xb2974113a18a25040408,0x5421240ad813894342a8,0x44ac11c96e52268443a8,0x7028b240c8104d6006a1,0x2d4c2c9e5728db34cb20,0x8318c6860d74f421b678,0x7ac50f42041a9d9398b0,0x8ccf494a352bd0eb096c,0x5dbfb0b4cd4f4201f1f2,0x5307d48af112f6986b00,0x1cab80a5c7b3a9d48503,0x4c1f520b4e2caae61bad,0x5963fc0a8b2ced96115d,0x51485aafc2a2cb1fe054,0x798e1089e015dd949e68,0xb0830b89a51c7d661643,0x1f69d6164153fce1090a,0x1f598592dcc70844eb0b,0x4428e3eb30b272592109,0x6d48557a420e6634353d,0xa9d4854e59352ca4fe61,0x56f01f614ce675466f37,0xba267abf5909fe8d5210],#[0x640cf90965ab675917cd,0x1e815dd94bc84b217909,0x452175fb342c207196c6,0xe967a157a919a2bbe4ec,0x4fa172e12514bf6131c9,0xd9606bcb9520659352cb,0x16b09d24fceeca0de15d,0x4b795265e7f46a9094c1,0x4b070fa1acf42f379d64,0xab01454b8a435f10a8fc,0xb382ad59c2938d9c1cdf,0x1cdf1a18a417e1374842,0xf291aca37d88a8e1bb4c,0xd6404917684afa0b5923,0xb1f81293287416b2661c,0x2c2428e41dc2868255ec,0xcc2d08ce42e1685578d8,0x2953e05acb6ecc2d096e,0xa97d8101486f57b2204,0x81975eb06084d64e80c1,0x511fbd938ae3084efecc,0xb4d975e8860d99b26708,0x87480d9c156ace19a1bd,0xfaa577e4d291f0af71b5,0xd978afd4abeb0cf41d5d,0x3c191661270c2e70c90f,0xb10c2fb3107b9a5e88f1,0xc53d0fdf2a06427da108,0x213305466c2a4271d08,0xf2ecd265de0028a5fdba,0x70548c2c7fe27cace67a,0xfb12d0849ad39e46cfa4],#[0x566d129ef8a0e66f30a9,0xa539289021d1ca8b4215,0x6b294658a63ff5880cf8,0x50c333b7f5117202044d,0xfe3a480981a11faaac8,0x116ca22515f69ad10968,0xf14490cc8fedd8c84291,0x39275911ab4fd0951628,0xd3455f4d6884b3bb260a,0x434a5de119a3fb0841cd,0x84167764c157fdb50110,0x66449c6cacd8522707f9,0x1161fe5300852d7931db,0x6417e82c37c668b38d0e,0x97b4c32343b616508e50,0x468612cf38d0e1148acd,0x1051a9ffcab411487af4,0x5c1c0a449b5d61197fa8,0x8ce3f28c453c661932f4,0xbe519c3e4498bfe85c0d,0xc7e9014627e225908e7b,0x51ebe05074db166b0b1c,0xe82c76c504a70a8a8c9a,0x1935b36d04286317e499,0x3b79104330794634e72d,0xa1fe2c1080887776920c,0xcdf426976d9a169c4d8,0x20b82bf884f33f7e0c0d,0x2cbed7d913216df86264,0xceafda134c8862907d8,0x811bf400811f3ca1e008,0x3bfbdc4014bf51021fa8],#[0xd22c2a3f673004204380,0xfff9a009049a6d8ad91d,0xdd2f6b321fdbe7a222ad,0x67e23c94342b653b6c8c,0x4e060cd042896a7cac0c,0x72766c25be5441a141ff,0x811a10ba47565658e873,0x4960d3ae99878e6727fe,0x920002943f3810606707,0x68e8628e8f2e5014817f,0x2204af01e111d594d8a1,0xd24110867941b1dc0bd8,0x88086affd133ce701a23,0x7c7fe84601810fefc7d3,0xadfa22462f7263be2062,0xf80a46cfff5950001034,0xddf723c7fe278a3733ee,0x5a7f75ce342c6d063d13,0x11011a4ef43f64e5f568,0x64a95306487cd0821377,0x5fdbeeb733c7062aa170,0xc52ffed010d97082d186,0x7b224c50a1f995520cc0,0x61f7a4195bdb1e630661,0x6b7eae6010a9ef09032f,0x147bc28a14237b3e416,0x14193b793d209665ef49,0x5fe04193a37b3e41663e,0xc995277807322be60742,0x1414dbf571481021c2ce,0x10524fd7d410c4873ded,0xe21928bfd0e0421ff8f0],#[0x7d4ceaa143dff90a09ef,0xd20c81fd625506068075,0xfaa0c509e3f91043327b,0x43919c91c9de90844dff,0x43b89a0e0ffd8a45001,0x84dfd20824757d4cf38c,0x93c650fc760265c75480,0xdcdf59286c35724c789c,0x5fe1004e1ff2c001019c,0xe7224fe089169ff08314,0xf13f1a065cefe81937e,0x9e8a10ffcd808510e696,0x1a40701a67778f311cfc,0x75782ca37f02c3b9e665,0xe9b63333a305946f8358,0x15336976413e145465fb,0x5471932796557f932472,0x43f20662960b83281ea6,0x1f064cf00064be08d8ba,0xa19eed0f2671fe41118a,0x62085de821d29fc10a14,0xcdad5014b5e0c48fef8,0x18939ff532266daf6112,0xfa7922651fcc800290df,0x4d99789f222599ea4a4e,0xc8997d8b10a13bf3cbb6,0x5df33a4479ce033e784b,0x77c0011acea4bd190147,0xd0bdf4f244cbbb7a011b,0x90a3fa3f0048f2fee870,0x50a1772f808c8fc1870,0x9463fd16751d4f843bec],#[0x4db78116bf414515fe50,0x7f0a27b670a13a76d9b6,0x207cddb2c7eec0099afd,0x35a66d9730622e8cdb2,0x4333c0123b0a978cc929,0x1365e3324a3f7f60b820,0x244d87bc21f26cbde1ec,0x3e36b25197969b996e3c,0xa48dcc21851d0d97c24a,0x100121bed56c89997663,0x97de5095f5301d7fffa4,0xfe0004ebe63912bd30cc,0x94e941dbe66ee591e653,0x2be1b19c7d7fd984004,0x7631d28ede4cf86c676d,0x6a592993e6c8bca783ed,0xe19872ca3d76b73464cb,0xf8c5218242616d839668,0xb367d031df3ee010a37f,0x2c8da22fc2598b26af84,0x3327963bff21413a61e1,0xf0c11043393e4d5870e4,0xafff910123399e4a22ff,0x206068ad3ff2c2024682,0x8508911e7380cedff2cc,0xe5ec959cce87ca183f82,0xd389521f9032679031b7,0xd133aef01a2f90052839,0xbdda8ca6fb1b9115864f,0xcb106597ea06e2c4876c,0x8fe2e045be7dc021457c,0x58b83a62960fa1f222b2],#[0x75aa44562e0a727844d5,0x5266c2c28fb5b81099e,0xd0a1cdff2a00217ee484,0x81f534c7b0146f6981a1,0x4d1aff97096a178d1e8c,0x9583b3685276f59379d4,0xd8c3eacc60ed67a115d,0x6f143d142fddc7554990,0x21bdf87210e4346d0a4e,0x5615dbbc8424bf939467,0xd7552059dea2a4c6cba2,0xd2010a173e39a011c60b,0x53ff28508bfe2240c8f7,0xe50010a9fff2b3002034,0x3e162f2a4cfdc3263a7f,0x471091c58b7f55b01920,0xb6f3a89a3bfc289915f0,0xb58ff00000068d607bd7,0xa3f218842651335f36e8,0x4dac8cd141f233d8433b,0x10960810f1cb31979096,0x440cf1e85848433dbf2,0xf780191f731182347970,0x8bde54884331629b1cff,0x33dbf212cc8021e7b102,0x199d32da9646fd44030,0x42ee722a5559a2a7eaa0,0xf3fd6e6144796cf604a1,0x102441f2187f500080c,0xfa18102387f32326f8f4,0xa0dbc20c7be3d0040913,0x47c342b7ea200199e984],#[0x100c0ce4f0730810b0cb,0xb25f508eec66c9615bf5,0x294eeb65d1c7d7810cb6,0xe149b32750827126627,0x7f92264d419c2120ac38,0x92fd800199be14900330,0x645b7fcf09d42a28f506,0x6424a4862ff32326f8e7,0xfb0b4a48587cc9ec243e,0xd665f610fa13b87baa32,0x404cccd2bcd6f2367d62,0x5288c5fc3040880d01ff,0x880d01fe504c80cebdff,0xbe849bfac088a5fc3040,0xaef22a61e12c979e1096,0x7c21f422ffe8248238e7,0x8dfe61cd651ad48f8465,0x5ac887cd8a8ecdc88574,0x96e58537abd910215398,0x42042b69f970006637d3,0x21021dcfa4101480ffde,0x5ffb100011034835766f,0x5c0a21ff0024c4f37106,0x8f84bea204455f618a35,0x204383af46b46204383c,0xfed2202206847e04e226,0xd4be7cc885791219491,0x6ac40d39f5d295feeac4,0x60e0b346102242bb7f0e,0x397d4408437cc20422b9,0x982109bbb85242dbca58,0xf70c4e855edb46cda8bc],#[0x4a7cc8626afa269065b4,0xb08a49c995211f467503,0x643747cd60c1b0e47748,0x3f0216719200a3f7f900,0x45139ff6f8c20c67f7e4,0xb6df7b16867ad20827ea,0x10a33ffe9f24224a0aed,0x12175eb07a085d64e80c,0xf21949bf4401189c9f24,0xe3a4f970685efda448b0,0xd135eb46c085be08e81b,0x8ccfefc03b35810e86f1,0x83fa633691f3fedf188,0xfdf2c63d755b06afb649,0xf4a0032443fa0c200910,0xeaa032b7e654084cf3ff,0x47bfed6189f7800a2c7f,0x6802891564a299f8f309,0x4630c16503f842237ffe,0x6d1f0b2c305940fd0684,0x9f7f4028c4996afeb311,0x40a1529b103fd1330e86,0x12903f8f8470433dbf82,0x60121bdfd040425103ec,0x19d263ccf374d113fd84,0xa0e108387c1ec1aad0c4,0x942bd0704ecfcd550b70,0x21aa5ef8200866ef9631,0xa4893ffe095023d5eb48,0xb7c43bc8339986864f38,0xbe540c88f2cf158a90f5,0x34ef80cf5fe30efb019f],#[0x5850ff09a77d80d01fe1,0x34323c47928686f656b1,0x3d90a1bb603091e2a2f4,0x68740432fad81179fb3c,0xda021a8ee1ed010defdb,0x29d68eda14ce05151dc3,0xe5e5a6e679febe944012,0x7fcea02145d1e80844f5,0x3e0c0d1091e10f29067d,0x60b2ade1b231128c1652,0xfbc5988547d03e220868,0xa00087c02e4688f687e7,0xe0e68b3ed6c43a3c9ee5,0x22b98111436807e21590,0x97f8821474021c40d737,0x47bb3635112a972d4085,0x97041334686f6043535e,0x1225c1049497e4102068,0x7fdb618000438ffec100,0x7e2f0990d0e5a6ca385d,0x5407f68086dfa1508a60,0x6227f4041a525fa2419a,0x15206567fdcc230a1aad,0x9fa94115f9403003397e,0x164afea9010ad6fc4132,0xfe000044043a15fd0e16,0x83d1b0e2ea07f529434b,0xcd5c30635d184430babd,0x8801a0c4f820fa3efe44,0x69ffb11001134c7aff00,0x87ac842021da1fb01328,0xce770cdffe7e231033d3],#[0x8dd2285f8a3dd0bad8cf,0x44e85975f04f942f918a,0xc4f08ea3532e751ebeb6,0x4285cf290320029973a8,0x850ef88457921060eb76,0xd8cfee125a72fa8a1287,0x196ca0e8fccb4a39d4ba,0xd0fdfd04a165cf93123a,0x8e5f49a0742861f465cc,0xa647f26597fb741d7cb9,0x4283d70453de8b82ba22,0x7aa9262e790eaff1ddb1,0xd7054fe3bc5098a1d019,0x4156165a32f4160d1a3,0x706840f5c16be1214263,0x286c10f6e2bf07d05834,0xd608cfebdb82a5a7f1de,0x5cb57b931432030eb05c,0x108e061d60b5818a068a,0xc3e2e12119e66f252a81,0xc4e1514973459f90aab2,0xcd87042b92744c7e90a8,0xc582cb46889e585a120a,0x81e6067410cd87306008,0x54e04cedfc52bf4019f9,0x240fd0a9c89e4d21fe9c,0xedc90485cfa823374c8c,0x79edc0c81f5163b418a0,0xd32903307d151933d82c,0x89075ed814c167404c1f,0x2a022f8244d71f0328bc,0x7e012b9dafbca4df8002],#[0xfc2634fe003207864c67,0x8b3ca40c88083fa04c89,0x4102195f0fe42042c936,0xd3ca944de8906967d72f,0xc1d1f3309583127c898,0x424697831f6a2c74f10a,0x21cdfef2102155f082a6,0xb563cee0434bf6a94e31,0x4ad82c7a922cb841e212,0xe221815bf49062f80028,0x14785f4918cd69305baa,0x3f7f004819ebc1261e13,0xff518e411f7fc68e411e,0x56546336ae20d7d68222,0xd8c96d2886db621eb8b1,0x920975a78bc84086eff1,0xf1f000810adce190329f,0x29032874528fba08481a,0xc0863e228f981032e7bf,0x42f3f874702149fc652d,0x4de8c50c1046fc58ae0,0x9132669b10f5e92253cd,0xf9044df801133a9b1878,0x1db96107d5c2c74cd05b,0x16bc118e770822edf35d,0x26344b82a7901073b841,0x128cbf0263cfa9464af2,0xd10644f226376ce0b2f4,0x57e2432f021a7e00c69e,0xd804539b2f6e043539b2,0x7264f71141ba9cd06f6f,0xb8aa186f3424f3416784],#[0xf8c9ec54838b0c586940,0xaf1d408407ee46084c66,0x432b571c1a155a2ed908,0x8bf15121010d8c09f040,0x292043360337f4484042,0x20347af01642021b9f5b,0xdf8c7a7c4a0293c706ce,0x940c353da93ef6e051c7,0x986ea123748049d01302,0x8ed507870bc642ba7402,0x418c3e119178bd600e19,0x9063dfa0892e060b623,0x7d866450b2fc4083d7f,0x545969d17be02e3a0186,0x84fa450620747dd1758,0xfe05461d989013bf0885,0x3854477e0128031e108c,0xc6a51e3dd60421018039,0xb804d7878129ddc026f2,0xf00e0f4878076ccc853b,0x61418ce90f7090f6521b,0x50dafd48a104827e0d1f,0x7edd8d7a450dedd8d7a4,0x91f24c71ce00c96f3450,0xe013138f40a101fa8050,0xca4834b7fc158001a0ee,0x28e1f500010abf801115,0xf2097dffa800085f14f3,0xd2014367ff150006633,0x6c3f0b66369b13094a7,0x2ddca0e8c018e858e85b,0xafd72457001108d4d793],#[0xf1663f042d377c628427,0xcc7006507b98cb7d30da,0x300067a73652065343e7,0xd00c233ff0050859d3fe,0xffd430019a2e005470f8,0x24e001469]]
def g63H7 := limbs80 #[#[0x331c0704260101030a01,0xf000201081b120e0015,0x34360a040a01162703,0x2e021b5e0f060c530101,0x3b350201c95206070001,0x2c0a0443c10c0204003b,0xf0c4d9d8f0e05e30011,0x11122b133d0c8602131c,0x5a5402dd0007157a1201,0x1d023b02650269010647,0x94dbf44006085a000552,0x1f412f0ad62763a55b,0x49d22943aa0763566900,0xa7a9755ee8e8099dd248,0x51cafc92804e6202000f,0xa9239921da1238680000,0xc172f2820f957fda3a12,0xdd82344001a5a7acfb45,0xafda049bf0b0003c53f0,0x2608673e8001ba8b9471,0xada2272ec9035b770024,0x87c800181482a5365,0x94ab5d7c58a2218dd60e,0x4b68000095820926,0xb80024cdcc3f03a1f800,0x48cdd013e8a0911ea366,0x79e15354d9257fb9c3,0x58a13c9779f395581d0,0x6777371a075263767354,0xfe2dc5bb637042c6c437,0x821ff8019f9327c6529e,0x9a10bc6f8521c3261f0d],#[0x40ba5c814e9e8f294ee,0x675923e5a92356670817,0x1142462c508a24b1f8b6,0x5bf9223cf8021bd46233,0x372432cc6611bc649a13,0x83a4e4e234e859986906,0x5c9693247bc3c8ac1b29,0x2bc316a10095e4c703f8,0x22aa8788fa17b5ed92bf,0x48832c95fda4b4a8425b,0x74dba61aac940cd39a9d,0x400031e7c564da72d799,0x51c4485bb92921b58e95,0xa448500008bfc02916c1,0x2bf624000f92a84bcb92,0x632d0294b059a43e60ad,0x44f4117007832c2d357,0xc46177fb2ec0004d8000,0x15c846098a9d5eb3,0x676e334184b5cfb04200,0x6cc8f2c30a9e664019e9,0x6df8eea12cb82d974d4f,0x392848a553d08292d,0x292952e8690003de16cf,0xe26698c046d4c57130a,0xe257ca4721ad949a17e9,0x628639295d5d253f9921,0xac3c9920a064e8ed5448,0x2234bd59a6ea9d3d1,0x48a5844ae1a877ab6188,0x34ab50ca20b8e766a385,0xa5d58ed9b23b4520e1de],#[0x6000066ff0272328c150,0x3853f5e56236d109b9a4,0x467709727c3d14830ed7,0xb564a2e073109e4fd473,0xd24e2bd7494d35a3a4b7,0x32395bc8d094f62879dc,0xbc000d0205a81489ac4d,0x180007c08000e3460e78,0x3380014fbd3f80000013,0x4a166f115828181f2936,0xfaf0000000d5052028ab,0xe000e6d9ba5d1bd0d960,0xeec85c192a67435ad01d,0xa800087538909ce466e1,0xb62260066255ca49434,0xcdd6774d4da66d074c0c,0xe1d007a1cd31e35d0dc1,0xa488860283aa4a60b960,0xcf7fcafea44ca7b5c403,0x478162f30cd0002c674c,0x5263b1a13c2f268b2e28,0x15512da08743960ea9,0x309808ad258d8]]
def g63D8 := limbs80 #[#[0x100100c8100c01008010,0x508104c81010c1010810,0x8801058c105881050c10,0x90810900108c8108c010,0xcc81098c109801090c10,0xc4200c020d0c10d0810,0x4c42010c201042010020,0x54c205442050c2050420,0x8c02058c205842055020,0x90c2090420900208c420,0x980209502094c2094420,0xd0c20d0420cc42098c20,0x58c215802150c2110c21,0xd0c2198c219802190c21,0x10830104301003008430,0x4c8304c4304c03048430,0x5443050c305083050430,0x58830584305503054830,0x8c4308c0308843059030,0x9083090430900308c830,0x98030950309483094430,0xd0430c84309883098430,0x4c43110831d0c30d0830,0x5883150c31508314c831,0xd083198031908318c831,0x54c3250c324c832d0c31,0x98032950325843255032,0x8440d5032d4c32d0c32,0x4c440484400c8400c440,0x5884058440504404c840,0x8c8408c4408844058c40,0xc844098c4090c4090840],#[0x4c8410c841cc840cc440,0x980418c84158c4158841,0x5844214c42cc84198c41,0xd4c4298c429804258c42,0x98043588435844350c43,0x4c85010c50108500c850,0x8c85058c505885054850,0xd0850cc85098c5094c50,0x10c51108510c851d0c50,0x8c85158c51588514c851,0xd0c51d0851cc85198c51,0x54c53d0c5294c5210c52,0x10d10109100c91058853,0x4c9104c5104851018d10,0x8811050d105091050510,0xc851090d10909108c910,0xd0910d0510cc910cc510,0xc520d8d10d8910d0d10,0x4852018d2010d2010520,0x50920505204c9204c520,0x905208c5208852050d20,0xd0520cc920cc52090d20,0xd8d20d8520d0d20d0920,0x1912118d211812110d21,0x50921505214c9214c521,0x5512154d215492150d21,0x595215912158d2158121,0x981219512194d2190d21,0xcc921cc5219912198d21,0xd8121d0d21d0921d0521,0xc53008530d9121d8d21,0x10d3010930105300c930],#[0x88530509305053048530,0xc853090d309093090530,0xd0930d0530cc930cc530,0x109310c931d8930d8530,0x19131189311813110d31,0x55131549315093150531,0x951319493190d3190931,0xd0931d0531cc931cc531,0x14d3210d32d8931d8131,0x19532191321853218132,0x90d32551325493250932,0xd0932cc9329513294d32,0xd8532d8132d5132d4932,0xc9400c54008540d9132,0x4c9404c5404854018d40,0xc85408c9408c54088540,0xd8940d8540cc940cc540,0x18d41181410c941d8d40,0xd0941cc9418c9414c941,0x18142d8d41d8941d0d41,0x18143d8d42d854218d42,0x18d500c950d8943d8543,0x8c9504c9504c55048550,0xd8550cc950cc550c8550,0x18d5218152d8d50d8950,0x18153d8d52d8552d4d52,0x18d5418154d8953d8553,0x8210d8d54d8954d8554,0x10a10102100ca100c210,0x1921018e1018a1010e10,0x4ca104c6104861048210,0x54a1050e1050a1050610],#[0x58e1058a105521054e10,0x8c210882105961059210,0x90e1090a10902108ca10,0x98a109521094e1094a10,0xcc610c86109921098e10,0xd0e10d0a10d0610cca10,0xc6200c220d8e10d8a10,0x1862010e201062010220,0x4c620486201922018e20,0x50e2050a20506204ca20,0x586205522054e2054a20,0x8c220886205922058e20,0x90e2090620902208c620,0x986209522094e2094620,0xcca20cc6209922098e20,0xd8620d0e20d0a20d0620,0x4ca2110e21d9220d8e20,0x58e2158a2150e2150a21,0xcca2198e219822190e21,0xc63008630d0e21d0a21,0x10a3010630102300ca30,0x50a30506304863010e30,0x58a30586305523054a30,0x90a30906309023088630,0x982309523094a3094630,0xcc230c863098a3098630,0x10a310ca31d0a30d0630,0x90a3158a3150a3110e31,0xd0a31cca319823190e31,0x95232586325523210e32,0xc64008640d523298232,0x4864010e4010a400ca40],#[0x58a40586404ca404c640,0x8ca408c6408864058e40,0xcca40cc640c864098e40,0x58a414ca410ca41d0640,0x98e41982418ca4158e41,0x9824258e4258642cca41,0x9824358a435864398e42,0x4c650486500ca50d0e43,0xcc650c86508ca504ca50,0x58a514ca510ca51cca50,0x98e51982518ca5158e51,0x9825258e5258652cca51,0x9825358a535865398e52,0x9825458e5458a5458654,0x10f1010b100cb1098e54,0x58b1050f1050b104cb10,0x90f1090b108cb1058f10,0xd0f10d0b10ccb1098f10,0x4c72010f20107200c720,0x58f205872050f2050720,0x98f2090f20907208c720,0x10f21d0f20d0720cc720,0x54f2150f21507214c721,0x94f2190f2158f2155321,0xcc72198f219832195321,0x1073008730d0f21d0721,0x4cb304c7304873010b30,0x5873050f3050b3050730,0x8cb308c7308873058b30,0xd0730c873090b3090730,0x4cb3110b31d0f30d0b30,0x54b3150f3150b3150731],#[0x5933158b315833155331,0x9533194b3190b318cb31,0xd0b31d073198b3198331,0x54b3250f3250b32d0f31,0x59332587325833255332,0x99332987329833295332,0xd5332d4b32d0f32d0b32,0x487400cb400c74008740,0x58b40587404cb404c740,0x8cb408c7408874058f40,0xccb40cc740c874098f40,0x50f4150b414cb410cb41,0x983418cb4158f4158b41,0x5874214f42ccb4198f41,0xd4f4298f429834258f42,0x9834358b435874314f43,0x4cb5010f5010b500cb50,0x98f508cb5058f5058b50,0xcb51d0f50d0b50ccb50,0x54b514cb5110f5110b51,0x94f518cb5158f5158b51,0xd0f51d0b51ccb5198f51,0xd0f5298f525535210f52,0xe9ecee5f1f98f5458f54,0xf7fbf5f6f777b7d7e7f3,0xfbfd7dfefb7bbbdbebf3,0xf7fffefeff3f7fafbfb,0xb0ca3dd85b20e0749376,0xdd89004ecb201762b45b,0x82c40029710001bb15e1,0x5ca6002cabb000d59400,0x2dab281705880b52e20],#[0x2802f58c0152e2009776,0x98c0c52e2061576005ab,0x52e2019576031ab2818f,0x115720454b881c65d403,0x8cba804d994026aca0,0x100cadc40658e0031576,0x994066aca033e6301a0b,0x82c4069776018dba80cd,0x99576035b3281ad5940d,0x4db32826d594137ac60,0xb00865d4046cca021576,0xdd8076cca03c16201cab,0x2aec07b66503e0b101e5,0x2b665014abb028d99414,0x21b32810f98c082aec0,0xb020d994107ac6081776,0x5d81532ea0ab665054ab,0x94ec5d9572048bb90145,0xfb7652d61b116ab1c0b5,0x2fdbb297f0d88bf5ce05,0x296cf18cb658e05b1676,0xd8cc05ce06014762d9bb,0x58e05c1676301bb2980f,0x8ae702c4cba984b9c0c2,0x2c5fb19630d88b152e25,0xb16265d4b16eca58b465,0xdd4b76eca5bb4652dcb3,0x78c65e2e702f0a3b16e6,0x96762f1bb2978d194bc,0x305bb2982d194c186c46,0x1164a5c4b25ce0591676,0x9d8b232ea5934652ca1b],#[0x5ce05e94762e5a329725,0x1c36230cb3b17ad194bd,0x2cd4b896659d8c368ca6,0x817459d8b368ca59bf63,0x194be28ec5d34652e963,0x68ca623c63310b3b17cd,0x315722d0b3b18865d4c4,0x5e20b12dea5c56f2ae46,0x8b0d05898652e2c32f76,0x98986c2c4c36a7161b4b,0x52e2c3bd635c14b8ae18,0x499755c94b8ae4f98d87,0x64a0b12f2b1c17952e2c,0x1af4b1c17a82c4c92e70,0x1c17c7ac6c9ae7064df3,0x5ce0b8997565573832ab,0xd96765c4abb2e265d571,0x5eca3b2f66dd57b56e2b,0xb31055d9885ce0c41776,0x9c1732cecca1576650b3,0x2cecb995765cccbaae6b,0x52e70628bbb2fa51d97d,0x658abb32c59d98a2aecc,0xb2fe51d97f56e2bf9676,0x9d98c2aecc62e70630bb,0x86c4c7c36260a0b12ea5,0xa457166253833065d58f,0x5f96382fc59d9742aecb,0xb31655d98b2eecbf1476,0x9d9972aeccb997565cb3,0x2aecc69776600a3b3005,0x195725d9eb1aec59d98d],#[0x641fb1b205dc98336eac,0xb30251d9812ae4cc9572,0x591772cecc71576638bb,0x52e31cbb64644cbaaeee,0xc99758e5d32472e59239,0x8f1f31c78b1c23c2aed1,0xb4786dd63c74c91e3964,0x5da4174c920b964904bb,0x74c922b964915eb1c8a5,0xd19758e94b8c7455da45,0x918abb4845dda3d2aed1,0xb47c55da3b52e31d9576,0x5da4732eb23957690cbb,0x4ae40b1572910bb94805,0x1a57208cabb02cf58c16,0x612b903055d8237cc61,0xa02e75d0174ae4129975,0x5841b58e00d957605cf3,0x2eec0dbe6306d3b90371,0x69576090cba849158424,0x70abb03255d82d7ac61,0x84c5dd81c4ee40e4561,0x5d82e32ea17157609a2b,0x2aec1445610a22b083c5,0xebe6307563803a55d81a,0xbcabb04ef58c272eec0,0xb03ef98c1f2aec179975,0xdc4222aec14bd630a4bb,0x2aec151776080ab88585,0x5b86432e3b0996b1c0cb,0x3463b09a2b9c0d176c86,0x98eb9c0c776c868b864],#[0x190c77ec663a57231e3b,0x3ce8639d7431ddb218ee,0x63b64331c3219859d8c7,0x349e319a4b9c0d228ec6,0xb1a465d4d276c8693864,0xd90d570c86ac761354b3,0x4ae4642e70320b3b1aae,0x9ae7034ca3b19c59d8c8,0x334b3b1ae65d4d72cec6,0x219ae190cd78c666ac70,0x9c0d628ec669b75335db,0x76c86b3864359fb19acb,0x4ae7036163819e59d8d6,0x340b3b19295c8c95ce06,0xb1b265d4d92cec6a1476,0x5c99a2ae26d9571328b3,0x7cc6d7a5726bdeb1b349,0x125726c4cbab3895c99c,0x6b973835d1585a258e0d,0xa33675d19b5ce0cdc561,0xdc9a32ceccd957666cf3,0x5ce0d8177668ca3b3469,0xd16766c0abb36065d5b0,0x67573833a59d9ba2aecd,0xb34a9dc9a52cecce9576,0x5d9b25ce0d91776694a3,0x2aecde19756f0b3b3645,0xa15766d173836859d9bc,0x6dccbab3f15859f2cecd,0x834879d1b73ae8dbc761,0x9c1bb36ead23e6369163,0x5ce0deac70699eb1b76b],#[0xf157667973833cb1c1a8,0x6ccbbb34e51d9a72cecc,0xb37c65d5be2cecd99576,0xdd9a928ecd496766f8ab,0x7ac6d016766d4abb36a5,0xc3f636e0bb8b5855c5a0,0x6a8ab8b8065d5c02ae2d,0xb36c55d9b62eecd51476,0xd91b932ead0b964684b3,0x3ce9241d749212b9490e,0x5ac7092cabb490d59648,0x940bbb496d5964b7cc72,0x1ca855da5032eb283565,0x5ca492aed2a3565951eb,0x2aed289776930abb4929,0x52572928abb4aa65d655,0x934abb494d9964a7ac72,0x2ca45dda4d6ccb26ac70,0x996567cc72b1576949b3,0x2ee3279576958cbacacd,0x699750e50b987255c653,0xe10b9870b9c03842e62,0xb07065d4383ce81c1d74,0x5883c8ac21e2c700f0ab,0x2eec1e15760f11b98790,0xb4162158abb093158449,0x12ccba8965dd83e2aec2,0x98811584402aec1d1576,0x5844e5ce02717761011b,0x2aec2b997515cabb09d1,0x821731422b08a1158443,0xfcdba87e5dc8462aec2],#[0xb07665d43b2aec261776,0xdd84182c420ac70104ab,0x2aec27a17313e0b109e5,0x223731120b108855d858,0x11cabb0a30588512eec2,0xb0b265d4592eec211771,0xdd84546e622ac70114ab,0x8ec27d2e703e8abb0a45,0xd38643e91399f50d88fa,0x3e8f3a1f475d0fa76c87,0x220059d8fa32ea7d3765,0x1d9006eca803b64401c3,0x70c881c36240cb3b2005,0x3967640dbb2a06ed9103,0x41ddb220ee191078ec28,0x21f6e190fb2cec83b765,0xd94fb3ce87d9d743eddb,0x76c8843864420b3b1f6d,0xea2733f4b3b210dd9508,0x428b3b20851d9012cec7,0x21f855c90c2cec851975,0xd94fc68ca7e3b643f1c3,0x70c88496763f0cba9f8d,0x4b765425a32a12ed9109,0x3f91399fcb9c0fe2cec8,0x2a0459d8fe32ea7f3465,0x9d90568ca829476409a3,0x2ae286967642da32a165,0x33465418b3b1fed194ff,0x774cbaba289cdd12cec8,0xa39c89cdce5ce0e72273,0x5d9ce32eae71e74738eb],#[0x2eecea9576755039baa5,0x79d7473cabb3cc55d9dc,0x759039bac55d9d23ce8e,0xb3d065d5e82aecef1776,0xdc9da2aecf02273780ab,0x32eae81e74790eba3c85,0xb957674ccbaba6b9c1d3,0x7a4abb3be89cddf2eece,0xb3c25dd9d840e6ec1576,0x1cdd932eaf2977176cab,0x5ce1331576788bbb3b28,0x31e74998eba4cc85ce66,0x9a56384d255da6632eb3,0xb4ec55da712eed349576,0x5da6742e73399759c8ab,0x2aed3a2e709d0bbb4d85,0x597729bcabb4ee65d677,0x9a0cbacd085ce6836eb3,0xb4ea5dda6d58e1369576,0x5d6792ee33815769e0ab,0x44e637a1731bd7380de6,0x945611c8abb0ded5946f,0x1c8abb0e4d5947282c43,0xb0f2d594798ac23c9776,0x5d87f6aca3fc1621fcab,0x8ac23995761c1ab28e05,0xd17761cdab28e6f98c73,0x1e9ab28f515847a5ce03,0xb100d594807ac6401576,0x1cc7572c63ab9621d4ab,0x6cca38b5651c4bb90ec7,0xa41621d16380e855d871],#[0x1d1b328e8d594747cc63,0x28f6d5947b82c43d9776,0x594817ac64095761edb3,0x3ae23e1576205b32902d,0xc1d711f4bb88ee79cc7c,0x1f8ab88fc5dc8782ee23,0x9a6b0d89355ce09a9572,0x1d9392cec9aa2734d50b,0x2cec9e43624f0b3b2725,0xd16764d9fb1a6c59d93f,0x500b3b27af18d3d28ec9,0xb26eb9c1372ae4a11676,0x9d93e28ec9dbc634ecb3,0x2ae2a19676505fb1a825,0x21571510ab927055c538,0x7e90b9bf4b9c1fa2ae4a,0xb3fe55d9ff2aecfd2273,0x5d9fb2aed049576814bb,0x2aed051576818bbb4005,0x11e73831cb1c18e58a0c,0x7f17383f8d1d6022ee50,0xb41655da072eed009576,0xdc6033ce6fe9d717f4ab,0x2ee5021771810eb8bfc5,0xe2e70a70ab941055c608,0xa7cabb53889ce9c42e74,0xb55255daa52eed4f9576,0x9c2a62eed501576a74ab,0x2ee5511576aa8abb54cb,0x39776a8563854255da9e,0xa90bb8d4655daab2aed5,0x955055c6a82ee5521771],#[0x98c9782c44b9576250ab,0x2aec4dc16226cbbb12ef,0xf9576254abb13cf58c9e,0x258c39930d58c982aec4,0x913465c89c2aec501576,0x9d95828ecac1572274bb,0x78c6ac96765723b0ab85,0xf9676575fb1aba51d959,0x568b3b2acfd8d562ae4a,0xb2bc59d95b78c6ad9476,0x5c9572ae2ab9571580b3,0x2aed601572584ab8ac25,0x9576b20abb58c5ddac3,0xb09aaa58855dac92aed6,0x958e5dcac52aed651576,0x50c329086193554b1cab,0x90861acb430ca5218652,0xacb430d652186b250c35,0xd653986b25cc3590e61,0xa06b25d03590e81acb73,0x994307ac6184b740d653,0x7cc618ab710c4abb060d,0xa3d630d0bbb062d99431,0xddf3186e55d8346cca1,0x806655d83732ea1bb665,0x1d0337ee019bc700cca3,0x7ae01b16700d9fba066f,0xebe740d9eba06cf9c036,0x3a11b99d081cce892c06,0x1de6dd4e83ee8741c74,0x5c8f278c67027723825b,0x4ae47a2772389fb19e49],#[0xbc633855b89c265d4f4,0x38dfb19e6a5c4f336ea7,0x89b8adc4e552e27aab71,0x1d8e42cec6e15763714b,0x2cec7615763b0bbb1c85,0x316763d8abb1ec65d4f6,0x3b4abb1da5dd8e628ec7,0x81d259c0de7ac66f1676,0xdd0e938e874af703a563,0x2ee27494703a4dba9d27,0x816703c1fb19e05dc8e9,0x39cb381f055c8f02ae27,0xb1dc55d8ee2eec739476,0x5d4f176c878b96437cb3,0x36eae1be6370d5b8b866,0x62b71711eb1b96a5c5cb,0x714abb384a5c5c252e2e,0xb39a65d5cd2aece41776,0xdca582ce0e5147071cab,0x7ac731a57298df31cb09,0xb99759912b94c89dca59,0x978bbb4b4adc65a2aed2,0xb4b655da6532eb329576,0x9c26228e12e957697cbb,0x2ae4311576980bbb4b85,0xe3a64171cb20b8f98c5c,0x181cb20c05dd85c36ea2,0xb0b465d45a2aec303a64,0x5d8612eec2eab71174ab,0x2eec2f147017cabb0c65,0xa1572444abb0c865d464,0x438cbaa3c89cd1e40e68],#[0xb23a59d90e32ea872273,0x5c50f44ec8ebe76474b3,0x2cec87997543d139a1ea,0xf9676461139a3051d915,0x469139a3451d9162cec8,0xb22059c12132ea891676,0x5c51b28ec8b9676464b3,0x2ae4f8967646d139a36a,0x919757a9b32bd4d595ea,0x7ad4b8bd6d995f26acaf,0x2bda55d9eb32eaf5b665,0x5d9ef6ccaf797767b5b3,0x28e0f715767cdb32be65,0x9c74a05b32be0d995ec,0xa291b9cf855ca883ee94,0xacf66dd67b32eb452173,0xdda7b7eed3dd3759ee83,0x2aed3d19759e90b9cf48,0x2a173a14bbb4faadc67d,0xa18bbb4fe55da8b2aed4,0xad1851c2822aed432173,0x5da8742e7439776a00cb,0x56e2419576208ab910e5,0x49576218bbb106f98c83,0x214a3810855d8897ac64,0x911059c0882ee4429470,0x5c5456ceaa31572518ab,0x2ceca49476520b3b28aa,0x69d7352cf3829659d94a,0x51ceb929879c14c2ce0a,0x929c59c14e2ae4a39670,0x5da0d52e3069572848ab],#[0x2aed089776839f31c1c5,0x8147083cabb428f58e14,0x84cb384265dca1028e10,0x2d58d596ac2ae5599572,0x596ad56e3569576ab1b3,0x6acb591776ab5b32d5ad,0xab565ad4abb564d996b2,0xab8e3855c55dab56ccb5,0x955e71c2af28e1581f73,0x9c2b42ee5589470ac4fb,0x82c4521576284ab95685,0x3c16229cbbb148f98ca4,0x288abb152f58ca92aec5,0x8946d550a52aec551576,0xdc8a62aec55957628d4b,0x2ae51535542a0ab91505,0x49776899f31c4c55da25,0x89cabb458f58e2c2aed1,0x84565dca2828e1141470,0xddace2aed6595728acb3,0x2aed661576b54abb5a45,0x69873b3dab1d9e55dad6,0xb4cabb5ae55dacd52e36,0x88d655cad42ee5689972,0xdd8666cca3314701a4ab,0x34ea3619751b1b328d85,0x415761b4bbb0ce55d86c,0x490abb0dc55d86a2eec3,0x2a6455c5246eca923465,0xd95253ce8929d74495bb,0x2ce099b7654cda32a66d,0x420734a1bb2a5cd1952e],#[0x4a5a32a5e89cd2f68ca9,0xb244d1952244e6982073,0x9d9232cec95b4654acb3,0x2cec9694764a8b3b2585,0x316764c5139a6295c931,0x49da32a68dd952668ca9,0xb3ea51c1f62ae2fc3765,0x5d9f94ae4fc95767dcbb,0x2ae34a9b75a44c3ad225,0x69a75a58cbad2c51c292,0xa691b9d1e85ce9846e74,0xb52069d69932eb4ca173,0x5da9b42e74d9576a50bb,0x2ae2469a75a5ccbad2e5,0x795762292b911451c08b,0x238bb891851c08c2aec4,0x82a255c54f2ae2471670,0x9c1522ae2a81670540b3,0x28e10a957185cab8aa45,0xc1670860bb8c2c51c216,0xad8a3856e55c6b92ae30,0x857055dabb2aed5b2572,0x5c6ba2ce15d1771ae0a3,0x7cc65715762b1eb19585,0x19670594ab8ac455d8ae,0x598b382cc55c5632ce0b,0x845c51c22d2ae3179571,0x5c6302ce11817718b8a3,0x6aa96d1576b6cabb5b05,0x8957224cab89266dced9,0x249ca19225dc89128e04,0x8aa671c0902ee2491470],#[0x5c9542ce0aa157254cab,0x2ae30d9571554b382aa5,0xc9772864a3843255ca1b,0x870bb8c3451c21a76870,0x857a55cabf2ae35f9e70,0xdc6be28e15f1772af4a3,0x2ae2b3b5542c1aa99605,0x495725a0b382d055c967,0x8ccab8c6655c5692ce0b,0x84645dca3128e1189572,0x5c56a6ea71917718c8a3,0x2ae4b616705b0ab92d45,0x596705acab8ada59c16d,0x5b8b382dc55c96b2ae2b,0x946e55c6372ae4b71571,0x1c2352ee51a14708d0ab,0x2ee31b14708d8bb8c6a5,0xc15718e0b384705dca36,0xab95ba5dcadc2ae51,0x1817358c0b64e6004e63,0x5880c9ac400b27302e73,0x64e601ce6300e6b10073,0x8cc320466b181d35880e,0x1279902338c8119a640,0x981ec1cc0764e6024e63,0x1c00964e60a4e6305193,0x9c8604cd430266218133,0x4cf730266398133d0c09,0x2ef8989773dd00998e80,0x1977cd04bbe2825df331,0xd0cbbe4865df1432ef82,0xda825aed312d783816bc],#[0xab1732d67b196b318cb5,0x2d98b997f318cbf66e65,0x916d74c8b6da825b7070,0x1d8b666e45b4f622daf9,0x62e4604f62302e991813,0x1594230a7b19713d88b8,0x30aca1984c5c8c29ec46,0x896ec5c4b162e6614c63,0x5c4bc98ec5bd7752dd9b,0x98c65931713058b9978c,0xeb3732e59b8972c5ccb2,0x30e631986c5ccbd62e25,0x198b350cc5988662b173,0xdc4ba62e459cf4331672,0x62e45f31712f99b9174c,0x7ce635bd8b8adec5c8c4,0x5e3898af0c9cd6f62e6b,0x1af1c90d78e286bc7331,0x58d8662e2c373635e383,0x64e6c3317361a731b0d3,0x3734161b998b0dc4c586,0x61b8b1b0dcd0d86e086c,0x8ae1c9cd86e2e6c37263,0x5c58762e4b84d625c18b,0x62e4b9317261e6b130ec,0xcf0705e5939ae4c5cd72,0x5e66b1af3318d79e6e0b,0x9af2c1cd799ec6bcce63,0xcc59266e6bcb2735e58b,0x62e6c94e6364a631b25b,0xd73705eb8382f4c9cd92,0x5eaf992f574c97ade62b],#[0xb2f4cdc97a9ec4bd4d62,0x58993be64c9dd3264e7b,0xb284cab17264e7b13273,0xad9436558b932b3d8995,0x5c5939b2ac5cd9598c6c,0x8af7b1c57bca64b8b171,0x1d57bce64bdb3715ef7b,0x9eecbdcc765eebbaaf75,0x9b171653399310c5c588,0x5f5939ae6c5cd7398c6b,0x8b14cdcd7d60e6beb371,0x18d9664e6c531736298b,0x9ac6bfb2736598b9b2d3,0x631736319b9afec1cd7f,0x5d58b9aeb398d7564e6c,0x9b053d8d8298c6c13273,0x90d829a86c1337360983,0x98e6c14e5360a6a9b053,0x7cc6363e6aa3053dcd82,0x6626b1b30c9cd8f62e6c,0x1b30c9cd9862e6cc4e63,0x9cd989ae6cc4f4366262,0x66e2bf59435d18b92e93,0x5b17262d8b8b16cdc97e,0x6359b9300c5c997b686c,0x9307358d7662e4bb3172,0x5c9999ec6c831726419b,0x66e6c0b0736059b9302c,0xbb2736398b9b1cc5c98e,0x611939aeec5cd7762e4b,0x930acdcd8460e6c23372,0x98e3a66e6c2b0736159b],#[0x9a871fcc438fe731c8d3,0xb4d6105a7a1c7f390e3f,0x618b884735842362e20,0x84b6d042562e20c4d61,0x58c25b08612b1710966b,0x9e6215cd310ad93984b3,0xbcf430ae6218573d042b,0x726b085b35841b64e60,0x9839358c1cb6860e4d61,0x9cc289ac217327309983,0x988610ce70086638042c,0xcf43086721843350c21,0x86639843394c219aa61,0xa0433dcc219ce610cd73,0x5d02198e810ce540866a,0x9aea10cf7408673a0433,0x7b3710758b88353dd421,0x818b8852cdc41f62e21,0x1996c5c42a60e6103371,0x18cd166e665cf6332e63,0x98ec664f613318b99a33,0x44c633227b09aac5ccd2,0x35d8b99a73d8cce62e66,0x19b4c5ccd798c66bd943,0xdccda98e66d4e4336a6a,0x62e66c4c633619b999f3,0xd4d616698b89a8cdc4d0,0x6718b8b5f3585af62e2c,0x9b39398d9c62e2ce4d61,0x585b1b682d8b2736718b,0x9ac6d8d8436c58b8b633,0x14d63689939b62c5cdb1],#[0x6b99b9b44c1cda29cc6d,0x8b36c9cdae62e6d74e63,0x1c9a39ac2d1ef3168f69,0x9eecd1cc7668f3b93479,0xece636766b0b75bcc5b0,0x6966b0b4ac9cd9d62e6c,0x9b4ac1cda59ac6d2db43,0x585bc64e6d931736c99b,0x9cc6de4c636f2ca1b793,0xa31736d1939b78c5cdbc,0x67d8b9b3f398d9f64e6d,0x1b57350dab9886d5b273,0x94dab9aa6d5cf436ae72,0x62e6dbce546ae6aa3573,0xfce636fe6b1b7ec9cdb7,0x699839b4cc9cdbf62e6d,0x9b7ac5cdbd9cc6deb373,0xdc5a7b286cf317167993,0x62e2df5b436cd8b8b66c,0x64d636818b8b6acdc5a9,0x6e18b8b713d91ac66e2d,0x9b54cdc5aa98c8dc4f63,0x5cdb662e2db33736a983,0x64e6d0b173685939b6cc,0xb3736b5839b5acdc5ad,0x9526b0c96c9cdc162e6e,0x1c9d350e4e9ac7264d61,0xdc64d9ce7274d7393a72,0x9ac4254d6112b89087ac,0xcb1710e66b0873c4844a,0x136da089ac5c8399ac41,0x109b61084d62e226cd61],#[0x5d8389a4229b1721366b,0xdac21e73700f3838078c,0xe65620f373087935843c,0xf2fb987971cc3cccc41,0xb0793dd83c62ec1e4c76,0x5d84962e424ed611259b,0x62ec2b656215a6b08acc,0xd317212d9b907d35883e,0x1026b0880c5d83a62e41,0x909ccdc8409ac4205b42,0x58857b2842bcd6115d8b,0xb2c82bd94315d8b90af3,0x34d621198b90a0c5d857,0x11a6b208ccdc8469cc42,0x808d31c0469aca234e64,0x108469c64234d3211a73,0x9e84234e4211a6a108d3,0x34c7211a72908d354846,0x11a7b908d39c8469ae42,0xa08d354c469e86234d43,0x5d04698e8234e5411a6a,0x9aea234f7411a73a08d3,0xfb1721527310a93dd446,0xed8b8876c5c44c66e21,0x88b0c5c44f66e220b176,0xdc44462ec2c59641618b,0x9ac823b37111d8b88a2c,0x3cc7011e6b288f399047,0x11e6a988f3d0c479a862,0xa08f31d0479ca823cd54,0xdc84266e22131711567b,0x66e22433721159b888ac],#[0x1cc764027b0a00cdc848,0x4218b91f73d850762e48,0x9218c5c9049ec480cf62,0x9090c9a84864f3243261,0x9c86864f724326392193,0x8f12179d8b8a0ac5c4fc,0x776da0bbac5c5d19ac2e,0x13bb6109dd62e2eecd61,0x885e39842f1b1727766b,0x9e82f1cc4178e790bc73,0xacd617567a13c73109e3,0x75663b3ab7dcdd5b8e6e,0xbacc5c9cf9ac2f34f76,0xdc9d69ac4eb5b4275a6b,0x62e4f04d617a18b93bcc,0xd4e4276a6a13b53109da,0x76a7293b53549da9e84e,0x8ba0c5c9e49ca8ed4d54,0x5c5e962e2efb17174d8b,0x9aa8edb1717859b8bb0c,0x4b1717898b8ba8c5c5e5,0x9c67bb4d3358669e0e13,0x94d5358a6a9ac33b3172,0x58a6c62e533b1729c99b,0x9ac53bd9429dd8b94e93,0x7cd329beca1ceec5ca77,0x9be7214df350a6f9c653,0x8cd7350e6f9ce537cd72,0x5c67566e336b1719cd9b,0x66e3374f439c26a1ce0c,0x94d611caca08e4cdca6e,0x1ca7318e5358c72b4863],#[0xb0e56dd07264e6393073,0x98c79b4863cb1721e67b,0x9ac23fd9411fd9398f33,0x9b2731c18b90e1690870,0x202ca0901358473b2823,0x11017cc880ba64404d61,0xc87562e4404d62202d2,0xb6643ada321d6c990eb6,0xb4e321da6990ed30c876,0x1da7390ed35c8769e643,0x88e8c5c4719ce63b4d73,0x5cd3598c69ab1711ed9b,0x9ec69ccc634e67b0a72c,0xe4c764e59b9a72c5cd39,0x4fd8b9a79318d3c62e49,0x926cc5cd3f98c69fcf61,0xcc93aba649d4f614e98b,0x98ec9d33724ea7b12757,0x4f615018b9a7ac5c93d,0x5098b92813d8940ba64a,0x928538c9429a64a14c32,0x1cd429ee4a14c7250a79,0x66e29db1714de7b9a853,0xb1734f98b8a7d31d93b,0x7feda0bfec5cdfa62e2a,0x1bff358dffb086ffcd61,0x1d1ff66e6ffb1737fe73,0x62e702b1728167bb3ff6,0x4d8438266b0c136d0609,0x8018b93f6c5ce099cc70,0x940174ca009ac3005b41,0xdca009ac5005842802f9],#[0x9eed005874802c21c00c,0x55b418298b9c0cc5ca06,0x82ac2141574ca0a9ac30,0x941960ca0c62e5054d62,0xca02b665065a32832c9,0x9e65014e3280a6994053,0xd8438059b8c02c5c5fc,0x81e7bb40351d601b0e90,0x8c16c5ce07b08703b171,0x98e9f9ac74fcd61a7d8b,0x9cc752b172a967bb53f3,0x54d61a818b953b3586a9,0xaaa6b155574caaa9ac35,0x954534caa29865513172,0xdc6a162e34f4f32a8a71,0x9e864ccc432658b8d4ec,0xc31735627b1ab1318d58,0x572631ab931d95866e6a,0x12b37cc959ba64acb173,0x4c95d98ecacb3725667b,0x9864afb1725767b12bb7,0xfcf3257e7192bf34c95f,0x57e639abf3dc95f98e4a,0xb2b4cdc55a62e2ab4f73,0x5c55e62e6adb17156e63,0x62e71133738798b9c3cc,0x1b37287ef9943f74ca1f,0x8818b8c3ac5ca23ba651,0x8c48c5ce2162e310b371,0x1c0319e87624c43b118b,0x9cc66ecd633766319bac,0xeb2733758b99bb3d8cdd],#[0x3766909bb3990dd98c86,0x91bb3d04dd9e626ecd31,0x10cdd9e846ecf3237669,0x9ce66ecd733767a19bb3,0x433733a18399d13d8ce8,0x3be7b19df318cef9ec87,0x19ef3190ef64e677b173,0x9ccf762e67bcf633de6b,0x60e0704f643de6b21eec,0x64723836a09c1bcc4e0,0x382fb19c1718ce0cee47,0x19e5718cf264e0794c76,0x58ce2b68671307038afb,0x66e671307338a7b19c53,0xa59433d19381e96190e2,0x3d18b99e9398cf498c67,0x81e6c1c0e1b6c87a3273,0xdcce360e671b07038d93,0x62e67acc633d59381eac,0x2cf633958381cac9ccf5,0x3719381b8cdcce560e67,0xb1b96d90dcb2866e3171,0x1d8e466e272307039193,0xb6867631713b19381d8c,0xb32703d993b1d96190ec,0x3998381ccc9d8f662e27,0x81bcc9d8ed64e076b076,0x190de9ec66f4d6337993,0x9a426f327637a7321bd3,0x832703c27b21d2c1c0e9,0x3e19381f13190f09ec67,0x29f13594f89ec87c4d64],#[0xdcce760e673b07039e7b,0x64e077307639ec321cec,0xfb2763b99399dcc5ccee,0x3a99399bec5ccdf64e06,0x81e2cdccea60e6753070,0x9c0f964e678b1733c593,0x60e075b2733e58b99f2c,0x4cd327259b99d6c1cceb,0x711938396c1c1c39e64e,0x9b99398dcc60e6e23070,0x50dc69886e34f7071993,0x98e8e34f4371a721b8d3,0xb27072183838b3dd1c6,0x9867a0cc33cc6619a633,0x84c6c1c2589e8730cc43,0x58e59b6872cb07096593,0x64e12bb270991839cb33,0x2b3719698384b4c5c657,0x97d8384b6c5c66564e13,0x84c0c1ce5c60e12e3270,0x1c05c9c64314d3218993,0x60e02ece631699380c0c,0xfcc7017e7318c6c9c061,0x17e7a18bf350c5f9ee02,0xa22c1c05e9ee82fcc74,0xd891198c488df324467b,0x9e8288cc644458b92233,0x8cc4244679922330c911,0x44673922335c9119e848,0x92413d8920be64904c43,0x1c1149ec48e4f644818b,0xb6848a5f32452e99228c],#[0xa58644519b92293d8914,0x47593821cc9c11e60ec8,0x8a1ec9c10fbeca8edd54,0x9c11f62e28c32704618b,0x60ec8b30704598b8a3ec,0xcf61449938224c9c11a,0x4426aa243394d219eca9,0xa26c9c11364e08db270,0x9c1ea9e64f8cc327c67b,0x9e83443372a059383dec,0xe30709f27a1511310a88,0x9f26b14f96d0a7cba653,0x951574ca8a64e1453372,0x5ca8a9ac5455942a2af9,0xbee13ddc709ed8384f6c,0xddc749eef2a4f775527b,0x9e99384f4c9c284bee93,0x850acdc67d60e13eb171,0x5c68b64e145b171a1593,0x60e1413270a198384fec,0x14d54a0a7b850531c282,0xa267ba50531d2829ca94,0x8500cdca7e60e13f3270,0xdca8360e141b372a0183,0x9c6443cd3221e61910ec,0x3307020d9381053cc887,0x51a69928d30c94664e04,0x928d35c9469e64a34e32,0x5c5459ce6a34d7351a73,0x98eca454755219b8a90c,0x931715298b9a92c5c549,0x84a71942534ca1298650],#[0x956734cab3986559cf32,0x5c6ac64e1564f32ace71,0x64e1593371ab583855ac,0x54f4329662194ac5c6b2,0x8aa71945534ca2a98651,0x18d73d0ed09887684f32,0x9c0699ae034cc701a67a,0x9e8634cd431a67b80d33,0x4ce541a66aa0d3354c69,0x1a673a0d335d06998e83,0x80cd3dd4699aea34cf74,0xdc46860e034337119983,0x62e2924f61492630a48c,0x24d714926322493d8924,0x4ca621a493d09249ce29,0x824b3d913262e2994f61,0x1c1339ec899cc644cd93,0x9c8699cc434ce7b82673,0x9cc744ce72a267355133,0x489838252c9c12f9ee89,0x8a5ac9c12d62e2913270,0x10df862e29332704998b,0x9886fb4e707da6b83ed3,0xb4e547da6aa3ed390df6,0x7d19383e939d1f69ae8f,0x8d22c5c5f764e0fbb171,0x9c29864e14b4d54a499b,0x66e3473070a3983851ec,0x9b070a4d9b8d20c1c290,0x53e73991735cc8b66e34,0x842b35c2159ce2a7cd71,0x5c5629ce70acd7385673],#[0x9ae448ce7358a6b9ac53,0x9ce7154e6b8aa739c891,0x5526382a939c9539ae4a,0x95793dc95498e4aa4f70,0x9c9679ae4b3cd7159d8b,0x9ce4b54d725aa6b8ad53,0x7743203bb99007d0c803,0x2d7b2196bd50cb5ee640,0x197fd50cbfeee65af473,0x4c8c2ee645c75322e3b2,0xeee85bf4742dfb99185d,0x3f7215c3a90ae1dcc586,0x5cba192e5dc8587ea42c,0x1af3dcc989e864c4f732,0xdcd79e8e6bcf6435e7aa,0xea64be764364baa1b25d,0x8f732657a9932bdcc97c,0x653aa1b29dd0d71ea86b,0x2329d95194eaa8ca7743,0xd9194ecc8ca7564653a3,0xee6212f674653aba329d,0xd752166bb21997d50ccb,0x673b10b5fd485afec42c,0x1b45d50da2ee62d8f731,0x50d9bec86d775436bbb2,0xee82dd75416ebaa0b47d,0xd75546ebba1b75d50dba,0x6ebb32375d591baeca8d,0x873d4844aece8dd7574,0x9c03ce8e01e7521137a9,0xee821e75410f3a98879d,0xe75420f3a99079d5843c],#[0xf3ab1079d5483cee841,0x9879d54c3cee861e7543,0x9503ceaa81e77730f3ab,0xe8e81e76640f3ab2079d,0xe77740f3b3a079d5d03c,0xf3bba879d5d43ceaca1,0x1093d50849eeec1e7576,0x55056eac22b754115bab,0xece423757211ba3908dd,0x3f57111fa3888fddc846,0x757a90bbbddc447ece22,0x8cd3d551d5ece0eaf470,0x5ce69ea8734f5329a7a9,0xee629cf5314e7bb9cd3d,0xcf4734e7b99273d4c939,0x4ffb99279d4c93ceee69,0x8bffddc53be8e29df731,0xcc9ffea64fff7317ffa9,0xea6502f7737ffa39bffd,0xf471807b98c13dcca05,0x377b989bbd4c4ddeee30,0x19bbd18cddec866ef543,0x9ccddeae66ef473377bb,0xee627bf5313dfbb99bbd,0xbf4633dfb219efd50cf7,0x37bbb81c1d1c0e0eec67,0x81f1d5c0f8ece06f7570,0xdd0b5eee0a47470523b3,0xea846077742dbaa116dd,0xd77325ebbba2f3d1c179,0x64fbba2f5d90d7aea84b,0xa2e3d55171eac6b8f542],#[0x59571ecc8b8f5645c7b2,0xeaa8bdf6435efa21af7d,0xdf6645efab22f7d9517b,0x623ab2af7ddd17be8e8b,0xa311d55188ec86c47443,0x59588ecc8c47564623b2,0xeacaca7763653ab1b29d,0x6f676653abb329dd9594,0x6c7a90b39d5d02deaa81,0x1b45d10da2ee64d8f521,0x551a3eca6d1f73168fba,0xeac6dd777568fab2347d,0x5f4436afb31b79d5d9ba,0x127ab2071dc844dee86d,0x1075d59456eac82b7564,0x10846eac42bf56115fab,0xece823747411bba108dd,0x767411fa3a08fd58858,0x403aba201d9cd00e8e68,0x9babd549d5ea82eaf774,0xdd1d5eae8eaf673757a3,0xeaeceaf775757abababd,0x4f5749a7aa14d3ddd9d5,0x1cbb380e5d1c072eee93,0x9101d9cc72e8e6397731,0x1c1ffece69cf5734e7ab,0xece6fff5737ffb383ffd,0xc7673a7fa39d3fdcc69f,0x567a392b3ddcd58e8e6a,0x943fddce1ee8e70f7772,0xd04ddea826ef77287fa3,0xee866ef443377ab89bbd],#[0xef554377b299bbd54cdd,0x377bb21bbd190ddeca86,0xa1bbd9d0ddeae86ef474,0x50ce8eeea6ef575377bb,0xea8677f4433bfb219d1d,0x77643dfba19dfd90cef,0x3cba321e5dd90e0e8c67,0x19e9dd8ce2e8c6717764,0x18cf6ecc6727463393a3,0xeae26f746339bb319edd,0xf765437baaa1bddd8cde,0x37baba1bddd90dee8c86,0x21f1d550f8eaea6f7674,0x54911eae288f541447bb,0xeaea88f574447ab9223d,0x27571493ba1511d10a88,0xa00001d5d524eae89,0x73003140148007c002a,0x9f00bd00540026201070,0x2021e00fe00794038801,0x5ac02a301408099c048,0xde806a80335018980bf0,0xc8100807ca03c601cd00,0x2720130c0922046c021,0x59e02bf015500a5e0509,0xa006300308817ac0b720,0xde606c30349819ec0c,0x1eb00f100760039a81c3,0x30020e8102207e803e90,0x204870238c1160088604,0x9ca04cb825cc12a4093,0x4fa0a67051c0285013e8],#[0xec16220af2056802abc1,0x82e5817020b6305a782c,0x627030e418240be305dd,0xe506608328418fa0c610,0xd7d06ad034d41a220c,0x1c6c0e0506f2037001b4,0xc141dd40eb8074c839a4,0x703ec41f0e0f5c079483,0x827840a4202c0ff007e,0x11d0876042ec21261078,0xa811ae08c304598229e1,0x824cc123e0911847c423,0x4c5825c612c00950049f,0xdc04e1426e2135e099e0,0xa0a26050ac280813e309,0x14d50a5f052842902146,0xab6153e0a938544029d4,0x942b8a15a00ac4855c82,0x859482c7616240b04857,0xb6d85b042d4c16890b34,0x9d0bb885d2c2e5416fb0,0xa183f0c1005fb82f8a17,0x31ec18cd0c528622030b,0x6e0331c19600c9986458,0x106924344a1a090cf606,0xd8406bb835701a8b0d3,0xba60dc386da0369c1b2c,0x541c0b0df906f6c377a1,0x8397a1c9c0e3b0712438,0x75543a821d180e7f8739,0x18078443be21dc60ec50,0xa0f5807a583ce21e5a0f],#[0x1f6c0fa107c743de21ed,0x161fe70fe507e903f10,0xf0412e20721022880944,0x84d4423221061072082,0xe4086ac431e216e10a9,0x5f111d8886843f621e91,0xc22f4116b08ac4450622,0x472c237611a808cb0462,0x118484423fe11ef08ee0,0xc092ec494a2480123189,0x12a4894c04a1824f5126,0x60a12f1897304b48256e,0x9a26ae1348899884c5e2,0x4eea2748138f09bd04d,0xa04c4fde27d013d889e6,0x668a2a451082860141f8,0x614a38a49c521828fa14,0x29e514e20a6945306296,0x5482a7015230a898540a,0x9c560a2af0156e0ab005,0x8ae6856e42b5915a18ac,0x6088affc57c62bd015de,0xae16460b1a858902c2f1,0x42d3f168a8b3bc599e2c,0x5b9c2da916c68b5a45aa,0x9ac5ca22e2d17088b7ac,0x10bb905d902e9c17430b,0x17ca0be045eb62f36178,0x1f18058bfa85f9c2fb2,0x58308c18358c13c60623,0x86256310b18780c33061,0xc7206354319018b48c52],#[0x280c8e4643c320718f68,0x919650caac6526326a19,0x335a199c0cc6c660632e,0x81a33e819e08ce806700,0xa46910346b1a280d0cc6,0xd5186a3834f81a658d2,0xaf68d7446b6235871aba,0x9e1b3a0d9406c4236031,0xc37071b768db386d6236,0x6f2e377f1bb18dd206e5,0x80700837e91be90dedc,0x78e29470fe38521c1f8e,0x1ca78e498721638f01c6,0xa001cf00e718733e396e,0x4a3a771d290e8e874403,0x76783b131d780eaf475,0xef3077723b9c1dc00ed9,0x3d8f13c78463c061df98,0xd1e850f39479843c9a1e,0x3dce1ed38f5ec7aac3d2,0xcdc3e4a1f178f8387bd4,0x547de83ecf1f570fa387,0x8fe0c7ede3f521f970fc,0xf900087fc63fbf1fcf,0xbf2049101c4809c403b2,0x24135208a1040881ba40,0x83b641b620cb905dc82b,0xb2c85284266211e90840,0xe10dd886aa432c218210,0x22141100487b843bc21c,0x4c12250911c488ac4444,0x24561229f1143889d04],#[0x88c1e45f422e2116748b,0x1aec8d52467f2327118b,0xab91cbc8e3646f7236d9,0x623f191f088f4a478623,0x489c2435921549050480,0x29c49322488123989180,0xe493a649a624c9925ec9,0x12a6c94de4a4a2512927,0x5a292c98960e4ae72560,0xd625dd12e7497164b6a2,0xa4c4626131303097e44b,0x99bc4cbb264c1321098c,0x6809b084d5a269b9342c,0xf9387c9bec4dd626dd93,0x276613ab09d164e6b271,0xf8527ae13ce49e204eed,0x44500727f593f389f4e4,0xa12c5078282f940f8a0,0x4510a23650f8286c942e,0xed94710a352518628b31,0x52927148bca428520028,0x52d1295a14a4ca502526,0x6ba5337298d14c0ca5ca,0x28a7c853cc29d794e10a,0x95218a8cc54542a14950,0xa9095400a9c854bf2a53,0xc82ad215638aade55462,0xe563c2b1495820abca55,0xad8856b12b48159ccac9,0xd4cae8057192b7915b70,0x295f98af9057aa2bc215,0x2c5916228b0c4582d2c0],#[0x95e2c9c16468b1f458d1,0x2659f42ced166d8b3145,0x8b4f85a652d2a168e0b4,0x6c34b5d25ac52d5496a4,0xe516e64b6e05b4b2d989,0xe2e3417100b82a5bf62d,0x5d202e8097388b9705c8,0xb7c5d9d2ebf9757cba8e,0x38bcd05e3c2f09177acb,0x97c94bdf05ed52f5a97a,0xff117f08bf365f712fa7,0xb4304098170c064600b2,0xc61483091183f0c1b660,0xc40c61eb30dd98648c2c,0xaf4c52a62753129988b4,0xb98d30c6566313317698,0x321299008c7aa639e31b,0x4ce325399220c8c2643e,0xda654f329799434c9dc6,0xcbf865d832da19638ca,0x9a4cccdc664e331a1985,0x9799c3ccdee66df335d9,0x733d699e44cef2675d33,0x685134141a020cfc267c,0x1fa68da345d9a25cd0e0,0xb0d322697034a59a49cd,0x1a8ecd44269ff34e71a6,0x5699aae8d53e6a7a352b,0x7535a61aca8d61c6af33,0x66bee35e41aeb4d72a6b,0xd9166c6a36279b0b0d81,0x45cd9ee6cd1365b1b290],#[0x91b5d0dac46d50369e9b,0x37089b7ccdba26daf36c,0xecb37569ba34dcba6e3f,0xf06f57379f9bc58ddec6,0x8e0286fea37e51be88de,0xc390e172709438339c0f,0xcb1c5c0e2a0713138879,0xa390f1c7f0e3b871bd38,0x72ce39531ca2ce4be723,0x6d0734839961cc18e5cc,0x3ce7dc73c539cf9ce10e,0x1d270e90274553a189d0,0xaa79d4b0ea1874e73a61,0xf13ae89d6c8eb2c756e3,0x8767c3b2c9d8f0ec3275,0xee3877003b6e1db18ed5,0xed0ef3477793baa1dcdc,0xc9e0d0f02c77f43bec1d,0x3c6f1e2c4f12a78783c2,0x9973cbe9e554f25a7909,0x8c7a223d041e76cf36c7,0xf59c7aa63d3e1e984f4,0xee20f6e47b523d939ebf,0x69efccf7c07bc23dd39,0x13e539f220f8be7c403e,0x7d323e8a9f3b8f9b67cc,0xc067dde3edc9f634faba,0x14fd507e733f271f8b4f,0x9fde0fe967f1d3f799fb,0x1920034ffca7fbe3fcb,0xef406aa02b50110805b4,0xc816f40a3a04b9021280],#[0x47c821440f7a0715032,0xb81057c82a3413b20955,0xb20cfd064a8311417ea0,0x41e520ed9072c837541a,0x459422121085080883e4,0xa284be4252a122108d88,0x90a9a85394291a13c109,0x17e10b9e85bb42cba15d,0x4a219cd0cbe863d430ea,0xf438ca1c010db886b343,0x87db43d8a1e2d0ece873,0x1188863441c2204d0ff4,0x5512408900446e222c11,0x227751370899344bea25,0x555a2a2d14cc8a2f4503,0x8945ae22cb516008ad84,0x8c2945fda2f5d175c8b,0x19928cb3464723189188,0x5a51a988d394687a33a5,0x2a38051bb68db646c5a3,0x474fa39e91cac8e45471,0xf4a479423c111dbc8ebf,0xd88fc747d123e2d1ed28,0x920d4905648152402d1f,0x44bd220690d5485d2424,0xfca47392340917848a5a,0x5493aa494d247e921948,0x931e4981a4b85259c92a,0x7fe93c949cda4dc12694,0xd52920946b4a23a50a52,0x255492a4c95024a6ca52,0xb16257ed2b9e95a94abc],#[0xe14b5c25a4d2cc496484,0xe97814bac25ca52e1296,0x304297ff4bf1a5f0d2f4,0x385317c98a64c3d26145,0x4a65993282991b4c81a6,0x4d15267e133a499af4cc,0xb024d6826a9d34fa9a58,0x689b994dbf26d3136409,0x5387e9c194dfb26f5937,0x746d39d49cce4e4ca719,0xf1a770d3b449d6d4ea42,0x24f30279013c409dff4e,0x9f024f69a7af53d309e7,0xf6a9f904fb627d353e44,0xa94088a0254ffb27f553,0xa83d5419ca0ac5048281,0xdda863542cea141508d,0x7f512828899440aa1e45,0xaa32c517ea8b394548a2,0x4800a3ca51cfa8de9469,0x3014916a46a522aa90d1,0xca95754a6aa514527429,0x530aa97b94b7aa59552b,0x7005365a9aa14cfca654,0x92a7a553c129d554e52a,0x1508ca8245402a9f8d4f,0xa3f151b2a8b154472a1b,0xe9aa6b552f6a94d54912,0x155332a901543aa9fa54,0xab1f55832ab515564aa9,0x794abab55c3aad8d5682,0xe158baac41560e2afa55],#[0x2b3815982acaa5645ab1,0x6c2ab5b15aa0ad2f5686,0x5e5715ab7b95b9eada45,0xcaef75765abab15d1aae,0x5fa0afb057c1abd3d5e4,0x20960a8b02f5806abfad,0xaac41d61d8b0ca58532c,0x58f6ac735634cb171589,0x2c8594aac9d56482b210,0xecb34c5995acc2165d6b,0x56800b3de59dbace5566,0xd2bd691ab4655a222d09,0xaa2d4b96a24b4ec5a652,0xd5b112d7996b70b57c5a,0xb6f75b65adaa96cf4b64,0xf6cb7965bba2dd516e56,0xa57088b81c5bfeadf3d6,0xae3a97196b8a65c42ae1,0xcecae6c57302b94d5c8f,0xa05d422e94d7448b9ff5,0xcbb165d7eaeb85757eba,0x77b0bba75dbdaed3d766,0x2d17908bc5f5e15af009,0x4af5757a72bd0c5e70af,0x5f19af8357bc0bdb65ec,0xef75f6e2fae57d08be64,0x4ebf8d5fb3afcf57e22b,0xd805ac0115ff9aff157f,0x44d81ccc0b760443017,0xab07d18382c18b60a6b,0xa616fb0ac584dcc23b61,0xc3eb61de30e1d86b6c31],#[0x9a4c49c6240b113d8830,0x198b32c568629b313fd8,0xb19958c78c61862f4b17,0x3a731c658dccc6aa633e,0x3263fa31f458f28c77f6,0x8c9066465b226590d0c8,0x93aac9af64c4b2539926,0xa9194f4ca546514b2801,0x9b2d0d961ccaeb6567b2,0x6617b302197b0cba865b,0xd146675b32fd9922cc64,0xeccdd566d2b35ed9a92c,0x19d5ace89672f338b19b,0x3ef59f0ecf50678933b9,0x5ab4215a0acd01a67fd3,0x568b33451da21ed0ec68,0xd235690034755a354d18,0x676d2fe6960b4a55a4ce,0x3da822d3e369d934dcda,0xb5479a9d8d4c26a44351,0xaf735715ab0ad5606a9f,0xc36b52b5a1daca6d6136,0xd76d6b93b5bf9adb4d6,0xb13ad8656c1435f95af5,0x711b312d9466c89b6359,0x2b69c5b4b4da3a6cffb6,0x6db8b6c95b5fadad46d5,0xc566e15b6ffdb7acdbb2,0xc8dd4a6e85b7395b94cd,0x1bbeaddce6ed6b75e9ba,0x7b59bd50de886f30378d,0xe837e81bedcdf3c6f823],#[0x4704cb81a5c072e00d6f,0xe13b708ab83b5c1a6e0b,0x420e1e870dab8635c2de,0x9dc570e2837131388e1c,0xb8e89c6f0e34c718ab8b,0x24939171c870e41771ee,0x6d72a3b947dc9eee4c47,0xce62872fcb9729cb38e5,0xce08e6ce735839a45cca,0xebdcf30e76673a639ccd,0x73a181d06ee80673f0b9,0x74953a3d1d190e896743,0xa1574ef3a6c1d316e960,0xa6eabc75473a9a1d486e,0x1d67aeb2675843aba9d5,0xaf49d766eb9475bb3ad6,0x50bb1c5d870ec1975f8b,0x476b23b4e1da1cecda76,0xee5a77163b7e1db98ed9,0xe52ef09776d3bac5dcf8,0x25e024efe177ce3bd89d,0x3c479e1eaf0bb78423c1,0x8f03c6d9e320f16c78a2,0xa2793d3c90de43cf2007,0xef34b798e3cbb1e57af2,0xe870f40179ed3ce99e6f,0x42de9c2f4b57a43bd17d,0x83d72deb28f5607a9cbd,0x7b613da6decbaf62c7af,0x7c87bcd3dd9dee62f6fc,0x30f8747c21be07deff6f,0x5f268f9067c6b3e2d1f1],#[0xe8d1f40af9d27cd33e5c,0x7e3eb35f552fa7b7d2c3,0x7defbeec1f6defb377d,0xfce17e5bbf231f8befc2,0xba0fd977eb73f4f5fa24,0xf5fcfcfe5f7f1c3f805f,0xbfe69fec4ff2e7f7d3fa,0x4cc01aa007900107fea,0x6a809f4045e01df00cf8,0x7021e80fbc073e033501,0x5e702cc8152c09aa047,0xf120729035e819d40c66,0x2c11a20895042881fd40,0x8298c13fe09bd04be824,0x63f83084176a0b4f056c,0x2106da835d41a6a0cdb0,0xa0f41077a83b0c1d220e,0x221a10a7082983ffc1f1,0xab424a2120708d48453c,0xf8510c27f6138f098f84,0xb1b856bc2aaa14e70a4,0x7f10bd885d7c2dce1693,0x9e190d0c698624c307e1,0xc356a1a330cd88660432,0x71bc38421bd50db086c5,0x1d877343b161d4b0e748,0x10ff287dec3e2a1ead0f,0x21a3109f883a440fe204,0x76a2351116d88a4c440a,0x1c4a8624ed123f8902c4,0x89dfc4e222697131b897,0x4af8a45c5132284f13f5],#[0x7915808aa04545a29d31,0xa2cbb163f8b0dc57e22b,0x5d362e3916e28b6145a8,0x18460222fbd17a58bbb4,0x88c7bc62fe311318578c,0x19cc8cd2c660632b5192,0x59b1a968d32468ae33e7,0x7637251b678d9b46c023,0x4730a39271c5f8e0b46f,0xed1475ca3a911d0a8e70,0x6d8f22478923be91dc98,0x91f4d8f8947b7a3d411e,0x404b1fec8fdb47e4a3ed,0x47a41eb20b5903c4813a,0xcc86ae432f217790a9c8,0x913b48942443d21fc90e,0x376919fc8c264579229e,0xf2442920cc8faa47672,0x24a9525129275c92b649,0x998a4c7125fa92e1c963,0x9849c364dcb26bd93424,0xc93f1c9f124f21275e93,0x28b194434a146504f280,0x3bb299994abca45a51b9,0x3e552f2a64951d4a83a5,0xcae6656cb2b28957ecab,0x65e4b212589b2c1495ef,0xad96bdcb5265a3b2cec9,0x72e7597234b80a5b992d,0x5e672f129777cbb3e5d5,0xb65fd92fb697c54bd46,0x9cc2ee614d3081982bcc],#[0x98e2cc66662bf3135987,0x2b6994d4c9e664873208,0xd336599a2ccc5665e53,0xe690534499a02ccf2667,0xd5ba6a7335069a6e4d2b,0x224d87e6c0735c49ac4c,0x99b884db8a6d5536759b,0x37e89bdbcde426eeb374,0x1a938999c3cce12e701d,0x92736b39749ca24e43a7,0x4eaea74ff3a429d094e7,0xde34ee3676cb3b259d7a,0xc79e484f1ba78693bfd9,0xb3da99ebe4f4fa7a033c,0x7d2b3e609f124f7f67ba,0xe0a7ea93f179f7a4fb22,0xd500a280053fd99fd4cf,0xa074502fe81414080a02,0x1cda0d6505ba828d4117,0x3d427ea125d08a283fb4,0x286e14333a18050b1685,0x116a88774408a1e9d0ea,0x8e513a289614494a23cd,0xa2e3516968ae94541a2,0x4691a331d18e28c0745e,0xedd474ca39951be68d87,0x42904b47f2a3e451e568,0xd23da91ab48b6a43f521,0x4e7d268292f1495ca490,0xa5a5415297e94714a07a,0xb4b62a594d2c0e95934a,0x98d54c2ba5f852ea6971],#[0x5b29a734cfea665d328a,0xf539a69c674df2a6d7d3,0xa7bed3d129e054ed4a74,0x80a82d540869fc34fab,0x975113a875d4316a1475,0xaa3e751c4a8c8d45b2a2,0x4b9aa565527fa92a5487,0xf054eb2a6f55342a9905,0xaa435516ea8635406a9,0x5556aa92553d6a9a554b,0xc0155e4aae4d5692aaf1,0x42adb9569dab2f558aaa,0xd5e76af035766ab9dd5c,0xc375613ab04357fcabe5,0x3bac8a563cab18b5899a,0x559bfacced6602b2bd59,0xb4eb5a4dad13d6816b3c,0xddeb6815aecad61d6a72,0xb571f6b87d5c07addfd6,0xaed95757aba335ce4ae5,0xedaaf52579babc495dea,0xaf5fa3afb4d7d02be195,0x2c13f606bb01757ffebf,0x86d6c2df613fb090d838,0x6858a12c4ad621bb0eed,0xbb1cd58de6c6896312b1,0x6482b22a5905ac7b563b,0xb196549b2855936ac945,0xc2cc5f65fab2ed596d2c,0x59c9ace0d66ccb34e599,0x427da036cfbb67a0b3ab,0x5cb49a5a3fad1896887b],#[0x56a31b4ff5a74ed33b69,0xd6276aebb55b5aa5ad4d,0xfaed78f6b98b5b8dad3a,0xd5b1ced8976c2cb606da,0xb6aadb46ed9ef6cc9b64,0xe76b71d5b7d6db6f6d75,0xd56f36b7815bb3add4d6,0x6e0ab7011b7f6dbeaede,0xc57ee24d7100b860dc23,0x265c89ae3eb71ccb8cbd,0xeb9805cb32e545727eb9,0x73f1b9dfdce2ee6a5732,0x9c174b0ba425d172e845,0x46eb3d7572baa35d45ee,0xddac6ed137650bb085d7,0xbd05dd8eee737717bb74,0x7fbc28de0c6f00377dbb,0x3794ebc86de356f15378,0xf4b57a1fbcf35e6caf30,0xd3ef6417afabd5edea42,0x3defa6f7a17ba9bdc1de,0xbe645f246f8b77c2dbe0,0xdb5bec5df56afa517cf3,0x197e5dbf1adf846fbd97,0x2fe737f10bf70dfad2fd,0x7affdf7fbcbfc7dfd8,0x90603d3019780a1c02e6,0x6c0f7606d70301815ac0,0x82e2c14fe09d7048f821,0x7338369c19ae0c730603,0x5f08858412c1f2e0f070,0x613b7099984a1c237e11],#[0x2e8e164f0ac1853ac289,0xa9c33b619370c2f85f4c,0x38749c392e1c130db186,0xfd987cec3d461e1b0ed,0x377116d8883c42ce2083,0xfe26eb130f8950c48fe2,0xc54ce296b146f89fdc4e,0xb5cc59de2c1f15d58ac1,0x4f8c06c5f562ef717278,0xf19758c98c63b6314318,0x35bb1a8b8d12c67c6335,0x28e38931bd38db0c6c96,0x2c78d63bd31d6b8e81c7,0x8fc2c7d263e271ecf8f4,0x1459068c822640a71fef,0x6b22cf9131c87de432f2,0x649db248b9207c8e8e46,0x9b164cfb262792dec95b,0x51ca0964fc3278b9397c,0xb9512ca73e52bf291b94,0x2c1195cdcacce55972a6,0xc732de396b6cb3f658ff,0x865fd32f839790cbade5,0xcc7fe6337312d9865cc1,0xa0bcce86665732b79931,0xf39abfcd4d669df34879,0xf37979b8dcdace6c7b35,0x72bb38fd9c54ce1666ff,0xe1e76473aaf9d16ce6f6,0x3cf46679873c719dfbce,0x9f95cfb467cd73df79ec,0x123a05dd016e80033f93],#[0x3742bda11dd07a6831f4,0x689334449a1efd0dc686,0x1b168cb745f7a2bed146,0x5ad216e8fdb4797a39ad,0xba518d274e930748ffa4,0x4c1da5ebd2d9695f74a7,0xb874d91a698d32f69917,0x4e9e2b4ee3a740d38669,0xd4186a0634fefa7d3d3d,0x90cd472ea2f7511da863,0xeba9c5d4c86a5935271a,0x75533aa7bd528ea88353,0xad73566bab0ed572eaae,0x1aeb02357bdabb5d5c2e,0xad671eb2e35915ac63d6,0xada1d6bd6b5475a5dad0,0xd03ae54d712eb7d75b8d,0xaf5e1daeefd7696baa75,0x6bf035f25af61d7a3ebc,0x834ec10f6067b023d7fc,0xcd870ec2bf613db08dd,0x7b1c3d8cb6c5af627fb1,0x64f7b24cd912ec7df63b,0xcc76611b2e1d95eeca7b,0xeecf076747b378d9a9ec,0xda3bed123682db3fbd9e,0x529da846d39f698db4a2,0xbbb5b7dacc6d5a76a8bb,0x76ce9b654db1bed8336b,0xdcab6e0bb6cedb54eda2,0x4edf436f4bb77ddbaa6,0x3dc5c6e20770a5b82adc],#[0xb98cdcae6e4bb7209b8e,0x4f9ba4ddd0d6e75f7361,0x2b76abbb1ddd6eeeaab7,0x6f0e37839bbf2dddceee,0xe70ef31b7937bc81de2d,0xa5dec16f5a37a87bd19d,0x7be21df02ef7bf7ba5bd,0x7dadbebbdf446f98b7c8,0xd9b7e91bf29df85efbcf,0xf6ffef7fa3bfb3dfc36f,0xe0537020380d3c04be00,0x171e0a57047f81f3c0cd,0x65c208e0eef06cf8325c,0x38593c2a6e13df095f84,0xe2f86c1c345e18b70bd,0x20f108387e9c3d8e1d9f,0x1e264f12938913c465e2,0xc583e2b1f14eb8a37c4f,0xc1bc605e2fef17538b57,0xd78c5bc625e30ef18578,0xf19578c9bc645e31ef18,0x33ef19d78cdbc665e32e,0xa5e34ef1a578d1bc685e,0xbc6c5e35ef1ad78d5bc6,0x8ddbc6e5e36ef1b578d9,0xc578e1bc705e37ef1bd7,0xef1cd78e5bc725e38ef1,0xe3aef1d578e9bc745e39,0x785e3bef1dd78edbc765,0x5bc7a5e3cef1e578f1bc,0x78f9bc7c5e3def1ed78f,0x1fd78fdbc7e5e3eef1f5],#[0xef2057901bc805e3fef,0x5e41ef20d7905bc825e4,0xc865e42ef2157909bc84,0x11bc885e43ef21d790db,0xd7915bc8a5e44ef22579,0xf2357919bc8c5e45ef22,0x47ef23d791dbc8e5e46e,0x25e48ef2457921bc905e,0xbc945e49ef24d7925bc9,0x92dbc965e4aef2557929,0x657931bc985e4bef25d7,0xef26d7935bc9a5e4cef2,0xe4eef2757939bc9c5e4d,0xa05e4fef27d793dbc9e5,0x5bca25e50ef2857941bc,0x7949bca45e51ef28d794,0x29d794dbca65e52ef295,0x4ef2a57951bca85e53ef,0x5e55ef2ad7955bcaa5e5,0xcae5e56ef2b57959bcac,0x61bcb05e57ef2bd795db,0xd7965bcb25e58ef2c579,0x1213068301e12e59ef2c,0x14908a0c8b8880e1681c,0x20a44a47086002c49211,0x108c10384384e188d82a,0x62c8005715844042e144,0x682c560b09110845a260,0xd090a0142607064b0251,0x834050785828018d4602,0x486250f101f0d21e0f02,0x50c84306c804a0120505],#[0x2d958b0530006170ed00,0x5b0c461e045286e06100,0xb260c61a141a8d860221,0x22410c4866cb19230314,0x468c746c645ec9c4d1e9,0xc3c4e968645a26569013,0xb1602674fd2dac8662f,0x2dac866afd2dac866eff,0x104978b08821b7784cfd,0x8c508dd7e5b33be05221,0xe19b7f4b1e82471dedd4,0xc0084efda031335375d4,0x197bc720265ee00c6277,0x3122774e0804cc5e93d8,0xeba982034774f000cabf,0x2c74263a969d8099bbf6,0x402665de7e08bddbb003,0x675065a2bf6ead92a5b7,0xa57e0488a0db76a10baa,0x5d3cc0d09e3b75c54101,0x488c93d2fa66a66eff20,0x3606657d000426f838fd,0xf75023aafc5c088f1d74,0x3f981943fa4f0406655d,0xf83afc5c4093ab2a1142,0x655de78c8aabb8f0223e,0x331c1d7e0c464802e9e8,0xf3033b7feb8a8203387e,0x4e9e8660f2831e7f8174,0x200a66e2cbc920acedf9,0x8fe60654c7f202656f2f,0xcc94c7f202667e7015bf],#[0x65dfffa0c919bfa5d3d0,0x68cfcf818019d3fafe60,0xd630a1233f7f902e9e60,0x957f3dc1152dfd801943,0x3034253fc0032d784809,0x55e7fc1a091fbfc8174f,0x82484f87058659fcf704,0xc1d0893df231eff47f96,0xc54046474600426f8be3,0x3ccab5ad0c3f8c31157c,0xd977bda298e121d8124,0x979c6145fde5240a1e38,0x54091f1e655814b4387f,0x7ef6895d091ed80a3fac,0xa0f958108be3f5048d9,0x8d5e3319032d10c99581,0x6d187afd08a8d3fac2d4,0xbf7b45ee80b58cd37bac,0x25f444565afeadad650b,0x15cd6b5a37c93fac25c9,0xe84fc87985a02d0e5fd6,0x989b7c1ff3122049b433,0xae6b5ad127e172a8d791,0x23243be655ad6862feb0,0x2bbb596bc120c917eeb1,0x3c8e07c8e1e616d685ac,0x6d442fdb4800b34fb8c4,0x1015a4c7f39ad6b32fc,0xad0bf9f7d4a16495f3fc,0x95996b44b1e71f0ae6b5,0x1c8591ebf5cd6b59b3d0,0xf0ae6b5ad15e090649f7],#[0xbfcd11299ade8741e71,0x68465af1b6b59662251,0xc2b9ad6b405f522047cf,0xa6dad65dd7d4a091cbfa,0xae6b5ad01fcc507c8f3,0x837424bf0621ce862feb,0xcd3d032b699b78066059,0xf3010855c98f7b44a464,0x7808655c98d73c808a6f,0xbd21ed7a43379bca8a15,0x59498cab931cc0ce9176,0x4cccabf985f6462ae4c7,0x39af8088dfc38accb5fd,0x808c1cb98c3f131a7846,0x88bfc011373a108ab6a7,0x12870242585f0234fe60,0x7527523e47a379967fcf,0x200150bbcff0299690bd,0x21781a279f24214906fe,0x3e6813da19f427af9679,0xbbac624597dbe12010c4,0x275e16264906fe200150,0x253345b98c09c1d793a1,0x99d7cff0082b48cf3c21,0xf9c4f884164acfa0e102,0xe5c8dabd808b79c44279,0xe3fc1059217ed488bc71,0x1aa0a04acfae0f040344,0xfbce4428b67709567fd7,0x5461fcb912796408472,0x4c9b5e90c7f40b234eba,0x326d72d136bd21e7696],#[0xb25cc8d09f2c01913e58,0x7c62046cfec0599983d6,0x224e769110fea7508901,0x237a8697f75044485bed,0x504811ad387ad268288d,0x85f860da519a3a0f5c9,0x369466c7e2b5084fe2b5,0x2b2eac00cdb5e90dbe18,0xe90fa9d70440679855d1,0x2e340cdb93f7dd4091b5,0xe706283af8605c519913,0x5d15dc107248587f0d83,0xa31aba24787533330c48,0x98bb656a6c0ce1c7910c,0x867ea7c33533717a7981,0x7308dbfe40065a42eb6e,0x32a1163fcc0c81fcc0c8,0x43215a9c32237f981946,0x822dd8468df488652f4f,0xffdb82317a7981957b9f,0x4f02082b437adbe2b2cd,0x55f9021153f65414cd11,0x5c6d865ac3095387c0a6,0x7b5849196b1e4014666f,0x196b96805866ad790519,0xbf911a4fb3fd11a3cb89,0x65ad3c1326eab01164fb,0xaeb293277a4c65f5a782,0xaf70966cc24c75d65264,0x1a03fb3cc4cc5fae63ca,0x27f81c8470ff0fa59154,0x121657de68723c7ce241],#[0x9c3f5a7040ab3453fd47,0x518bf880c81e5fea6111,0x396669a7f82788fa3566,0x6267afc23fb199b3fa6d,0xae638e3e584cbde786b0,0x23238e0284f65d85085f,0x422457cc48cb44fe7919,0xf85858d130e165e13c11,0x6c324ce9c35814cd6a2a,0x1420be02839390d31cf,0x297eb4991196d1425bc9,0xa8b845f10748b12f24cb,0x945517086ff1b5090a2,0x69579414e1a19d9b56a1,0xa396ae283ced44fac186,0x120ca67b053b024abb14,0xda885c73197b4832370c,0xcb09b59434e018359978,0x118c78e2207c230f8471,0x80652f4831c7c120c976,0xbe09065ef98601953f8e,0x238c6fcc22c7d8241951,0x118ff9e85808fbf7d1a4,0x8bae4ed010a3f610ce6,0xf89a1166ffd1308c3195,0x8d94d20c93f03c4c236,0x46bee220f5b08937efee,0x10644ff30a08067ac309,0x99e15bb9a57e40845097,0x80280332365dbc1973f1,0x5b4191396d064398479f,0xc21e7f180194632a1172],#[0x62b832272da0c976118e,0x84b7a7008446fd50329,0x618064d9ff1b646978ac,0x25917e5952367834232e,0xb0fe63cefc45dcce1f90,0x8937c1ff046d17f2116,0xe4c63cf01123b931eff0,0x1c27ee11999f6fc0448e,0x5eebc1913e5803217883,0xcfb0032573f3197e04c6,0x650fb5a2419bbfe60065,0xa4a0cd5f040265ad61c0,0xb42010b5ff560065287e,0x8326aca845afc003263e,0x390567095f040265ab72,0xfe414065c2b7f8c00339,0xd780811a33f3e060067a,0x89ffe0120335f023cf0,0x33f380b3f5c0880f0d85,0x656fa575c392cf3c8422,0x8f3f3e0240676cff70a,0xc633c8911b7c8108b79,0x2fc098d3f908023327e0,0x1f981257ba8322e7da44,0x7f409356542287847832,0xd000849fae04416ac107,0x3307ce61a199a2f211fb,0x32e7c65c880cf5e11d27,0x87bed222f9da44aff120,0x9a2be22f32c7d7f11019,0x33c3cb00335635e01d06,0x255a84e7255a84dfa211],#[0x58019932c98f7ca84487,0x964c75fb789ca033d65d,0xc44065ae9a0663080d29,0x17080660f4f8a983317f,0x84563926a3a746283af8,0x197ea094066bc8473f40,0xfe2c753397187992f81,0x990bb4207ee1d50d3387,0xcdfc4249960df5c61d1c,0x4cf1ca5d3597b6f1194c,0x633838c851617285f119,0x191b46e988b317fe00c6,0x27fa1953294b2d962bfa,0xa13b0ca8299b9e18c1a0,0xe57b997b2f0299406eae,0x7ce6801844a277dfb2a7,0x7e399202b8b2d9bbe18c,0xaa4a4257165b21369202,0x911d5ed424057165b32b,0x5956ea1e7165b24161bd,0x85299d3342f0cb9f9a14,0xb8e9ccdbcd512327d33e,0xed68c19748265bb48e31,0x17b44432de74cc4c87d6,0x134658ff50518f0e9993,0xa446a3d6490fd3f228b0,0xfea59919f3cee2480cf2,0xe35078544af6da06acb7,0xa77cf0648ccada4062a1,0x59f702509973c4f14480,0x8468ab73c460756e04a1,0x7c04cdb9ec13c47d1aca],#[0x98a0eee235e3f244cf09,0x5e84c9dffe642080cfcd,0x33f0c9661af38d048e5f,0xa69cd94bc314b3409a12,0x88e359508b0d3c510909,0x60e291c3940681ae351a,0xeec45190d1f8a2db3d12,0xa41733d7f978024159e6,0x141e7fb003249c865f0d,0x33527121787e8032dbb3,0x1a5f1d9893467c3b371,0x756a105fab5074ed4021,0xaf9935595ab87a5b2833,0x443db32495f48ec39667,0x855f1348247e7f000812,0x84e7f85040a191359e26,0xd21099d6cd9a8dd0d58b,0xda99eea124d50a2570f4,0x78ce1d764d6335728614,0x2195bff0d10ca1c72f30,0x432871cbcc1e3387fce2,0x7432b68df488666ffc34,0xc5e2c6194bc58c32d72c,0x891b7ca201977fea2028,0x4e190ad4e190bd3d0c97,0x7a19571c34498c5114ad,0x35ee9e28abdd3c516bb2,0x95a1e32865e9ac651d84,0x1d5a833870fe2c4419e3,0xd6c57122395a1e3287ee,0xc3217b3864af9e8649b8,0xc3504021a7b1d5118bd9],#[0x69a62b4a33c7971232c3,0x884c6fc2732f6b092328,0xbd358ca99c7246550b83,0xbbb1f28c1c72b43c660c,0x753e18aca1c72b43c660,0x5b2572c45933c821f433,0x518bc52d93b8a5b2178a,0x8bf22a64972741cf6224,0x1cc985f2ee659ddc3e51,0x5e2bab305dd5af46aff1,0x95c536a117770f9464a7,0x43063a70710617756bd1,0x1376430e24af39a1e337,0xe12c958258c3f204b275,0x288641ebfd922dda475e,0xe999244b110cb4cc481f,0xccefc40e24287ca2192,0x323be0a8874862a247d2,0x3fb2d00664e50630f854,0x30f5cca404ce1d7a3590,0xd784809965e290a12ee2,0xe884562fef0a32d614b1,0xbb5fd40cccbf78d4451a,0xc903af46b2261fcb4019,0xa5e499644fe841665bab,0xbc48cf8a4284cf6d11ac,0xead41b73f8b6b2e5b43a,0xe5063cb6868fa8568417,0x50a0fd0830a16eaf244,0x1e9a42133e134307e604,0xbce99898a18534c664fe,0x8228e7874cc983588865],#[0x9dbffc8300c04d1179cf,0x1579e862251d2b186a81,0xa11a2e3f18308ebf8c51,0x31eb54471afaa1175632,0x60020219bc31f01519c7,0x4278ba0c735e3511adf1,0xd126efcb9223291de358,0x8cceb24abae4b0723333,0x9f68daacb6e837075a25,0xc905d3780cd5df10e2cb,0x265662ff6ae332c7c18,0x79a230a7086510d11b7f,0x50ccf4cb23a12a31b2d7,0x6666eb7a7c4066af5b4e,0x2a674d269e2019ead4f4,0xfe9cc8de9d3993a09a74,0x32272831b7a7424466a8,0x1bfbccb0d3204227fa33,0xad3e333575e884911a23,0x7e6ce4806fea60999eb5,0xea401981bfa98a669b5f,0x44f8f8cca2f4b0d08df0,0xb6e2080cf9b057c9d468,0x6934f448cf1dfa3332f5,0x997ebc0114b970f00332,0x9dbeb802233363fcb389,0xd39ad69316684a97c659,0x61f2682666c2d56be2da,0x99bfa982666af8ba032b,0x4a59f1d0388448fd3b19,0xf24a76fee2d99b0b4dfd,0x6959ab498b24d95fd549],#[0xfe4b2f5b6e20ccdd6fee,0xe826d96cd5ad262cb181,0x254050b5ae3e541c4d1d,0x46707dd014227283183e,0x1aba5f3a203314bb7100,0x97ee480cf1ebaf745081,0x194a9e0c71f4e109943e,0xa658f942c10cd1f2853,0x1c20196395a1853356b4,0x32afa3c488d8c819210b,0x30c28cb8cb1642163840,0x7196aa858e5ec3919a8,0xe24452fc86355e631c46,0x99ad8b14a135c52831c7,0xb42db95890b4347c2fb2,0x32b7a6b1b7a6b1db60b0,0xc89fe4061a233c07840,0xd0701f40c81f90c705f0,0xb786510cdee2741fb89,0xcb58fcf0806652307184,0x4032d7cac30a66afa014,0xdc6119894da1c247e78,0x7a0f9232e7a86f168cf5,0x60ebcc08406d8f0042e,0xdd7cda17fb0a046978a5,0xbe6506dfc65332a06298,0x2d96a3e1b8d9603ef324,0x2879158dbe17325533f3,0x3961191be17324780403,0xb2be20e84482ebd10195,0xd13d689bcd488bf1d408,0x32ef20c919385360866],#[0x743922d7f2862658fd04,0x63b23dc2d2247e820197,0x1232cfee81848fba1691,0x232bc495c8382233567f,0xc035917e85a458f88e3e,0x234b8e48cb5d384032f7,0x3227e5b46888cf5d3d03,0x9081aebd4ed94d15dbc0,0x48e78b3c7cf94c86fcc8,0xa473a159a06fce213b91,0xa66489788b29788b1b7,0x1611be19e82999bf867a,0xe54664f5e0950d989ce9,0x61b3b7f03395198bfc0c,0x88cf17c4ff446eeab180,0x2327282430a676d2b06e,0x7080655ed9c68ab1bf12,0xb0b8c711e7366c88482c,0x446a2e724655ee7e08aa,0x6014a14ad0f190477e2,0xab4e532369eb4e06b3db,0x20195bd358f3f85f0359,0x4b7806491878f911e03c,0xc456480fa064c84f2465,0xdcc388acf91f30e6b377,0xca37d702a3247b22d96b,0xc90f99a631b0d1fe8e14,0xbfd11a44f8d1c47ee11a,0x33dad842fbe23d32c1e3,0x19b1c2544205d8bf1462,0xcd2197285e191bf0825e,0xdf892e84ccaf29050916],#[0xc48d02fe2455e05f8c8c,0x244b7e8809482875e05f,0x64a74948285ef198f2fe,0x66b786322bb2e83ab472,0xa1901ade90ca5808fe86,0x5a8fe86495242ea85cf0,0xfe866a4a5d6130be1066,0x91881f6464dfb5085808,0x99d7f1e20d429115fd0c,0x6cd17f6fcc8c1e363941,0x2891f0a4f78cc9f8b075,0x5fc3f591a9d01ac269f1,0x174f914408f85243d33c,0x7b0107d4d9d9154e90aa,0x97c0a919bbd9be084678,0x324a4674e1e651291a13,0xdb0191b879925233b70f,0xa222cf85845ef918e3f,0xf062259923423fc1147f,0xe4084cfb7f00841cd1b,0x9c0cfc266fe384403362,0x198de11ebc8107237a41,0x88399ddfd09061f1d930,0xccfd6ff480880d01e9c9,0x19a3edc00ccdd6fe4c8c,0xcca5e1fd2a03317f3890,0x92034afea5b051c3de98,0xcaccf97e76454f6a5fa0,0x8cf9ede3282332176f28,0x4cdbca32b3387a078ca0,0x99a743d78123f7f45064,0xccc9cbe0548cc9a7c8a0],#[0x2340fb79150921bfb541,0xce3c78f82462c3e8545,0xaf2041ebc810751ae688,0x2033079418dde180050b,0x4299e743c7c123d7aebe,0x42d38ed01090c5ede498,0x816129b172686c76f202,0xfd62031227f22808c6df,0x4583f81911a2dd4326f7,0x929060e9040e90530231,0xe288d3bc7051639f319b,0x21909b4927d60111a778,0xcab7f8245ddff14458f9,0x864ed2c5d9418c38e804,0x588bf5cc71c078648fba,0x95e04940695f10668bda,0xc45c08f870874e99276b,0xa9c9a042e7c8bb99657f,0x8265df8f117023e1c21f,0xf020109ae4c850910ffb,0xf88454af30a329de119b,0x5af8065e0fb6f803349e,0x334f935fc08c19ec258f,0x32406dab7db286cdd759,0x2a2c44bc1a0acf26bd60,0x4f5c7a032f7bc18d7fa9,0xe079e7023e6d87e62667,0xff62c004671f387c2469,0x69ddfe3445cce3e0c66e,0xfc34500ccde891e16800,0xa0652eb0844b353e9059,0xd019bb9d2888acedfa73],#[0x5a39e96d40133557ad25,0xb3abec8542471fda819,0x48ed7f088d664878704a,0xd7be1024cd1b59fe0197,0xf1a0348d5f8314e5667e,0x373f5f328e7f1c1591e7,0x650daac749c1be32b33b,0x9956f3ef172d21b86c56,0x5f40c8cb4fa4157f9514,0x2676d0284317f5f7c8cb,0x74e0c8cadfbc664ed2c5,0x42b64c59ba36eb68e33b,0xb0e5c2810bd2f0862b36,0x39b26b1997a8411f540c,0x3283af27422ff0109d1b,0x9ac66ead395019abcd50,0x9e6a819503f4c665ed6c,0x6a81983e931a752e80cb,0x3e24884e974d5033653a,0x33d23f65819d5f504422,0xa3799cbe1951819acd09,0xbfad270cf963c116be8a,0xbe1441b3c3d426043354,0x7f6888666fc36d03033d,0xe20199d7cff0082b48e9,0x942080cdd0f3c0cbdaf7,0x80d01fb40332d331267,0xc8f7f358c408fdae784a,0x21adf911307ed00ccb4c,0x6667374112149fc84092,0x9ff8350023387fe40560,0x7683330728469e0408d2],#[0x7ad7c032c79ec0c95e9a,0xb152f806668ae7820334,0x94579fec408f1eb1f40c,0x19b2d7dd4119eb5f9f91,0xd95a56f204681bfdfc11,0x65d78120338378e408cc,0xac20164486ce3d65b347,0x2870e0340d01a39f3283,0xcd0841b7468602fc371b,0x8d03f3e008b1f8fb400,0xb58ff71a2668e1afa04,0xf2032c79133253ba4801,0xd05d7a2032c782332607,0x3e7e5910cdd9689e0408,0x197be018f340e3b4199d,0x7d03186df00cca187c10,0xa2f1e1088e1c76820336,0x232f93fe088d327fc111,0x40685f37fa111a66ff42,0xceab57046da03943bf02,0xb268bf886cd9ad693166,0x6abb699b680e35acf033,0x6a2feb3067c740e213b8,0x5a4c59029caee811b69c,0x4c5963293e9657736507,0x474e90b9c77d5996b5a,0x9fa0408d2dfde9b032f3,0x20f3853b7874c0d0d94b,0x33b652b7a5011a21f90,0xd269b2c14854ca1dfa2,0x24b4724a11a34500fe48,0x9f604223f6041fa8f224],#[0x23f51c928467a8f88414,0xff440a65aa7db9819aec,0x13962adab56c3d6184a9,0x8cadf8ddb8919c5d1b22,0xf37a6593ecff446cefc4,0xe6cfc488ca17d5b085d7,0x62eeb00cadfe551b4199,0x640c8be0199832cf0406,0xd42112347f620462f1a0,0x4ff82234c1fd6088f17c,0x963902334c1fe5088ebe,0xde9604346baa7d90ace5,0x9225e22cb827c9284c79,0xfe12a08067effdd10299,0xfc12bd06648cbc7db2c7,0xc88a8cf6ede3117421c3,0x60186cf807c58848b7d3,0x1ba233c5f13fd11bbaac,0x696c36e3a79309a5b4ac,0xb5aacf165c2c37d288b2,0x207143456333c5962ca4,0xc8674dbf6bec662ffe18,0x796ccae2cda840f3f344,0xd6fcef064fcef060da32,0xf3c73b2c8d1c8492c750,0xc7cd08099dfc2c68199b,0x199b9bf33a06743d7327,0x2348718750650f5e5b40,0x1f46f3a0660c4bbf858b,0xdfe3000ce4d4f96340ce,0xe5c2810a1514cc59b0a,0x20109514cd6330fd1089],#[0xfa6ba019b2299ac66978,0xcd23af5d1181da2e4842,0x66551d7ae88d8dcf9790,0xcce1f1a357f19b3ff2c0,0x5ec00be3eb434bb6fcca,0x3a67f223312e9b66b0b4,0x85e6c2beacbcdf3fa994,0x8df50eb2819e4afd4c4,0x9c2686fdcf31979eca49,0x2067c24e789133f891a6,0xf37cfa2328a5819f0828,0x6a1318642c21728d87b2,0x650ff987c9800d0af23,0xe704107b54708b5ff560,0x967b090bff50321ec23,0xc6527f21024886b75989,0xb562a3a5cae2c2370f1e,0x81c86b499b5089ed5635,0xfd0592d1e44e423a9f90,0xba93fd81334e43d563f5,0x48ec7099fd0a7370d9d2,0xb74a1fda333c24763848,0x50f4f999a9c81eca0343,0x12033a7ca11f0a133436,0x7e6645ff0a0452f9792,0x336afe8088da3f830237,0x94bfd572026672fbb820,0x19963f5ed19973fec099,0x97921333d53e6642ea5c,0xd2978a3ffbf414097de5,0xa7370d992b450fe0480,0x68ce39396cbd9c47ec9d],#[0x817ee080d0d953d72202,0xe169080d06eb829089f2,0x48678b245067ac664fc7,0x49484728b2c5067ca66,0x88d09de8201944c1fa0a,0xab21a1028dfc502443d9,0x608ee14ca5f770406687,0xccbdfa9748cccbdbe164,0xc0bd5996a9f3321752e0,0x6140bc45911e0c458852,0x44b4f900363662496e94,0x13fb4067c87aaf7bff04,0x9a65aabeefaaf1130394,0x9f16610110d9f4bfc911,0x3e790211b2b7ba2d01a2,0xe5698234f22fa9024435,0x4650f0b0fa033743c4,0xf18b61a10bef00465cef,0xc89fe07a40233a70c18,0xb40662facbb04662c3d2,0xa75b7c08d0fa91065e4b,0xd1a67f351229792ed019,0xda813fa0339550a5a4b6,0xe008ce95a2b73e008d21,0x410add2d7fa4cd9e502f,0xaa56822309b942d396b0,0x4ee5e0152da34257336d,0x780232e77e24654a7a06,0x851953860c747a45465f,0x7f0b9d823387a418f03b,0x6c90823427f899d8233b,0x424a183cb0fb40664ef8],#[0x42c72cf1521a234e349b,0x7538f1e70844986cda80,0xc7f91608cd9e3a472046,0x967fccca5c63f724067a,0x7ee480cf3eace3d0891d,0x8e0448af69fa51999b94,0xeb2341377e880cca7d77,0x404699cfc08450e8dfa3,0x4838fe0088cadfad0e39,0xebf14808cf2f2041e3c5,0x1dfa20334176e2008cf1,0x480ce987e33243829070,0x6f4c9dc13e3237800fe,0x867133aec56f3e7c4925,0x3456149b8f00682dbe,0x661630e9541a2832ed7a,0xe5804d6bb153d7f70412,0x3e8f7b1412567d360936,0x88f4659f46b43e00953f,0x12c74b4d37c8ebccdb36,0x81270ab76b8c13c21b04,0x67e326c9c2eb73e093bc,0xe04eafc0813e40887027,0x22b4ceb14b9f12448110,0x17fc2150067ef853e204,0x34ff004befb782371339,0x4c1ff2c504483428f5bb,0xa0288c0ffa4144b3c9c4,0x877bf0412605663e0809,0x4689e944fe0a092828e,0x82e0eee008959f847b50,0x4c3971e404ce38afc511],#[0x83813fe70470319af846,0x49af1bc209d20cf3a808,0x3766b012ebed1284ee49,0x9a2bed984f24a4d23a14,0x4684d73e02b6df0ee4db,0xd1fbd0908d3fe1436f6a,0x88312840f4390bb558c4,0xb1f16c42e84a51e87aef,0xbbde4262c7c496a23094,0x55ef5b500ad2440f4390,0xde3cb85b11449aaf3262,0x56db018332f7ed4d68c,0x56f22030675a27075f09,0xa1a5760668f4cb04c4ce,0x7a5f2f0485a27f39c120,0x1a69be7a732a7ce0322f,0x35229483437fa84b0058,0x3849efcb01222a83487f,0xa4f2c342b068dfaadd20,0xd457888b25ea5d611848,0x1a0d0b67bcf5204915c,0x3238365e904833c714bf,0xab5f91940b84b5cd7f8c,0x1d3ef338ae6b2bf14095,0x2d08c9fa7881110d1d55,0x669cff8a312a181aa4fe,0x9fe721a219eb6d2b0e08,0xb188110c0d5df0fb08cb,0xe748bc2d3ecff0c494fe,0x33798c24c2a7e0717f3,0x973e378d9fe1a250597,0x7c6319177f07f3e50023],#[0x19a13f7c141015041ac,0x7d44fc91820d15b71b44,0xfb59d28df8f428202309,0x3123081e84899eefa581,0x20190e6cc9633a9196ea,0xf31e544cc3813ef9c122,0x74cd15f6cc279252692f,0x5fe72d9713397f100cd,0x9139df889bbf813c9469,0x81e8489d3bf113444ad0,0xc32182c7c00b51030260,0x80076841a2f3f9c285c0,0x8bc4d63813ab1f824b78,0x4a083d1935374d861084,0x19b2e1e10790b26aafb4,0xf88066ba66836ded270a,0x28cf47803281cf9e114b,0xa1217afb9089c07f9864,0xe6190a1bcb39c00ce207,0x5881e8485fbd4822701f,0xf4cbd813ac7c0d2a2b02,0xf3f0c89c47b2219dd604,0x53fe022847fc10199983,0x4242fd1f898207a0a048,0xe207a12267ab3c4d112b,0x5c2f112b4140d53f8889,0xca09c09b79f9e18170c,0xebdffd85c07c85ab57d4,0x9b1a4de7e78503619b0b,0x12242de78813e7ac5fdb,0xe103d09133d9f098207a,0x80ee975e7e7861621dd2],#[0xd9106e70291af3f3c30b,0x630921ca98489318d2b1,0xe8e5ce08ab0675cf8ac8,0x848d5af7048a0b42f873,0xffca01243248633f881e,0x7c1d7c11e12e106614f2,0xf0d78a42e7c52adc242f,0x3d091ab5f0821145685,0x77dff861701d90be7f1,0xd1a969721270d4dae009,0xe924fb0245cf21116575,0xa8f6ee384eabe2e39c5,0xbffb0b2186a616c2e5c7,0xae3066589fac90f48a57,0x73752049f434d58428e3,0x590695a27eb243d2563d,0x563fd28d849284be54d7,0xf566671bf7aad2f01247,0x7bff300f0c8d2f6d3c6d,0x3ef14092b13f5921e905,0x5a4d45c214a164d02b1e,0x819be242205cbad28b77,0x525940fb3205471f4f9f,0x490bbc31232fae0600a2,0x8a0cba9f004d2be3ca6d,0x38fa3cf60d38fb3de60c,0x5cdd20e11dbd37867466,0x13022b495ef402c088c2,0x3ac9abde86e215a4af7a,0xdf8803132490b40027d9,0xf9f37b04bd7f85210a48,0x85a0013cf32089c57003],#[0x24b2ed8764290b244f23,0x8fde9409282a1c7fd010,0xe53347a4c83771c690b3,0x1d33440321ee33a5b1f3,0xb2aefa669d2e4cfd8742,0xdff0e188b99c0bfae4bf,0xee69344b6ffc614418ce,0x5057003f9f37b04bc01b,0x404092e95e30282179a0,0x2cfc7e62182490a2b1ff,0x1a156812a3f3025afe81,0xf80148c52553ee249ff8,0x2958892a814eee05527,0x832e22afca370033cdfe,0x5af8d20446129c3acf7d,0xf02c0c269dfeb7261848,0x861f8037d8261d2dbeb2,0x68b2ed8779468db3d04e,0x878004309a6b100c9603,0x7b8146ffcf0118090df5,0x112e12223e77702988fe,0x909ef8e125f1c24dff43,0x48a23d910ceea427a65e,0x69ced011a79b40469e9b,0xb861196d70c232989174,0xeafcc0cb59e4d3d0cf30,0x7fa89214700501fe144c,0x28e00a03fc2898157121,0x8e08923304cb00bc91a4,0x4c267dbfcd6780485f19,0xafca06112614d4ffae03,0x3041692f2e0b2c2675],#[0x79963ecc8996e688d3c4,0xce3c7fa63a0e84a8e31d,0x14412f4b5da1bd35107c,0x870240f8f0981c92bcca,0xa500221c095fd8c13408,0xe06494b7813d18d9a964,0x3e07fd9ec0c9282cfbb3,0x4164bbeffb60b82f085f,0x20b5f1a0b260fa882e7f,0x54e899ab31ab61cce3ea,0x2e5ee286c8d3f4266aec,0xf3cc8399ef05c3e629bc,0x1214e19a4683b83146c6,0x7a8afd4c612a54af0e90,0xcd12f80a0c3fc2cb0998,0x41f5514d0870d3b530c1,0x8d94334a7bd71864a68a,0xa19a47b8d28b2477ec03,0xd231ccd45923bf601c6c,0xdd8850856ff80ea64882,0xed90513387d539073313,0x6584cd9f0e44144ce9d7,0x22ccdc53ae210b3a75fb,0xd0ffee0de0ee688a75c6,0x808eea44efd000c33a24,0xa688f297501b00586bda,0x3ea03583ad714ff5034e,0x260da87c19547a394a3d,0xc89dafd944b4c7b7136c,0x7e166c3c89ebc4589787,0x60f031a5c5a2ffe08589,0xff134235ffc105887f2c],#[0xca05c25b7e5004b281,0x5eaed06403ff928465f9,0x6b31984d381a63875506,0x9a8a1a26b9fd502a4e12,0x17dc44ed7ed0951f290e,0xbaff86092647f812b752,0xd28468f5696d004d03fc,0x549c2485d7e68460b8f,0x28170935fd5da0cb3faa,0x9fffb402a27e22fdff03,0xd050272ff9f209386125,0xf88ef54249103d09135f,0x31103d09135fd0502769,0x7f20245e7f2e80532e81,0xd9339e40997a12bdfb84,0x26fcbe03c1fc5691b61a,0xfe90532dcd0b8da82a79,0x3e122225d6478d9f99e3,0x959eddaa883e681e3f42,0xa77a129030628731afe,0x8489afeb1376a4cea35f,0x40f4244e5ff289aa2256,0x142e12d7baa80312612c,0x445d0913a7fd2d7baa81,0xf025f7dfeea0b10f84bc,0xaf5ac90f48beffea0b82,0x7ff110a96af5ac90f495,0x4245a1e5e43340d3179f,0x283367816128332beb4a,0x81296bf52543d23bf209,0xf5bb32ff0129685cfe82,0xf70bc21485fa61f214a8],#[0xbedfa41d13387c30190b,0xe64539656a0ef5f90131,0xdf8145f0a773229be172,0xe1c301942e1f20517c29,0xb0068df815a5487012d3,0xbc16092bc006a20fe0d4,0x7487134635b0124be4b6,0xaf8983e0f04588e44194,0x917be5009962e6001a23,0x5a167d9fc0c0256ff5e0,0xffc502d2cfe38bfff8a0,0xfeafc40c025167f1c5f,0x108068593c073c70212c,0x9107aecd7e02435baa7,0x4196b45d41960fcb9cfb,0x2d2b805effefb0b2b45d,0x4a5fd0252b805eff3f94,0x3bf028be172fc0a0de60,0x158a8f5bb32ff012ef85,0x5de85c07c8577a1621f2,0x7e1149967f03768dc22,0x602911a49ae01513f117,0xa897812e9fa1c0d234ff,0x355f5fd4ce16ec4baf00,0x2ff0f026678758aa2452,0xeb5092b2221708e16800,0x870262c8c05c238531ab,0xcd2d6bf761226b4013fd,0x13421ff9ebadd212a126,0x5ce23a2384905f310da8,0x40ee2447c56a98151523,0x879600666ea949659c47],#[0xbf4d808d9f19722033e7,0xe212ae08ae9197b9b48a,0x842f3bd054e2724253d,0x40f41085e77a0a9c207a,0xcc72f335064955ef21a4,0xd1c28e04e81b1c54d0a,0x70a605d01c63470ba13e,0xa2009b768dfff9d82152,0xbbf68a4cb5d7884ca9eb,0xce164969eba2018deb5a,0x7f9800d52592f75c7188,0x18e849750f7cc19009a5,0x64eca1f454f99c75e680,0x61e3fcf78403254714fe,0x1cd23f2349787f483e6,0xf8b13e7d4095a9089740,0x5cfa828d3f500443813b,0x44490fdb3e458d404d4b,0x839118ce392374fff310,0x5710250f62005cff1089,0xda3911cf581210ff933c,0x1323545b5e872331d408,0xdf8eaa1d624c748f156a,0xb44c51107a8c57cbd266,0x68d062bdb56f788cad0a,0x8323ef7888f46e894904,0x7bffb0590c80131933f7,0x173fc50262d63de0a35,0x159fa1c84e14cd03d88,0x3d0913f8dca04eef101c,0x12fae7e7981162f92f10,0x164ce129af7ff400f172],#[0x49bdfacf326784b0932c,0x3002117e078ffc24b61d,0x162c2092fd83412139b,0xcd8de715920869dfffa,0xa589fcc2901a13fb3420,0x15aa19c7e3c805a0c889,0x6c1266af76e0d266efe9,0x499dff80d602234147e,0xf4f66fc91685ade30312,0x26698f888c0482348791,0xbdc7f49899839f886a4,0x266cf816124cc0fb8d31,0x9f52e47a00226e784a05,0x82a69c221c6e955e326e,0xad791086c09aaa896f45,0x19846aaa4b88406c4d3d,0xb752c3e5a91a1aa941e1,0xc088ca113da45d72e533,0xd62b188983ef7fc018,0xb1c57c01ad631113b4f8,0xb21344fc006b19e2250f,0x5971665afd8914b23e4d,0x8fa11701d4cb05ac36b7,0xf08464a9a13dbae97166,0xe4b144ce1ff466899bb9,0xd5984406f6c223268a87,0x6aec4d18c1987988607d,0xc75ef11ed4044d8f0e41,0x3314baff71006cfc4b52,0x26603d756515effcc03c,0x4c92bb5cb0019b3dbe2a,0xf02007aa44b9fff89094],#[0x872899d3e9841a4cdbff,0x95f9293718e0806b2f8a,0xc854dfc524c2310814d,0x2965efda18811a4cedc3,0xb812032d7c424b42f014,0x13e3348c5a7f38601339,0x7e61d4cc5a0c093c5849,0xe1cb1019b58f881285ca,0x456808504504f3c01933,0xff1004a98c9535b5f8fc,0x189ac63f80006322262f,0xf58201349007edd8e90,0xcc89f9d58309a0b097,0x8280bc8d3ad141bf855a,0x8a899cdd34c733081e,0xa82fd3e5a242feb5f90b,0xabc2d13c3c040386ab51,0xd459cd9f84b11174242f,0xa536283e7cc4492352ca,0x234acb67de40938133de,0x305b3e34c06fa3a59401,0xf5290046a7d6890a02ae,0x84614900e91d2ca070a9,0x69adb4e601605a47e4f3,0x3af85a2464f5d100c6ed,0x3333a1c4d45ef000c273,0x878ff3da414c9555d57b,0x8006bc12ce5e1f945b99,0xe29377ffd401e80844ba,0x9d8fe26cf79024e3de8,0x21c09dcfd09d3f90221c,0x99cbc2b38d0d2d13f902],#[0x9ee077f3799e8bef84b0,0x7fe28225b61594db8026,0x8cdbfa8bf096240f8801,0xeabeaed5a4d0ffe9d08,0x40a0904cc305c12d3313,0xc34225881e8280b989ea,0x2b017f5988a4b1185bd7,0xdc04b0ffb4088a3c4d2b,0xfd40b0602685958137eb,0xea33cd15fc002920268e,0xa4f7fe0358088d1955c,0x24b043c0508a00faff1a,0x161d7a093d4059c57f9a,0x790c33c3091a2780a3ac,0x2f85c42ac93c02ff1229,0x1836cb46b2f7805432c3,0xc984d207adb93cf38845,0x6bf80061399f3ffe0184,0x188294c8fca4dc61231a,0xca692d8a90dbff5a9e07,0x23d6c09ccd1f850422b3,0x7c7f9f20b040134d0dc9,0x31cce23468280bcef922,0x7dffd82c8748977374c8,0x5d7e2489f3c2f9fa4891,0xe7981522f92e11046848,0x7250b5fc805086e265e7,0x162c2093149fe1120b27,0xca0d0354b6cd1f7fff20,0xaa28c0799324fd49b681,0xb8a024e04cf7c913f74b,0xef89c2808870267bc69b],#[0xadd3c698bfa0a3802b70,0x24560182cd29a05055c0,0x2b050f52a675f0ba9f92,0x2c0222977ff10164fc4b,0x84a264995d301916bea0,0xab81df31a44c5f9fd44,0xb302c8f9949383741aff,0xdd7d4c0d23f800160ec4,0x9e61a8c746f11132b096,0x5f978e044bced524e3a5,0xc12c9d45d48f8cd0a3d0,0x5fd4a124d76bb28667ac,0xc1911303b984e9661fb1,0x9daa49c74b3affa93f02,0xebf9280a8c965dee9ccb,0x12ab096d81693606a9f1,0xc3066f6751ea7cd7a18,0x13d61d13f92a5444e2f0,0x2fb4fc967ef5d69740cd,0x3581ae47bc6bb85925b2,0xbd61770b261796183646,0x8de3788cb298c13547a0,0x16c986d79e9eea02b36,0x25ea7e1fcc08f9e740a9,0x6009ec5a42ff9e560cc0,0xad8aff058f98094dfb6d,0x23a597bda18cc135576,0x2b25cf007d47ad4e4a2c,0xf397471c9b3c2fa8f034,0xac019e70fb159347242c,0xf4e548cf10f70f461671,0xf666cc1ee1c874cc186],#[0x2c1d539e054140e4e0f7,0xd2cd94a587e7e6124eac,0x825650d25a637b678fdf,0x8112b523991f1626c7f8,0x1ca5d2059b31d31b9a46,0xb265e52be70160a9495,0x2d16712c60e98ded98fe,0xc99f278e98d8d19afff8,0x8e98dcf033afbe2c4582,0xf5a9d2248e3a0328ab4a,0x16115acb24e10e99b2f3,0xd13a5313466ff189111,0x3f82b0772574193681ca,0xff00b159c96472f60965,0x459270f719a03e87c9ef,0x2860690fb7868824c10d,0xfcfe15459c97400659f,0x2449eee0004bb6816abf,0x900679ddf14a5ccd0e62,0x7df16228033ce3151c4a,0x52d64887b8c8b3be0d14,0xdc2dd35fa01505034c88,0x58dd69c0d66bffc01634,0xf053b5b2bbffc02c6ca6,0x65f713a0c2e0eb8521ff,0x9985884fe2225c7d35de,0x56c3ec2341649e8c1e67,0x2872540065d4fb08d358,0x38e808a21697bf1e7006,0x51c3a27de65ed779937e,0xdfafd00319c923f8e0ab,0xc427f1812bbccf8e5066],#[0x7dc0682c93d183ccebc2,0x37e3ec2006ab92e832ea,0x85921d23be9081ff0b99,0xff104811144ad53951fb,0x68778840ee850bf73446,0x6d0084f626c66d847c40,0x4166ef0b8d93a4b4411c,0x28b99a3c2694b2c784d2,0x6174c0d45f6978ccb1e2,0x26d52a3f70b239796183,0xfc14b83a1b3ba7306d11,0xe7f0aa2ec2623fe60890,0x70f1b58027b16a3d9de7,0x5da631cbdca001438b5b,0x72c023a598be98186c8b,0x6311324fa7c0f58f249,0x3cfe03c2fc9327de701e,0x27d76fd0741a315046c9,0xb4a1387c16bf402a0a07,0x694a2c1b4af5ae380028,0x1a53aedd019268d31d43,0xdc0655e6708fc2b0aa15,0xa5eb5f80065146193c3e,0x13b4cd19daa405b35236,0x9d077e068143026478a4,0xdc5898b2b41472a07c58,0x65a97703a599665a0bfb,0x1d2cd0593b914b6dae49,0x321262fd0f11623d4bb8,0xc662e12e532e11cfd095,0x80ffb705248ad0405c3d,0xe1583b915d06415fc606],#[0x8c249de465ebef92928f,0x2e42cf3a87e5252ed299,0x150512934653cea45471,0x4689342c9c7029c37fa0,0xe7c220dd11a37f800651,0x98fc47efbf4483744680,0x4232ce3f589ec711d648,0xded9c2bd8a412b3827a5,0x209596489cf846220e98,0x26a68862a3a80a50f9f5,0xc46899be2a1183f9f54a,0xed06b585f7846cfcc20e,0x113fa585672fc6064f75,0x6f8a5330e4e079be0d28,0x71a337c5298bfc39385d,0x66cf4c876b481695fc72,0xbfeb1b40b317fc5b4a4,0xd488a9110a5ac910f719,0x88503f8f252f424e5f8f,0xa12bf70820d0d16ea91d,0x3c9011c3807419e0cebd,0x1e7fc5b9456913fe2dcb,0x2b297a15925668b728ad,0xc5ab838b728ad1cbc3c9,0x95bc2dc2b2c5ba8568e2,0x5e428ed94568e11e838d,0xc48911ea3b8b2ce2c5a0,0x54323c51b7e24488a36f,0xa28000b55ce84529fcf8,0xef5a04fd6ac04b9ffef0,0x28cfff785a000bf1f026,0x52350ef8282001b8e782],#[0xf0f005509323f1e53031,0x378530bcd5f08983f7e3,0x1f8cbc4a6ca3f13611a,0x24b206e35ec0a1be1c,0xe380121c05a8c7881447,0x613066b7bf55b1092e7f,0x8f5406ed8014e17eb6,0x2b29d5689a93f10042ac,0x9242881cff81024b4c0,0xfffa5b082491f738fec6,0xb11f70961fe516026659,0x66df6ef0032348fe0c01,0xf4da024234272f815233,0xc25ef0b40017f3a8135b,0x83182c812685a0003f5c,0xf8fc3c0245824d1ffc7e,0xb81672d03427fabcc83f,0xc3f8282000335d7a2877,0xea7d385b8989e3e0082c,0xc30e04904f028352f2a7,0x611b04524ebfd012119,0x7e5025a34e5fac788410,0x96cfc2b77105a40fc624,0x38a482cad0f0da20da46,0x29ac79a92232cf85a118,0x2e07804c1a58c83408c5,0x1a3fcb8426467beff06c,0x4ffe94f0d2712c47e0c1,0x74790136a5ff66a4f99e,0x8baa2377809f1478035d,0xe8c48b6070b992a1147a,0x1e53112a7711051b2c08],#[0xb7086a2a2289364dffa9,0xf006808fc07612676f,0x37fc56040a0dc4caf458,0x63e5c108289a0c4f7521,0x2fdfe17c020006294114,0x18cc09579ff2181e2cc1,0x58fac02a139049e3f840,0x70268fff5602a2e025af,0x791f8c04b1ff7f2806c3,0x79fff020502e129451eb,0x6be1632dc4def2a2ae46,0x3165a4f060936d3be365,0xc2b645b51a399b460224,0x21a3717f581a3708995f,0x9a17a83891b3d1e808,0x675bf93273327ffc1082,0xbbe98a377ea71b322222,0x3c10e4a6e1f592acd6e,0x7ab7123a7ff161328fa8,0x955aec9484c5d929099,0x39a07e96a20a39e053bd,0xb7cb330a08d09ef7f58b,0x52d83040a354aaf4cd42,0x20122849d6969f5095fa,0xa00c9e30cc26eff8fd30,0x7f0860002e719789ebf5,0x941a30fc29a175f19130,0x1a438df490599b292c87,0xe3ac8a09a43b4402b959,0x93988bf8e30401a4214,0xfc6dc276f7e3f4d40164,0x9e6d6bc810b87e168000],#[0x18095b7fa1d683182a84,0xffe639c349387e16c7f3,0x851cf6ff002fd0f89794,0x67e94c61b1131d1591cd,0xe125763e45520881350f,0x5ebd9257665cff4b6a0,0x64d8aba1403d793583ad,0x8524d1973fd2e06dc49b,0xc160469742577552197f,0x217bdf9cc424680fbf02,0xf7e3e9c682b12fd6e805,0x8c8124efc7ef8a2c1250,0x2c3cf8583004d1bf1fbc,0xb80e466581dff9c2ac91,0xc68248a3f960ca12c6ff,0x6efc7cf110c24a1ffe9e,0xe5131919c31f10644a34,0x638912fbfd42b9119fbf,0x59c0ef3ffc825f3640f3,0x4d9f85f14000c6444e03,0x80319a8eb03ea048026e,0x90d1bf1f5805417496bf,0x8cc10b97b945065d6e6,0xa231bcfa0a2617fec80,0x9332f855c48d7e824b1f,0xca9e3a2e6848d00df470,0x23a69fce9004cf5f6908,0x83ea00f09c933f0be302,0xf60409c044381a3ebc09,0x86be78c692470221c01f,0xc0c9282cfbb3e06495b0,0x758a04a138137607fd9e],#[0xe12afbfc36170bc2172c,0xf5ca87c8489fff05e1a0,0x70a4451ea2eaaeef49bb,0x2507f20018c668b6172e,0xb3fc20a23ec7fac0d1bb,0xda4e6762265ebf10c08f,0x30a80d03f5b88a2381eb,0x97315af4b753725b7cb3,0xa54100671cff4a630dc0,0x7849439fe84794f2567f,0x43264239d9a67a4e079e,0xc0c14984903e99815d,0xf8ccd5f87d48659af8a,0x9e8c0d189128f4cce918,0x604671e72e84248a0cba,0x664ff744c804d05fed52,0x685f9cba188f1f867452,0xafd5e99024a7ead52802,0x26d4b4172e0c0f160695,0x9d0c000fc21e536382e8,0xcc3f82d000c278d3c501,0x7e87f5a333317fc5a0a0,0xb103f9bb4c88957c2126,0xec0a4a004afd35986408,0x70b3e9fe304963226bcf,0x9f40c09a22a8bf2c99a4,0xb52cd10acb7a51340755,0x5a00184f19e2787e609,0x449791d072ed902107f,0x60d13ffe7a4243092b1f,0xca54f4db14cc058cbe04,0xa0b9053b4a0ce9ff035c],#[0x75920d750fbfa2260c01,0x5a5c91d0f9000c63349f,0x8728b0a4e4074845efd4,0xbc00a99b7fd4cbd91c50,0xa99272c74aa20cbe4bcc,0x6205ef4853ba9fd40920,0xaf7a439d90258fea1084,0xf94f27929bb7c7a20cdb,0xb867efcf409a12d0275e,0x28b0b2a13c584ecc609c,0x63787a4d0ca6e9094b63,0x11432ff46665ef7ef199,0x4b19027aed7bb4a9f5cc,0xfa90968e3802b81ebf60,0x5819abf9ace240b34ac7,0xa087a31cdd5809fdf889,0xf5024a8820eff3513488,0x3ec05ec02034af41679f,0x9710f9823017bfd8197,0xeadbc81488a3d0d79fe0,0xc0cdb8fc6a00c4408136,0xc09813cb45e0cc09fdae,0xa14137e4203a0034d773,0x31ff3040fa6242ebab6f,0x3d4030ec0cf5f00c3b03,0xb0330be80d611d2bbe0e,0xccc9f96784c0858f122f,0x47b85c980f5d052a3af0,0xba14b4ce302611fac323,0xa93fc20504cc7fbb08e,0xd6204cafb0b09c817bc5,0xbe53a0380c9a3657bd2d],#[0x2c88d11fe1a056067dd7,0x71f068e2c408d31f00ee,0x56285ae596608c142e4d,0xf2e1969be232e19b1c86,0x65e1e08a75e19993d078,0x861c9e41e181a4f2df02,0x55f0e08ab74ff5d78024,0x65f96bf0204cafea1606,0x9e7e324af9c9f8811c64,0x972329e75f81025c8ca7,0x68a8034ef79f60685d4,0xd3bf9e600c2ba92ebf00,0x5f384227727050e01a6c,0x3568e23c2fc923a96e70,0x3ad997eab4a370bf4f13,0x386dcec9b5411a5a8dd9,0x2b5cc9e32179b9f366d3,0x8592f424eea8ffc62089,0xabc8464f2af2160ceb9f,0x99ba8cfc01945129396b,0xfc5c0cab3f1fc0248b80,0x2033b7e33a15382034e7,0x1010f9e29c199738c538,0xb616f51fb9c940fce290,0xe42fc9ab616f55f39c94,0x8034f23fce4bd242d3ca,0x92f763abc79209352765,0x844e901307ea98fc6208,0xa4ed1f794bd09187aff8,0x286252568fd5f3510d26,0xd1dfa3737024681fa3ef,0xd4bf0204defbf46e6e88],#[0x23c9c2ea7e204ac39385,0xd2fc0812c7270ba9f8c9,0x3477e8904e088d039385,0x6be8f8a4cfdfa2413822,0xe2c983ffc06f154e5259,0x6ecd9ca4c9ee5f80f93,0x5cd7f8dc213c7254fcbe,0x6b9f3123055c6e87cd12,0xe03a89e1353a0af43617,0x985ab58c5c450a9f32,0xa2b77a2784d35d117960,0x134afacb6bf2f93c6965,0x43d5694843c03796409e,0xea3004e480f7ad39b66a,0x3eacda3bf4b535509a07,0x5a9ca9b6560c9a430e2c,0x90260fef087173b3e093,0xc7a68224d1bc21a03f67,0x26ef08680f5fb025a61,0x2fcb0066de12c05d0e79,0x17fc04ad516378010d49,0xe15654ff94125cf0167d,0x80d23f08680f9f90258,0x25c92184706724c78075,0xadff5094586d8362200d,0xd05c925b70067c3f096,0x8c105f080d35f800c5fc,0xb124136159c8f484d55e,0xd81dbacaf2661bc60fe,0x8bf81a23969546a4cf80,0x204aaca78c7c0cf590da,0x25acb448348ff3cf5c03],#[0x24086b51cf8c6e47ec3,0xa172cf134684fb7b8565,0x4b4253953ee710751ac3,0x4677f2a0d29a7f46268,0x19a2388566129949aa3c,0x8703757f0a407d803ad8,0x81fc49158544b025d09a,0x5b213613b2188a146fd1,0x55f846d0cd1e30d89903,0xf5266e4726f62ed6d0d1,0xc945ff1ca494088d0d73,0x9dce204da92e38fd5133,0xaf7012bbf94a832a53d7,0xa5a812e5c8106bf7889d,0xefa5af2950681ff7c604,0x4690fe0b8930cf3a1344,0xd0f5e952680c3b281d39,0x54ceafa252127426889d,0xc34267b108733079ed60,0x869621c2692f4e639716,0x5cb09a23e5d10e133c37,0x96ccd19fc4384cd0de1b,0x4667efa5bd204674e056,0x68af839af0e678d3a5b9,0xa0f5a6cd05ff839af084,0x1f4068acf1e0880cfd8a,0xc3217fadb808cdd8aa0e,0xdec404cfd59684ca5d65,0x717d19abe9c2c84cd5fc,0x4a74666ce054a6ccc9aa,0x4e6cc1e74a7a808d01e7,0xb46780f083cbd9abc0e5],#[0x42d4f9b3c2e9101e27a5,0x9dcf9bbd79210c6eb28a,0x2e197e52457907056967,0x8fb9696b11d477e5291d,0x8eb865f901237fedad58,0x1e2710d0d5a1477c680,0x6504e82d09f8822b4a0d,0x86c6ce1f2826c5067ce2,0xfe19153f70682acf9cde,0x722af81811563234236c,0x7f50c6bc933e30224c70,0x635e4a8bfa04ea792471,0x1f52b08376671c8e2fac,0x588eb130716241711971,0xe060b49f010f808b031d,0x3498d3bc0cc2cf1a77c5,0x695c83a0b3cf8bfa5cac,0xc7022899d3e490d5133a,0x5133abe8c419601b1d7f,0x66870b8ba850a14c2bff,0xa1232f98b32c61c32441,0xc0b2cd1870eccca8cba8,0x50fccbae1e00d8868eb2,0x947e02672d1478133262,0x88ab1f8888b915e22a72,0x9753812a7fa2222f1e8,0x8133f503d127406883f1,0xb091a3ca3849963c839b,0x3f21c046437fa12321bf,0xc0d09fb6884cab67908b,0x7432af9430468ffa44cc,0xe8660b65fb6a4cf9fe59],#[0xf00644ebe8322018bd01,0x8ccccff591095f424ef8,0xc168e31005eb930bd6f0,0x96e15014d19d312a6bcc,0xf723df0985224c063ac4,0x30a782404befa261400c,0xc8e691264d475c8dbf5e,0x7c84951e4d0c3009a105,0x377b7d7834669ff74b01,0x99e3907326267939eb02,0xf5c129cac68afe412ea0,0xb7048534661318f2c478,0xc9a073c0cf38519b5d26,0x6f94c2d2cd1c9f92c20d,0x3427f126216f42b72674,0xe3c8543641004d987e70,0xa04d387e703407e58961,0xd0fca9db599c3c7904f5,0x4e459fbe932b538d48d4,0xbd53c465debd84480ae9,0x33b30a7071e180f9199,0x44bad5cc9760ebe44d86,0x3057c3b124ce09c1bce4,0x88959798b283cff62713,0xa669193fecd89c4cf5f0,0xc6dcca32e308a36fa18d,0xee8c54d1993ea9a32317,0xa60f2a2e79d604787d68,0x1a54732a175b1cc59951,0x1851af1e0f266f1a26c9,0xd76228fc7ee8531227e9,0xf22aa32c79ac8aa8cf27],#[0x27d76228fc7ee853120b,0xa419bb9b0c2d6639684b,0x5ccc9f56d201ccede1e0,0x919978efd8862436bed8,0x861194bd8308cad087eb,0x1e92cebf0dfb16a4078,0x9af99b3fca2660676872,0x2f8d23387a41b832f45a,0x4e9a04cfbcdfe511a3a5,0x3c83551a367d742462fe,0x64a9ed1667c7149070dc,0xff06aa32d27f06aa335,0x458ca5e54a4671782683,0xc04ca5fd1e04cbbff994,0xf042048557e89069f1f,0x7e81805acc1fd75442cc,0x247f8340519b9d3a2420,0x1b3f4a5e05a3323c10b4,0x195f5d5a267eeaf5c1]]
def g63H8 := limbs80 #[#[0x10600e420501c4a00,0xc0300008090a0240c,0x70121001000060902038,0x10040409120140a650e0,0x6080080c330a80000030,0x784c080202854020,0x42a140681c00040387c0,0x4c190080828020602,0x9681a00078040e0400,0x10e88c0007048042404,0x420d0380c22170300010,0x5c060c03804261b038f8,0x90141a1a000081e01000,0x41a0583c050084c12020,0x400020080600070083a0,0x820010080416020000c0,0x804165d00000200a0c03,0x1800000803854020226,0x2110801606110140802,0x1a0504085500a070000c,0xc040206800000400098,0x40a11098541e03028,0x1480002040000012030,0x25e0000c140000804061,0xc0a070b8349e23000b48,0x80c220203818000b0007,0x2814240a1c87810180c,0x6030d0164b0581c0452,0x3a010001c3415180043a,0x18e2060607c42070e010,0x3028142301834140f048,0x5058040a020002558040],#[0xa492802c0803128b8161,0xce2012503c0e020c0000,0xb402760502408000383,0x181434701f00404a000,0x21e800020d010044e0d,0x1007298c000040701800,0x40001020ac1a020094c,0x281886260a8440a18078,0x5059b41e07e4814382f0,0x813038000c4a01838480,0x1c26058200c1b020140,0x828001106818502c1031,0x81806033a004082203,0x22028142e0b1403c1434,0x60111a6400010095c16,0x940c1d068b5001145078,0x3c0c272d8280a08128,0x10800400360a87c16050,0xe0d038505c000f00c0a0,0x434760e800043c940004,0x82c08351d0dc1e081900,0x82a22180080e0102,0x1038293001108140e35,0x1411038001c060083816,0x9c040203810660b0482c,0x650517eb68a2eab5f161,0x250ff90fa91c036d7ab6,0xa4b051528881c0002e31,0x8bca2fc5c4bfa517ca3c,0x935400000000000c,0x5a9ee9e4d82e60000000,0xdc6e1cbb6e80005620b0],#[0x8bcb0000ac92ada8000a,0x5a8196c10000f8a8b21,0x4b3c0000000b94642,0x7e26e2f32a499050ca60,0xad42cdcdf36415879faf,0xc6db10400072391ed5d6,0x55484344217d2c9000c4,0x600675bb9515fe8fbc4f,0xc965c46c6c78bfbe1,0x992772d8901047405e20,0xf0fc438cf587be8ab0a4,0x8d78de50859f44dad985,0x96bc8d9be851a7ae3add,0x6000046187eedbe99021,0xb10037800076ac95629a,0x1d19dc5bc77f6d92223d,0x716576582476a54f63c7,0x7268fc84959bce000025,0xbeca0000da916d880007,0x31b2c243e26b3bba696,0x10f440005b636e7000,0xbaf06512525dd460b350,0x4000000000003a14c94,0xc9cba40d38754d9d61fa,0x15ec6165b2e84e9109c2,0x52e9db8159b84000245a,0xe4ba32aad743f1a20a73,0xeaf1144e9dea5365d383,0x2897ad8c2825bb6e78d4,0x9c8000000025976bcc07,0x8000624a6b653c9ca345,0x740001c96d4ce0001e72],#[0x1170c0002955000047,0x929add7000008fe0,0x841a9e491b52badbc000,0xd9600000007894ec6548,0x82d01280748c00000008,0x9a5ec000000000002a42,0x5c9d35f1cff5c5534393,0x1c151e863,0x163ce6f360d40000000,0x6743d840006734f39a00,0x688cab34000342080009,0x9f91b00000e5755a7817,0x67e0719b0190001ec,0x7a03aa673757de60f850,0x700003d463a40f7a0000,0x7da000000000000000a7,0x766200018bac5b900007,0x1112e38400000000000,0x2509e5c000000,0xf2be769b89db2c881be0,0x56398800000018420863,0xad4000317f5521b1c00f,0x11b73e853c5488e024ab,0x1535680000001c46887a,0x187924232496a9000168,0x90e7749a61a51c880006,0x980007c745126f5c08b3,0xb8f8c6bc3fe69ca34bfd,0x7c8a0001edc02ec68dfd,0x8c72fe3b318e6bda7f21,0x2a800000002c72bbe2ca,0xef78ed6cfe6709e31aea],#[0x30106b0ace4d134ddc71,0xe960000608a9c8000127,0x26e4e4926ac0cc600005,0x291070000501400026ef,0xdbd400043ffee03cd,0x98b5dcdc00037ae80000,0x8ad5d00007a5e84cc91a,0xad9ab33f47daec3b1ef4,0x8f9bad6322a1325c27c6,0x2cab2c3e3a13f903c5ec,0x1dcdcf5f00a9a4c492,0x1619fb420001da300000,0x12e28a57536d424,0x2b4b7180000b8f000117,0x4d24d10acb7c0005767d,0xeec496157900aa128000,0x76e826800040d940065d,0xa241db5fc2ec3bf80004,0x738550000264c4b28a09,0xaccc03c0000000320681,0xdc05d2425e055b98226a,0xdafdcd800017309a62,0xc500002cbae2cd000000,0xef3fec7d8b6c0000000d,0xe7844eb56a2ffd9797aa,0x1c2b95aadd8000535f43,0x3beb0001cff8f8554e8b,0x787d514ffbe73367a5d4,0x67896f4216fd25abdfce,0xe42a0002c695b7cf,0x6697ee0a3edd374128cc,0x6b2c6d3b07923b6ee08e],#[0x8000eedffe00b7e250e3,0x1c659b080002ad1,0x78638adddee2ad735000,0x31e1970f3bfbc3e1aded,0x34000641ee12a00029cd,0x816b1dc508a8835ec52a,0x80008d22000257a1697e,0xa00000000000059e809b,0xb32ce1a80002d5768,0x1ee500000,0xda5fdc41d46980000000,0xefd36f68000e7cc0d,0x6812000000016148c1f0,0x2c319ced920f594c628,0x79146fc000559b6dd800,0x70b1096800012c846a3f,0x2ecc1d3ef82e6bef831,0x1bc800000000c62600,0xb536902620d000045760,0x1e41e47800008639169,0x170d600cbf0000000000,0xe460493d43534a7d1699,0xd000076b443299d9680e,0x61a0001ba979d900000c,0x33b0049c0002f0d6756d,0xbc58a0f0d3b4fb8000,0x96050d0000732d000000,0xc432e6e9f8d400000009,0x9de25e10a9582db03637,0x11e000206b3ba14c0259,0x8000000056b451e00009,0x59c826ab55e748000b99],#[0x2dcb8e149180000001bc,0x5500001595665900001,0x765158c9869fdf713159,0x2f1fa85a95c119,0x5747ce877c8a3743f580,0xe67640cf78e4d955c000,0x9c40003c2b80000000d9,0x251a462efabc0004e6b9,0xc6919972c89cd49f459f,0x27ff47800062da6e4e71,0x119bd2402ff5f8e6ba79,0x134c9c5da0001b817d73,0x919b1f1f0e1634fbc85e,0x80008d0400038cf20fbf,0x40fd3ab4ddccc29,0x1d46c000000082a600,0x8000000114d6ce0fa130,0xa5caa9fe02e,0xd8400016e08000aafc00,0xb6113db4a12632c70f38,0x280007c5d6983e5bfc0f,0x3358da6780050ad85dae,0x26b10000f68081952371,0xa800041166c8a0000000,0x7d503c1f69200016a,0x1af19c280,0x8400000547a4c0024000,0xaebf9b4e6900003b0f8c,0x18759396c8ea06280008,0xb7c8c318500014452eb7,0x14d27a03123df3cf12,0xbc3b8499f135f0a167b0],#[0x2d41800000000001ea7,0xa27afd40ca8000000000,0x7f603763a75ab3baece5,0x26f0ed69b9ae997e35e2,0xe2747267cd0000853b7b,0xb97baaf7b3b293916f97,0x1460800090eea19646b,0x115d957dbf77dd600,0x95fba74bea9800000000,0x8f93700000db600010e7,0xaf90752839b00012e,0x2f1ef0d862c279e3e3c0,0xcc90200008e51d800199,0x990a23ac5174f40001b8,0xc68700008466d8706314,0xce48f0b71f1aaa6729b6,0x4fc000035cb0000e6,0x9ae60000e0aa1a40,0x7800057a7a6d6b830e49,0x3adfb5953912e5,0x31a300000000000302c0,0x31f7100ddc9b80000000,0xdce000076ad9f1b56f10,0xc59e9c0ef163f1bfbcf6,0x200006bba000192c4c26,0x1682041b702bdc52ca,0xb3bf4b7984dc1bb2910,0x75617bb96e6389616a4d,0x1969c00008d3892677,0x556b848094279c589ce0,0x4ee638be80ec63d64000,0x7ecec3fa5fc9c776ccda],#[0x8c2717642ea427c1cf2c,0x342ca4151b3f2c64b165,0xccd2f700001963b45bc4,0x55b8da9bf9e80005,0xc6497949c40eb5c000,0xaa800001a43e64000000,0xa2c88fb1e5464ace,0x18000347600002e62c9f,0x157b7c8f91f827e9d7b2,0xd017dc10fa1274d2d5d9,0xa7b9264ca57e69d20ab1,0x1bb3db69eab85dedf2,0xf68c6f1a00027a80e720,0x733bac011454ecfe03c8,0x217b70000a2b3d6,0xdec5bc460002b1627570,0x905d5a0bd9d06d81264c,0xee40000000000036efae,0x61838b68e24a639fa8,0x2376a48186aab080d3a,0x89c812c0af9b95fcde00,0x15bccc5f4d2f82b46216,0x1233ab48ce60808f30,0x16ab00001be0a52800,0xca86875c528a31eec4f0,0x4eda3a1bc1b9c000338e,0x7a4d62d2a500000b58b3,0xd2002646b7eaadf73498,0x1934b5109fdf4ca4d14b,0xde16b106c1c7710f4840,0x3d7153e6589c801626df,0x390ad0ccced7a87c9a],#[0xcb27eb25427a06b61600,0x53a63baef00e8dc0000e,0x4dd0f2d3934a8e2dc000,0x9de3d0400059b01654fd,0x2287abfe67d406da21bf,0x2c97b43821c80001f08,0xac200000002556c81400,0x9e9f6a3000000000000b,0x300001d86f4afe13ec2a,0x548b4ba288c47f46c395,0xc652adbc74e95e6a7106,0xda8306bc0ea2ac149e59,0x78f4c584532d066b9202,0x78ff94f1a7780002944f,0x30f61c1e4fd120001cb4,0xd2984771a7e2694bfcd9,0xd4e000000000c6464d15,0xf49f90ede5c83e36a3,0x1ac566228000d1a000,0x64c42100e32c000176d0,0x2b603f00756eb67f590b,0x40e2a725d60000bcc3f6,0xbdf5f1b51b17d9d0,0x400000000ca8a0000000,0x62000398c383b048406,0x437dbc949c2c0007e7cc,0x40023bedf2f3cc2f0000,0xbe0a528946c0001ef,0x2a9b838d383543f78ed0,0xf15effe9900019a83471,0x3d2107203416718052cb,0x80002ade56640006f18d],#[0x1ac4c80007893a1d0c59,0xa388086887e2e1000019,0xf94b000195bbf8380007,0xafa108000c05072fb266,0x2c15753182ebda070012,0x6bf2d2a9194f833d,0x2b708000000108bfae8,0xdb180131635813a00,0x3e75bf1e0001b5b00000,0x4472200000001ef9e6da,0x69697735a91f1acd89f9,0x2583528739c3f5accaff,0xa38459c51663c7d0077a,0x72454501a1df6289e999,0x696d17402c28d1f8cfdb,0xaf9b235caa0b79b71c62,0xa2000010d8b26fdb4dec,0xd9e2a609741c00034dec,0xddc737777c67e49dd5ab,0x9a17723673a8ebaf21b5,0x20f3239400072200,0x18f90c1be70cec02c11,0x9b570ffe6cb31f743a00,0xe732c2190623f570cc95,0xd05e669f21b,0xa4e6c0400049c2bd7400,0x4ea7000000020f317740,0x1adaa00007a3b94fd9e5,0xe050e400000400001e6,0x51a695bacd612661a7e6,0xbd9aedb50e68ff605aa9,0xab6000000048c08e8a0e],#[0xe531a1146b1f8cceb825,0x616a1fa10942e0000e4f,0xc818c224105609703d70,0x518bf76cd606037cd02c,0xb233eff3b33fd48920c1,0x8d228728f186a860749d,0x4ebfa3e0e9708dee6b80,0x4300b2d9f0885d1f4277,0x8aacd79294f1388ab002,0x9a32c58d90f13bcd95b2,0x7fc1c625845a5c3c13c4,0x8f5cb500002306000117,0x26e05072834555138252,0xa82f73f4f0bcb2b57799,0x6f07c193897910235885,0xec30b971463e47577adf,0x486046ad1b4c81bf67be,0x1b06b3b6b9582da9aa94,0x3b3307680001588f8f54,0xedb843abf1f0d39aa466,0x4f78f0cef00d7c853f53,0x80006cf00fbcdf4d1f4a,0xa1f3d528daa00024f2,0x8a60001f9858c6f9adcd,0x167420f6c334e1376e69,0x71e3709a04db1874c000,0xd17fc240000f2fcf4412,0xabbed579b8e4eafd69f5,0x88b01a218f4b40002230,0x9732603261800000012e,0x8000581b6e04000207af,0x861e102c9133baa96af4],#[0x3df9000a19b4f36e2e1e,0xc0ee184a000141af846a,0x52e1533689cffc7d9d59,0xb9adca86bc98644b13b1,0x80004f24e1c40006554b,0x3b0426a633ba297ada82,0x6f7baf652b6688971b0d,0xc90078cedbff522c4884,0x740002f4a012d8a87976,0xf38333d0ede8dc0000bc,0x5556949665c1900c447c,0xbb27b06b23aab7bdc198,0x6fe723dac74ed7d4914d,0x5336501db73203b487da,0xd98c9d68b52dd5ffe5e,0x9d260929f0e5647291fc,0x2c21ab3335542121774,0x18083301ae38690916dd,0x203b4c0f66465a653caf,0x5939e8cde5e86320c467,0xb0ee72b7ee3dd9d1bf36,0xd44754f9cee35d385634,0x457833fff6df2e981ba4,0x69312f130e6454c0c1c6,0x8b2795d0b9712e6149a8,0x92f29a108b9cb183f4c2,0x9544c3cddab1b8c95de2,0x4c02af7a7d76d9a2b076,0xbcffcc3789426f0bb672,0x2cef9db6a9534c26d788,0x8e174d0977d3d4d251e0,0xc484f54114f3da219328],#[0x84afac045fe9203a50eb,0xafa628503779117f3a33,0x9b5ea0e78c74ccbad4d4,0x58b9b220b5699aa3db4a,0xe0af93c5328c4357939e,0xbf4eabed425e7c56c22b,0xe306d1440dc4879d0183,0x777796f35bc088266a05,0x692a50f000009e0f44a0,0xf76af377cba9ce5589ef,0xb6187600000018ea0012,0x2ca70e1c4ff07286c2c8,0x2b8815142f7c415888a9,0x9f88294cb2a1d1f244ca,0x2b340000c1435966c027,0x9e077bbbce28b1c6d626,0x27af8000abe177,0x3bb800000002e2dc7a00,0x5ea500000000095e8000,0xdd40003e5b800018344f,0x25a90ac12a089df80002,0x78762df4f141d08de75,0x87485ad986000085176d,0x313190cc00036ae7b883,0xfab4e0000583200118f0,0xf46a230a2e318,0x528db84ae2b56e50,0x826000028a47c08000,0x116dbb690000502800,0x212ccc80000124745cf0,0x19678ea2200011d94000,0x66fc6d40000000655062],#[0x2983ea2fc63400000006,0x9a70b000000000000fb2,0x3f81406114a1ecebb6a4,0x935a445c0000d774b5b0,0x5000073940000e6ca9e9,0xdde123607e404ecd37a7,0x2aec0000175800000000,0x400000000217369d4581,0xc7600013554cc6ff472e,0xaea06023c96a5a47e3,0x15aeca70ceeb40d44000,0x5f45d4673f7c5a00018d,0x3ec980003,0xf8000601c0000000056b,0xde40003435800014621d,0xd68a96d922e939f78f15,0x3d7f80009cd00ab8443,0x3a1c49374f0000e43200,0x9704528e00000006eaf2,0x353580002adbe29eea8,0x824000064db444a29400,0xd480286dcfaad8a24bb2,0x858e0614e0d67cf6d671,0x6412475e41885,0xd9b60000000000054310,0x52aa1127ac2edaaee3ca,0x2740001b1d00003c1cdc,0x518a00010ada18dc5eaf,0x7070599d500008a4265b,0x72ef88afc64df700002d,0xb2c834be94c837d911fc,0x95d3994ce83f7861230b],#[0x871000002a9ee5bb2,0xeb36b87e1559e690,0x674d0000276a522,0xca80002e95246818d400,0xcd4959c17693787c2c5b,0xdf0f58000000126ad7cf,0xed0644c0000000a6e46b,0x3d448da136ab49b39b9e,0xda3adb8236ed78624000,0xf2f5171720f051d50143,0xd50b39e000fc378d4959,0xe1529c342007aa93ed40,0x15a72d728fc3f94089d6,0x2610001e5f7dfd493d9,0x52d863020000000,0x1992000028012b6600,0x518c57b45410,0x10d8951ed0d760002929,0x15c6793312710000cd,0xa67a9a7400052090,0x5b99b0000e42507a8000,0xd4eebe464a7f1f00019b,0x6cc000004a640002b7a0,0x3e8e9e6bb01c000,0xdf0302774f0000000000,0xc01b05d20003a4ef9123,0x7f4fbbda8fa2c446ef32,0x2e980f13033c01af31a8,0x432f732249740000f0dd,0xcc2fe347b0000191c000,0x2a3959cc724a33f4b,0x2309da0943dc00079660],#[0x288a9d6718296d80d2f,0x17d220a93cd596fc2bd5,0x393b7cc78cc5a2452855,0x728ae86800000e0351eb,0x71c2b00000000024584e,0xd30e26b7d71f9966,0xa39d53eb9707c329059c,0x820980bf7c291755d13e,0xe5a23da9f4341c1d58cc,0xef8a0d787b0bc458a52a,0x1f52b0e72599e824d4c6,0xa571000138bb00800000,0x6000012b9ff52d74ae7c,0x12200008a873857cf3ca,0x7b2e2]]
def g63D9 := limbs80 #[#[0x104400c8310c02108010,0x4811014c521445010c42,0x50d42505404c9314c121,0x886208415454d5254550,0x9424390a41902328c630,0xcc321c83109525394a51,0xd4750d0f42d0740ccb31,0xf7efefadebe7f54d4f52,0x650016503fffbf7efdfb,0x64b0564b036538065382,0x65b4165b47643c4643c6,0x65440654476444464442,0x6008d600826518165183,0x640856408a630896308e,0x64105641026508165086,0x65cc165cc26584165846,0x654c0654c26514165142,0x65d4165d426520165203,0x63011630116201260002,0x6339063393623aa20392,0x627516276a2076920753,0x63752637516375063753,0x6005263b1163b1162b13,0x613d2630516305161052,0x6379161793633d0633d3,0x61b53637926379163790,0x300e9300d263b5163b51,0x61451620d1610d2600ea,0x618126082b3081362453,0x4119162bd161bd162811,0x431916219a4219161199,0x6251361512631916319a],#[0x618db418d36351063513,0x638d8438d1628d8428d1,0x63c9162c9161c92638d1,0x53291622955229263c91,0x62613616126329163296,0x63d9162d936361063613,0x630926009554d9263d91,0x63410634106041263091,0x627d2607d36341263411,0x63b9260b92637d1637d1,0x62125311126011263b91,0x324a7314906049263111,0x31852608536249f3249d,0x32c1260c116385162867,0x621d2601d162c1f32c1d,0x4255060552631d1631d1,0x635506355b435536255b,0x63911639116291260913,0x43cd162cd942cd260cd2,0x632d1622d263cd163cd9,0x62a1260a15542d2632d1,0x62dd552dd263a1163a11,0x6015263dd163dd653dd1,0x604d2631613215161152,0x654d4654e3324d3614d0,0x638a3328916189260897,0x612126021161c5260c51,0x61590605926321163211,0x61952609536359063593,0x61d1260d126395163951,0x633165331263d1163d11,0x53693616906069263311],#[0x61a5260a536369063697,0x53e1263a5163a5453a51,0x6025554e1263e1163e15,0x605d9432516225161252,0x6199260993625d3615d0,0x61d5260d5b4399162991,0x54355533516235162d51,0x60a93626d3616d0606d5,0x62e5753a9162a9161a92,0x63713627136171060711,0x62ad161ad260ad363710,0x63e9162e9263ad163ad1,0x3002e2002c2001263e91,0x3202e4002c4002e3002c,0x4202f3202e3202d3202c,0x4302f4202e4202d4202c,0x213af4302e4302d4302c,0x413af313ad313af213ad,0x323ad323ac323af413ad,0x423ad423ac423af323ae,0x433ad433ac433af423ae,0x3076e2076c2076f433ae,0x2176e4076c4076e3076c,0x4176f3176d3176f2176d,0x3276d3276c3276f4176d,0x4276d4276c4276f3276e,0x6276e5276d5276f4276e,0x4376f6276e6276d6276c,0x5376f4376e4376d4376c,0x6376d6376c6376e5376d,0x6476e5476d5476f6376e,0x6576f6476e6476d6476c],#[0x32b2d32b2c32b2f6576d,0x42b2d42b2c42b2f32b2e,0x43b2d43b2c43b2f42b2e,0x4006e3006c3006f43b2e,0x3106d3106c3106e4006c,0x4106d4106c4106f3106e,0x4306e5106d5106f4106e,0x5306f4306e4306d4306c,0x213ee5406d5406e5306d,0x313ed313ec313ee213ed,0x413ed413ec413ef313ee,0x423ef323ed323ef413ee,0x433ed433ec433ef423ed,0x407ae307ac307af433ee,0x317ae217ad217ae407ac,0x417af317ae317ad317ac,0x517af417ae417ad417ac,0x617ad617ac617ae517ad,0x427af327ad327af617ae,0x437ac437ad527af427ad,0x537ad537af437ae437ad,0x637ae637ad637ac637ae,0x647ac647ae547ad547af,0x657ad657af647ae647ad,0x31b6e31b6d31b6c31b6f,0x41b6e41b6d41b6c41b6f,0x43b6e43b6d43b6c43b6f,0x210ee400ec400ee300ef,0x310ef210ee210ed210ec,0x410ed410ec410ee310ed,0x610ee510ed510ef410ee,0x420ee320ed320ee610ed],#[0x520ef420ee420ed420ec,0x430ee620ed620ee520ed,0x540ed540ed530ef430ed,0x2146d650ee640ed640ee,0x3146f2146e2146d2146c,0x4146d4146c4146f3146c,0x4246f3246c3246f4146e,0x4346f4246e4246d4246c,0x2182e4082c4082e4346c,0x3182f2182e2182d2182c,0x4182d4182c4182f3182c,0x6182e5182d5182f4182e,0x4282f3282c3282e6182d,0x5282f4282e4282d4282c,0x4382e6282d6282e5282d,0x5482d5482e5382e4382c,0x21bed6582e6482d6482e,0x31bef21bee21bed21bec,0x41bed41bec41bee31bed,0x42bee32bed32bef41bee,0x43bef42bee42bed42bec,0x211ad211ac211af43bed,0x311ad311ac311af211ae,0x321ad321ac321af311ae,0x2152d2152c2152f321ae,0x3152d3152c3152f2152e,0x3252d3252c3252f3152e,0x218ed218ec218ef3252e,0x318ed318ec318ef218ee,0x328ed328ec328ef318ee,0x21cad21cac21caf328ee,0x31cad31cac31caf21cae],#[0x32cad32cac32caf31cae,0x322ad322ac322af32cae,0x432af422ac422af322ae,0x3162f2162d2162f432ac,0x3262d3262c3262f3162d,0x319ef219ed219ef3262e,0x329ed329ec329ef319ed,0x32dad32dac32daf329ee,0x43daf42dac42daf32dae,0x430ad430ac430af43dac,0x6042d6042c6042f430ae,0x4142f3142d3142f6042e,0x4242f3242d3242f4142d,0x4342c4342d5242f4242d,0x5342d5342f4342e4342d,0x6342e6342d6342c6342e,0x6442c6442e5442d5442f,0x6542d6542f6442e6442d,0x427ed427ef327ed327ef,0x437ee437ed437ec437ef,0x41bad41baf31bad31baf,0x43bae43bad43bac43baf,0x54bad54bae53bad53baf,0x4212c4212e3212d3212e,0x4312d4312f4212e4212d,0x414af314af604ac604af,0x424af324ac324af414ad,0x524af424ae424ad424ac,0x434af624ac624ae524ad,0x544ad544ae534ae434ac,0x3286f654af644ac644ae,0x4286d4286c4286f3286c],#[0x60c2e4386c4386f4286e,0x32c2f41c2d41c2e60c2d,0x42c2d42c2c42c2e32c2d,0x62c2e52c2d52c2f42c2e,0x53c2f43c2d43c2e62c2d,0x64c2d64c2e54c2d54c2d,0x321ed321ec321ed65c2e,0x3256d3256c3256f321ee,0x3292d3292c3292f3256e,0x32ced32cec32cef3292e,0x322ed322ec322ef32cee,0x432ef422ec422ef322ee,0x3266d3266c3266f432ec,0x32a2d32a2c32a2f3266e,0x32ded32dec32def32a2e,0x43def42dec42def32dee,0x5316f4316d4316f43dec,0x5416d5416c5416f5316d,0x614ef604ec604ef5416e,0x424ed424ef324ef614ec,0x434ec434ef524ed524ef,0x544ec544ee534ec534ee,0x644ec644ef544ee544ed,0x438ac438af654ec654ef,0x548ac548ae538ac538ae,0x60c6d60c6f548ae548ad,0x42c6d42c6e61c6d61c6e,0x43c6d43c6f52c6d52c6f,0x54c6c54c6f53c6d53c6f,0x64c6d64c6f54c6e54c6d,0x5322c5322e65c6d65c6e,0x4332f53d2c53d2f52d2f],#[0x5326f43e2c43e2f4332c,0x1b002400280002c53d6f,0x264042807200c001300,0x5020003ac06b00c3015c,0xba016202a404fc096011,0x74c0e001ac033406180,0xa046e088010681f903ce,0x59029b050e09c812f024,0xcb018482f105ba0b181,0x907940ea81c08362068c,0x4e0477089e108c1ff83e,0x155829f851709e0132c2,0xf0c2e17cc2e285a10ae6,0x7786bc0d2a1998326862,0x1e843c187620e941c703,0xf10ac20a840307e30f84,0x8788e211782294443086,0x26a44c7096d12a0249c4,0xa14aa28c450909f21398,0x890af915982ac05498a7,0x2f245d10b8716bc2d085,0x418bc30c46090bfc17be,0x970d1419dc33206520c8,0x37586db8d931ae635286,0xa1cfc395c7160e0e1bdc,0xa80f351e243be87688ea,0x40187f48fc41f363db87,0x22160423c833904a204e,0xb8914f2260444c87710d,0x48848fb11d9236a46308,0x225b04a98945926f249a,0xd5138426b64cfc99112f],#[0x5160a1d140927dc4f489,0xf29fe534ca59949428f8,0xe815b42b18558caa1951,0x59ccb29962d2c0057a0a,0x52e765c34b7396c52d2e,0x1898032fba5ee8bca176,0x63fcc6c98ae31046170c,0x5338e6680cb99948324c,0x461a6834866878d0119e,0x6d7cd981b0335a06a9cd,0xe37e46f24dd31b8f36f0,0x671cb539107180e1b9c0,0x75c0ea11d1e3a0473a0e,0x83c4c7824eee9dbc3b2c,0x7c1ecb3d487a00f311e4,0x7ee4fc51f5d3e747c4cf,0x740e481210101ffb3fa6,0xaa212e420c83b5060209,0x88750f821ce435e860d0,0xc45c88aed14ca2774496,0xc4236f468e8cb918922f,0x917d21a240447b08ecd1,0xb4a1e93ad265a4ab4918,0xf425c24b3495fd2aa253,0x9b1134ba66d4c8c98692,0x4f089d913a2a71c4ddc,0x2e282e501a9fc13eaa7b,0xa44547528d0514aa2014,0xf53faa72d4cca9675264,0x96aaf15578aa0d5262a1,0xaf515da2b9356d2ad255,0x15934b1c56232c1e57ee],#[0xc3ad5d5a64b41966facc,0xb9bd721ae135bd4b6e96,0x95e32bbdd76baeb65d18,0xfdafd15f60be317b0af3,0xc29d83eb05d6074c06d7,0x162a0c4c188430ee6186,0x2c322263eac7158cd317,0xcc29973b2c6654ec9ed9,0xa6778ce5d9bcb358665c,0x4534706892d0ada00b3d,0xd52da98350969bad2c9a,0xe6c00d75dad435866ad0,0x66b6a76d08d97db1e361,0xde65bb737436e3edbe5b,0xf7104e135c10b7e96f82,0xa7b9317210e36dc5fb89,0xe809ce9b9b87322e5adc,0xf7576ea39d38ba4d7460,0xd5bb8876c2ecd9d83bad,0xf1dde283c2a7808ef5dd,0x27a2af3e5e6e3cb77930,0xfb3dd97b56f619eac3d3,0xfa2df383e4e7c68f849e,0xa7e74fc25f6d3ec07d4a,0x36c03d8010ff51fd1bf6,0x4c208740de815d02360,0xb8437079e0d8c18282c1,0x91c2f885a50a82139424,0xf4e1d9c39386e90d161,0xf891311a6227c42487fb,0xb445468a4113ee26d44a,0x183a2f5c5d18b69161a2],#[0xe8d491a06332464a8c5d,0xc0c74b8e471bf236dc6b,0x20ca408c7f58fa91eaa3,0x1919f22da446486b90a5,0xcac97992ad24ea487c8f,0x28fe50e4a0093ab26d24,0x595b32aca54b4a8094c7,0xcecb7096832c965864af,0x31c2621cc1b97e72f1a5,0x49a6934366724cb99919,0x24ded9b9d368e6bacd5,0x3b3274fce799ca938ae7,0x99f3d3dc27a44f1e9def,0x385052a05f40427f7cfc,0x446e87e50e0a161423e8,0x2a3ab46ba8c8d171a291,0x585288a4c148ce90bd1f,0x4de69afd336a60f4b5a9,0xca8294fe69ec53bfa739,0x61d4a8a91b51bea27d42,0x564aaba5545aa3d53c6a,0x2ac8d58a6b0455e0ab67,0x9156ffadad5aaeb47d67,0x5f02bd15784aec35d0eb,0x7b0d7612ac14d808afcb,0x9dd90db1d56326c54588,0x67a6cdf59a2b3076576c,0xab5696a16d28da2ab417,0xd45b81b6b56caed7f5ad,0x71bae235c1db7ed6f32d,0xcba797452e76dcbdb927,0x135e02bbc97702ecc5d6],#[0x7b82f5ade8dbcd9792ef,0x9bf2f7dbefa5df23be07,0x376046c04b8002febdfb,0x846b07a60d4c161824b0,0x7c3a786cf0c5e163c287,0x56e27fc4c788fb10de1f,0x8dff1a7e32dc5eb8b571,0x1c881906b1f763cec745,0x926506c9cd92fb248e47,0x97672dd659acaf195332,0xeccff998b3246627cc01,0x97e711cddf9b5335de69,0xa0073e967b0cf159d773,0x8d195a29b4406851d051,0xc1695ad27da48b48368e,0xa8834fbe9dbd381a69f4,0x6d5adaaaf53eea63d489,0xe2eb9cd6fbad635976b0,0xb2036306c3dd829afc35,0xdda29b3db66c6cbbd941,0xf3edc5db3db5df6abed3,0xba8f73aee4ddc5fb83b6,0x6ded3bd177926ef5dd9d,0x22f021dffbbf777df6f9,0xc41b86d70b1e117c19b8,0x2e397c6bf8c4f165e269,0x60f29be4f7c917912f1f,0xce239b1f337e613cbaf9,0xbe8b5d09ba0373e5e773,0x90f4fbe9a7d2d7a4af47,0xd6cfaccf57aeab7d503a,0xecabd8e7b0b75e9eb8b],#[0x91f6fded97dab7b46f67,0xdf0bbd0f781eec9dd33b,0x7f0f5e157c157808efcb,0x83f921f203e37bc5a789,0x81891742244502220284,0x4022840c899680850587,0x8e25c1a0c4218b164580,0xa48fc0a506a008010642,0x9844900a94a103128d1b,0x918c140b9a41189a88a3,0x4315178e8a0dc3910719,0xe8618b149a12d9a19223,0xd43b32473621cd9a1cc9,0x867e08c7a2871714393,0x1c4b4638bc218f610e2f,0x311de847a2846cc8cbc9,0xd991ea8a1de247aa2877,0x9bc23d5843bc88f4690c,0x5cc48bc4865e48e0ba31,0xe2491c918e7210c33848,0x2813e8092f824ce40c65,0x6ebc44f75b413dfb8f00,0x4e3fc41200484f2d10ca,0x225d25bf0ed04e6787c4,0xecf9653800b2f978194a,0x687eb2788a43f59ac00a,0xdf594c88a8dcf9658941,0xe75e268012037564f415,0xc80e00a8f0dc44e6ba81,0xe10904aa7f3c80283fff,0xc75e022f3ec488a57367,0x9d100589aea083c24c89],#[0x6482607fc85122abfb73,0x65fdf1e9888ae5737739,0xd0503fd00f786fe428c1,0x61cdf0273c3588a2fe0d,0x517788ba0aaddcd7c4f,0x4103e7e14000934fe790,0x9075130708c63a82037d,0x329000956f91e401513e,0xff100a09206fa41c7ef,0x4c24c7c3c802838f7093,0xbd4c108243ffb8d00a8e,0x46bf6244515ea65053,0xdecc4abf9a340479fe2f,0xa00249267093135dd09c,0x832000951be1255e7e49,0xc905520924af904e3f9c,0x79ff528008f13b889f7,0x3c8ad74835c9ba09d8f8,0x1908f3fa8e1600481f10,0x38d4123d3f2f413eaf88,0xfe306808f3fc5d8023ce,0xac009106fe84d4cf3128,0x11ea091e99f7a09e7511,0xbd04e4fd010dae745967,0xfdc84c01654d6c45279e,0x5e1ce705578534988ac0,0xe1ed682a0f0a4e64546e,0x8273e7af00504ef01173,0x3d928009553199141eb6,0x29bb1154d9895a412471,0x8a2cb33e04f641e228bc,0xc9e00aaa6bc4507cf5c0],#[0x3c71102359667c09c0fd,0xa0a0bc3dd80527e5204d,0x3e7ada0a2cb33f135907,0x460f9913c0159eb6827,0xc76005619cba275feb28,0x6c0279c2f7540049b3e1,0x954ed889c9f7a098f9f,0x944cb0934fe85e2e80,0xb889ce0ee44e3f9c8320,0xfd58023ef920aa412493,0xc4dee84c3f9cd1808fba,0x4dbf1ab6b4004a21ecc4,0x759135d0f76014de7962,0x12294dd88a683df4145,0xa091e9f9ba09e7f51e68,0xc62c0121b10ad59671e2,0xddcca134fd759c023eeb,0x470b0024186e92d9c312,0x9f97a09f57c40c8479fd,0xc97ce4b88ae71c6a091e,0xd5f2a27011edcf6e228b,0x1ff21300a8eefa9a1622,0x5d180242e7b9142004a2,0x463e82847d845f908e39,0xb9ca9049bc97ce4ba0ac,0x73952094be544e023ae7,0x42c02a25fa4958058b37,0xb3f00505e7cee00a6dcf,0x74aa0926dfe677741493,0xfe3e0203fef06014eebc,0x6008e6b2704e43932276,0x4ab823c7a550019a6bf5],#[0x979f29300a887b3134fc,0xcea4e0ab7f0540a10025,0x6709775e3a6821255bfc,0xa77604e3fa4187f50318,0xf665cc4c3ffacd8047bf,0xf5f117c11c7af893548,0xf8fac880244d7c238024,0x4fc312d3f284a619c259,0x849069f867051665cc4d,0x453bd55c0ea3eff9e008,0x1622a27677114179d9dc,0xe6ae08f607f02633f33e,0xd1241370e84e6bba1305,0x849247fe6ad123cf04a,0xeb3ba0aac2fe12cfc734,0x791f0e82bb759dd0521b,0xc3e0269fd471a0049276,0xd7b405819b7557038120,0xbfd74618242ffd691823,0x975eb01099d7f861c48f,0x5261e4259affa300924,0x24ecf40e00917dc7cbd,0xb7d0bd1e01247fb3d488,0x241f5cf284f3d18891,0x2471ffc840048dcfe31a,0x273e3fca09f7cf812001,0xa128fd7813011cfdf922,0x3de0db62dc8c17312997,0x95b45d822fdf35580a9a,0x166fd520d120fe3c8d56,0xc74c0273a16d1d3827b2,0x3827b80b4e3a704fe951],#[0x9dfbc2ac26e234a94d1d,0x280b2fc18424a6873334,0x4e83015bc4c826ffe0c8,0x7b7c4d0a549644c2ef9e,0x3dbe275016ce92a4ac92,0xb04689173dbb13b45677,0xc73a8af79802296499f4,0x740587b78b2d0165ce4b,0x1283dbc728515dcf6f16,0x451822532f85b855919c,0x17b51092795d00952fc2,0xd40547b7421282799a85,0x2323afd342723dffcf2b,0xba049be7f83602a5fd00,0x23e3b446df8084889069,0x30792f7d0e503208c99,0xbc9c76c327602edf43a4,0x87eb87446ba3b6509d80,0x3a66ef2175fcfe16104a,0x79471c76f64e80c4361e,0x741dd24e2b238edd7f51,0xf0b7093e395269c44328,0xfec9049d7e080c664967,0x91f5706b323eafc93231,0xc91df35014ccfbf5d87b,0x50b5eb8d2e471fac6a0a,0x481246f3350a3ffee140,0x4c91bfd28090093bd1b8,0x12d751f02264811e3e04,0x7d8d2d0092b1c55d1ea0,0x69f780acacffdf40523e,0x3111609f803611283bf7],#[0xf0808cb247d484224cf1,0x65923e3d1183fa029943,0xc42bad3330ac672e3c46,0x6b23ced9384244725c9e,0x47d4a23db93da02b9db2,0x7a125e42524872a4a29c,0x49ef9731d442b3f11db2,0xeaa4f7ee13c120ae9e08,0x10fc7a13df21fad81498,0x597f8577292927c8d894,0xa99d9a8304ba3c4d6e38,0xacee5c5c71d1a5d332c5,0x20d12a7b8400a387878e,0x9182252073a1c9c7c0da,0x43c6c5128ed8f683198f,0x2636f35414df21de8185,0x9582333de5e3c28ff346,0xa5c40c4998cd40809033,0x1edf1943299c0e511a0d,0x20567b78e50c543de783,0x2a1e76add804a3f7c604,0x68a4a223a1939edf1956,0x259fc1d12504873493d7,0x47a4efa18a879dab7080,0x788944d41ca8c4dca894,0xed69494db4d4e88acff0,0xa6fd4902b32783c88aa9,0xf74234ca690f63902a37,0xb607866567a7abb944ac,0x5d571c2ba9ae21f32a23,0x1e2b33471f73e2102f8f,0x198f1db93ee2d38f1cba],#[0x89c99bfc4ac262741650,0xe684a45fff32022caa33,0x1e0f16d157f34945de88,0xa22fd5b211481c756845,0x205b48f3974a40b67c05,0x10329af8a894047d85e5,0x3dad31657df64c643e33,0x499e68ca6929e718a4f7,0x33942914f9c3b4658b2f,0xf5a0230677fb2c281e22,0xdeb40ad7ff0509012079,0xbada9038fa5a023d367e,0xf44249e08ad470a44097,0x2eff410911f7fa9a229f,0xdf64c6442fcc641d79a2,0x3d838ce6159ed719d653,0xec1c6758b2720332a917,0x7e13726524c7ba4326b9,0x9b37880524d24930d9de,0xd9bcc25ddad1160ed4a2,0x2cbffdd089c057222da2,0x3d7257c059673f6ee100,0x80b6e9ea55c79840627e,0x3c7ae7cd0169fa9ae25f,0x6e02ebe758612ff016dd,0x34229bf88a0293ac3097,0x140597ffa53a0c0591e4,0x3015f47b418cd7ffb323,0xa4946797bd139fcf3cd8,0x9d63a937a02f1ff54192,0x3280b2f9d67527e80b6f,0x954d1c9c08aeffe1da],#[0x7fc7742650168fc18631,0x7119cc4024ae6f282490,0x9f1aec8924a3eef5a8a2,0x31942131f0a0b999213a,0x542473e9fcad08ab3c27,0xc589c6feb8c01244f19d,0x276cd2a0490afdcc65b4,0x2371240c8f658f0d218b,0xc501a3e6a215ce839205,0xc1868927ba4c13873d3a,0xa49a492677699840ffd2,0xf304c54bfec4e455ff10,0xc128832fa236ed688b66,0xa2f7ea44c4e4c1344f37,0x90a8fdb1c2c1513e46e0,0xf3d4b79e250ba3d7257,0xc723f06091535987b42b,0x84695135452259fe13a,0xa5ea6c0edde4701731e8,0xc0f5ee8ed06341f23060,0x86d76046c3606611dba6,0x852a176a8a7f3576f10a,0xfcec261f1284521dc61,0xde267cf102a37e60c141,0x710a6d9eeca140ce5422,0x8c87d4925cf8309a9ded,0xb8e845136be090911ed9,0x8f6cc64b306131f5825d,0xdb1150251f3dac9fa02b,0xc4540943f7022a0489a8,0xfb10aae616fe80aa73a0,0xcc935ffec9ea80aae616],#[0xa41049df1c2909025561,0xfc429b8ea4fd015cf9c4,0x3044f239e1f00145cea4,0xdad041247e0c318104ac,0x623ea5d442dbcc0503d4,0x9550cf95214ac7fe219,0x800b6f2f34c129bbc2a6,0x4a4f787ea4c155f4f91a,0x95199e054ac597873292,0x47bc1ccc94165e0e6660,0x2f07ec92293dd07cf825,0xf94a140c5f230643784a,0xbdea114064f3a4d6192,0x1ffe19b6b015864f380a,0xd2012a2f6f09397bed13,0xfa279f4062e9244fc86e,0x64999c2526f5e126b17b,0x49af24ce3a513464446b,0x22241ef237cc00aee538,0xbe949f9329a1150fe6a9,0xb0f43113de005c64c63,0x684c6cf8456733113fc0,0x721942ce8e014795c911,0x45bb93aa940f80510bb9,0xc7d185923cae2a268e08,0xbd64592b8211a491b591,0xb971d37f10ae639922a9,0xd0e8bac907dc74df942a,0xb31eb22dcb8e9bfa02c9,0x681f04d281290fd1c88d,0x261d608f230c7e9a4224,0xb44c3f5823900935267d],#[0x7c6ed201269dfa898f33,0x3e1da491c7f876900903,0x5646dd7959160ebcac8c,0xee37ac8bbaf2b228f75e,0x230f7c3d6461bb8deb23,0xd6f08dbe687e4583e1eb,0x2354324c9967a1f9112c,0x5ec8e96697c469e94e2,0x7300a6f9ff017da2a1f0,0x73cd489cff4c258293b1,0x47552466e829562e704f,0x192653b7752d197a948b,0x2edf9b2260d004c33bd,0x517ef42289546d386989,0xb4373872520597fa44a6,0xbe4f02a25406e70f0a40,0x58c5bd50a39f9ca1512a,0xa37b4c21c5466f34b519,0x6f121b8c5666dcf3512,0xd5c28be2252237dfb8c5,0xdd982404932de86bc902,0x6e8d6802596f6d7b8156,0x9c90a492af3f94c950d7,0xbda9a231bcd3d1944527,0x18d3bf4a2523cc816891,0x7b42a8a2faca30c5bd65,0xa8954499c1fa62b37383,0x765ec0a6f617c49ccd29,0x6f4b4b0aafd284a4a6e6,0x8ae7ddb046bec0e649ef,0x447bf7a41494c6d3db4b,0x5465067e36e58533aad9],#[0xf8d371945cf3464c7b9e,0x9322f62142445ed50a31,0xc0aa01fd851a0cb9c41a,0xa2e722bf80aae722bd,0x2cd1123716013122387c,0xddbeb60177386700a246,0x8aa4e67c9c0aee466499,0x4db2ca7e275ad685684,0xff75b8275f3dee10400,0x581dfc0a0be86866790b,0x464f3584e7cfd075d854,0x1dcf649053391838b209,0x8bdaa8465f18bf244025,0x63afa0091b0163af6849,0x5241fb31c4c38a9528c1,0x23da7ff821c154e2f620,0xe6b04ebbb9d08d37aca8,0x6877f0154e717b59473b,0x688cb498a296077f89e8,0x17745988d3a38a51b471,0x5f41b491f4714a2e93a1,0xa3f7ee10d08ad7513a45,0x1c314dc0577f7f2153a2,0xbf3f121b345670c1fd14,0x9ce107a924df36403a2a,0x17e489245f9dc92c9a2b,0x14060f7450317d6248e3,0x8594fc4c72f344c18b9d,0x948e76cfe5b453ded58c,0x92cacf13179089b762fe,0x9e141d3ea3d90abbdab1,0xb8f878970d61f2353ea3],#[0xc9b4ac00b4fd266b2e12,0xc8584567e9934c384594,0xd23c1499ebb4ac8576e6,0x3ee9d70150d70ee463ee,0xf6aedc149f3ed5db12a3,0x9f6bbb22898ec9662249,0x93326efe182337199332,0x88ba33eb22b7d9899239,0xf5527be791ea2154f8f4,0x377579592246e9f9188,0xa7b03ab1661bbb87ac9,0x3591b72ce108f77b67b1,0x4dfc42bbbdb3da02adcb,0xbac903543a2e2126e5c7,0x2235cb8e9bfa02c9d0e8,0x34a04a1af0e14479f874,0x98e4e31fa690891a07c1,0x6f630a06660ff7e08321,0xa8ea42f8946b57df2c28,0x4048d13057f51f44eafd,0x9229693be909435abe0,0xa8f10978c248f3cc5ea9,0x2e597733289c60f58461,0x974ef8f3a0a4f8aa0a,0x4bdb0ff046dea283f8a,0x20f866389d7c79581a84,0x1562a4fc0a48d845f501,0xa8421863f484a5227e5,0x248d6cfac11c8c697fe7,0xfced21904914bfcbf094,0x95146f40ca96c3f846d,0x923e1d0e4ebe3c8d0185],#[0x42f89456eb10c656eaf9,0xd984f231204db3cc3126,0xc7291763e52227ab0c65,0xe416a3c2641f78948a3b,0x2a2e78a24ac3e2142472,0xf25b978e26df61fc48c2,0x5d5057a46ee5c132160f,0x7b86ae7f34c8b242f894,0x30d6af8101237d9d5424,0xa6cb82652c4ef13dca91,0x475539a808fa2238a46,0x3e6855de8929b2aa9cd4,0x7ea04e64777e6282601f,0x1bab826842490fd409c8,0xa0478b673d46bc43f0c5,0x16ce7]]
def g63H9 := limbs80 #[#[0xc010140b000371c800,0x42f1580400c150f802,0x7c060000101c0913c00,0xf0020983700c0004800,0x5c1c01c1300c00008b5,0x8020e02b0401802401,0x10110081b0980300429,0x281201407010070000d,0x18220000e02c0505011,0x300b010010f00200c04,0xc000b0020440101012,0x1002504420e01300000,0x20330d404004000000a,0x8008030980600c00,0x4260004c0901615804,0x54000f0000182205805,0x12c0004c1406c1712800,0xe804010360740701802,0xb81200403004020e802,0x2b00901c2500c0702001,0x40d1680700c0309024,0xc09030522980000403,0x38e30880e06c02000a0,0x1300010002018cc09439,0x2400064072744c07c00,0x880a060010940a1a444,0xb1bc1e0040109404,0x68401000010600a03018,0x1a8180ac1401c0001c32,0xa0c4000780b04c00,0x342b0000001c3100809,0x701c01c070181000002],#[0xc01004010141100402,0x4c2b0000104c0300416,0x881137c1b0740000c04,0x988e36c0c00c02018eb,0x1585402c0a054110c017,0xb706003008331ec05,0x580b02cb7060300d456,0x38702ecb40ac4b03c3f,0x27c1e02c1403c000001c,0x1a806080001cc0004000,0x2a02c320000b05845,0xb04c1f03c0802403,0x4000782c01c0e00800,0x804078220000014c1c,0xc070d0080f00a01004,0x450080003401c690284f,0x2e170140640d00000,0x14780543c07c0002800,0x1d4030006e0802b0f80b,0xc0a1e845034080200a,0x1b804068000c01100416,0x3cc9a00c090200202c3c,0x4f83b00c0704c0e0cc1c,0x21240383036c2505c04,0x1825000053901d05c4d,0x1c0260b02c07000020d2,0x4c1f1180a1882f09413,0x640b000251380031000,0x27c401500202c4f29802,0x100a090b7084712f01f,0x1b48529801000010280b,0x4050302b1c8021a800],#[0x2c0230ec02014025c955,0xc800018201080c23406,0xa0101d000054841a409,0x1f1310000e1680902c02,0x40936e4030100b00401,0x106c16c310942c33835,0xdc06380500001a02838,0x134e009cd3004260f089,0x258e00780f188010e439,0xbf0401b1380f02c0c,0x3c3d0440a0953529408,0x2184a45b0c41401400,0x230d500d260105800402,0x8d521825094430789e,0x100d00c3d41d300047d,0x1200703401038120b000,0x6a0120380e1b03009809,0x1800584000301c0fc62,0xc4752180500ced0147c,0x5416004b02940240007,0x28171c0000ac0006404,0x5ed60acdb7105500013,0x4c0150373240703574,0xf090000900805814,0x33cbb000000195906c00,0xd04f000021300624896,0x180306400048b445804,0x1171104130559e00000,0xb82010071285361f00b,0xa010013341603d1d,0x6a0043a0001501c00083,0xd048e5013540003d6ab9],#[0xcac000194dada170645d,0xb67212b81d8000000032,0xb492ddd17dc000385d78,0xb5c0001d4b1086b17405,0xb6143b0000022d31a668,0x8ea9fd6283020cf12491,0xe5668934ec80002a5464,0x822d2958839181fa56fe,0xc775bebdb96e6c121336,0x9e00002e6245feee1f26,0xb591bc80000ab636a63d,0x39d858ac1985b87c55,0x98665b00002c95c00000,0x452521417e00002adc60,0xabce12a9ad5bc5c8fad,0x15c608b14de23e44fe50,0xcb79c000894c1614e934,0xfa808ecae82a7bdd5d7a,0xf051c64c791524c0b71,0x42ba00d0248a001e3f68,0x4a34d04ab6bc44b6e9e5,0xebe1f846988e05a81e72,0x39b9d9d834727ff4b580,0xd1ccadc5f1464db9db1c,0xaea47af98d09f5414049,0x4f46867a0d6a676d6488,0xb880002ee9902a3a85b5,0xb6c5864c9b2dc684e5a2,0xa040002a3796bc3025f6,0xcaed80a9f22ed761efc1,0xcbf9e9400000002acb94,0x79000000002d963e8d45],#[0xec5a2c813f40552d0f2e,0xfe51e7fd6e5009e27774,0x10f1724f6da105,0x80866d150faaaa5a4680,0x8fed1bc90b943584a974,0x321c3e29bf3eae9e6ba9,0xeebd8054957cf86df012,0xa1dcb2f64eb6ef3030b0,0xa92a6898d38606b29ee9,0x290a428a9f5cfa6dca06,0x9131f79495142e5536e6,0x417e158117c8f73c9cc8,0x1e000039829d763e2b9e,0x9be6446ec2384621cf6d,0xe7710040f444d84aa28a,0x12efa0ab943fd40ac,0x9be0f558520d667d2540,0x3e800000002ce69183ad,0x16b2b4cdbdbc983ae159,0x9bb900b27a9e6eccad00,0x6dd1d0b64f1e91e621a8,0x368dc2c5a2dedd9ca4,0x36660f4431619b18e940,0x4cb20a7cbd901e2c600c,0xc9811342e632afd18eae,0xa668a3800016d6e9b278,0xea69110c51b06ec43604,0x11c0001e7d5280043a64,0x348660ef000006,0x9f08b1b9b14aa9926dc0,0x69cd2380b3010dce60b1,0x2461c2b0adb1204e56],#[0x72c1218a654d6b0e2540,0xd8dd981ea9c4d80818e4,0xcdde99d6572691b22,0x5d8eb31e721c60943940,0x410e340c08a1f95c22a5,0x15366d8df400002e3bd1,0xb42d9dce79cca82dba0a,0x932c8da4f9edffea1630,0xf27e8e217f46c45e5d34,0xdfad13c4abea9,0x6194233e770c9c283ac0,0x9de4fc0000268747372,0xed898f08a1cd,0x676c99400000001a0700,0xae9aee28818a83a29c84,0x6bb6b7000005770ec485,0xea3706c1d4984e8ec,0x358ba16dd040b9ca40,0xd3de45428d0000189900,0x1700000e3c3d234db5f8,0xce000025b280003d7cb1,0x8bc4d489ab38e4d0ff25,0xda5f60ef081edd67ad4,0x10f7e1b440000a36cc,0xbabea18000363fd27840,0x1089c090ed91400008,0xee0edc480,0x4329304c9f869fdec40,0x368842ada47ed2251a,0x62c5ef10512a30140680,0xd9400030d90c76acd301,0x78da873594b06f400034],#[0xaaa2eaf29d400015f498,0xe1a826814ada7d9de734,0x96242ac0001d2d00eb7c,0xb500001e02c0000ad3c8,0x2d7867de9fe312025,0xba48880002449c00000,0xb9ad8abedbfd5086cece,0x597decdd4976195845d8,0xa8d8dc7aad689d400002,0xa2216206783d776d5ad9,0x671c7262da1e2e7e7109,0x919634d0b73a9ce90ebd,0x757e283ceaf09596681c,0xc2d00000669612275,0xa6f4f18d8769e6300000,0x3680cb800035ee69c5b1,0x95816d000000f7722c0e,0xc950f258efe18a3567d2,0xd2fadb79537cf88a0382,0x9411aa4476255d2692ea,0x7b2cafc8ac70df4e8792,0x8535ea940a01c189b6ee,0x26a5e658c1d8f2999a,0x8000022d7c0002c1980,0x3e115ebd9e9d5031003d,0x782cfb0c1faac2c94c99,0x2579cc5b265f6875cd,0x5a357c7a472a83cdd700,0x2ae5393ed8ef893ba9,0x8aec0480003007b48b00,0x1080002a08d60bf0ce24,0x828df2c0edfaea290ca8],#[0x8966ed800004eb8826f2,0xf04ec6a4dc800009e9ce,0xaf0000000000002ec1d4,0x3191d11887fd0bc00031,0xc3000000003222de66a4,0x342740003d91c0002d,0xb59a612cf1182254c940,0xe4f941744c0d9778025a,0xcd49dc6dbb00001ccf0e,0x7ddd121653e651b05568,0x1fb82105aa0ca1bd70a0,0x3af6ceca45e849,0x220422e1a440002dbf80,0x12ce99a2e00002a5364,0x8cd5c78955c0a9305965,0xb2c4499675c000229031,0xa0b248b08059a2ad72d1,0xe1f0c929c700c6cecb2a,0xd2684156e716660058f2,0x61865895ed987462b408,0xf36ae3517aceb1000038,0xb9800019c0449658f958,0x84d4b6d06a5223b54ed6,0x5c3adfa88781d5755968,0xf91dec84af85689c75b1,0x8f6227a5c2ee5eea5879,0x1f7cc386670000155cae,0xc505cb4082ad0b0b86d,0x75d506b297c00038d518,0xd2b061442bcb483e9,0x4b516f5a16800038d640,0xc4f55436efca328ad52a],#[0x5f866991d0dca26c31f4,0x2df60e00003df32e87f1,0x75a13a4e7cd2cd01a4b5,0x23c00015c5f1377a24d6,0xec2d457aa318742ea235,0xa3ead5b1b062da6af11e,0xe02220caf18ab5e81660,0x926d321e45fe5e4642c1,0x22b51276b57cf6f364,0x5464650000000000ce80,0xa2c1b9f8450000341388,0x3708a05d13800021e050,0x2838bb2a558c7a3cb118,0x862db65ea95a0d0e631c,0x2ffa978a0836d2a6b7aa,0x3bb427adbe6d9b480e0d,0x24000104b4566e16342,0x63e8194cf66ac6f61f79,0x74f18d8185fab5400012,0x3263aedd89f77a616e,0x61a944405a910f5c1900,0x2a6587a4310cc5400019,0xb740002d152c5c000024,0xdb79d6809280003689a8,0x2c105201000bae0f20,0x36ecf957c00021f0c0,0x9f0000000008f5ccbc80,0x2d85aec0003a2601bc38,0xf62c65fdc4de0ec823be,0xf740000000300140002a,0x80aa2b2e9e92a742e8a6,0x8bc62a40001aee81588e],#[0xdde9944d10000342c86,0x341a551c84000004be48,0xfa00000a3fb9d7d891e9,0x8d8cb35cdb18905c7e69,0x3ebdefb1e99561000012,0x52a1d409d9a02526d85e,0x3399b3329c1aa11deb1a,0x164000257fa11f0434e4,0x2e71016c7936c3e5459a,0x6a752db08cf0a6d24bb9,0xb44d28d503e107261482,0xeb4221180399028259fc,0x12ac4a40003cfdbebd9d,0x3aa90ecc6d5139a8c189,0x5dc4a9dab67ca88ddec4,0xa4e158291eb9c8bce358,0x287030c028800005df4e,0xaed8bc1dbb83c946c8e,0x190f680002d2a222cf1,0x20e5dd000029e6423596,0x3b52b3d1e0b2100e9478,0x28ac881aeee32e953c,0x3af21a50c074e05900,0xf04959f2498d0e7ccbc0,0x1a6d418e1aac7f0c4829,0x4ee2387d20747024bc48,0x39576532682f7d2696,0xac3ab9e8ee4163898480,0x81e6347cd2ee1c896059,0x4234b68d58cae416d4f4,0xc41a3a5d3cea2bcae478,0x35787b3e2961177902d2],#[0x3cc293e235c1c3ed0a04,0x9db28171c3590c2d1db8,0xe05cca0d4775e462eb05,0xe6c0001413f55215b216,0x9fa1eebcbf0086000020,0xb39c1dd908c64585c878,0xc460672a1fee915eca80,0xcfa922d130b6cd50b091,0xc86ab1927a2abf049d38,0x40f548864e18a7dd787a,0x5c63522f05527400008,0x1996d9400036ec800019,0xabc0001e516682c00022,0x4335926217425fc00002,0xc489058995a02ddc810e,0xa3ec2bc20f9e5ccd2828,0x3c1a906800002998c9,0x3aaadcb925a2e2ac00,0x8baad5d16eeacf744900,0xf7923d9441da0991c2b6,0xc5b6009206ce6aa6c62e,0x2ed709bff19024,0x35046466ad916da3040,0xd82d3588814243425aa9,0x442c4d28b56670000012,0xd9dd7441c1e520fda536,0xd8ae8ae183ee981168fe,0xba80dc3aaaac2a9df09c,0xc92954ede582805e5575,0xa514d1b16b5ac919c0c9,0xdd4046b5661db8fec8f4,0x230d1951cdc5b7561545],#[0xd49acdc11ec43a1bbae,0x48e0ed6e64c8dd09,0x9b1c0724697d92800000,0xa8253c28ff4118b1731a,0xe1417b80000aefb9e565,0xe4c0003916156680002d,0xa77a5eaea25532c6b8ed,0xce14c8bd9f800012acdc,0x971439342f80000a5b9e,0x235d97ac04796ff12e3e,0x3eb76db4c19ff69202,0xc1e5dde94d000021cec0,0xcc8de93180003d4fa4,0xd7c0000536750a418f89,0xd8c01c59f800b611d5fc,0xf4faebc00000002dab60,0xae2ea8c0001c41a05d1c,0xf6c00038974981000028,0xc21d999986d49cb92648,0x9884d9ca91151188442c,0xee350d0000000022a83c,0x7f497bd1507c8e5e3cac,0x6ca473ae41000024ca48,0x8f545311232d9702df1e,0x7306bbf812028460e0e8,0x6a000021ccc0d431093c,0x37b1953d14dd1c000026,0xa204d9ae4d283f4df181,0x675363cacc0003ace58,0x400590f0f424c1400035,0xd0d0b4f0300d15407841,0xd3b46e9a3f0a243cfc08],#[0x587d1acd3d16e8554f3e,0xff25f286e7c0002cbc2d,0x4a45a9f6cc2dfcf127d9,0xd5d611598dceed20a699,0xa1913355021a842c38c8,0x565a34917efc48918d59,0xd1645880001e9f9a113e,0x1834d019e6a0cffcb7e2,0x8346dc25cfb8cc20a0c9,0xd59dbd685ee2cc55b0ec,0xe10945c0857e97483a09,0x4fdb7000000de4d50ea,0x82e0614661e079b086e0,0x21e619f4dd8d913993e0,0x5b9c947c444df5f8faa8,0xf6800006cbfd1d21b3c9,0x104ae662fce8ad70d2,0x184eb2a44ce24fb61c00,0xfbaeb2ccb27528606339,0xa9982e190c65512c6cec,0x4d5465a667fc06264615,0xfbe57f04abc94481da31,0xd63c14f4572cf5b98244,0x7ce12c4982eaba000004,0xa9429dcec3764b00cde8,0x1153be9f04ececfd69,0x7551f72944f525b1ee00,0x149e68ec0b14de1db898,0x939ad678e9d29a00003c,0x11d3de94bd06e1f699,0x270438aa955c7d566280,0x47fc6e38feec935a5dd9],#[0x714af42a7ba42d50ab21,0xfd2cb1eaae15964832fd,0x6d6c5428157604418ef4,0xc269442ee25239c286b6,0x1b4136a95b54b03557b1,0xd745372d49162fc00018,0xaf915c87fb146c12aa5,0x8e4188dcb8c589fcb2be,0xa03988be375e8830d085,0x653e5db02444428dcd4e,0xe205e12119aef3118f6d,0x843d0d98284929a67080,0x2e85c770a495ad86d1e5,0xff6d2c2cd59d0b51b821,0x2922f7c2c61ac4de439,0xf4498b5a4840b0f5e370,0x1ff1552a21ec94d2371a,0x9ec2330e247aad2a2030,0x150657254c3951800008,0x657a5c7ddf25ac9561f0,0x5b6a07e4084dc6483bf8,0x82406b23d5dc946bc,0x6b599b80001a4e650b00,0x34154619ff917392c162,0x4915af845299a6bdc9bc,0x2340001e27541ee6c07e,0xc30d76c0000c2f1d3c84,0x3c7e259e6516859ef4,0xfc8660223cc47210a340,0x3bfac5263ee2ef7d9080,0x6d800015d7bc8a400019,0xc5e5b1fceabd47b8dcf9],#[0xad68a4fdfeb937dad37a,0x16f57215de84a5ad9925,0x1b0e52d2adc8267468b2,0x5a4ae9253391696816da,0x29be1a56724c59a65490,0x5b1898f44dc4304dd16e,0xe186ccfe477e24aa7799,0x88d0e3dc6f3560aa6b19,0x6f21564425b9a7006ac2,0x984ac992c8a497b0e25d,0x28c2a6966e2eb005fc7e,0x78854800c7e124483dbc,0x76149e69fe1861a4ace,0xb020254000391a9d74e8,0x10a4d158ffc4c252c7ed,0x32f4a31e928450ae604d,0xa702a52c3c6ebfd614da,0x1b1638d91ca429dd5ab8,0xe1e0b18c6696c8e2b7c,0x8266d40caf6e96080e41,0x668ff8dd4916c6930e2,0xc418938e47dea3fde904,0x1bca60c480c9fb78cb29,0x435df111f8fd2f503202,0x6c44bb1bac48a91a431,0x51c062c6c028db814b70,0x7c94e72d6bbd07ccc8e1,0x9e9003c8b20412ca7e0a,0x12c1c8d0b52992045bb4,0x1136926edce9b7d1d029,0xbdca22381bc0001069b0,0xbf622e8cc8196772e0b1],#[0xac84f285c9722f96d89c,0xf16a064864c86066f1c6,0xf6661270f0a5d39e6f46,0x504d38ccc6901f32f0ee,0x6f06bae9a77e65f6c13a,0x1c80deeaab50f789d902,0xab81b905c7e947211ddc,0x59e98e1a6920437180ca,0x9c2c1b99bee2642138b8,0x7e90e02ea14143308205,0xdabde82cbae09006dca8,0x3c41ceba78e5f8921b46,0x847221604c61278e5922,0x48f070edf3cc3d501190,0x9925b3a87b78f536a492,0x5f18c3ce6ce5d95dd826,0x5bf53b50b4b1e1f8899c,0xcc100064c0c21dde44c9,0xf704610a30a9dbfc71f9,0x7fa0cd35033047eedd62,0x45961ad8dadcc13409aa,0x1312a8a13a127445850c,0x3f8eb94196f447a07099,0x67c1290d7294be243781,0xd9b9a0055e051599144c,0x90aa7959213c66e6c9d6,0x3f1036c07b8e5316ca18,0x944d220ba018975dc81,0x77c0351ecd91dac948ce,0x718504a2c252d06673d5,0xbe3a0264d450a03c4f4e,0xcf04853641a41f71ea2a],#[0x7a766c64c01d0404643a,0xc3004d813d849bcc4d7a,0x6d020dee4df468551d62,0xc522eeec765442c99c4c,0xff43ebc7d91d620f620,0xa5c9e25c4abef50e86d0,0x17f2326c2625061690c8,0xfa693fec10fd31e1591e,0xd791cda60ffa72fef54d,0x334cbb62a46a7e625234,0xd4f852c8a85da3725f08,0xdbe9143a139d944a5ac1,0xcd022ee4bf9231891168,0x63f9f9dd317a55f0a121,0x8c51dcd510cda5b280f1,0xbfa548551b8a9d2a10ed,0xf7408eedb100332562e,0xaec0002ab9308241ed7c,0x6fed822d84eed2641310,0x2b857198a8ce3a800014,0x99c85346d228c361d8bd,0x41e13296af00000e9652,0x88adeb8693489e2cbdf9,0xd4c679a4e2be364d5f3e,0xe7e64aa95fee7f183850,0x44e6170819d97aa6e488,0x51ee404e543c7ffc9210,0x4bfa2ab9ea7a67909d8e,0xd37a4a7289c5628aa7d2,0xe84c9434e2c48fc09dfd,0x8afe5020e490e78aab38,0x8b4d26e8c09dcac698e1],#[0x59940af65a515590bd58,0xf980496dde4ce09c57aa,0x18f6e2f533254cd437f9,0x23eae4c01ad24c00435,0x600a5a0c2b7d4a987104,0xcab04ee9646a0c40aa65,0x99a6bb142004e4343269,0xd7270694e0a6580002c,0xaa9424e4eee477e82174,0x4d8e390ae70635d658d,0x93ecbffddf88f1c2dac6,0x85653b57c384a028370,0x1a3d4c759a40003c4072,0x8a6a40e4ad817d34af2d,0xbf7c7a9a635c9142f5ce,0xc802ea68c76e8a0581ad,0xbd08b82eebb457748c22,0xaecc6b5eec61883e6236,0xe5e91fd2debc79c80592,0x525c8316ce9043e919d8,0x70ca4828d77a8cdc376c,0x5ae52224a455b1aa0e4e,0x122a0c18401511fe1c70,0x84518c02ee5a021995ce,0xde3da24a7352b35ca549,0x6a6c5e414a1d42524d52,0xfe212d4c0c1a23f10479,0xd6606604100de3ba01cc,0x9404332c2088789a33ad,0x85fee29e64506d940a65,0xbcced4b9209855de43ae,0x8b66d44dfd00f9808900],#[0x5ef56e0c46cc29b4ad4e,0xc54a3b76bd52f4a96805,0xd280002c010c204e5cbd,0xd1a2e3e6004dae3db7a1,0xcc4d96b40d083c051b42,0x5041d2261db060ecccac,0x15ce189c17d0c5e97b08,0x46c1c091ae5c0c9243c2,0x34a681902bb46a01fdfe,0x6a862c52e219dc2d25e4,0x2892d61cfc46b7fc4b30,0xcfd1db561b96b0dae952,0xd1e13906d905643e1cd1,0x5840000a0508a9846640,0x9c522ac017b86221a630,0x3ee2d12807f650b5795e,0x54b2aa1eb04873ccb9e8,0x69121ec50a8c36917fe8,0x6bf68e753e4c54f5562c,0xc571c9c560f6a40c129c,0x5d1678ef27c8f21c12e,0x832c56598686876d312c,0x1190ef6002d4c6000025,0xe7b45a02452c7c02e026,0x2a05a7e1fb1097c0003e,0x9e08bbf1fd8000084e3a,0xb9997ead7900ceda1e7e,0x3041fc314e41ba4c3bbd,0xa28c329a8e9da92a31c9,0x92d42718706abab9e894,0x9ab4fddd395dbe126fa9,0xa70d7d90fac000087a61],#[0xe4813875c825904629f2,0xbbf2ea800008ea0e27d1,0x70681cfc17092a7543b9,0xed207925b40b0705ebd,0x5d4e0ca838046790da58,0xcf6664be09021e22650a,0x475e09ea4274580191a8,0x92e93af9190dd1a896dc,0x4bc69bb413727b61cc4c,0x9e400005e2a1a0800019,0xa2cc4c81d24993268c82,0x3e337696cac0c83fde,0xa7d3a732e8f24be80,0x22af6a7efc4fd52b40,0x96b4ab482ec2e39a6e80,0xb240002a4230aaf5420e,0x6af971dd42f8bec00016,0xe17690497349ccae7639,0x86921ecc718797d545c,0x66a0d2a9a0fd08800099,0x28eaf4d291958a5d556c,0x8a1a6bea57fa03529ab2,0x8fb0e8245bd90551a39c,0x3dc00025703d12404252,0x8c400011f4f11e6c051d,0x9c40002896800021dfca,0x185c33fa04947d321d0c,0xa5e9da48872d836c62aa,0xf2d1c158145df38d5981,0xc2f50ce4a60000008814,0xa224ce2bdf929c87488,0x627a224000000036017e],#[0xe0b6099ea382135cd,0xf0fe20712f3a38be2680,0x3d45af4e357e14367c00,0x3630e2310daff2a1ce,0x27e5f7f89a1a20b52400,0x187868f21784971295e8,0x3e8a80c4009a7885a0,0x5166d3000016575cf380,0x5684b7a193453a946c71,0xd6a16d4429640fb8dfb5,0xfe1b4225bc23e3aedca,0xb4be1090430146699add,0x611bd195a40002ed0f2,0x64cc218000088b80000a,0x780003d300000164c4d,0xce60a7a04f196300f205,0x4fb09af2bc643dd5fbac,0x1e93b12ae8cce1d470,0x187cac2cc684be4080,0xdfdd53ea857cca800000,0x38cdba25ba12e80cc6,0x44a5532c5390bb88fb40,0xef72f3f9fbe16c314fc6,0xb56035f8fce05da463b9,0x3496c2800021ce767381,0xf922b1742fdd52bd1cc1,0x887d01c95cd540c63d2c,0xb940f30910793440fea9,0x471676f0f8c9bb7076c0,0x52fe5116e644d6ec56e8,0xcdc6054965ce6e7aa855,0x9b5cda20e1f8f00cb3c2],#[0xe6b4729505283d3c1d24,0xa59d5e5085fe753605f6,0x72962dfc3e70e47ac652,0xaae451fa8fc922b67552,0x9a80000e8ef57b54180d,0xa562ed44189a33eda308,0x2e8e581af5a636381d52,0x49f671d48d01cb3de2cc,0x3904c45a52719571f356,0xa0459ce6f2d8da91abe6,0x3529e3ddc614d72998ae,0x8e02cfca7c745fc9e205,0x26ed9940887c56a59f4c,0xdf7de0c04e8cdfe21fbe,0x9d066640001a2d45749a,0xe6f853e91ed9699a7e81,0xa0b0627c01e9f5017e45,0x6cf202ac1ead01b997fc,0x1828f3eedd305e29d6f9,0x2f18fa169a46d55d8726,0xad0c7186465aa0e2bbb2,0x812dadd276468c20803d,0x56c1cb642da1a5623b32,0x94f08d506fb94e989e75,0x3f576b21d46c1855f65,0x3acde524b8ada8b52bfe,0x38248776e6e4ba74562a,0xf1d8e656de5ac090d6a5,0x89b2b396bb45102684ed,0xb086a39a41ddf6565fb1,0xe561ebc40570b14973f1,0x1c396912bcc8091477ac],#[0xe5f57980848587cdbcc8,0x13d9548c5c4c517df6d2,0x74c9f6d261acf92e766,0x4848aa0dd51e39587825,0x50e4c87045602c2c948c,0xf2ac15ac037a74000018,0x2ce218f1ec2dc53a0302,0x5e1ed0063dc5c3a2105d,0x5cf0f8061e80003d1a72,0x8552717d6e800000f4b0,0x714e19157a440bfde8d5,0xa6563145b37109811788,0x8c4882a9f471c6edeed6,0x687a1a06e8c0000edbb4,0x5700e054cb48d545ddb1,0x118931b84000000001,0x3d5c4e569a0dada4c0,0xb1da74b28b1e25f266c0,0x90a62700002c6b38ec0e,0xd32575045f400021cb96,0xb6824976b44961541a21,0xeb35de2e47b16fa8bd31,0xed3e9b6c0940002dd2c0,0xdd40003cc06c500088d1,0xf39237f81268de98a408,0xe7bef026eb72076c23fe,0x764c29000000003839dd,0xe76904e565513b1681c5,0x39e294d5251ce315a7bd,0x69dc5fbc11526fd25785,0xafa53d55da916bd9a87d,0xa782c4dd34d09ffd4ba2],#[0xe31581684bc654c0003e,0xcc824c3d80360ebeac41,0xaba47761164639b863ca,0x8c86267041027f712889,0xa6c0000000264024c295,0xb830e6112ca2c3a000c2,0x22aabefc0e98750d99ce,0x175277dc7bfdeac52fbe,0x7a198b32e580000e3a34,0x5c0000229d99e5f17d4d,0x7731038855a4a15578ee,0x33ed759ac7b2e185c230,0x9a043f1aba583fadf5a5,0x3c2b3cd370141ac72d,0x8caeb84977ac64aebf40,0xc6e40002dcf34,0xfc8a137178bcab9d7100,0xdf2513fd0950ed199871,0x39148457e2be48]]
def g63D10 := limbs80 #[#[0x1102401062108220087f,0x12028020661182601864,0x310a4210ea1282a02868,0x320a8220e6318a6218e4,0x519264196a328aa228e8,0x5292a429685212842166,0x729aa629e8721a8621ea,0x210020006a92a2a82a6a,0x65412a418e6310a42086,0xc90a28839f2751b66697,0xed2322bfadcaf29a9ea5,0xb1042702becf3bb0e4b6,0x956d3d454ed3149d1d45,0xb95e31825ef755bb6857,0x5dcf51cdf11bb6c7a8e7,0xe24101000c5881414279,0x6580534032c029602860,0x1601d6014b00cb00a580,0x811005560192c03b5806,0xa3031020015804280a5,0x18580c580a2c062c0548,0xc040b01d960322c074b0,0x20c0d005480a5810a02a,0x43810438108381000510,0x31604280af280c83810,0xca038014408204002bca,0x5e0063940765019ca032,0x5028c0df0033c40af881,0x408e8053]]
def g63H10 := limbs80 #[#[0x23c403041800f0000810,0x1c0000a0401404200000,0x81840620681020078102,0x8100003000008001081,0x118446820204303003c,0x384033a1c08104082,0x1a202801e001834a0438,0x22819620ac0800c0c9ad,0x4486180c0850a000001,0xc983000c484060048138,0x40400203880004202020,0x8062888e00206230010,0x20e042840218405820ce,0x3483c08143890e0011,0xc040050404b830410084,0x380040000010081081,0x410a040d10c903c00500,0x2024a90060001d002,0x520800a80001021e1c15,0xb00010c5249728ee6e6e,0x418c00000022e5d07290,0xab9a1b4374000b9e4c25,0xcaaf84adaf1428f80005,0xcd8900030e60003e5ea7,0x370d6e700000007a6,0x9d48af2600c000b910,0x72240,0x0,0x71f0000ab79d78000,0x12a5000026e0002f280,0xf8d10003eea000000078,0x16ffc4f08b0000624e3c],#[0xf0ebdc00000000000001,0xa35ac0000003a45651c9,0xd8708b1000219100036a,0xad302402113939e5a,0x0,0x2b2700007480003ab500,0x83b59200001896ea0acf,0x4558aa7764c0000002,0xf841ea145029e8a00000,0x79738a85a580008665e0,0x4c05d4ca140005c14e50,0xf0000434ad249ae24260,0x698000ed80000d4,0x94e0000000000,0x68810b20001e6c0000,0x2fcbe0cd70fe647b5900,0x12265cd32c9071f5c,0xa70000438a6d40002c76,0x85665a8c85810002dc1f,0xc4886b33333043670195,0x882000111140138006b0,0xb30001b5a3b1c0000002,0x246da512c868300c664,0x552d33e75e5f3b000000,0x6940002d87cae2784104,0xd222d629000019827232,0x365423d8633b8ade6da8,0xb39fb6e5f90001f4fe42,0x7684d9b2940780002863,0xc44ea6dea975ec2b0a09,0x37f069fb6b24f028c06a,0x400eecfb009220000000],#[0xa34a6ecf4000f1240000,0x347100001f73cd782206,0x450e794000668165fcc8,0xed35460a0925c000194d,0x248f582abfb1d8443b6,0xb40d13b000386e19c000,0x1417e0c4c837ba6dd3,0x344fd26fc0006b659750,0x4680001ea40003a76c6,0x7c90000000,0x9a4400032140008474,0xa67cb37000000000000,0x1f110001605154800,0x72966fe8580000000000,0x6c000284c000d4625da4,0x3553000000068d4cd982,0xd32d540e3d0cb4000000,0x4a00015c0f2728460002,0x24e2f,0x24980000000000000,0x3128b26ac2d6c9adc9,0xec000a56c0000002b420,0xc000000394013f145ab5,0xe8294aeace33b81d0790,0xefca1fdae0000c330002,0x5904d6748122d43855c4,0x65748b0f3d58a,0xb2c000f79f27c5518000,0xf0000074689434bb106e,0xac9f8391688eb8893fe2,0xca170438c40001f4c5c5,0x770000000a1aa67f5d5b],#[0x45aa000059d40004be91,0x2254f0e208558800022e,0x7c7c7d000000022b4c57,0x2a21900000003a0016de,0x64792d18000049c27bc4,0xdd2f1c8000c47fe4fab0,0x2f1b74e5b865d30815a0,0xd9799d800002dfb8686a,0x4654a8d0003c923d1cc9,0x34d80003f5dd842eba,0x70b000000038292b20,0x29db414840b513b9cc00,0x4c1b58000e0222d78af,0x3ab4040000000000b6df,0x9f928abf0002f0c00003,0x23fdddd8c1f40,0x2437f9e00000000000,0x3eb1000000000028f10,0xd1e800000001782ae100,0x8147c0500012d14d7,0x4e000000000000000424,0x8385dacf000000000023,0x3a4de09fb18000c7b26c,0x44f034000274b000114a,0x40000638c00000000001,0xcda9c2ee88f0000e77fd,0x9900000b540000000b3e,0x987b7dc7ef61e84b5368,0x417f5c86d61800000011,0x5158000b3180000002c8,0x1848d500010e5000248d,0x17011cb694dbc86a548b],#[0x18810002db5e0ade0d84,0xa842d36e2a000145c67e,0x350003b3071c2a8c9091,0xfa54cdc0002949e6fbd,0xb4b62f6bbf6e62f39c00,0xcaf54579580000001a3a,0x13827da764e8000011a3,0x31f6c6e0000000214c9c,0xc3ddbcc00000022b4000,0x4db380000e45c0000002,0x107d400072fb75100018,0x5197e29000226a0001cc,0xb4ab49329c00060b160b,0x290000000000316a8,0x20b90000000b9cb20100,0x6f57063419dc0e664b20,0x356017fe469dc00,0x40000000000160200000,0x461000011e1a67000217,0x79221da58c0004c616d0,0xa3a3fd1645bd7900f1e9,0xc01baac71b7d8b3535b,0x63670fa0fe00015e2000,0x68c6780005d62332d98f,0xf0838ee6d550000b0802,0x45986ff7386f1c57f852,0xae44a38c5eabe1a2c55f,0x1bf5b9110d4d977c0004,0x1b158b61d85b43c29817,0x2cc775764ab69a657,0xd750765eac49a14253a4,0x1084b592e4f805e00030],#[0x41ec603b878000119c68,0x87f638f443a9926d16f9,0x2f1c500004a28352ee04,0x9a7e4b5500e0000000e6,0x862905000048848d0c56,0x24fae7bb5ab0001,0xb00015ed396362240180,0xf933802aa5ea5723b485,0xc438eb692fcf208e4686,0x7ce41f6c958e31d1073b,0xc249ba3d57a071000031,0x97305c8047c258000334,0x3308000000382e0000,0xe30489bc78f3b0a35e00,0xcb28000c1d446b9c3569,0x6b40000a880000000000,0x2400036ed19c00039eb9,0xb0b40003f0f0000039e3,0x61dce6b6674a9200e,0xe300000000001da20000,0x1000332a0000340ecdba,0x753ee3b233a9d6000153,0x2b000000024de0002d6c,0x19557cfc000fb7222e7,0x5721344da8662300,0x26ce9ef22fc000000,0xf964b2568b085d99e8,0xc0002e4d97e80006ab40,0x10c0000003c6,0x33c0006cb32610000000,0xbe6088954000c5978ecd,0x39d500035a4e2],#[0xeeb7a98000f65300d000,0x4e79210003,0x6478000323b48c00000,0x30e24a965f6159030000,0xd056b000009e35279d70,0x54000d10713782e8000e,0xc000c3300000000000cd,0x24350003aa9e32,0x29b000000002068,0x356311200000,0x244000000000045f800,0x856d9a222b2719058000,0x38533bd040c0002eefa,0x480f0000000060d6c500,0x24098dfa5c,0xa300021b100000008114,0x7dd0c000906c00000029,0xf0662d417c55ba8b,0x8c700001d9d432855,0x6fa690001823e0db4f40,0x94b09670000000e6,0x1af18a147f010ad44000,0x96399b44a00000009c75,0x2c75e63702e0000d3e25,0x22aa75974a6d7f0001f0,0x2c40f5795a7b35920c,0x70e07907fb1a37371ce0,0x9acd872c000758a5413d,0x68900010bd000060672d,0x322c1b4ab3fbf1,0x719cc000c198e46dabc0,0xc6a8458130c00000034f],#[0xf7a7db60001e7d,0xb38000000000000990,0x142f000000027d052000,0x64500000000000000,0x22ae493432b86430a8,0xcbc76c440540003bec0,0x363c000b0f0000245800,0x51f00000000000,0x220400000008af40000,0xaee00000c866eac6f00,0xf464000ad178ea918,0xbbe1e8000fc2593323e4,0xa873e51c863032ef13da,0xe8c40000002854921f98,0x2e27000000000036a3,0x65a483200019150,0x31f3a4d1e835772a4200,0xaf000020070001dde0a5,0x12000169000000000001,0x113d00017]]
def g63D11 := limbs80 #[#[0x3f]]
def g63H11 := limbs80 #[#[0x9000ece00030108331d,0x3b7590010e889db6180b,0xf4400a4ae324c000b2e6,0x7b31d464fe68d6a16b,0x25520cc4d6203d8f4107,0xe2e43887b4003020e800,0xfedf0dbbe5e159fda8ca,0x1480038f0018957697,0x1e05cbdcefdc9d419c00,0xa7bb60114c36800003e9]]
def g63L : Nat → Packing
  | 5 => (4,6,6,262148,34,5,1024,g63D5)
  | 6 => (303,5,6,4456652,120,12,1055,g63D6)
  | 7 => (1965,4,6,5571515,122,16,1246,g63D7)
  | 8 => (3039,3,6,1966814,90,17,1164,g63D8)
  | 9 => (867,2,6,786491,70,15,1097,g63D9)
  | 10 => (60,1,6,65537,0,10,1036,g63D10)
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
set_option profiler true in
theorem matchedRoot41932 : block g63 8 2434 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel

end PEqualNP.Outside.L_meta_41932
