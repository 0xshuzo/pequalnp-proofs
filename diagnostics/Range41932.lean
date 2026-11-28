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
  if m=4119 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) else
  if m=4111 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=2110 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2107 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) else
  if m=2105 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2103 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=2102 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) else
  if m=2095 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=2094 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2091 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=2079 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2078 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) else
  if m=2071 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 4) else
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
  if m=4119 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) else
  if m=4111 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=2110 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2107 then (x 1) ||| (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) else
  if m=2105 then (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 5) else
  if m=2103 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=2102 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 2 &&& x 5) else
  if m=2095 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=2094 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) else
  if m=2091 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3 &&& x 5) else
  if m=2079 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) else
  if m=2078 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=2075 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) else
  if m=2071 then (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 4) else
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
  by_cases h0 : m=4119
  · simp only [graphGoal,liftGoal,if_pos h0,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h1 : m=4111
  · simp only [graphGoal,liftGoal,if_neg h0,if_pos h1,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h2 : m=2110
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_pos h2,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h3 : m=2107
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_pos h3,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h4 : m=2105
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h5 : m=2103
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h6 : m=2102
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h7 : m=2095
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_pos h7,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h8 : m=2094
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_pos h8,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h9 : m=2091
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_pos h9,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h10 : m=2079
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_pos h10,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h11 : m=2078
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_pos h11,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h12 : m=2075
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_pos h12,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h13 : m=2071
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_pos h13,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h14 : m=60
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_pos h14,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h15 : m=58
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_pos h15,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h16 : m=57
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_pos h16,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h17 : m=54
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_pos h17,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h18 : m=53
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_pos h18,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h19 : m=51
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_pos h19,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h20 : m=46
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_pos h20,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h21 : m=44
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_pos h21,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h22 : m=39
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_pos h22,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h23 : m=35
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_pos h23,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 5 (by decide)]
  by_cases h24 : m=30
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_pos h24,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h25 : m=28
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_pos h25,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h26 : m=26
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_pos h26,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h27 : m=25
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_pos h27,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h28 : m=22
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_pos h28,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h29 : m=21
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_pos h29,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h30 : m=14
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_pos h30,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h31 : m=13
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_pos h31,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h32 : m=11
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_pos h32,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide)]
  by_cases h33 : m=7
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_pos h33,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide)]
  simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,if_neg h20,if_neg h21,if_neg h22,if_neg h23,if_neg h24,if_neg h25,if_neg h26,if_neg h27,if_neg h28,if_neg h29,if_neg h30,if_neg h31,if_neg h32,if_neg h33,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
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
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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
    (lower : Impossible true graph 10 instanceInputs.toFinset) (gates : List Gate) (o : Nat) (width : gates.length ≠ 12)
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
def g7D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
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
def g15D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
def g27D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
def g29D3 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [32808,0x23ca621021e02108010])
def g29D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x609085870,0x2f90810bc42043e08010])
def g29H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18f
def g29D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd1027c10
def g29H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [654313056,0xbc2002120000003,0xe0002100000000000002])
def g29D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3904f
def g29H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x480091001,0x80003800000000000000,0xf52200000000000000])
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
def g30D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
def K30 := extendKnown K29 5 [(30,[]),(46,[33,84]),(2071,[48,33,16]),(2075,[32,49]),(2091,[32,16,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V30 : Known true K30 := extend_ok (m:=30) V29 low30 (by decide +kernel)
def g39Y : Array (Bits × Bits) := #[((bitLimbs [0x75ef25b6f9ffa3f75e,0xf25b6f9ffa3f75ef25b6]),(bitLimbs [0x110025800680040110,0x2580068004011002580])),((bitLimbs [0x9af9fe4df6c77fe9af,0x9fe4df6c77fe9af9fe4d]),(bitLimbs [0x1480c0834002000,0x1480c08340020001480c])),((bitLimbs [0xd5b2db235de5bc7d5b,0x2db235de5bc7d5b2db23]),(bitLimbs [0x8cb40223a04a40d8cb,0x40223a04a40d8cb40223])),(0x0,0x0),(0x0,0x0),((bitLimbs [0xaf6772f89edee90af6,0x772f89edee90af6772f8]),(bitLimbs [0x87612706102325087,0x61270610232508761270])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g39C : List ColumnInfo := [(4,0,35,0,4)]
def g39A : List (List Nat) := [[],[82],[16],[16,82]]
def g39D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
def K39 := extendKnown K30 5 [(39,[]),(60,[32,49,64,16]),(2094,[32,49,16]),(4119,[33,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V30 low39 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((bitLimbs [0xc7ffeabedff3fd7d8f,0xffd57dbfe7fafb1fffaa]),(bitLimbs [0x800dc0010104000100,0x1b800202080002003700])),((bitLimbs [0xffd51f75ff5c7683ff,0xaa3eebfeb8ed07ff547d]),(bitLimbs [0x22501a4a48210d0244,0xa0349490421a04894069])),(0x0,0x0),(0x0,0x0),((bitLimbs [0x24ee49e71d3bc7e849,0xdc93ce3a778fd093b927]),(bitLimbs [0xcb209d8e4b0371a19,0x6413b1c9606e3432c827])),((bitLimbs [0xfa88b5ebe9fe5edff5,0x116bd7d3fcbdbfea22d7]),(bitLimbs [0x48a025940600d0d091,0x404b280c01a1a1228096])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := [(16,0,35,0,4)]
def g51A : List (List Nat) := [[],[81]]
def g51D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
def g54D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
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
def K54 := extendKnown K51 4 [(2105,[16,50,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V54 : Known true K54 := extend_ok (m:=54) V51 low54 (by decide +kernel)
def g2078Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0x3f6997f9e86ed67ed3,0x2ff3d0ddacfda65fe7a1]),(bitLimbs [0x48800294810280910,0x52902050122000a520])),((bitLimbs [0xdf4e679d13fb6bbe9c,0xcf3a27f6d77d399e744f]),(bitLimbs [0x10041410c4d00020,0x8282189a00040105043])),((bitLimbs [0x56f6d97ec5bd74aded,0xb2fd8b7ae95bdb65fb16]),(bitLimbs [0xb80211008502017004,0x22010a0402e008440214])),((bitLimbs [0xf69b7ce63e36cfed36,0xf9cc7c6d9fda6df398f8]),(bitLimbs [0x32040c22209000640,0x81844412000c81030888])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2078C : List ColumnInfo := [(2,0,28,0,4),(4,0,26,0,4),(8,0,22,0,4),(16,0,14,0,4)]
def g2078A : List (List Nat) := [[],[67],[50],[50,66],[66,50],[66],[33],[33,67],[33,49],[33,49,65],[33,65,49],[33,65],[49,33],[49,33,66],[49],[49,65],[49,66],[49,66,33],[65,33,50],[65,33],[65,49],[65],[65,50,33],[65,50]]
def g2078D3 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [32808,0x23ea6a1221e12148110])
def g2078D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x609085870,0x2fd0910bd42443e48110])
def g2078H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x99
def g2078D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd1027d10
def g2078H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [4244,0x5037e100fc3100042002])
def g2078D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3904f
def g2078H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x1e20000000000,0x1c4280000068000,0,0x14a0000000000000000,0x34000000000000])
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
def g31Y : Array (Bits × Bits) := #[((bitLimbs [0xdc67c33ddd1dffef37,0x7ae27fb8664f7ad3fea9]),(bitLimbs [0xc448c0a23003220230,0x38c028646609125346a9])),((bitLimbs [0x41926dee3fe7e5fa9e,0x3fbdfbfe9b9b8737b362]),(bitLimbs [0xbe020408814c727982,0x1815431c183a0314b242])),((bitLimbs [0xbbfdfdcffbf62bd4ee,0x97dfee67bdfdfd7c4df6]),(bitLimbs [0x9227408030d8044,0x20a84620585cc284d24])),((bitLimbs [0xae3b9ef1923cf8fd7b,0xfc7ea0914ea77a89e1df]),(bitLimbs [0x4af42a88914c81dd8a,0xe478209a10242881a1de])),((bitLimbs [0x77fdf71ed43f763ffb,0xea6d1f29e4ecc1ea9e1f]),(bitLimbs [0x3086095a88f09c25bb,0x2341a1981f041ea9813])),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,1,2078,0,7)]
def g31A : List (List Nat) := [[],[67]]
def g31D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
theorem g31G : graphValid g31 (boundsBefore K2078) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 8 := lower_forest (g:=g31) (i:=0) (hints:=206561609738) (before_sound K2078 V2078) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K2078 8 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V2078 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((bitLimbs [0xc3bdcafe3dff7f4758,0xf0fff7e8b1af3c5f5bd9]),(bitLimbs [0x1264053dc034d30390,0x20bf2f8c2208244d4359])),((bitLimbs [0x7f673573facbbbbef7,0x9ff55f3f5e74f7e0a7f6]),(bitLimbs [0x81460509a07b1a8594,0x441540c3e6061e083c4])),((bitLimbs [0x3d7ff97dff71deda7f,0xeecf8bd7f6fd7373f479]),(bitLimbs [0x6201aa800804802868,0xc28089d340951a137430])),((bitLimbs [0xcbbe6fc298bff77ffe,0x553a75f8492bdd9f0fae]),(bitLimbs [0xe030d0d41c41247a4a,0x5410103105b89d1a0cae])),(0x0,0x0),((bitLimbs [0xf4e8f6ae951758f5b0,0xffb2b6d0bb9af8bc7967]),(bitLimbs [0x501f1a03be18207db8,0x9923024ab2d258b43963])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,1,2094,0,5),(0,8,39,0,5),(2,0,45,0,5),(4,0,43,0,5),(32,0,15,0,5),(2,1,44,0,4),(4,8,35,0,4),(32,1,14,0,4),(32,8,7,0,4)]
def g47A : List (List Nat) := [[],[48,33]]
def g47D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2786055121
def g47D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [776,0x2001002a98480bfa9283,0xbd42506fea890df55121])
def g47H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x270
def g47D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x20a41883001062,0x90620807398b424c7210,0x4059cc520e4208099970,0x3300fd41fd21fc30fe20])
def g47H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5d9ea8
def g47D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x43b2a190813f
def g47H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6405f48005300000980
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
def g55D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x930c0ae29a43,0x7850486bca610de94021])
def g55D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x2108842321010c8404ea,0xc580ff21fe21fd21fc21])
def g55H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20000000000000aa3b40
def g55D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g55H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [524912,0x1200003d000000])
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
def g59D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [3,0x8f59642043e02108010])
def g59D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x40820050450c21440c21,0x30400012410a11c9b18,0x138c090784802fca2105,0xf94a10df21421bd54042,0xfca4085f14810df21021,0xf721043e842087e08010])
def g59H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x60
def g59D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x941aa5a1062,0x80b49aa520c41012935,0x4a4188202527acc5100e,0x8a92628807b885522900,0xfc20fe10fc10de30dc30])
def g59H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x51b0b9145000,0x14c0000000000050802,0x20e70000253370000000,0x2800000795922600])
def g59D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2a19080df
def g59H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x8a28732,0x20000b900b10b00a0748])
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
def g61D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g62D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g2079D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g2095D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g2103D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7209f
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
def g2107D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g2110Y : Array (Bits × Bits) := #[(0x0,0x0),((bitLimbs [0xa696457375f9fd2837,0xd2ac4d95db74ee9b720a]),(bitLimbs [0x496c00242342210108,0x109811109050a6037008])),((bitLimbs [0xfdbdff1d7f0925d65f,0x7eebb3a92c35b84198b7]),(bitLimbs [0x2000010081c022000,0x40210201000410000017])),((bitLimbs [0x77445fbeaa6efa7bf5,0xbb74a652f79a33ac4d58]),(bitLimbs [0x800285000000040e00,0x2008440210000280c00])),((bitLimbs [0x58e7d3f399f263ca0b,0xe045cf6f946bcdf6a384]),(bitLimbs [0x2090780840205040a3,0x46400e04a308948380])),((bitLimbs [0xb28836c85f4ef08fcd,0xdd975172af955d1704e9]),(bitLimbs [0x2d010228f2a339500f,0x881e112c8ed24b1700e8])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g2110C : List ColumnInfo := [(32,0,2078,0,7)]
def g2110A : List (List Nat) := [[],[50],[65],[65,50]]
def g2110D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
theorem g2110G : graphValid g2110 (boundsBefore K2107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low2110 : Lower true (varsX 2110) (graphGoal 2110) 8 := lower_forest (g:=g2110) (i:=0) (hints:=140875196270592) (before_sound K2107 V2107) g2110G g2110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K2110 := extendKnown K2107 8 [(2110,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V2110 : Known true K2110 := extend_ok (m:=2110) V2107 low2110 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((bitLimbs [0x5d373b73aed7feb55,0x7ff7eefbe4fc068ff368]),(bitLimbs [0x110502091ca02c144,0x9b2ae3064d0048f7360])),((bitLimbs [0xff7ccfc6f7daf217ba,0xca82829c5d86d176cb97]),(bitLimbs [0xa45046c4a083f2109c,0x40028a880d04c126c296])),((bitLimbs [0xff6ff8f88974577f67,0x2fbc1762632b7df52c3b]),(bitLimbs [0x5b2b80380924040e22,0x16200062402b3c500c29])),((bitLimbs [0x10fea72f742f8b9c99,0xbb4bfd9fbf53bf0854cc]),(bitLimbs [0x10cfa3435021890001,0xbb48259fbb123b001088])),((bitLimbs [0x35b63b5902913cc07b,0xc5adf1c09addabaaaf31]),(bitLimbs [0x64a42d410a1190c03b,0xc49d51c09acd83a8ad11])),((bitLimbs [0x6805c52fdc52fe6aed,0xf676ff25186fa2317bce]),(bitLimbs [0xc28d050e8cf27eaa47,0x321cdb05106fa2316b4e])),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,1,2110,0,8),(0,16,2095,0,8),(0,32,2079,0,8),(2,0,61,0,8),(4,0,59,0,8),(16,0,47,0,8),(32,0,31,0,8),(0,8,2103,0,7),(8,0,55,0,7),(32,1,2078,0,7),(0,4,2107,0,6),(1,0,62,0,6),(1,32,30,0,5),(2,1,60,0,5),(2,4,57,0,5),(2,8,53,0,5),(4,1,58,0,5),(8,1,2102,0,5)]
def g63A : List (List Nat) := [[]]
def g63D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [4,0xe0b201aa478f02bd,0xe057258430ed77358521,0xc3b9e096148430ddb73,0x1c1210c3bc5847048430])
def g63D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [32,0x1614100806c040004858,0x3b010000a1650100f404,0x385b4041383d01000,0x100e0852383861410c80,0x84628523b332b2023130,0xa0121009460620524046,0x815908e0020605d483,0x8302e231f1017080d000,0x1c0e0c0a094606040380,0x52404520211d150e01,0x1c0f8b488780003e397,0x7561354b91f420e1338b,0xb2a06d1081f0017f9c36,0x3486ff380c690eff6318,0x121df8c630243bfdd921,0x8c3ee39a43186ff72584,0x30dfae4b0861bfdd9210,0xc3efb9a42187f8704843,0x9fae2302653fdd9210c,0x37ab0a42185f7714ca10])
def g63H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x7200000000,0x1a00000007941ac000])
def g63D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x14a04270f993654,0xb1024307891614381026,0x294084e1f326ca962048,0x60f122c2870204c5284f,0x993654b12183c48b0a14,0x1022284470f193454a,0x90223070914143000262,0xc548111c3c64d152a408,0x8c1c245050c000a0f1c2,0x94084e1e3268a9620446,0xe12282860005480e149,0xc3c64d152c4088c1c245,0x50c00098d16a04270f1,0x93454a90243070914143,0x28345a70f193454a9,0x2430709141430002438,0x5888f983650b10223078,0x81610380024445888f98,0x3650b102630788161028,0x2438587cc1b2858811,0x183c40b081c0011161f3,0x6ca16204c60f102c205,0x4058a111f306ca152,0x4860f102c2070004840,0x7cd95204860f161c058b,0x14223e60d942e4090c1e,0x205840a00090b141f306,0xca15204860f102c20700,0x44407cd95204860f161,0xc058b141f306ca172048,0x60f102c2050004458a10,0x1f306ca1624307881610,0x28002238507cc1b28548,0x13183c40b081800111e2,0x83e60d942e4088c1e205,0x840c00088e14223e60d9,0x42a4098c1e205840c000,0x90a111f306ca17204460,0xf102c2060004470a101f,0x306ca162230788161030,0x2228407cc1b285490f,0x102c20601c28407cc1b2,0x85490c1e205840c00080,0xb559b2a4090c1e2c200b,0xd21c96c20b95b03a6a9d,0xf94d8c98457c17446ce6,0x4a5f75734f64a34263a9,0x32c2af22b1ae1310c905,0x3000ffd8d21ff18d21ff,0x18121ff48630ff48430f,0xfcc620ff4c620ffcca10,0xff4ca10bf58732bf9833,0x2bfd8532bf18132bf58b,0x31f74cb31bf98331bfd8,0x931f7cc931bf18131bf1,0x8121bf58a30bf58630bf,0x58830bf58430bf58620b,0xfd8a10bf58a10fe88210])
def g63H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [13,0x3e803d7b4f80000e,0x20c00000044000059c13,0x1c800000000000,0x1e49c0000016c0000023])
def g63D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x103cc34a289187105,0x8300078f30d28a2461c,0x41420c001c40f30d28b2,0x81c41420c001e3cc34a,0x2c820710508300071440,0xf30d28a2071050830007,0x8f30d28b209187105082,0x1c40f30d28b20918710,0x508201e81c5103cc34a2,0x8918710508202269640f,0x30d28b2081c414208086,0x15348cf6318991a4330,0x1ff32fe997fcc7fa63f,0xd21ff187f0c3fc41fe10])
def g63H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0xcc00000000000,0xac00004c000000044c0,0x1d4003124c8d00000000,0x1480000eba5400000,0x8800016e002200000000,0x3bf140000000,0x1d00000005d80000,120320,805306546,0x80000000000000000000,0x189000000000408008,0xf02004e40183a0001c01])
def g63D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18a4188201ff
def g63H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (natLimbs [0x347200000000000,946176,0x1500980046000010730,0x6100000000000000002])
def g63L : Nat → Packing
  | 6 => (5,4,5,0,0,6,0,g63D6)
  | 7 => (15,3,5,0,0,10,0,g63D7)
  | 8 => (28,2,5,0,0,12,0,g63D8)
  | 9 => (9,1,5,0,0,10,0,g63D9)
  | 10 => (1,0,5,0,0,0,0,g63D10)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 19 0 7 3 0 g63H7
  | 8 => lookupWord 3 41 2 8 4 0 g63H8
  | 9 => lookupWord 7 107 2 9 5 0 g63H9
  | 10 => lookupWord 2 37 2 8 4 0 g63H10
  | _ => fun _ => none
def g63 : Forest := ⟨63,10,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 5=true := g63P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_4 : block g63 7 4 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 15=true := (@block_merge g63 7 0 4 11 g63P7_0 g63P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 19=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_19 : block g63 8 19 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 28=true := (@block_merge g63 8 0 19 9 g63P8_0 g63P8_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_0 : block g63 9 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B9 : block g63 9 0 9=true := g63P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P10_0 : block g63 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B10 : block g63 10 0 1=true := g63P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g63 0 0 0 = true)
  · exact (rfl : block g63 1 0 0 = true)
  · exact (rfl : block g63 2 0 0 = true)
  · exact (rfl : block g63 3 0 0 = true)
  · exact (rfl : block g63 4 0 0 = true)
  · exact (rfl : block g63 5 0 0 = true)
  · exact g63B6
  · exact g63B7
  · exact g63B8
  · exact g63B9
  · exact g63B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K2110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullLower : Impossible true graph 10 instanceInputs.toFinset := by
  rw [show graph = targetOf g63 by decide +kernel]
  exact root_index (g:=g63) (top:=10) (i:=0) (before_sound K2110 V2110) g63G g63T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_41932

open PEqualNP.Outside.L_meta_41932 in
theorem PEqualNP.Outside.L_meta_41932 : ∀ s : ℕ, s ≠ 12 → PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276678368 * 2 ^ 32 + 4209567936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276678368 * 2 ^ 32 + 4209567936) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  rintro s width ⟨⟨gates,o⟩,fit,sz,correct⟩
  have legal : ∀ g ∈ gates, (g.op=PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op=PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op=PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length≤2 := by
    intro g hg
    simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using fit g hg
  by_cases enough : 13 ≤ s
  · exact ⟨smallCircuit,witnessMonotone,witnessSize.symm ▸ enough,witnessCorrect⟩
  have bound : gates.length ≤ s := sz
  obtain ⟨gs,out,mono,small,ok⟩ := replaceShort fullLower gates o (by omega) legal correct
  refine ⟨⟨gs,out⟩,?_,small.trans sz,ok⟩
  intro g hg
  simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using mono g hg
