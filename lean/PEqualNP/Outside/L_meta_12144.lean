import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The truth table, restrictions and search certificates below are instance-specific.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_12144
open PEqualNP.CircuitLowerBounds
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

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xfee8fe00fe80e800fee8fe00fe80e800fee8fe00fe80e800fee8fe00fe80e800fee8fe00fe80e800fee8fe00fe80e800fee8fe00fe80e800fee8fe00fe80e800
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1 && x 3) || (x 0 && x 2 && x 3) || (x 1 && x 2 && x 3) || (x 0 && x 1 && x 2 && x 4) || (x 0 && x 3 && x 4) || (x 1 && x 3 && x 4) || (x 2 && x 3 && x 4) || (x 0 && x 3 && x 5) || (x 1 && x 3 && x 5) || (x 2 && x 3 && x 5) || (x 0 && x 1 && x 4 && x 5) || (x 0 && x 2 && x 4 && x 5) || (x 1 && x 2 && x 4 && x 5)
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
def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [typeWord (m/512-1)]
def vertex (m j : Nat) := if m.testBit j then inputs.getD j zero else zero
def graphGoal (m : Nat) : Sig :=
  let x := vertex m
  if m=58 then (x 1 &&& x 3) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 1 &&& x 4 &&& x 5) else
  if m=57 then (x 0 &&& x 3) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 0 &&& x 4 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=47 then (x 0 &&& x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 5) ||| (x 0 &&& x 2 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) else
  if m=39 then (x 0 &&& x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 5) ||| (x 0 &&& x 2 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) else
  if m=38 then (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) else
  if m=37 then (x 0 &&& x 2) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=35 then (x 0 &&& x 1) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=30 then (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=29 then (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 0 &&& x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=27 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 3 &&& x 4) else
  if m=23 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=22 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=21 then (x 0 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) else
  if m=19 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) else
  if m=15 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=13 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=11 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  if m=7 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) else
  (x 0 &&& x 1 &&& x 3) ||| (x 0 &&& x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) ||| (x 0 &&& x 1 &&& x 4 &&& x 5) ||| (x 0 &&& x 2 &&& x 4 &&& x 5) ||| (x 1 &&& x 2 &&& x 4 &&& x 5)
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
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
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
  if m=58 then (x 1 &&& x 3) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 1 &&& x 4 &&& x 5) else
  if m=57 then (x 0 &&& x 3) ||| (x 3 &&& x 4) ||| (x 3 &&& x 5) ||| (x 0 &&& x 4 &&& x 5) else
  if m=51 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=47 then (x 0 &&& x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 5) ||| (x 0 &&& x 2 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) else
  if m=39 then (x 0 &&& x 1 &&& x 2) ||| (x 0 &&& x 1 &&& x 5) ||| (x 0 &&& x 2 &&& x 5) ||| (x 1 &&& x 2 &&& x 5) else
  if m=38 then (x 1 &&& x 2) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) else
  if m=37 then (x 0 &&& x 2) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) else
  if m=35 then (x 0 &&& x 1) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) else
  if m=30 then (x 1 &&& x 3) ||| (x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=29 then (x 0 &&& x 3) ||| (x 2 &&& x 3) ||| (x 0 &&& x 2 &&& x 4) ||| (x 3 &&& x 4) else
  if m=27 then (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 0 &&& x 1 &&& x 4) ||| (x 3 &&& x 4) else
  if m=23 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=22 then (x 1 &&& x 2) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) else
  if m=21 then (x 0 &&& x 2) ||| (x 0 &&& x 4) ||| (x 2 &&& x 4) else
  if m=19 then (x 0 &&& x 1) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) else
  if m=15 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=14 then (x 1 &&& x 2) ||| (x 1 &&& x 3) ||| (x 2 &&& x 3) else
  if m=13 then (x 0 &&& x 2) ||| (x 0 &&& x 3) ||| (x 2 &&& x 3) else
  if m=11 then (x 0 &&& x 1) ||| (x 0 &&& x 3) ||| (x 1 &&& x 3) else
  if m=7 then (x 0 &&& x 1) ||| (x 0 &&& x 2) ||| (x 1 &&& x 2) else
  (x 0 &&& x 1 &&& x 3) ||| (x 0 &&& x 2 &&& x 3) ||| (x 1 &&& x 2 &&& x 3) ||| (x 0 &&& x 1 &&& x 2 &&& x 4) ||| (x 0 &&& x 3 &&& x 4) ||| (x 1 &&& x 3 &&& x 4) ||| (x 2 &&& x 3 &&& x 4) ||| (x 0 &&& x 3 &&& x 5) ||| (x 1 &&& x 3 &&& x 5) ||| (x 2 &&& x 3 &&& x 5) ||| (x 0 &&& x 1 &&& x 4 &&& x 5) ||| (x 0 &&& x 2 &&& x 4 &&& x 5) ||| (x 1 &&& x 2 &&& x 4 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  by_cases h0 : m=58
  · simp only [graphGoal,liftGoal,if_pos h0,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h1 : m=57
  · simp only [graphGoal,liftGoal,if_neg h0,if_pos h1,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h2 : m=51
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_pos h2,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide),pos 5 (by decide)]
  by_cases h3 : m=47
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_pos h3,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 5 (by decide)]
  by_cases h4 : m=39
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_pos h4,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h5 : m=38
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_pos h5,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h6 : m=37
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_pos h6,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 5 (by decide)]
  by_cases h7 : m=35
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_pos h7,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 5 (by decide)]
  by_cases h8 : m=30
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_pos h8,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h9 : m=29
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_pos h9,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h10 : m=27
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_pos h10,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide),pos 4 (by decide)]
  by_cases h11 : m=23
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_pos h11,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h12 : m=22
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_pos h12,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h13 : m=21
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_pos h13,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 4 (by decide)]
  by_cases h14 : m=19
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_pos h14,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 4 (by decide)]
  by_cases h15 : m=15
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_pos h15,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h16 : m=14
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_pos h16,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 1 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h17 : m=13
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_pos h17,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 2 (by decide),pos 3 (by decide)]
  by_cases h18 : m=11
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_pos h18,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 3 (by decide)]
  by_cases h19 : m=7
  · simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_pos h19,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
    simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide)]
  simp only [graphGoal,liftGoal,if_neg h0,if_neg h1,if_neg h2,if_neg h3,if_neg h4,if_neg h5,if_neg h6,if_neg h7,if_neg h8,if_neg h9,if_neg h10,if_neg h11,if_neg h12,if_neg h13,if_neg h14,if_neg h15,if_neg h16,if_neg h17,if_neg h18,if_neg h19,bit,BitVec.getLsbD_and,BitVec.getLsbD_or]
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



def target (x : Fin 6 → Bool) : Bool := Nat.testBit (4276682240 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)
def smallCircuit : Circuit := ⟨[⟨.and,[0,1]⟩,⟨.or,[0,1]⟩,⟨.and,[3,4]⟩,⟨.or,[5,8]⟩,⟨.and,[2,9]⟩,⟨.or,[2,9]⟩,⟨.or,[6,10]⟩,⟨.and,[3,12]⟩,⟨.and,[4,12]⟩,⟨.or,[3,14]⟩,⟨.and,[7,11]⟩,⟨.or,[13,16]⟩,⟨.and,[15,17]⟩], 18⟩
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

def lowRow (i : Fin 6) : Row := Fin.ofNat 512 (([10, 9, 9, 3, 7, 9] : List Nat).getD i.val 0)
def highRow (i : Fin 6) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (([10, 9, 9, 3, 7, 9] : List Nat).getD i.val 0))

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

def g7Y : Array (Bits × Bits) := #[(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x92409240924092409240924092409240924092),(0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def K7 := extendKnown [] 4 [(7,[]),(11,[50]),(13,[33,49]),(14,[16,32,48]),(19,[66,50]),(21,[33,65,49]),(22,[16,32,64,48]),(35,[82,50,67]),(37,[33,81,49,67]),(38,[16,32,80,48,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V7 : Known true K7 := extend_ok (m:=7) baseKnown low7 (by decide +kernel)
def g15Y : Array (Bits × Bits) := #[(0xdf7ec03c3ffe0fbefd80787ffc1f7dfb00f0ff,0x82040444444421040808888888420810111111),(0x1fbf43c3c3fff03f7e878787ffe07efd0f0f0f,0x4080888888842081011111110841020222222),(0xe03fbc03fc3fffc07f7807f87fff80fef00ff0,0x8101111111084102022222221082040444444),(0xffc03ffc003fffff807ff8007fffff00fff000,0x10202222222108204044444442104080888888),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g15C : List ColumnInfo := [(1,0,14,0,4),(2,0,13,0,4),(4,0,11,0,4),(8,0,7,0,4)]
def g15A : List (List Nat) := [[],[50],[33],[33,49],[49,33],[49],[16],[16,50],[16,32],[16,32,48],[16,48,32],[16,48],[32,16],[32,16,49],[32],[32,48],[32,49],[32,49,16],[48,16,33],[48,16],[48,32],[48],[48,33,16],[48,33]]
def g15D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8028023ea6a1221e12148110
def g15D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6090858702fd0910bd42443e48110
def g15H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x389
def g15D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd1027d10
def g15H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10400370000000000000080c1801c00009401e2000000000000000138c
def g15D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3904f
def g15H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf200000000000001b0940024000c15a80000
def g15L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g15D3)
  | 4 => (3,2,2,0,0,5,0,g15D4)
  | 5 => (1,1,2,0,0,0,0,g15D5)
  | 6 => (1,0,2,0,0,0,0,g15D6)
  | _ => emptyPacking
def g15I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g15H4
  | 5 => lookupWord 2 31 2 9 2 3 g15H5
  | 6 => lookupWord 1 17 0 9 0 5 g15H6
  | _ => fun _ => none
def g15 : Forest := ⟨15,6,fun i => g15Y[i]?.getD (0,0),g15C,g15A,g15L,g15I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P3_0 : block g15 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B3 : block g15 3 0 2=true := g15P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P4_0 : block g15 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B4 : block g15 4 0 3=true := g15P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P5_0 : block g15 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B5 : block g15 5 0 1=true := g15P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15P6_0 : block g15 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g15B6 : block g15 6 0 1=true := g15P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15T : checkedTables g15 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact g15B3
  · exact g15B4
  · exact g15B5
  · exact g15B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g15G : graphValid g15 (boundsBefore K7) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (varsX 15) (graphGoal 15) 7 := lower_forest (g:=g15) (i:=0) (hints:=134480386) (before_sound K7 V7) g15G g15T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K15 := extendKnown K7 7 [(15,[]),(23,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V15 : Known true K15 := extend_ok (m:=15) V7 low15 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[(0xcb0f0fff01fc7ff1cb0f0fff01fc7ff1cb0f0f,0xb55554a942912240b55554a942912240b5555),(0x160ff0fffe007ffe160ff0fffe007ffe160ff0,0x9699998c193224409699998c19322440969999),(0x0,0x0),(0xfff0ffffffff87fffff0ffffffff87fffff0ff,0x222210204000800022221020400080002222),(0x31ff00fffffff80031ff00fffffff80031ff00,0x31cccce0c180470931cccce0c180470931cccc),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[65],[16],[16,64],[64,16],[64]]
def g27D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x91e61230602dd0520b441482d90420b541082790e109d43843c44010
def g27D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x48f30918301fc83f107d20f841f843e887c10
def g27H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xfc0000000000000000000600000000004d000000000000d20000000000003b009430a3752e0000002190
def g27D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g27H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb0f84e64260031366a544480078800001e5993d500380000005aae300298a280011556b1a810000000000f0a09920604843e
def g27L : Nat → Packing
  | 3 => (7,2,1,0,0,6,0,g27D3)
  | 4 => (7,1,1,0,0,6,0,g27D4)
  | 5 => (1,0,1,0,0,0,0,g27D5)
  | _ => emptyPacking
def g27I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 2 41 4 8 3 1 g27H4
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
theorem g27G : graphValid g27 (boundsBefore K15) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 6 := lower_forest (g:=g27) (i:=0) (hints:=206292652040) (before_sound K15 V15) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K15 6 [(27,[]),(29,[33]),(30,[16,32]),(57,[65,33,82]),(58,[16,64,32,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V15 low27 (by decide +kernel)
def g39Y : Array (Bits × Bits) := #[(0x1fffc0fffffff83fff81fffffff07fff03ffff,0x42108b2cb2c950842116596592a108422cb2cb),(0xe0ffff03ffffffc1fffe07ffffff83fffc0fff,0x8421155555526108422aaaaaa4c21084555555),(0xff07fffc0ffffffe0ffff81ffffffc1ffff03f,0x842269a69a38210844d34d3470421089a69a6),(0x0,0x0),(0x0,0x0),(0xfff83ffff03ffffff07fffe07fffffe0ffffc0,0x108438e38e3c04210871c71c78084210e38e38),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g39C : List ColumnInfo := [(0,1,38,0,4),(0,2,37,0,4),(0,4,35,0,4),(0,32,7,0,4)]
def g39A : List (List Nat) := [[],[82],[33],[33,81],[81,33],[81],[16],[16,82],[16,32],[16,32,80],[16,80,32],[16,80],[32,16],[32,16,81],[32],[32,80],[32,81],[32,81,16],[80,16,33],[80,16],[80,32],[80],[80,33,16],[80,33]]
def g39D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8028023ca621021e02108010
def g39D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6090858702f90810bc42043e08010
def g39H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x64
def g39D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd1027c10
def g39H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4000000000414840000005980000000017000003f00000504940000000000000
def g39D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3904f
def g39H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x108e068b092ab80000000
def g39L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g39D3)
  | 4 => (3,2,2,0,0,5,0,g39D4)
  | 5 => (1,1,2,0,0,0,0,g39D5)
  | 6 => (1,0,2,0,0,0,0,g39D6)
  | _ => emptyPacking
def g39I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g39H4
  | 5 => lookupWord 2 31 0 9 2 3 g39H5
  | 6 => lookupWord 1 11 0 9 0 5 g39H6
  | _ => fun _ => none
def g39 : Forest := ⟨39,6,fun i => g39Y[i]?.getD (0,0),g39C,g39A,g39L,g39I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P3_0 : block g39 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g39B3 : block g39 3 0 2=true := g39P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P4_0 : block g39 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g39B4 : block g39 4 0 3=true := g39P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P5_0 : block g39 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g39B5 : block g39 5 0 1=true := g39P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39P6_0 : block g39 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g39B6 : block g39 6 0 1=true := g39P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39T : checkedTables g39 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g39 0 0 0 = true)
  · exact (rfl : block g39 1 0 0 = true)
  · exact (rfl : block g39 2 0 0 = true)
  · exact g39B3
  · exact g39B4
  · exact g39B5
  · exact g39B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g39G : graphValid g39 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low39 : Lower true (varsX 39) (graphGoal 39) 7 := lower_forest (g:=g39) (i:=0) (hints:=105553117055494) (before_sound K27 V27) g39G g39T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K39 := extendKnown K27 7 [(39,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V39 : Known true K39 := extend_ok (m:=39) V27 low39 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[(0xffffe03fffe0ffffe03fffe0ffffe03fffe0ff,0x5525528522e55525528522e55525528522e555),(0xfffffc07fbf0fffffc07fbf0fffffc07fbf0f,0x6649832644b66649832644b66649832644b666),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffff,0xbb8e0408080bbb8e0408080bbb8e0408080bbb),(0x0,0x0),(0xf0ffffff80dff0ffffff80dff0ffffff80dff0,0xccf0183070dcccf0183070dcccf0183070dccc),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(0,8,35,0,4)]
def g43A : List (List Nat) := [[],[81],[16],[16,80],[80,16],[80]]
def g43D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g43D4)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4_0 : block g43 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B4 : block g43 4 0 1=true := g43P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K39) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=316659751457290) (before_sound K39 V39) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K39 5 [(43,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V39 low43 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[(0xf3e58e3ffc1ffcff3e58e3ffc1ffcff3e58e3f,0x20001249084208020001249084208020001249),(0xfcfa71c7ffe0ff3fcfa71c7ffe0ff3fcfa71c7,0x40002492108410040002492108410040002492),(0x0,0x0),(0x0,0x0),(0xff0e81f8ffff003ff0e81f8ffff003ff0e81f8,0x804ec924a108a2a804ec924a108a2a804ec924),(0x19fe00ffffffc0019fe00ffffffc0019fe00,0xa99c924c210c030a99c924c210c030a99c924),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := [(16,0,35,0,4)]
def g51A : List (List Nat) := [[],[84],[16],[16,84]]
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
theorem g51G : graphValid g51 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 5 := lower_forest (g:=g51) (i:=0) (hints:=35253091566082) (before_sound K43 V43) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K43 5 [(51,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V43 low51 (by decide +kernel)
def g31Y : Array (Bits × Bits) := #[(0x1ffffffffff800fffffeb60000ffff00ffff,0x4540a88a8a89512a21444ab633333333333333),(0xffe003ffffffffff001fffd800ff00ffff00ff,0x98931131312620c458893d855555555555555),(0x3ffffffffffffe00157ff0000ffffff00,0x8e11c21c1c2384308610e15769696969696969),(0xfffffc003fffffffffffffffffffff00ffffff,0x10020020203c0040080100008e8e8e8e8e8e8e),(0xffffffffc00000000000032bffffffff000000,0xe01c03c03fc00780f01e032bf0f0f0f0f0f0f0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g31C : List ColumnInfo := [(0,8,23,0,7),(0,1,30,0,6),(0,2,29,0,6),(0,4,27,0,6),(1,8,22,0,4),(2,8,21,0,4),(4,8,19,0,4),(16,8,7,0,4)]
def g31A : List (List Nat) := [[],[66],[33],[33,65],[65,33],[65],[16],[16,66],[16,32],[16,32,64],[16,64,32],[16,64],[32,16],[32,16,65],[32],[32,64],[32,65],[32,65,16],[64,16,33],[64,16],[64,32],[64],[64,33,16],[64,33]]
def g31D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x310430400c1f49809f596420433d54908109f594420433d5410810
def g31D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x148288453989110e62916314424988390a21c00980663300ff20c81fe42043f884085f55010
def g31H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x63c0700015
def g31D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7654b3a21802dd92cc86009a80fe40fc10
def g31H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc08000000000000001830000000000000000000000000000000000000000000000000000000d04000008b00000003e200000000000000000000000000000000000
def g31D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x34409f
def g31H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc40000000000000006340000299003c80000000000a514100000002e0000000000000000000000000000000000000001000000000000000000000
def g31L : Nat → Packing
  | 5 => (4,3,3,0,0,5,0,g31D5)
  | 6 => (4,2,3,0,0,8,0,g31D6)
  | 7 => (2,1,3,0,0,6,0,g31D7)
  | 8 => (1,0,3,0,0,0,0,g31D8)
  | _ => emptyPacking
def g31I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 7 0 6 2 0 g31H6
  | 7 => lookupWord 1 53 0 10 2 4 g31H7
  | 8 => lookupWord 2 47 0 10 1 5 g31H8
  | _ => fun _ => none
def g31 : Forest := ⟨31,8,fun i => g31Y[i]?.getD (0,0),g31C,g31A,g31L,g31I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P5_0 : block g31 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B5 : block g31 5 0 4=true := g31P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_0 : block g31 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P6_1 : block g31 6 1 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B6 : block g31 6 0 4=true := (@block_merge g31 6 0 1 3 g31P6_0 g31P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P7_0 : block g31 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B7 : block g31 7 0 2=true := g31P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31P8_0 : block g31 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g31B8 : block g31 8 0 1=true := g31P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31T : checkedTables g31 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact (rfl : block g31 4 0 0 = true)
  · exact g31B5
  · exact g31B6
  · exact g31B7
  · exact g31B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g31G : graphValid g31 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (varsX 31) (graphGoal 31) 9 := lower_forest (g:=g31) (i:=0) (hints:=481441354250) (before_sound K51 V51) g31G g31T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K31 := extendKnown K51 9 [(31,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V31 : Known true K31 := extend_ok (m:=31) V51 low31 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[(0xe07fffffc003ffc3ffc3ff0d0e03fff0003fff,0x4104108a84a842884488020d082c58b162c58b),(0xff81fffffffc0003fffc3f26e1fc07f01fc07f,0x8208211308308b10890084066054a952a54a95),(0xfffe07fffffffffc00003fd311fff80fe0007f,0x410421c10c10c010e11088310993264c99326),(0x7ffffffffffffffc0fffe00000fffff80,0x8208420210210021000107087020408102040),(0x0,0x0),(0xfffff80000000000000000b02dfffff0000000,0x104107c03e03e023e02220b02de3c78f1e3c78),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(0,32,15,0,7),(8,0,39,0,7),(1,32,14,0,4),(2,32,13,0,4),(4,32,11,0,4),(8,1,38,0,4),(8,2,37,0,4),(8,4,35,0,4)]
def g47A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g47D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc0d735886215110
def g47D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc28eb98c42a2218b5886215110
def g47H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x80
def g47D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc264391e600cfd88544433e6215110cf588544433c6215110
def g47H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20017
def g47D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc518b2818a2ce04d0278a8887c44010
def g47H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a200000f47
def g47D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3b2a1948c014eca865230053a1948c01151300fe10fd10fc10
def g47H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x72
def g47D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x405f
def g47H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xac70800014ae28348c922700384d60061001c0080
def g47L : Nat → Packing
  | 3 => (1,5,3,0,0,0,0,g47D3)
  | 4 => (2,4,3,0,0,3,0,g47D4)
  | 5 => (4,3,3,0,0,6,0,g47D5)
  | 6 => (2,2,3,0,0,5,0,g47D6)
  | 7 => (3,1,3,0,0,7,0,g47D7)
  | 8 => (1,0,3,0,0,0,0,g47D8)
  | _ => emptyPacking
def g47I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 g47H4
  | 5 => lookupWord 1 5 0 5 1 0 g47H5
  | 6 => lookupWord 1 7 0 6 2 0 g47H6
  | 7 => lookupWord 1 2 0 5 1 0 g47H7
  | 8 => lookupWord 3 19 4 9 2 3 g47H8
  | _ => fun _ => none
def g47 : Forest := ⟨47,8,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P3_0 : block g47 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B3 : block g47 3 0 1=true := g47P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P4_0 : block g47 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B4 : block g47 4 0 2=true := g47P4_0
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
theorem g47P6_0 : block g47 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B6 : block g47 6 0 2=true := g47P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P7_0 : block g47 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B7 : block g47 7 0 3=true := g47P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47P8_0 : block g47 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g47B8 : block g47 8 0 1=true := g47P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47T : checkedTables g47 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g47 0 0 0 = true)
  · exact (rfl : block g47 1 0 0 = true)
  · exact (rfl : block g47 2 0 0 = true)
  · exact g47B3
  · exact g47B4
  · exact g47B5
  · exact g47B6
  · exact g47B7
  · exact g47B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K31) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 9 := lower_forest (g:=g47) (i:=0) (hints:=105553251273222) (before_sound K31 V31) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K31 9 [(47,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V31 low47 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[(0xffffffffffe00003fffffffffffffef01fffff,0x66cd92a5554a8aa85155122aa2a254f366cd9b),(0x1ffffffffffffffc00007fffffffffefe03fff,0xab56a4c9998313316266244cc4c499e5ab56ad),(0xe03fffffffffffffffff80000fffffdfffc07f,0xd3a7470e1e0c23c18478388f0708e1d9d3a74e),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffff,0xfdfbf80fe0103c02078040f0080f000efdfbf7),(0xffc07ffffffffffffffffffff00001bfffff80,0x1e3c7ff0001fc003f8007f000ff001bf1e3c78),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := [(0,16,39,0,7)]
def g55A : List (List Nat) := [[],[82],[33],[33,81],[81,33],[81],[16],[16,82],[16,32],[16,32,80],[16,80,32],[16,80],[32,16],[32,16,81],[32],[32,80],[32,81],[32,81,16],[80,16,33],[80,16],[80,32],[80],[80,33,16],[80,33]]
def g55D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g55L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g55D7)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,7,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P7_0 : block g55 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B7 : block g55 7 0 1=true := g55P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact (rfl : block g55 4 0 0 = true)
  · exact (rfl : block g55 5 0 0 = true)
  · exact (rfl : block g55 6 0 0 = true)
  · exact g55B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 8 := lower_forest (g:=g55) (i:=0) (hints:=668984111016470) (before_sound K47 V47) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K47 8 [(55,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V47 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[(0xfffc003fffffffc003fffffed2eff80fe03fff,0x94a9128128944a8528428444906ce9d3a74e9d),(0xffffffc003fffffffc003fff3d3bfff01fc07f,0x193023123118930830930889152972e5cb972e),(0x0,0x0),(0xfffffffffffffffffffffffffffc07ffffffff,0x21c0440442211c10410411106a921c3870e1c3),(0x3ffffffffffc00169e7f8001fff80,0x3e02782783c1e021821821e169e7a74e9d3a74),(0xfffffffffc00000000000001e65bffffe00000,0xc003803803fe003e03e03e01e65bc78f1e3c78),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,1,58,0,6),(0,2,57,0,6),(0,8,51,0,5),(16,0,43,0,5),(0,48,11,0,4),(16,8,35,0,4),(32,8,19,0,4)]
def g59A : List (List Nat) := [[],[84],[16],[16,84]]
def g59D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe11439466010430
def g59D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10103802101000000a32e2b86494c121818069943980410c33928cc0208611d9c46550c20a3ce9a9ca60845f7654c530424fbb2862182147dd54310c10c3cc9318a40861e6458c520432cb1cc0290211bdd95214810
def g59H4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30
def g59D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x32080000000226c86c82c8200000808008c08018230810008020608630a0062041520800860820860840801020022601600880058022078062038020022601078058022061000822078060023081860600e00880881840000e00e00800800023081860060858001098058022478062460878021601600881e01800800820041020063661220c000e289cf024508951121f43886506a074027f8fd9f83e47b0f31e33ba750e71cb37e6ccd51a433c660c918c30c60cbe9772dc5a0af95929a51ca093b2644a49191a22e444828ff1e63c0750e41bc354690cc18c3005d0b71622945109912021c408750d218c2d0540901081e03304e03c0027e61942439f9805250e7e62141439f9845050e7e6194332de984504cb7861141329f984504ca7e61940329f986528c2de610ca309f98a518c35c3294630b7185430c35d43944309f594410c39d4310430be980410c2ee62d4c209fd95430827c6550c20bb18943082f86050c20b758c51082ee62144209f996310827d658c420dd94631082fa608c420bb59621083ea6008420be98021082be64d4c10af59353042fa60d4c10af99253042bd6494c10d7d4e530435d5314c10be980530427e6590c109f596430439f4390c109fd95430427c6550c10be181430439d4310c10be983520427e6294810dbd4a52042df6354810b718d520435e6314810d758c520427e6214810de98052042de6314810b758c520436e5214810db54852042fa60148109f997320427d65cc810be983320427f654c8109f19532042bf644c810af19132042f8604c8109f994320427d650c810af99032042bd640c810fa94820043e95208010fc98420043f02108010f8084200421f6550c43
def g59H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe28000000000000b17c42180000000000000000000000000000000000000000000000000000000008e8470000000000000000000000000000000000000000000000840000000000000000000000000000000000000f040000382000000000000111000000000000000002880000000000000000000000000003800000040c00000000000000000000000000000000948000000000000000000000092400
def g59D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3106100a520c32906200a62906200c24860014c548442906100a248600148380641c0320e0190700cc41c043106180063107010500841800410600105008831060018a41c0420c41800620e019483164280106292635082024831050018c41882800e498b2140073148316428012524c41800720c5000a41243000c520e5000c6290624860024a41a43000e6290624860024c41a43000e6289218007314490c0039883886001cc41c6029a62884031483ce0529072ce0624c59c0a498b3814931650298a41cb381ca41cb381b21e2ec1f7aee65b2b275d2afd4aa6b482834e29912e24f4848e91421b4127faf3dce37869ec9979aca556a1d31a3040e750d59822b24c0888ed19c2a84586c09a090007f10430ffa9841fd53083fa86107f94420fe28841fe31083f842107fd4c10ff29821fd53043f8a6087f90c10fea1821fc43043fea4087f94810fea9021fc52043fe64087f8c810fe99021fc32042fca121df14943be282877e50ccaf8a0995f94032bf29461dc328c2fca3187750c30bf28861de310c2fca3105f94420f710841ec21082fca4085f14810fc100219f4390f3a8621cfd51329e2a26578504ca7ca8194f55032
def g59H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1e240006051059499e08e1da83407f41bd1b00e143ba406130000001a4938780000007353020002a15827000f84902a00000038d040a000000000388ee25000000000000071830e883044d810e45d283e420003410000000e0fa25ac88000a1c8adf46e807e1aa414423e0c81448a9a9b22e31f68028560000002120000032d0f3f06967e1080d4a54001245b0a110407822940734b243929b3018003e61e4be4cd064e64a0900040b081e0008118a70000000201684db7a40b1125929c5fc06621b089674e469107ce6862a17f8fbc9d89c00021e90cd25e62d1a2526a6429a333260f600905c1824a11002000418004748081220006
def g59D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5432918021950ca46009543291802190ca4600854329180210ca460076543291802550ca44076543291021950ca4408654329102190c8406cd5c295247f3716490351103c00fe43fd43fc43ff32fe32fd32fc32fe30fc30fe20fc20fc10
def g59H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x31c000000000000044000001e380b4001020000001c4c030001117e1f30e0014dc446001a1400000000021200000000000000192a000001e05c00000cd4000001ec883a000000001a5400000000104a92c000ab62cbe48729354606000001608000000000000000000001c4000000000000000000000032e2d1260001057d2002bf0400000000020200161a001252000cbacde00000000163fe0a000e2e21c00000000062d21000000000000125ea0e00000085c000000000000000000000c26000000000000000000000001ace0000000000000000004cca5ad5a001524000001234c3c001658000000000000a24001a17eb8622000000000000000000000000000e36228443818000001aa160c00000164fa335320003a16500a01900001965d
def g59D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x405f
def g59H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe840000224b1a74357cb9219bc600018800d14000030474f230000030bc9151960000055f03e0400ecc0002887940535
def g59L : Nat → Packing
  | 3 => (1,5,3,0,0,0,0,g59D3)
  | 4 => (11,4,3,0,0,7,0,g59D4)
  | 5 => (79,3,3,0,0,11,0,g59D5)
  | 6 => (49,2,3,0,0,11,0,g59D6)
  | 7 => (12,1,3,0,0,9,0,g59D7)
  | 8 => (1,0,3,0,0,0,0,g59D8)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 g59H4
  | 5 => lookupWord 3 127 0 10 4 2 g59H5
  | 6 => lookupWord 27 137 7 13 7 2 g59H6
  | 7 => lookupWord 19 191 3 12 6 2 g59H7
  | 8 => lookupWord 6 37 4 10 4 2 g59H8
  | _ => fun _ => none
def g59 : Forest := ⟨59,8,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P3_0 : block g59 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B3 : block g59 3 0 1=true := g59P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 11=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 11=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_1 : block g59 5 1 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_2 : block g59 5 2 77=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 79=true := (@block_merge g59 5 0 1 78 g59P5_0 (@block_merge g59 5 1 1 77 g59P5_1 g59P5_2))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 7=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_7 : block g59 6 7 19=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_26 : block g59 6 26 23=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 49=true := (@block_merge g59 6 0 7 42 g59P6_0 (@block_merge g59 6 7 19 23 g59P6_7 g59P6_26))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P7_0 : block g59 7 0 12=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B7 : block g59 7 0 12=true := g59P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P8_0 : block g59 8 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B8 : block g59 8 0 1=true := g59P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 8 := by
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
  · exact g59B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 9 := lower_forest (g:=g59) (i:=0) (hints:=317278226747914) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 9 [(59,[]),(61,[33]),(62,[16,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[(0xb3000fffffc00000ffe000007ffffe003fffff,0xb30d91b23646c8d91b23646c8d91b23646c8d9),(0x43fff001ffc007ff000003ff800fffffc007ff,0x4396a2d45a8b516a2d45a8b516a2d45a8b516a),(0xee7ffffe003ff800001ffc00000ffffffff800,0xea2744e89d13a2744e89d13a2744e89d13a274),(0xfd800000003ffffffffffffffff001ffffffff,0x440780f01e03c0780f01e03c0780f01e03c07),(0x5affffffffc00000001ffffffffffe00000000,0x58fb8f71ee3dc7b8f71ee3dc7b8f71ee3dc7b8),(0x267fffffffffffffffe0000000000000000000,0x267c0f81f03e07c0f81f03e07c0f81f03e07c0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(0,16,47,0,9),(1,0,62,0,9),(2,0,61,0,9),(4,0,59,0,9),(32,0,31,0,9),(8,0,55,0,8),(0,48,15,0,7),(8,16,39,0,7),(32,8,23,0,7)]
def g63A : List (List Nat) := [[],[33],[16],[16,32],[32,16],[32]]
def g63D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40eabae5d9260043d8910
def g63D5 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then 0xd39258f7058910d321cf9258f705891093aea565dcb705891093a6a664dcb7058910b1a69664dcb705891093a6a663dcb705891093aea563dcb7058910b1ae9563dcb7058910b2a29163dcb7058910b2a29175d8b7058910b32e8d75d8b7058910b3228d75d8b7058910b1aa9c75d8b7058910f0add774d8b7058910f0a1d774d8b7058910b1a69674d8b7058910b2aa9274d8b7058910b3268e74d8b7058910f0add474d8b7058910f12dd773d8b7058910f121d773d8b7058910f22dd373d8b7058910f221d373d8b7058910b1a69673d8b7058910b2aa9273d8b7058910b1ae9573d8b7058910b2a29173d8b7058910b32a9c73d8b7058910f121d473d8b7058910f221d073d8b7058910b38e8965dc77058910b1c69664dc77058910b3868a64dc77058910b3868a63dc77058910b1ce9563dc77058910b2c29163dc77058910b38e8963dc77058910f18dd762dc77058910f181d762dc77058910f28dd362dc77058910f281d362dc77058910f30dcf62dc77058910f301cf62dc77058910a2ee8193a1376d091081fea585e0f76d0910c0f61694e0f76d0910c1e61590e0f76d0910c2ea1190e0f76d0910c2766284a0f76d0910e07a1684a0f76d0910e0761684a0f76d0910e07a168460f76d0910e076168460f76d0910a2e2919360376d0910e0ea168460376d0910a2ea938360376d0910a3c6878360376d0910e16a168360376d0910e166168360376d0910e26a128360376d0910e166158360376d0910e1ca158160376d0910e1c6158160376d0910e2ca118160376d0910e3460d8160376d0910e386098160376d0910c3ce479061e76d0910c17a5693a1c76d0910c1765693a1c76d0910c1765593a1c76d0910c1e65590a1c76d0910c36a4d90a1c76d0910c3664d90a1c76d0910c3c64590a1c76d0910a2b68b76a1373d0910a2e68376a1373d091082fa939661f63d091083e6839661f63d091083b2a192dd963d0910a2b68b7621163d0910a2e6837621163d0910a2ba9376e0963d0910a3a68376e0963d0910e38e0b81e0176cc910c3ae63905db62cc910d38e47905db62cc910d2c64590e18744c910a0f69786a18744c910d2624f90618744c910d2ce4790618744c910c2ea1b90618744c910a0f69786218744c91082fea586218744c910a2b6a296608744c910a2bea196608744c910b2ae8196608744c91092baa786608744c91092baa486608744c910c3ce4790618744c910c0f6569421e644c910c3c6459021e644c910c2baa47460a644c91083baa48760a644c910a3c68487602644c910e2c1d181602644c910a0fa9376616644c91082f6a2961d2644c910c0fa59851d2644c910a0f69494a1c644c91083baa487608644c91092baa474608644c91082fea1961d0644c910c0fa1d95990644c910c0f21d95990644c910 else (if j<2 then 0x1d3735891091729d9599373589109176a7759937358910d07654749937358910d13dd5929937358910b23e89651d0735891091729d9599073589109176a7759907358910d07654749907358910d13dd5929907358910d131d5929907358910d231d19299073589109336a7729907358910d13657729907358910b26680931d36358910e0b1d47460a6358910a2ee8197211635891082fa9c972116358910c0fa5f752116358910c0f25f752116358910a2baa372dd16358910c2ba6372dd16358910a0faa3751d16358910a17aa3751cd6358910a27a9c841cd6358910e07dd4841cd6358910e07e14741cd6358910a33aa3721cd6358910e13e17721cd6358910e23213721cd6358910e0bdd474e096358910e13dd473e096358910e231d073e096358910c17a1f9558c6358910c17e637558c6358910c27e607458c6358910d07e547458c6358910c27a5c8418d5358910a272a07418d5358910a0f29d851904358910c0fa5d85190435891083ba9c966084358910a2ea9c646004358910a36a9f636004358910d0b1d6949d36258910d131d6939d36258910f03dd774dcf6258910f031d474dcf6258910d0b1d6949cf6258910d131d6939cf625891092baa7745cf6258910b23291751cf6258910b13a9c751cf6258910d23a5f741cf6258910f03dd7741cf6258910f031d7741cf62589109336a6741cf6258910b13696741cf6258910b23a92741cf6258910f03dd4741cf6258910f031d4741cf6258910933ea5731cf6258910b13e95731cf6258910b23291731cf625891091b29d9510f625891091b29d959936258910a33ea1651cf625891092ba9c9458f625891087c6a3915977058910d1aa55929937058910d1a655929937058910d1ca5591993705891087cea1919937058910b2c68664193705891093ae8996953705891093a68a94d8f705891087cea19198f705891087c6a39158f7058910936ea56318f7058910b16e956318f705891093a68b9654f7058910d262506354f705891093ae899610f7058910c36a636310f705891093a2999210f705891087cea19110f7058910d2c1919110f7058910d34d8d9110f7058910b2aa9383d8b7058910e3260c83d8b7058910b2a29153d8b7058910a3aaa043d8b7058910a3a6a043d8b7058910b1a69443d8b7058910b3868443d8b7058910d1add5929937058910d1a1d5929937058910d2a1d1929937058910b32e8965dcf7058910b1669664dcf7058910b3268a64dcf7058910b32e89651cf7058910b16696641cf7058910d1add59298f7058910d1a1d59298f7058910d2a1d19298f7058910d32dcd9298f705891091eaa77558f705891092ea9c9458f7058910d0edd49458f705891092eaa77458f7058910d16e547358f7058910d262507358f7058910d1add79258f7058910d2ad else 0x358910c2e251805d67358910c3ce45805d67358910c1e602971d67358910a2ee8175a127358910a0fa9c75a127358910c0f660751d27358910a2729175a0e7358910a36e8175a0e7358910a17a9c75a0e7358910e16dc185dce7358910e1660375dce7358910e07dd684dce7358910a276a074dce7358910e0761474dce7358910c1ea6370dd57358910e0edc3752117358910a0faa375dd17358910c0fa6375dd17358910e0ee0375dd1735891081f2a1959d17358910c1ee01959d17358910a0faa3751d17358910d26253706147358910e16dc287dd47358910e07a1f75dd07358910c17662959d07358910d07a52959d07358910c17661959d07358910c36661909d07358910d16a55909d07358910d16655909d07358910c36642879d07358910c17a1d959d073589109176a7759d07358910c17663759d07358910c17660759d07358910c27a1e949d07358910d071d6949d07358910b07e95981d07358910b26e81981d07358910927ea5851d07358910e07a1f751d07358910927ea5751d07358910b07a9c751d07358910a276a2741d07358910b07696741d07358910837ea1979507358910936e81979507358910b07e95931d07358910b26e81931d07358910917aa7755cc7358910c17e63755cc7358910d07dd4945cc7358910c27e60745cc7358910d07e54745cc7358910b26a9393dc07358910c3c64590e1d5358910c27262931d15358910a27a93871cd5358910a36683871cd5358910a27aa0741cd5358910a272a0741cd5358910e26213701cd5358910c3ce4790a1c4358910c17e4f9561c4358910c0fe549461c4358910c1ee579061c4358910c1e2579061c4358910c2e2539061c4358910c3ce479061c4358910c0f29097614435891081fea587dd44358910a1ee8187dd44358910a1e6a370dd4435891081fea5871d44358910a1ee81871d44358910a27ea1931d04358910a2ee81871d04358910a0f29d851d04358910a0f6a3751d04358910a0f6a0751d04358910a2e6a3701d04358910a36e8187dcc4358910a1729d85dcc4358910a176a375dcc4358910e0761474dcc4358910a366a370dcc4358910c1ea5f756004358910e1cdc7756004358910e0e1d4746004358910e2cdc4746004358910c36a5f736004358910e16dd7736004358910e34dc7736004358910c2ea62849537058910936ea58320f7058910c2ea929810f7058910c2ea628410f7058910c36a618310f7058910a0f29d851d26458910a0f6a3751d26458910e0b1d47460a6458910a1ba9e8560a6458910a1b29d8560a6458910e0ba147460a6458910a1ea9e856026458910e0ea14746026458910e2c1d181602645891090f29d959906458910c0fa1d959906458910c2ea1d909906458910d34645909937358910b07696641937358910b23e8965)) else (if j<5 then (if j<4 then 0x10a2b6a2641937258d10b0b696641937258d10d2aa52929937058d10d1c655919937058d10d38649919937058d1087cea1919937058d10b0e696641937058d10a27a9392e1d6318d10a2be89652117218d10c27250936087654d10c3624f906087654d10c3ce47906087654d10c3ce479061b7254d1082fa929821b7254d1083e6829821b7254d1092b2919221b7254d10c0fe549460a7610d10c17e579360a7610d10c36e4f9060a7610d10c3ce479060a7610d10e2c21381e017610d10d2ce47905d86410d10d34e47905db6310d10d3864590e197210d10c1be60956197210d10d0be54946197210d10d13e57936197210d10d1ae57906197210d10d1a257906197210d10d2a253906197210d10d32e4f906197210d10d38e47906197210d10c3aa1b906197210d10a3a683862197210d1083bea5862197210d10a3ae81862197210d10c3c64590e197210d1083ee8198a197210d1093ae8192a197210d10a3ae8192a1c43d8910a3ae819261c43d8910a3ae819760843d8910c3ae5d9260043d8910ab8e859260043d89108bae8192a1a54d891083b69f9660a54d89108bae819221953d891083be9d96e0953d89108bae8192a1843d891083b69f9660843d891090f29e94a0f755891091ea9d90a0f7558910b0ea9393dc37558910d1664c93dc37558910b1c68683dc37558910a2e6a393dc37458910e16dc375a0e7458910a176a375a0e7458910e16dc37560e7458910a176a37560e7458910e07a107560e7458910e16dd6836027458910e161d6836027458910e16dd5836027458910e1cdd5816027458910e1c1d5816027458910e0ea1285dc27458910e16a1683dc27458910e1661683dc27458910e1661583dc27458910e1ca1581dc27458910e1c61581dc27458910e3460d81dc27458910e3860981dc27458910927ea58320c7458910a0f6a293dd47458910e07dd783a0c745891090faa77560c7458910d0edd79060c7458910d0edd59020c7458910d0e1d59020c745891090f6a7759d07458910d07dd6939d07458910d071d6939d07458910d07dd5939d07458910b26a8e84dc07458910c36e4f9061e5458910c3624f9061e5458910c3ce479061e5458910b0729198dd77358910b16e8198dd77358910c36e63705d77358910d26253705d773589109176a775a137358910d16dd590a137358910d07a52959d37358910d16655909d37358910d34645909d373589109176a7759d37358910d07a50759d37358910d16657709d37358910b07696841d37358910927ea5751d37358910a27ea1751d37358910b07696741d37358910837ea1979537358910936e81979537358910b3468684dc37358910b07a9293dd77358910b1668293dd7735891081f6a775a137358910c1e64375a137358910b07694931d37358910b26680931d37 else 0xd69e8560762d8740a1de9d8560762d874086eaa294d8970d8740d0e5d694d8d70d8740b2aa93639c970d8740b2aa93635c970d874091e6a675d8970d87408ada939160b63587408ad29191e096358740939e8592d8f7258740c2da5e84d8b6158740aaca93636036158740a3ca9f626036158740939e8592dd77258730939e8592e1b725473093ae8192a1d6254730a3cea192587705473093caa78258770547308aeaa782603711913092ee9d92e057019130d2ce5f816057019130aacaa3715c57019130e385c98160372d8530939e85929d172d8530c0fe549460a76d053092e68297e0864d05308adaa46460772d0530c2ba639219172d0530b296879219172d0530939e85929d972d053093ae8192e1f62d053083baa6875cb62d053093c68297e0b61d05308ad6a294dcb61d0530a2eaa39219170d0530a3caa392d8570d053093cea582d8570d0530c3ca61911d970d0530c2ea6064dc970d0530a3caa372d8570d0530a0f6a275a137299110a0fea175a137299110a176a275a0f7299110a17ea175a0f7299110e079d684a0f7299110e075d684a0f7299110e139d582a0f7299110e135d582a0f7299110a176a27560f7299110a17ea17560f7299110e079d68460f7299110e075d68460f7299110a1e6a2756037299110e0e9d6846037299110e169d6836037299110e165d6836037299110e165d5836037299110e1c9d5816037299110e1c5d5816037299110a2bea1939d27299110b2ae81939d2729911091b6a675dc9729911091bea575dc97299110d1a9d590dc97299110d1a5d590dc9729911091eea575dcd7099110d1c5d591dcd709911091e6a675dc97099110d1c9d591dc9709911093aaa7735c97099110b38687735c97099110b3868b735c57099110b3468f725c57099110b3869e725c5709911088fea585e0e6419110c8b61592e0e6419110c8e61590e0e641911088fea585e0a6419110c8761593e0a64191108ab6a783a0a6419110aaa68383a0a6419110aac687826026419110aaa6a2826026419110e8c615816026419110ea8a09816026419110ea860981602641911088f2a19599173191108ab6a664e097319110a8b69664e097319110a8e69664e017319110c3ce479060a7695110837aa7836097695110837aa4836097695110c36e0f906097695110c3620f906097695110e34e0f81e017695110d2ce47905d86495110c3c64590e19729511083ee8198a19729511092b29192a19729511092ba93926197295110d2a649909d064d8d10d2c645909d064d8d1087caa3915957098d10c2ba5e84a0a6458d10a1e29d856026458d10e0e614746026458d10e2a1d2826026458d10a3a29d826026458d10e2a1d1826026458d10e2c1d1816026458d1090f29d959906458d10c3a661909937258d10d38645909937258d) else (if j<6 then 0xd0ad04cfecf8cf2cecce6ce0cdacd4ccecc8cc2cbccb6cb0caaca4c9ec98c92c8cc86c80c7ac74c6ec68c62c5cc56c50c4ac44c3ec38c32c2cc26c20c10c00bf0beabe4bdebd8bd2bb8bb2bacba6ba0b9ab94b8eb88b82b7cb76b70b6ab64b5eb4eb48b42b3cb36b30b2ab1ab14b0eb08b02afcaf6af0ae0adaacaabaab4aaeaa8aa2a9ca96a90a8aa84a7ea6ea68a58a52a4ca46a40a3aa34a2ea28a18a12a029fc9ec9e69e09da9d49ce9c89c29bc9b69b09aa9a499e99899298c98698097a97496e96896295c95695094a94493e93893292c92692091a91490e9089028fc8f68f08ea8e48de8d88d28cc8c68c08ba8b48ae8a88a289c89689088a88487e87887286c86686085a85484e84884283c83683082a82481e81881280c8068007fa7f47ee7e87e27dc7d67d07ca7c47be7b87b27ac7a67a079a79478e78878277c77677076a76475e75875274c74674073a73472e72872271c71671070a7046fe6f86f26ec6e66e06da6d46ce6c86c26bc6b66b06aa6a469e69869268c68668067a67466e66866265c65665064a64463e63863262c62662061a61460e6086025fc5f65f05ea5e45de5d85d25cc5c65c05ba5b45ae5a85a259c59659058a58457e57857256c56656055a55454e54854253c53653052a52451e51851250c5065004fa4f44ee4e84e24dc4d64d04c04ba4b44ae4a84a249c49649048a48447e47847246c46646045a45444e44844243c43643042a42441440e4084023f23ec3e63e03c63b63b03aa3a439e39839238c37c37637036a36435e35835234c34634033a33432e32832231c31631030a3042fe2f82f22ec2e62e02da2d42ce2c82c22bc2b62b02aa2a429e29829228c28628027a27426e26826225c25625024a24423e23823222c22622021a21420e2082021fc1f61f01ea1e41de1d81d21cc1c61c01ba1b41ae1a81a219c19619018a18417e17817216c16616015a15414e14813813212c12612011a11410e1081020fc0f60f00ea0e40de0d80c80b80a80a209c09609008a08407e07807206c06606005a05404e04804203c03603002a02401e01801200c0060008aea939060b715825493ce8191dcb7158254837ea582dcd7158254a35e8582dcd7158254a36e8182dcd7158254837ea5821cd7158254a35e85821cd7158254a36e81821cd7158254a35aa373dc57158254a35aa073dc57158254ca6a5383e017158254ca6a5083e017158254e34dcf81e01715825493c683915c971d81538aea9c9460b71580438aeaa4846097158043c2ee5c846097158043cace448460971580438b6aa7836097158043cb4e4783609715804393ce8191dcb715804383ee9d92e017158043939e85929cd72d855082f29192e1d63d874083ee8192e1d63d8740939aa7635c672d8740b29a93635c672d8740a0fea1759d362d8740a1 else 0xc8100000000000000094410c810000000000c810033040000000000000000000003304000000002f306f304000000d2043304000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000098413841384100000003580042000000000000000000000000104000000000e1040000000000984100e104e104000000000000003e10403841000000000000f84103e1040f841000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f84100000000000000000000000000000000000000000410000001040000f4c010801040000000000004100000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000038410000000000000000000000009841b8413841000000000000000000000000000000000000000000f60f50f4af44f3ef38f32f2cf26f20f1af14f04ef4eeeee8ee2edced6ed0ec0ebaeaaea4e9ee98e92e8ce86e80e7ae74e6ee68e62e5ce56e46e40e3ae34e2ee28e22e12e02dfcdf6df0deaddadcadc4dbedb8db2dacda6da0d9ad94d8ed88d82d7cd76d70d6ad64d5ed58d52d4cd46d40d3ad34d2ed28d22d1cd16d10)))
def g63H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe
def g63D6 (j : Nat) : Nat := if 24 ≤ j then 0 else (if j<12 then (if j<6 then (if j<3 then (if j<1 then 0x624421bf30b98e7b122183d859d043d8910c573a30421ec48862e213705d5624431b707b82eab12218d883dc17558910c3db850e3aac48870edc375dd1624420fb31bace8b122187980dd67458910c1e3ad093a2c488617dd6839d1624430b8eb41ce8b122185f7560e7458910c3cc2ee13a2c488636a0f709d1624431b307b84e8b122189f83a0c7458910a1fcab063a2c48852ee41831d16244287b2a418e8b12214b99020c745891085fcc2ea3a2c488527e4d751d16244293926ba8e8b122143e971d4745891087dc830f2a2c488716dc375dcd624421bf30baee6b122149c945d77358910a6dc82ebb9ac488707dd774dcd62443838ebba6e6b122145d959d37358910e0fba8e9b9ac4887071d474dcd624430f301bace6b122183f75a127358910c1e3ad0939ac48860f614749cd624430b8eb41ce6b122185d85dce7358910c4f426e739ac488636603739cd624430f30bb84e6b12218da83dc2735891083f4c6eab9ac48860fdd4845cd6244217d31ba2e6b12218bb80dd17358910c1fc28e8b9ac48861ee17705cd6244317109b82e6b12218db70a1c7358910c2f43eea39ac488527251751cd624428bd2e3a8e6b122189e87dd07358910e0fbaee839ac4887071d7741cd62443936e1ba0e6b12210dd989d07358910a2ecace839ac488527a52741cd624429b3213a0e6b122189e871d07358910e0fba8e839ac4887071d4741cd624421bf30b98e6b122145f955cc7358910a4e4a2e639ac488536e41731cd6244217d29c3aa6b12210f990e1d535891085f4c0e8a9ac48842f2607454d624421f720c3886b122107c976144358910c1ec28e821ac48852ea5383dc1624431b30641ee0b12214b89454f705891087d4c087b82c48843e66043dc1624429e32221ee0b12214af92594745891083e4bb0b322c48860f61474991624428bb2b326e6b12214cd929937358910a67c92ca39ac48841fa637558d6244217d2e422c6b122183f752116358910c1fc28e8b1ac48861bdd78258d62443158e9c12c6b1221c2c751d36258910e47ba6e7b12c488713dd473d8962443898ea39ec4b1221c8c741cf6258910a75c92cbb82c48851e65664dc1624429d325326e0b12214e99298f7058910a3dcaac7b82c48852e25163dc1624429d724b1ee0b1221c6b75d8b7058910e343aec5b82c48872add362dc162443950e9b16e0b1221ccb73d8b7058910e71b16e3b82c48863c60580dd95244307d0b426eda122183d85a1376d0910c2f42d07bb6848861761683ddb4244313d0941eeda122185d8560f76d0910c4f42307bb6848861e61580ddb424431b506c06eda12218d98360376d0910c78c0b01bb6848863ce07805db424421f321438eda12218f381e0176cc910a67cbb07b16648843be6176d8b324431e302c06ec992218ac7460a644c910 else (if j<2 then 0x165cc910a77cc2edb16648863be6176d8b324439d720bb6c5992211ef985db62cc910af5c82edb16648853b65f65d8b324425df30b2ec5992214ef9759762cc910ae7cbb07b16648851f65484dd9324429f320426ec99221cf181603764c910cf8c0b01bb2648870f657861d13244395b25c30e899221cb990e18744c910a9ecaf0c3a2648856e643861d13244297b31430e8992218bf86a18744c910e4e49b0c3a2648872ee41861d13244317d0cc30e8992215bb90618744c910e56c910c3a2648852fa58861d13244317f0c430e8992218bd86218744c910e57cb3043a2648872ba59821d13244395b2cc10e899221cac96608744c910e57c33043a2648872ba19821d13244395b0cc10e899221cac86608744c910a5f4a70c3a2648843fa5a861d1324431f720c30e8992211fb90618744c91087f4c10c3a2648852fa50861d1324431792943cc89922187d9521e644c910c5f4a10f322648863e64087991324429f32043cc89922187e87616644c910c3e43b0b322648862fe60749913244387b0a3a4c8992218ee8760a644c910c7643b05322648872b1d182991324431f50ec04c8992218f887602644c910e5c3a30132264886bc60580991324421fb2c43cc8992211f99021e644c910a5f4a6ed322648843f66076991324430feecc2cc89922187c76616644c910a5f4b0e9322648864f61474991324431deecc14c8992218ec7660a644c910cd63a305322648863edd980991324431f0ecc04c8992219b874602644c910c5e4a50e322648862fa50871913244317f303a0c8992218ec87608644c910e563a304322648843fa5887191324421fb31bb0c8992214be941d8644c910a5ecb0e8322648852fa5e64191324429792f320c8992218be87990644c910c5e43cc8322648858f65664191324431d8ecc10c8992210de98dcd715825486f4c0e6b8ac12a4aea53805c56095257128c16e2b00874ae94d8d72d8740a5d4a6c6b86c3a042fa528758951cc29772ec0ae0322612ba98dc57019130c5d4c0c8b86829843ea60765c3414c20ff30baee73222186d7560b739911083ecc4ebb94c88860fa1275dca644420ff30baee53222185d7560f7299110c3cbab01b94c88843b663739ca6444295d29b9ce5322214e990dce7299110a564a306b94c88843ba63735ca644429e323b9ae132221c71755c57099110e70b92e2b84c88868ea15809906444355304c04c832221ab181602641911087dc83053b4a88863ce07805da544429e722b2ae131a2107c976166458d10c1ec28e9322c68843b25d8299163443158e8c14c8b1a218b8746026458d10876cc4c9b92c68851b65664dc9634429e323326e0b1a218f1816037654d1085e4a3043b2a68843ee41821d9534421f720c14ec21a218f381e017610d10a75c830cb90868862b9d182953 else 0xc60580ddb424430fb0d42eeda122187d8661776d0910c9f42d09bb6848864f61684ddb424431bb0d41eeda122195e85a0f76d0910caec2d07bb68488667a1283ddb424432bb0ac1eeda122199e8460f76d0910cb6c2b05bb68488673a0d82ddb4244339b06c16eda122197a8560376d0910cbcc2b01bb6848866ea1180ddb424433b506c06eda12219d98360376d0910cf4c1301bb6848867c60580ddb424430fd0f42eeda122187e8761776d0910d1f42d09bb6848868f61684ddb424431bd0f41eeda1221a5e85a0f76d0910d2ec2d07bb684886a7a1283ddb424434bb0ac1eeda1221a9e8460f76d0910d3742b05bb6848869b61582ddb4244355d08c16eda1221ace8360b76d0910d66c1b05bb6848869e61580ddb4244357508c06eda1221ada8360376d0910d6cc1b01bb684886ba60980ddb424435e302c06eda12214bc9460e76d0910c5f4a50d3b6848863b64a869db424431f720c3ceda12211fb9061e76d091095f4a50d3b684884bb64a869db4244297d29bb4eda12214dd93dda76d0910a76c96ed3b6848853e643769db424429f720c1aeda1221cf381e0176d0910cf9c0f00bb684886bce07805db4244297d29bb2eda12214dd93dd976d0910a76c96ecbb6848863e9db805db4244297d29c18eda12214ed92e0c76d0910e57423043b6848863be0d821db424431db06c10eda122187e95a1c76d0910c3ecad0e3b68488637a4e871db424431bb27438eda12218f990a1c76d091097cc850e3b684886aba11821db424423f321438eda12214dd93dd876d0910a7cc86ec3b6848843fe61761db4244317ced420eda12218ee7660876d0910a5f4a6edb9e848853b64b76dcf424429f321bb6e7a12210fd989db73d091087fcc2edb9e848853b64876dcf4244317eed426e7a12218be76a1373d0910c5ebb509b9e848862f1da84dcf4244257d28432e7a12210fe98dd973d0910a5f4a6ecb9e848853b64b765cf424429f321bb2e7a12210fe981d973d0910a76c90ecb9e848843f65a87d8f424423db2543ec7a12211f990a1f63d091087fcb30fb1e848843f66376d8f4244297d29bb6c7a12214ed92ddb63d0910a7cc86edb1e848843fe6176d8f424431dcecc16c7a12218ec7660b63d091087f4b70eb1e848843fa588758f4244297d29bb2c7a12214ed92dd963d0910a7cc86ecb1e848843fa627658f424421fd303b2c7a12218bf7621163d0910c5f3b108b1e848862f5d88458f42443178ec422c7a12218ef76e0963d0910c773b704b1e848863b5db8258f424431f4edc02c7a12218f976e0163d0910a5f4a70b3b6648853ee41855db324439d705c02ed99221cf381e0176cc910cf5c1700bb6648867ce07805db324421ff30bb6cb992210fe989d965cc910c773b704b2e648863b5db82597324431f4edc02cb992218f976e)) else (if j<4 then 0x221679959937058910e3dbacc9b82c48871e1d664dc162443970e9326e0b12216e9929937058910a7d4b8c9b82c48871edd464dc1624438f0ea326e0b1221cdb65dcf7058910e6cb2ee7b82c48873699373dc1624439b0c9b9ee0b1221d5b75dcf7058910eac3aee7b82c488766dd373dc162443b30e9b9ee0b12214f9969cf7058910abccace7b82c48856ea5273dc162442bb52739ee0b12215e9929cf7058910af8c8ce7b82c48853ee5973dc162442af72ab9ee0b12215b8945cf7058910af5c92e7b82c48857ce4573dc1624439b6ca39ee0b1221cd9651cf7058910e6d320e7b82c48873619073dc162442bb52e39ee0b1221d5b751cf7058910eac3a8e7b82c488766dd073dc162443b30e839ee0b12214fa97d8f7058910e3dbaec7b82c48872edd363dc1624439b0e7b1ee0b1221c7b7598f7058910e3c3acc7b82c48872e1d263dc1624439b6e731ee0b12216e99298f7058910b3dcaac7b82c48871edd563dc162442d7128b1ee0b1221cbb7458f7058910e6c39ac7b82c4885bae4963dc1624429f52e31ee0b1221c7b7518f7058910e3c3a8c7b82c48872e1d063dc1624439b6e631ee0b1221ceb65dcb7058910e74b2ee5b82c48873a99372dc1624439d0c9b96e0b1221ceb63dcb7058910e7531ee5b82c48873a58f72dc1624439d0c7b96e0b1221ceb75d8b7058910f35baec5b82c48873a5d762dc162443cd0ebb16e0b1221eab74d8b7058910e753a6c5b82c48873a1d362dc162443d50e9b16e0b1221ceb73d8b7058910f65b9ec5b82c48873a9cf62dc1624439d2e7b16e0b1221ce873d8b7058910f6439ec5b82c48875add762dc162443ad0ebb16e0b1221dab74d8b7058910ed43a6c5b82c488772dcf62dc162443b90e7b16e0b1221cf365dc77058910e78b2ee3b82c48873c99371dc1624439e0c9b8ee0b1221cf363dc77058910e7931ee3b82c48873c58f71dc1624439e0c7b8ee0b1221d7375dc77058910eb83aee3b82c48876cdd371dc162443b60e9b8ee0b1221dd373dc77058910ee839ee3b82c488778dcb71dc162443dc6c5b8ee0b12214f99020f7654910e78c0b01bb2a48867c60580dd95244297d28418eca92210fd981da6354910c7dbb30131aa48863e1d98098d524421fb31bb0c6a92218ec766086354910c5fc9d09bb6848862f64e84ddb4244387d0b426eda1221c3d85a1376d0910c3ec2f07bb6848852fa5383ddb4244317d09c1eeda12214f990e0f76d0910e2f42d07bb6848871761683ddb4244393d0941eeda1221c5e8560f76d0910e2ec2b07bb68488727a1183ddb424430fb0ac1eeda12218be8460f76d0910c7dc9b01bb6848863e64d80ddb424438f50ac06eda1221c798560376d0910e5d42301bb6848863ee0d80ddb424439b506c06eda12218f98360376d0910e6cc1b01bb6848873 else (if j<5 then 0xb12c48878b1d474d89624438d8ea3a6c4b12214ee979536258910a76cbca9b12c4885aba5383d896244359b0641ec4b1221e4f75dcf6258910f263aee7b12c4887a3dd373d8962443d18e9b9ec4b1221caf74dcf6258910b36cace7b12c48871bdd673d89624438d8eb39ec4b12216ae949cf6258910e563a4e7b12c4885b3a4e73d896244399ee739ec4b122166f955cf6258910b564a2e7b12c48872bdd173d896244399f0a39ec4b1221ccd851cf6258910b674b8e7b12c488733dd473d8962443c9eea39ec4b1221ccd751cf6258910f263a8e7b12c4887a3dd073d896244399ce839ec4b1221ccc741cf6258910f463a0e7b12c48871bdd473d89624438d8ea39ec4b1221cac741cf6258910e67b98e7b12c4887335cc73d89624429df2ea9ec4b12214ec9754f6258910b564a2a7b12c4884bba6043d89624425db3021ec4b12214ee9710f6258910a76cb887b12c48859b65443d8962442dd32021ec4b12214ee97d976258910977cc2cbb12c48874b1d474d89624425db31326c4b122166d959936258910a774b8c9b12c488763dd373d896244399eca39ec4b1221ccd651cf6258910ea7ba8e7b12c4887531d473d8962443b18e839ec4b12214ee97d8f6258910976cc4c7b12c4884bbe6163d8962442cdf2ab1ec4b12216ac9458f6258910a774b8c7b12c48857ce4565dc1624438f52b326e0b1221c79959937058910e74c94c9b82c48873c64664dc162442af32b326e0b12215f1919937058910e5d320c9b82c48853ea5a54dc1624429f32d2a6e0b12215ba94e0f7058910cecc1907b82c48853ea5363dc1624439b107b1ee0b12214f99898f7058910e6db1cc7b82c48857c64663dc1624429f730b1ee0b12214f89458f7058910abdcaac7b82c48856e25163dc162442be722b1ee0b1221cdb8318f7058910e6cb18c7b82c48853ee5953dc1624429f12ca9ee0b12215b89454f7058910e6c31aa7b82c48847ea6043dc1624423f33021ee0b12214fa9610f7058910a7ccb087b82c48855e65443dc162443970c821ee0b1221cdb6310f7058910af4c9087b82c48857c64443dc1624439d70bb16e0b1221ce985d8b7058910e75426c5b82c48873a21362dc1624439d4a9b16e0b1221ceb83d8b7058910e7541ec5b82c48873a60f62dc1624439d107b16e0b1221cea53d8b7058910e74a9ec5b82c48873ad0f62dc1624439d087b16e0b12214fb965d77058910adc4a2ebb82c488576e4d75dc162442bb126baee0b12215eb925d77058910af9c8aebb82c48855ea5c75dc1624429f52fb2ee0b12216eb925977058910e9dbaee9b82c48874e1d774dc1624429f32d3a6e0b1221579959d37058910add4a4e9b82c488576a4e74dc162442bb3273a6e0b12215e9929d37058910af8c8ce9b82c48874edd474dc162443a70ea3a6e0b1 else 0xca3a0e6b122199e871d07358910e8fba8e839ac4887471d4741cd62442cbb2b320e6b1221c5f759907358910e2e3acc839ac4887271d2641cd62442d9b25320e6b1221ccf729907358910a6f4b8c839ac488717dd4641cd624438b8ea320e6b1221ccf7219073589108efcc2e639ac488537e59731cd62442abf2ab98e6b122159c945cc7358910ae7c92e639ac488576e41731cd624421fd2943ec6b122187e87dd76358910976c9509b1ac48862fa1f74d8d6244395ee5ba6c6b12218bf981d36358910e4e498e9b1ac48843fe6074d8d6244317d083a6c6b12218be871d36358910e1fba8e9b1ac488717dd473d8d62443938e839ec6b1221ccf721cf6358910c5ecc0e931ac48870fdd47498d62443878ea3a4c6b1221c5f75dce6358910e4e3a6e731ac48869bdd58298d624434d8eac14c6b1221aac7460a6358910d67b9b0531ac488537a5f6398d624438beebb1cc6b1221c9c74d8e6358910cbdbab0131ac48866e1d18098d624424fd31baac6b12212be972116358910c5f4b908b1ac48862f65c8458d624425792e422c6b1221a3f75211635891087f4b908b1ac4884afa637458d6244395ee5ba2c6b12218bc841d16358910d1fc28e8b1ac48870fdd47458d624434bf0a39ac6b1221c5f751cd6358910d4e420e6b1ac4887271d07358d6244399ee439ac6b1221a6f75e096358910d57ba704b1ac48863b1d38258d62443558e9c12c6b1221acc73e0963589108bf4c6eab1ac48846fa5c8458d6244327eea422c6b122193f851d16358910cb7baf04b1ac48866b1d38258d624432f6ebc02c6b12219b874e016358910c3f43eea31ac48861fa1c7518d6244317f303a0c6b1221c9f931d06358910c5f438e831ac48870fdd47418d62443878ea3a0c6b1221c5f75dcc6358910e4e3a6e631ac4884b7e616318d624431bd0eb18c6b122165f9558c6358910e2fbaac631ac4887271d16318d624421fb2dc3aa6b12211be94e1d53589108fcc870ea9ac4884bb64b8654d624421fd2e432a6b12211be981d153589108de4c0e8a9ac48862fe187454d624431790c3a2a6b12214de9718d5358910c6e438c6a9ac4886a72106354d62443938e831aa6b12210ff9661c43589108fdc830e21ac48843fa5e8610d624425df24c3086b122117c976144358910c5f430e821ac48862f6187410d6244327b0a3a086b12214be971904358910c5f438c821ac48868f6146410d624429bd2fb1886b12218de87d8c4358910e4e3a6c621ac4884bb2598210d62443370e8c0086b1221ab8646004358910d6db1b0021ac4885ab25175d8962442d9f26baec4b12216cc935d76258910b374b8ebb12c48878bdd774d8962443c58ebba6c4b122166d959d36258910e363ace9b12c4885aba5274d8962442d9d273a6c4b12216cd939d36258910f17ba8e9))) else (if j<9 then (if j<7 then 0xcbc3ab013a2c48852fe59851d16244297d31b28e8b12214bf985947458910addc82ca3a2c48852f65a831d16244333f07418e8b12214bf9660c7458910a9fcab063a2c48856be49831d162442b7720c18e8b122153d9520c7458910ad6c91063a2c48856e640831d16244237f30ba8e8b12214bf965d47458910acfc9aea3a2c48856724d751d162442b5f24ba8e8b12215bb905d47458910a9f4b8ea3a2c48852fa5f651d162442d5f24b28e8b122147e97a16645891093e4bb0b322c48851f25d85991624424fb31bacc8b1221c3e851d26458910e1ec28e9322c48868f614749916244387eea3a4c8b1221c3c751d26458910d37bab05322c48869b1d58299162443558e8c14c8b1221a6e8560a6458910d36c2b05322c48872b1d182991624434f50ac04c8b1221cb8746026458910d78c0b01322c48845f25d859916244327b0a3a4c8b12219b8746026458910c3f43eea322c48861fa1c751916244317d0f320c8b122163d959906458910b5cc84c8322c48843fe5987951624423f720c3ca8b12210fe97a1a5458910977c930d2a2c48862fa18749516244317b0c3a4a8b12214be971925458910c5f438c92a2c48871765664dcd6244399b25326e6b1221cd9909937358910aaecacc9b9ac48857664264dcd6244393cc8326e6b12211df985d77358910a6fcb2ebb9ac48856725175dcd62442b9f24baee6b12215db905d77358910a6f4becbb9ac4885b3e4965dcd62443a3eebba6e6b1221d1c75dd37358910a6ecb4e9b9ac48855765674dcd62442b9b253a6e6b12215d9909d37358910e4fb28e9b9ac48872759474dcd62443a3eea3a6e6b1221d1c751d37358910b2ecacc9b9ac488717dd664dcd62443938e9326e6b12216cd929937358910a6f4b8c9b9ac488717dd464dcd624430fb0dbace6b122187d861d67358910c9fbad0939ac48864f1d6849cd6244317b0c3a4e6b122193d851d27358910cae3ad0739ac48863761b739cd624432bb0bb9ce6b122199e84dce7358910c76c36e539ac488673a0f729cd624432f6eac04e6b1221978756027358910cdc3a30139ac488676dcd809cd624433d6e4c04e6b122117e98dd57358910c3fc36eab9ac48864fdd4845cd6244237d31ba2e6b12218bf86dd17358910cd7c16e8b9ac48862fe18745cd6244327f0a3a2e6b122197b75e017358910cddba700b9ac48866e1d3805cd62442bb720b28e6b122195e87dd47358910a6fcb2ea39ac488567251751cd62442b9f24ba8e6b12215db905d47358910aaf4b8ea39ac488537a5f651cd62442d9f24b28e6b122199e87dd07358910e8fbaee839ac4887471d7741cd62443b1ee5ba0e6b12211dd989d07358910a6ecb4e839ac488557656741cd62442b3d293a0e6b12215cd929d07358910aecc84e839ac488727d94741cd6244393a else (if j<8 then 0xd624428fb2b3a2e6b12214be949d17358910a7cc84e8b9ac48868fe14745cd6244387eea3a2e6b12218f884dc17358910b4e4a30a39ac488736dc1851cd624438bb31ba8e6b1221a5e87dd47358910b4e4a2ea39ac488597a5c751cd6244353d0fba0e6b1221e1f75dd07358910f0e3aee839ac488637662741cd624438bd2b3a0e6b1221c5d959d07358910e6cc84e839ac4884b7662741cd624431bd0f3a0e6b122165d959d07358910e2fbace839ac4887171d6741cd62442d3d293a0e6b1221c9d981d07358910e4fca8e839ac488727654741cd6244393b0a3a0e6b1221a9e871d07358910e4fba8e839ac488787dd4741cd6244393aea3a0e6b1221e1c751d07358910c6f438e839ac488717dd4741cd624438b8ea3a0e6b1221c9e741d07358910a6f4bca839ac48853765e541cd62443938e92a0e6b1221cdb709507358910e2ec9eea39ac48852f251751cd624429f720ba8e6b122147e971d47358910e4fc98e839ac48872764c741cd6244387eea3a0e6b1221c3c751d07358910e2fbaee639ac4887271d3731cd624425bf30b98e6b122165f955cc7358910e2fbaae639ac4885a7251731cd62443938e8b98e6b1221cdb93dc07358910e6cc9ee039ac48862fa538754d624431f321c3aa6b12212be94e1d5358910c5e4a10ea9ac48862fa607454d62443179303a2a6b1221c9e931d1535891095f4c0e8a9ac4884af2607454d6244317f0e3a2a6b12218bc871d15358910c6fc38e6a9ac4886a72107354d62443938e839aa6b1221cdb701cd5358910e3db86eba1ac48870fdd474d0d624430ff2b43886b122187c95a1c4358910c7dc850e21ac48861fe558710d624430f92ac3886b12218bc9461c4358910c7dc830e21ac48849f25d8510d624424fb31ba886b122187e87dd44358910c3ec3eea21ac48871edc37510d624424fb303a886b122187e871d44358910c3ec38ea21ac48862f6607410d6244393b263a086b12218be871d04358910c5ec38e821ac48868f6147410d6244387eea3a086b1221c3c751d04358910e5db80e821ac48863761f7310d624434bb0bb9886b1221c5f75dcc4358910e4e3a6e621ac488736dc37310d624431f52ec0086b1221a7b756004358910d3c3ab0021ac4886ae1d18010d624435b6e6c0086b1221cba842137058910a7d4c4a9b82c48853e66254dc162443975092a6e0b12214fa94e0f7058910e6dc1d07b82c48853e25183dc1624439b30641ee0b12214fb9854f7058910a7c4c2a7b82c488736a0d53dc1624429f53021ee0b12214f99810f7058910e5d42087b82c48873660c43dc162443a5ee5baee8b122117d98dd67458910c3ec36eb3a2c48865b60b759d1624430fb0c3ace8b122193c75a127458910cafbad073a2c4886571d6839d1624432beeac1ce8b122197b75602745891 else 0xa0e7458910d2f42d073a2c488697616839d1624438beeb41ce8b1221c5c75a0e7458910d2fbab073a2c488697615839d1624438beeac1ce8b1221c5c7560e7458910d3d42b013a2c48869e615809d1624438f6eac04e8b1221c78756027458910d6d41b013a2c4886b660d809d1624435e302c04e8b1221c7a85dc27458910e3cc2ee13a2c488736a0f709d1624439b307b84e8b1221cf181dc27458910e4fc1d063a2c48872760c831d1624429f720c18e8b1221c3d98dd47458910e1f49eea3a2c48870f64f751d16244297f30ba8e8b12212bf985d47458910b4fc9aea3a2c4885a724d751d162442c7d2e3a8e8b1221c3f75e0c7458910e1fbad063a2c48870f1d6831d16244353f07418e8b122163f9560c7458910e1fbab063a2c4885aee41831d162442c7b2a418e8b1221c3f7520c7458910e1e3a9063a2c4885ae640831d1624438f6e1ba8e8b122163d959d07458910e1fbace83a2c48870f1d6741d162442d3d273a0e8b122169d939d07458910e5d4a6e03a2c48872ea13701d1624431bf26c3ca8b12218dc9361e5458910c7dc830f2a2c48862fa1c749516244317b0e3a4a8b1221c5d98dd77358910e6db86ebb9ac4884b7e6175dcd62442d3928baee6b1221cdb705d77358910b2ecad09b9ac488717dd684dcd62442db321426e6b1221e1f75dd37358910f0e3aee9b9ac488717a5674dcd624438bb2b3a6e6b1221cd9909d37358910b2ecace9b9ac488717dd674dcd624438b8eb3a6e6b1221cdb709d37358910e4ecc0e9b9ac488727e5474dcd6244393b2a3a6e6b1221c9e841d37358910e4fba8e9b9ac488787dd474dcd6244393aea3a6e6b1221e1c751d37358910e2fba8e9b9ac4887171d474dcd6244393ce83a6e6b1221cdb701d37358910a6f4bca9b9ac48853765e54dcd62443938e92a6e6b1221cdb95dc37358910e6ccaee1b9ac488736a5370dcd624439b129b86e6b1221cda84dc37358910e6d2a6e1b9ac488717a4f75dcd624438f6e1baee6b122187f75a137358910e1fbaee9b9ac48851f65674dcd6244297d293a6e6b12214f9909d37358910e4f498e9b9ac48872724c74dcd6244317d083a6e6b1221c3f751d37358910c7d426e1b9ac488736a4f70dcd624439b127b86e6b12218f980dd67358910a5e4a2eb39ac48853ee41759cd624431f300bace6b122147e971d67358910c5fbad0939ac48868fdd6849cd6244317aeb424e6b1221a3c75a127358910c5ecc0e939ac48868f614749cd6244387eea3a4e6b1221c3c751d27358910c6fbad0739ac4886375d6839cd624434b8eb41ce6b1221a5d85dce7358910e2fbaee739ac4886a7a13739cd62443938e9b9ce6b122187e98dd5735891093f4c6eab9ac48871edc3755cd6244347eea422e6b122187f75211735891095f4c6e8b9ac48870fdd7745c)) else (if j<10 then 0x2ee417619043442b7720bb0c821a21cdb905db6310d10aedc82edb18868873a643865c843442bd321c32e421a21cae94a197210d10a774b50cb90868863be1a865c8434438df2ac32e421a21c6c956197210d10e564a30cb908688733e4d865c8434439d720c32e421a218ee866197210d10af5c830cb90868853ba60865c8434431df0c432e421a218ed862197210d10c7cc870cb90868847e643865c8434421fb31432e421a214ed92a197210d10a77c930cb90868853ee41865c8434421fd2c432e421a214fa96e097010d10a7dcb304b80868857ce45825c043443b60c9c0ae021a21dd363e057010d10a77c93073a6c48863b64a879536244317d0f3a4a9b1221aae7460a54d8910d56c9509b9ec48853b64874dcf62443179093a2e7b12214ed921d173d8910c76c16ea39ec48863b609751cf624425bf30b98e7b12218ed9221d53d8910c6e43ce6a9ec4886b39cf8254f6244317d2943887b12218ed92a1c43d8910c76c930e21ec48862f6627410f6244393b273a087b12218be879d043d8910d1ec2ce821ec48863b65d8210f6244355ce8c1087b12218fb9760043d8910d74c930021ec4886ab25182d976244359f26c16cbb1221acc9360b65d8910c3ec3d0b326c48861f61d85993624431f30ec04c9b1221a7a8560264d8910d78c0b01326c4886ab9d1821936244395ce8c10c9b12214bd9799064d8910b1ecacc8326c4885ae64264193624421fd2d43ca9b12211fb9061e54d8910976c950d2a6c48843fe5d869536244317d0d3a4a9b12218bd8719254d8910977cb3052a6c48866b9d182953624429bd2db9ce7b12211df985cc73d8910c6f432e639ec48843f65e84d8f6244317d093a6c7b12218ee7460b63d8910d6739b05b1ec48863761f6398f624421fd29c3ac7b12218bf9721163d8910d56c9108b1ec4884bb6488458f624421f9313a2c7b12218bc849d163d8910d564a30431ec4886b35cd8218f624425bf30b18c7b12214df9758c63d8910b2fcaac631ec48847e6438754f624421fd2c43aa7b12210fd97e1953d8910976c910ca9ec488637e1c6354f624435390831aa7b12212ed96e0953d891087f4b50e21ec4884bb64a8610f624421ff2ec3087b12218be869d043d8910c9ec2ce821ec48862f61c6410f6244347b0a32087b12218dd87d8c43d8910e4f3a6c621ec4884bbe598210f6244335ce8c1087b1221ab86460043d8910d6db1b0021ec48858fa5283dd562442cf32141eeab1221c7a94dc37558910e3c4a6e1baac48871ee4f70dd5624438f527b86eab1221c7993dc37558910e3c49ee1baac48871ea0f70dd5624438f307b86eab1221cbb93dc37458910e5cc9ee1ba2c48868fa12859d1624428fb31bace8b122127d98dd67458910e3db86eb3a2c48868f1d6849d1624434beeb41ce8b1221a5c75 else (if j<11 then 0xa221cf381e017695110cedc1f00bb4a88867620f805da544433e703c02ed2a2214bf976086495110e5dc82ec324a88856ee4176192544431f321c32e52a2211f990e19729511087ecc50cb94a88853b64a865ca544429df24c32e52a2214fb90619729511087f4b10cb94a88863b259829d3634432f30ac04e9b1a219ea8260274d8d10cf4c13013a6c68867c605809d36344355d09414c9b1a21a798560264d8d10d7541301326c6886ba60980993634435e302c04c9b1a21c3d959d064d8d10e57494e8326c68872b64a7419363443973213a0c9b1a210ff9760864d8d10adcc84e8326c68858f65664193634428fb2b322e5b1a214ed9299172d8d1087f4c0c8b96c68862f210645cb6344257928c16cb31a218ed97e096598d1087ecbf04b2cc68853b64b655ca634421f930b2ae531a215eb925957098d10af9c8acab84c68852fe59821d1634428f92ec2cc8b1a21c3d851d26458d10a774bd05322c6886aba128299163443958e9414c8b1a218ec9760a6458d1087e4bb05322c68862f1d182991634429d92ec14c8b1a21cac7460a6458d10d3cc2b01322c68872e1d180991634435d504c04c8b1a21ae9826026458d10d78c0b01322c68845f25d859916344327b0a3a4c8b1a211ec9760a6458d10cd63a305322c68866e1d18099163442c7b2b320c8b1a214ed989937258d10c76cc4c9b92c68871b65664dc9634439d321326e4b1a211ed989937258d10ab6cacc9b92c68857a64264dc96344395d08326e4b1a21cae641937258d1087ecc4c9b92c68851f65664dc96344317d08326e4b1a214ed921937258d10e3ccacc9b82c68873aa4a64dc1634439d325326e0b1a21cf1919937058d10abccacc9b82c68857a64a64dc163442be323326e0b1a21cb8841937058d10e5d320c9b82c68843fe5d82d946344257928c16ca31a218df92e1d6318d10c6ec970eb18c68843fa63655c8634429df24b2ae431a218be962117218d10c5fb2908b90c68862f594845c86344297d29c16eca9a214f990e0b7654d10e78c0b01bb2a68867c60580dd95344317928c10eca9a218dc936087654d10c7dc83043b2a68852f251821d9534429f720c10eca9a211bc946087654d108fdc83043b2a6887366437618d53442bb321bb0c6a9a214be94e1b7254d10a76c970db92a68853e64386dc9534421fd2d436e4a9a218fb9061b7254d108fdc830db92a68843fa6086dc9534429db24436e4a9a2187f9560a7610d10c3e4ab053b0868862f251829d8434431bf26c14ec21a218fb9060a7610d10a5e4a3053b0868853ee41829d8434423f720c14ec21a218bc84e097610d10a7dc8304bb0868872e213805d8434439e703c02ec21a219b884e017610d10cf9c0f00bb0868870f5d7821904344297f2ec10c821a218bd876086410d10e1ebab0432086887 else 0x7b94c88862fa1373dca644421ff30b9ee5322218be845cf7299110d3d3ab01b94c88869e5d580dca644431f6e6c06e5322218f9736037299110d3d42b01b94c88869e61580dca644438f4eac06e532221c79756037299110d5d42301b94c8886b6a0d80dca644435b306c06e532221af1816037299110e57c9ce9394c88872b64e749ca644425db31b9ce5322218ed87dce7299110b74c86e7394c88863b61d739ca6444297928c1ae5322216ac9460d7299110a774c6e6b94c8884bba63735ca64442dd321b9ae5322210fe98dcd7299110a77c92e6b94c88871b9d7725ca644438daebb92e5322216cd93dc97299110b74c86e4b94c88871e5d7735c264442dd325b9ae1322216f191dcd7099110e3cbaae6b84c88871e9d7725c264442db327b92e1322216f191dc97099110e75c1ce4b84c88873a60e725c264442dd32f392e132221ceb739c97099110e74b9ce4b84c88873adcd725c2644439d2e6b92e132221c7a755c97099110e79c1ae2b84c88873c60d715c2644439e704b8ae132221cf1825c57099110f393aae2b84c88879c5d5715c2644439e6e6b8ae132221cf1735c57099110e79b92e2b84c8887b89c9715c2644439e2e4b8ae132221ee1725c570991108bfcc2ebb9cc88865b5d582dce644432f2eac06e73222117d989d77299110c3ec34ebb94c88864fa1275dca644422ff30baee53222187d865d77299110caebab07b94c88865e9d580dca644432f2eac06e5322211ed98dce7299110ad74a6e7394c88857a643739ca64442b5928c1ae5322211ee98dcd7299110af4c86e6b94c88857a64b735c264442be323b9ae1322214f996dc97099110aecc9ee4b84c88857c647725c264442bd32f392e132221d72755c57099110eb8baae2b84c8887789c9715c264443bc2e4b8ae132221aae94e097319110d5c4a700b98c88843fe6173dc86444297928c1ae4322214fb9060d721911087f4c6e6b90c88853be49735c86444347b0bc1cc8322216ad92e0e6419110b5cc8707320c88868f615839906444347b0bc14c83222169d93e0a6419110b5cc8705320c8885ab662829906444355f07414c832221aad83a0a6419110d1ec2b05320c88878ea158099064443c730ac04c832221abb826026419110f5541301320c8886ae6098099064443d5304c04c832221eb1816026419110d9d42b01320c8886ce615809906444375504c04c832221ba9826026419110dd8c0b01320c88858f65664dcc64442c7b2b322e632221aae64e097319110d5d32700b98c88858f65664dc864442c7b2b322e4322218bc9460a7695110c7dc83053b4a88852f251829da544429f720c14ed2a2211fb9060a7695110c6fc1f04bb4a88863720f825da544431bf06c12ed2a2218dc836097695110a7dc8304bb4a888736e0f805da544439b107c02ed2)))) else (if j<18 then (if j<15 then (if j<13 then 0xf22b92e232261eb190dc57119130b5cc9702b80c8985aee5d815c0644c39772ec0ae0322616bb926057019130f59c0b02b80c8985aea63715c0644c357531b8ae0322616b992dc57019130b5dc92e2b80c8987ace05715c0644c3d66e2b8ae0322612bd92a137119130a7dc8304b88c8984afa53825c4644c21fd31b92e2322614f7915c97119130b5b4a6e2b88c8984bde45829d3614c356d08c08e9b0a610fd989d372d853097a4a303b96c29873a5c980dcb614c35e302c06e5b0a618bc849d172d8530a76c94e8b96c29843fa60745cb614c2dcb23b92e5b0a6187f9560a76d0530c5e4a3053b6829863de45829db414c31f720c14eda0a614bc9460a76d0530a7bc8b053b6829853ee41829db414c257928c14eda0a612f79160a76d0530a5f4a7043b6829853d647821db414c396d08c08eda0a61ab68460476d0530a5f4bf0432682985ad64782193414c297f2ec10c9a0a610fd989db72d053095f4b509b96829862f9da84dcb414c3178ed426e5a0a612bf9819372d053097a4b303b96829863d9d981dcb414c31e8ecc0ee5a0a61ab46460772d0530c7d3b301b96829863e1d980dcb414c3570c8c06e5a0a618be9819172d0530e57c90c8b96829853b64a765cb414c21fd303b2e5a0a618ed92e1f62d0530a76c970fb16829862fa5287d8b414c31eb2343ec5a0a612be94a1f62d053097ac8d0fb16829843f66287d8b414c21fd2e43ec5a0a612be9421f62d053097ac890fb16829843fa6087d8b414c29db2443ec5a0a618ee875cb62d0530a7b4bf05b0e82985ada5382d87414c29ef2ec16c3a0a612f698dcb61d0530b5b4a6e5b0e82985bc64372d87414c397530322e1a0a61cbb9219170d0530e5cc90c8b86829853ea5b825c3414c3970c9c12e1a0a61cb86460970d0530e794c6c2b86829873ce4b615c3414c39e325b0ae1a0a61cf382d8570d0530e78c16c2b86829853ea60765c3414c31f5303b2e1a0a61cba941d970d0530e78c88ecb8682984bea60765c3414c2d75283b2e1a0a616f1911d970d0530d5d4c0c8b8682987ac644645c3414c23f531b92e1a0a614fa96dc970d0530e5c326e4b86829853e259725c3414c3970c8b92e1a0a61eb294d8570d0530e79b96c2b86829873c5cb615c3414c317d2c422e5b2a215e990a0f725951093fcc2ebb9cc88869b5d582dce644430faeac16e732221a79756037399110c3ebaf04b9cc88869b60985dca644428fb313aee53222127d989d77299110a3fcc2ebb94c88849fe6175dca6444347d0b426e532221a3d85a137299110e1f3ad09b94c88870f5d684dca644434bd0b41ee532221a5d85a0f7299110e2f3ad07b94c8887175d683dca6444353d0941ee532221acd82a0f7299110d2ebab07b94c88869761583dca644438bceac1ee532221c5d7560f7299110d4f4230 else (if j<14 then 0x40a774b6e7396c3a056ba53739cb61d02bcb23b9ce5b0e815e990dce72d8740b574a6c7396c3a072b9d3639cb61d029df2eb1ce5b0e81cae7458e72d8740e73b1ae3396c3a073958d719cb61d029dd2dc1ae5b0e815e990e0d72d8740ad64a306b96c3a057ae41835cb61d029dd31b1ae5b0e815ae94d8d72d8740a77cc2c6b96c3a043fa63635cb61d0297d29b1ae5b0e814ed92d8d72d874087fcc2c6b96c3a053be49635cb61d023dd31b9ae5b0e814ee96dcd72d8740ad74a6e6b96c3a057a643735cb61d02d5d29b1ae5b0e814ef9758d72d874093ecc4ebb16c3a049fe6175d8b61d0387aeb3a6c5b0e81a768560762d8740d3ac2b03b16c3a066d9d181d8b61d02b7529b1ae1b0e815ba94d8970d8740e9d3ace8b86c3a074e5d6745c361d02b7529b9ae1b0e815e992dcd70d8740af8c8ee6b86c3a071e5d7635c361d02d7529b1ae1b0e81c797558d70d8740a7d4b6e4b86c3a056ea53725c361d02bb327b92e1b0e815f191dc970d8740e75b1ce4b86c3a073a58e725c361d02bd32f392e1b0e81daa749c970d8740e75b1ae4b86c3a073a58d725c361d03b54e8b92e1b0e81c7a75d8970d8740e5d3a6c4b86c3a052fa5383dc961d029eb23c1ee4b0e814ed92dcf725874087fcc2e7b92c3a043fa63735c961d021fb2543ec6b0e81ab591a13635874097bc8b05b1ac3a043fa5f8258d61d025eb23c12c6b0e810fe98d8f7258740a5f4a6c7b92c3a053b64b63dc961d021ff30b1ee4b0e8187e87a176258740c3f43b0bb12c3a062fa1e84d8961d0347b0b426c4b0e818fa876036258740d3d42b01b12c3a06aea1180d8961d0356d29c0ac4b0e816b694e056258740e73b9702b12c3a04eda538158961d0366d0b426c2b0e81b3585a136158740a7b4bec7b0ac3a05ada5363d8561d025ef30b1ec2b0e81ba684a0b6158740dd342305b0ac3a053da5f62d8561d0356d09b16c2b0e812f79858b6158740d5b422c5b0ac3a06bcd8d80d8561d035e2c6c06c2b0e81af3626036158740d78b1301b0ac3a06dca1580d8561d036e30ac06c2b0e81bb2846036158740df141301b0ac3a06f860980d8561d025ef22c16eab0e614ed92dd7725873087fcc2ebb92c39843fa63755c961cc35cf05c0ae4b0e61af381e017258730a5f4a705bb2a39863de4582dd951cc31f720c16eca8e614f79160b7654730a7dc8305bb2a39852fa5386dc951cc29db25c36e4a8e618be94a1d6254730c76c950eb12a39852fa528758951cc29db2543ac4a8e614f697e096154730a7dcb305b82a39873ce6161dc151cc39e724b0ee0a8e61cf1925877054730e79c12c3b82a39873c60961dc151cc297d2fc16e23226163d95e0b7119130b5ac8ee5b88c8986aee0980dc4644c357304c06e2322614bf976097119130b5dc8304b88c8984afa63725c4644c2d6 else 0xd680d500d380d200d080cf00cd80cc00ca80c900c780c600c480c300c180c000be80bd00bb80ba00b880b700b580b400b280b100af80ae00ac80ab00a980a800a680a5009f009d8090c0888084c07c80768072c071406b4069c0684066c0654063c0624060c05f405dc05c405ac0594057c0564054c0534051c050404ec04d404bc04a4048c0474045c0444042c041403fc03e40384036c0354033c0324030c02f402dc02c402ac0294027c021c020401a400fc009c003c00029bf2e90ee6b04a94dc974877358254b6dc8243b9ac12a537e5d211cd609529b92e908e6b04a96db904847358254c6fc16e7b8ac12a637e0873dc56095257928c16e2b04a98df7360b7158254c6e39b05b8ac12a4bee4182dc5609529eb23b96e2b04a94de98dcd7158254c6ec16e6b8ac12a4b7a63735c5609529bd3039ae2b04a98dd821cd715825496f4c0e6b8ac12a637dcf825c5609531b8e7c12e2b04a90fe98dc97158254e6bb9ee2b8ac12a7351cf715c56095357529c02e2b04a9adb73e017158254d6c39f00b8ac12a5aea53805c5609535b707c02e2b04a9ad883e017158254e6db9f00b8ac12a7361cf805c5609535e703c02e2b04a9ad696e0520cc553cebc3f0290662a9eb6a0d80dc76054e5f321c12e3b02a70fe98dc971d8153a7bc8ae4b8ec0a9dbc643715c76054e9f52fc16e2b0087ab89460b7158043b5c4a305b8ac021dbc64772dc56010f57109c12e2b0087adb83e097158043a7dcbb04b8ac021eae211825c56010f5b706c12e2b00872fa98dc97158043b79c8ae4b8ac021fac213715c56010fda707b8ae2b00872bc9460b715804397dc8305b8ac021d3d64772dc56010e1fd31b92e2b0087aba94e01715804397cc9700b8ac021eae213805c56010f5b707c02e2b0087af381e01715804397bc8b0539ec2a843f66273dcb615429eb2239ee5b0aa14ed929cd72d855087f4c0e6b96c2a853d644735cb61542dcb23b92e5b0aa10fe96e0971d8f408df4a704b8ec7a043fe5982dc563d0237928c16e2b1e815af9260e74d8740adbc8b073a6c3a056ee41839d361d022ff30baee7b0e8187e865d773d8740c9ebad09b9ec3a062fa1a74dcf61d032daeac16e7b0e819ae7460b73d8740c7b432e3b9ec3a066da1171dcf61d032f2eac06e7b0e819ba7460373d8740cf8b8b01b9ec3a068f5d684d8f61d0387aeb3a6c7b0e810ff9760b63d8740cdb3a303b1ec3a043f64b8758f61d030ff0ebaac7b0e818bf879d163d8740e1ebace8b1ec3a045f66275dcb61d030fd0d3aee5b0e8117f985d772d8740c3f432ebb96c3a065d60575dcb61d0327ceb426e5b0e8193d75a1372d8740c5f434e9b96c3a06575d583dcb61d0333ce8c1ee5b0e8197a7560372d8740cbcbab01b96c3a066e9d180dcb61d0335b0f3a4e5b0e811ed98dce72d87)) else (if j<16 then 0x4adc4ad64ad04ac5cabfcabc0ab84aab8aa58a9f8a974a938a920a8c0a860a848a830a788a704a680a668a62ca584a548a4a0a488a404a3a4a2fca230a1d0a194a158a0f8a050a0149ffc9fe49fcc9fb49f789f609f489f309ef49eb89e7c9e1c9d749cf09c6c9be89b649abc9a389a20997898f498949810978c972c96a89624957c94d4947493f09390933092d0924c91c8918c9174915c914490e49084906c8fe88f888f048ea48dfc8d788d188c948c588bb08b088a848a00897c88d488bc885c87d887c0873c86b8863485b0852c84f084d884c084a88448840c83d0837082ec826881e4818480b880107f687f2c7f147efc7ee47ecc7eb47e787e187e007de87dd07d4c7d347d1c7cbc7c387c207bc07b3c7b247ae87ad07a947a107968795078f078b4789c7818780077c47740772876a475fc75e475cc7548747c746473bc735c72b4725471ac712870806ffc6f9c6f606f006ec46e646e046dc86d8c6d506d146c906c306bd06bb86b106a8c69e469846948690c68ac684c67ec67d467bc6780674466e466a8664865c465886570651064b06498645c642063e463a8636c633062f462b8627c6240620461c86168610860a860485fe85f885f045eec5eb05e745e385dfc5dc05d845d485d0c5cd05c945c585bf85bbc5b805b445b085acc5a905a545a1859b8595858f85898581457d8579c573c56dc567c561c5598555c54fc549c54845448540c53ac532852a45268522c51cc514850c450404f984f384efc4ec04e604e244e0c4dac4d4c4cec4c8c4c504c384bb44b784b3c4a944a3449f84974493848d84878481847b8477c471c46e046a4466845c04584456c4554453c450044a0441c43e0438042d842544188414c40c83ffc3f9c3f603f243e583df83dbc3d5c3cfc3cc03c3c3bb83b7c3af83a983a5c3a2039e43984394838c43888384c381037b03750373836fc36c03660360035a03564350434c8348c342c33f03390333032d032943258321c31bc315c312030c030a8306c30302f882f282f102ed42e742e382dd82d782d182c942bec2b8c2b2c2af02a902a3029d02994295828d42874281427fc279c2760270026a02664260425a4254424e42484242423c42388234c231022d42274223821d821782118207020341ff81f981f5c1efc1ee41e841e001da01d401d281cc81c8c1c501bf01bb41b781b181ab81a5819d4197418cc18b4189c1884186c1854183c1824180c17f417dc17a017881770175817401728171016f816e016801668165016381620160815f015d815c015a8154815301518150014a0146413e013c812fc129c1284126c1254123c1224120c11f411dc11c411ac1194117c1164114c10ec10d410bc0fa80f480f300f180f000ee80ed00eb80ea00e880e700e580e400e280e100df80de00dc80db00d980d8 else (if j<17 then 0x9643563f96375635d6291627962616249623161f5614d603960215f555f3d5f015ee95e895e055d5d5cfd5ce55c615bdd5b595b415abd5a815a695a5159f15991590d58ad582957ed57d5575156f1566d565555ad5595555954d5542d53a9536d535552d15295525951f9515150cd506d50314fd14f954f594f1d4ee14e814e214dc14da94d6d4d314cd14c954c7d4c654be14bc94b694b2d4acd4ab54a9d4a854a2549c54965492948ed48b1489948814869482d47cd47b5479d4785476d46c5464146054581452144e544a9442543a142d54275425d41d941c140f5404d3fc93f213e793df53ddd3da13d653d293ca53c453b9d3b3d3ab93a3539d5395138a93795373536d5362d35853525350d34d133bd32f1326d31a130d530752fa92f252e7d2db12d512ca92c492be92b892b052ac92a452a2d29f129b5299d29612949293128d128b92835281d27e127c92769272d26f126b52679261925dd257d254124e12481242123e523cd2349227d2241220521c9218d212d20a9206d1fe91fad1f711f351ef91ebd1e5d1e211de51d3d1cdd1c7d1c1d1bbd1b391ab51a5519f51971191118b1185117f11791173116d1169515c9154514e514851449140d13ad134d12c9126911e511a9112510e910410fe10fa50f690f2d0ecd0e6d0e0d0dad0d710d350cf90cbd0c5d0c210b790b190add0aa10a650a2909c909b10975093908d90879083d07b9073506f906e106810645060905a9056d053104d10471043503f90399033902b5025501f50171013500f900bd00810020ff9cff3cff00fec4fe64fde0fd80fcd8fc9cfc18fbb8fb58fad4fa74fa38f96cf90cf8acf84cf7ecf78cf708f6a8f648f5c4f540f528f4ecf4b0f450f3f0f390f354f2f4f270f1ecf1b0f174f15cf144f12cf0ccf048efe8ef88ef28eea4ee68ee2ced60ed24ed0cec1cebe0eaf0ea00e9c4e9ace994e97ce964e94ce934e8f8e8e0e8c8e844e7e4e760e6dce67ce640e604e5a4e544e49ce43ce424e37ce31ce2bce25ce1b4e130e0d0e04cdfecdf44dee4de60dddcdd7cdcd4dc08dbf0db6cdaa0da64da04d9c8d968d92cd8f0d86cd7e8d7acd770d758d740d704d6ecd6d4d6bcd6a4d5fcd5c0d53cd500d4c4d464d428d3a4d320d2e4d2a8d248d1e8d1acd194d17cd11cd104d0a4d020cf78ced0ce4ccdeccd8ccd08cccccc48cbc4cb88cb4ccb10ca8cca2cc9ccc948c8e8c864c7e0c780c744c6e4c684c624c5c4c564c4e0c45cc420c408c3ccc348c2e8c264c228c1ecc18cc12cc114c090c030bff4bf70bf10beb0be50bdf0bd90bd0cbcd0bc94bc34bc1cbbbcbb38bafcbac0ba60ba48b9e8b9d0b9b8b9a0b988b904b880b820b79cb718b694b634b5b0b550b4f0b4d8b454b3f4b394b334b2f8b298b280b268b208b1a8b148b10cb088b004af80af20af08ae84ae2 else 0x2133212f612961212118e1152111610b61056101a0fde0f7e0f420f060ea60e6a0e2e0dce0d260cea0cd20c720c120b6a0b520af20a920a560a1a09ba095a08fa0876083a07b6070e068a05e205ca05b20576055e04b6043203d2034e02ee028e025201f20192013200d200ba0059fff9ff75ff39fed9fe79fdf5fdddfd7dfd65fd4dfd35fcd5fc99fc15fbd9fbc1fb85fb6dfac5fa65fa4dfa35f98df92df8a9f86df855f819f7b9f735f6d5f675f5f1f549f4a1f3d5f399f315f291f231f1adf129f0c9f069f009efcdef6deee9ee89ee4dee11edb1ed75ed39ecd9ec31ebd1eb71eb35eb1deabdea5dea21e9c1e93de925e90de8f5e895e7ede78de775e75de721e709e6a9e625e60de5ade571e511e4d5e475e439e421e3c1e33de301e2c5e265e24de235e1d5e175e0f1e091e031dfaddf4ddeedde69de51de15ddd9dd55dcaddc05db5ddb21db09dacdda6dda31d9d1d995d935d91dd905d8edd8d5d8bdd839d7b5d755d719d6ddd6c5d6add671d5edd5b1d575d55dd545d509d461d425d3c5d341d2e1d239d1b5d131d089d005cfedcf8dcf75cecdce49cde9cd89cce1cc81cc21cb79cb19ca95ca59c9d5c951c939c8fdc8c1c885c825c7c5c765c729c6edc68dc675c639c5d9c555c4d1c44dc3edc369c2e5c285c249c1e9c1adc195c159c11dc0e1c05dc021c009bfcdbf6dbec5be65bde1bd15bc6dbbe9bbadbb71bb35bad5ba99ba81ba45b9e5b9a9b96db8e9b841b7bdb6f1b691b60db5adb505b481b445b39db33db325b27db21db1bdb15db0d9b079b03db001afc5afadaf95af59af1daebdae39add9ad79ad3dacddac59abd5ab51aaf1aa6daa0da9d1a971a8eda869a7c1a719a629a5c9a569a509a4a9a3dda2eda2d5a275a239a1fda1c1a185a149a0e9a089a04da0119ff99fe19fa59f699f2d9ef19e919e0d9dd19d959d359cf99c519bf19bb59b559ad19a4d99c999b19999995d9945992d98f198b5987998619849980d97d19771971196d596bd96819645960995cd956d953194ad9471943593f99399935d932192e592a9924991c5918991719135911d90e190a590458fc18fa98f918f558ed18e718e118dd58d518d158c918c558c3d8c018bc58bad8b958b118a8d8a758a3989fd89e589cd89b5890d88d18895885987f987bd875d872186c1863d85b9853584d58499843983b5833182f58295823581d58199813980d980557fd17f717f357ed57e757e157dfd7dc17da97d6d7d317cf57cdd7c357b8d7ae57a857a6d7a557a197995791178d5785177cd7701765975f975e17581754574c1746173dd73a1731d7299721571b5713170656fe16fc96f456ec16e616e016d596cd56c756c156bb56b556af56a716a3569d56975693968fd68e56819680167a16789674d6735671d66996681662165c165856549650d64f564b))) else (if j<21 then (if j<19 then 0x164c00102000178520178520164fc217841f083e107c20822421484190880269800269800213215488312600c0c1046c020402530004014c0010202c530ea6000811530808af842e883d10422200ae60b80113f4822b3c02b90402f9dc8201f49a4175bcbd2e808000000000000000d004000000000002c261080000000000000b0984200002c2610ba008d80db40c01b2d68541800a370384000000000000000000000783a84000363abd3a7e2f0ec0770ec02000000000000000000000000000000000000000000000000000000000000000000000000000000006db40809af4fc5e1d80a365ac003780278bb1d43ba3c02b802038ae01000000000000000000000000000000000000000000000584c21000000000000000016130840584c21160ae55c989e2f0856130849706760275c67566754e751274b2745273f273b6737a733e730272c6726672067182712270c2703e7026700e6fae6f4e6eee6eb26e766e3a6db66d7a6d3e6cde6c7e6c1e6be26ba66b6a6b0a6a866a4a69ea6966690668ca686a6852683a679266ea664265e2651664b66456641a6372633662d66276623a61b6613260ae6072605a5fd65f9a5f825f6a5f2e5ef25eb65e9e5e625e265e0e5dd25d725d365cd65c9a5c5e5c225bc25b865b4a5b0e5af65a725a1259d659be595e5946590a58aa584a580e57d25796575a56fa56be563a55fe55c25586554a54ea54ae547253ee538e532e52ce524a51ea51ae5172515a50fa507650164f924f324f1a4e964e7e4e424e2a4dee4dd64d9a4d3a4cfe4c9e4c624bde4bc64b664b064aa64a6a4a2e49f2494a493248d24896483647fa47be47824722470a46aa466e463245d24572453644fa449a445e444643e643aa432642ea42ae424e4236421e419a415e4122410a40ce40924056401a40023fea3fd23f963f7e3f423f2a3f123ed63ebe3e823e6a3e523e163d923cea3cae3c4e3c363bd63b763b3a3b223b0a3ace3a4a3a323a1a3a0239a23942392a38ee388e3876385e3846380a37f237923732371a370236ea368a364e361235fa35be35a6358e3552351634b63456341a3396335a32d632be32a6326a3252323a31fe317a311a30ba305a30422fe22fa62f6a2f0a2ece2e6e2e322e1a2dde2d362d1e2ce22ca62c6a2c522c3a2c222bc22b862b4a2b0e2af62aba2a3629d62976291628da28c228aa286e283227f627ba27a2276626be263a262225e625aa256e253224d22496247e244223e223a6236a22e622aa224a21ea21ae217220ee208e202e1fce1f6e1f561f1a1ede1ea21e8a1e4e1e361dd61d9a1d821d461d2e1cce1c921c561c3e1c261bea1b661b2a1aca1a8e1a5219f219b6197a193e190218c618ae1872181217b21776173a16fe16e616ce16921656163e162615c6151e14e214ca1446140a13ce139 else (if j<20 then 0xf02260413c74f0280100e980ae01f4c02114f43810088780294f027017030008f00d4c1c0c002e9886e10011e808000003c0100001e80bc017802f471047429e8542274f42b00fa7a1d807d3d0ec0329e87601f4d43b03809d3d0ec0300ec53c81c04e9e86601e8660114f42700fa7a19807a11805d3d0cc03e9e8660194f43709809d350cc0e0268660174f43300ee1100aa73008ed300ae870180770881c03380200002d1a6134d60101d3d0ec03d0ec02e9e85601e856011e0a7a15089d3d0ec03d0ac02e9e8760194c1e9a87607010ea53d0a844e9e87601f4f42b00ca7a1d807d350ec0e0200b46984f469ac0303a7a1d807d3d0ec03e9e87601f4f42b00fa7a15807d30400001c54c204033804115308ee533806783b64039ad4ee019e12011da6b74a99c0502dd2a77010f053c81c04e98200000002d017a2c02000016af47806000f4b804943a3c0301207009e890380603c0102e009e1e8f00d2a757a3c040361700aa608153d0a40302a60d4f43b00c05a1d1a61bd1a6b03808000b83c34c35a9d5e8d3780a074e43b0b809d39085d390ac0e0274e42174e43b0b80921d85c0369c87617013617078066100046106c2610bc2081006101642148410283e104ae0959e8500cad5009e9500800415ca00010ac05ba0608ab984002021ac13d016803576b05577a04576804000d705a00b5aa0154016814026b015e81d40101af500aa0d0080f083e107c20f841f083e107c20f841f083e107c20f841b0d402b0d402b09402b0d402b0d402b0d40230d41a0181d006a00d401e803d007a00b401e802d006a00d401681402a8035007a00b401e803d005a00f40129f8426800026800027080027080400180010003e12805e1e805e1280461e80408308003308361308461e80407841f08321e804572800030414000194010282752984080374c30274fa01823a7d00c1005e9f404e80002e802500402000ba0081e1e805e18805e188040702840504001784021f84102820823295c8278620178410429620180c1cb81424ba40212e402cbe4020402254985e107c208081040180a04100a0800000807c3100811100007d007c3d0080e96da64c4cb6d3201e580bb4c9e405e80203e80003041592ad4018b13f085e106260821ac956a0005f0c402f08321e804089085e1040c610006d3b0dc033082d3b0dc03b0984202820407c20a53c21484103016421f841f082e107c5e10b26e1080aa03180727e10bc37008c20008c20d84c2119012183d31005e104c22008102009a7e10810088011002611004435805b005a620080f08330051026720804f0cc0202600a204014c0121800202ec02d8000200ec00018180a040188430005d300040407a6000ba6000ba60009200820142a0e60196148100d20100978184d30410d30ba6200b2008200010040 else 0x3f085e10643300a433008a6b008a608036308c033c0d8e853580be107c20f841f082621805d3f0ec03f083d3316c03f083e107c20f841f082611805e107a608dae9901809d34805b04805d3480493d80436e9c4035a74e201cc220164e6010db27300f6130092d300920300b2f100b2f100a26900b2f5308600e5ba95369e405e9f87601f862014846012c01580353000517880517ea14c3037842e9804001f841cbe40001f8415c2d527e11009930a6809d012983d33805e1b804613804d33805e107c20f841f082613805d304ed95ba1c04e9f842f083e107c20f841309c0201a60f841e9f842cadc02a98374a99c03cadc0e019c010071e108100f841e9f8425c03e107a7e10811e10bc20f84129f842a9f842e9c86601c8660148460174e43300da60f841f083e107a7e1096a93f08693f085e107c20c8660174e42000e423008edd3309c04f0827429f843e9f84229f842e9984e01f4fc2174c18c1dae853380bd3f085d3f085d3f084d3f085d3f08453f09c03e9f842e9f84229f86e01f4cc2700c06983e107a7e10ba7e10931700aa609daa615d2a6700f317038077404e0080001d3f0840529f843e9f842e9f84229f842e9984e018141e98356ca815a75017a6080365aad126a2508cd3040c050200c0401186cb449a8942001ba6080000000064c10006b4d6601cd66014d5a0300c6e05980793f085e107c20c866014846010e0ac044989384a840020acd42809384a84386a04030004b80b9592624db69300ea693097036a80737c98438042da2a264f6010e011150c0fb4c987b4d804386b3526024e12ed68980050270d01806380425e273017c20f4fc2178415c7842f083e1047121980738908c03e983d304003a60800000057a853e80953043115e8075306a6081bc217841e9804001e57a0000fc20f8415c78425a7842f08200096ca040017c2174c02000c0be16080448af53200013a7e1d807e15084931805e1884003c983380b24c34c0592a1e4c1498393062be1c80722400515ea05960ae4035814022b15760195ae9b00cadb00a60095a6015c260115a6011406015c2601156e1300de9709807300402802062a9403aab4020424fa01ec01d802575804f058040158abb00c71700810095560500e717408afb008117008adb009605008ad35ba06f405e80ec1e0100f4d804585a3c03d802b005e8b0080782c0200000002bd1e01818aa500ee85008ad5540065502d4032a80ea0180ca01014a8500cab000aa100080aa00fa01e4fc2155ea0155e2011401c9f842000c9f842c9f842c9f842c9825509f403aa80fa01d57a1900eaa900803b74ce019da20174e20114e20174ce0174f03708809d3380470070209e00c7529e045e9e842e9a8420394cc41c84102a7810ba67008000f1d3c0e404e9e052019e3a6700c06982063a14)) else (if j<22 then 0xd9f402047402b9f8820298fc402200bc8b1b8805c0200c058aa012c01000206046c09c011a81423800024982040400000081010402b005600009e8035807300660081e6014001442198880106e80080a0815601019a0300e0c35e80706a9f403000d8020003004600cc01000f08202046000080de10bc2081e107c20f841f08208f08570046e36a9865304100f84101bc024a8295040a08141380002a9b4060194c100a60800207c2081bc210d460000c003c20817c3b00c6000080be10bc20d0fc3300d260d4e87100d26081e107c208001dcebb40e0c751a0603c01780200000e168d37108b605600adc11b2c025803b05804b0046d300870f4d806085b6c03042db601bd36010e01042d829abd3601cdde9b00e6a0ada6a12da6016c26014c015b4c02d84c025bec2601ec260b00d6d300a600ae26012d66014c160100b0040580274046c08036ba0c00020d8eb74d808781b5d36026c16010001e013c01e6019e06db00e6009e360300c6c75d806363a54ec56114e953b158443aec0200e9300a6009e06d300cf13008f0759806b005e8b0180605da6c03046d3601ec00014d260000d70065aad0602b89c2f00c03b5d0e019dae8700ce9700a6f7008ed53b158449b8d6e01cdde814dcec14dcec14dce814dce014dce9700e6e0cdcec14dce011c017a0203d1a6e2709c0501e970080b802000377a1c0302e07008e87008e80bd017a0203c011bb4dc41bc0171385e01813589c8a4370140000016a0bd1a6e27088365a24d44a1380007000eb549a89e028121040034d02034d3601ce00a04b80808d80404d5e9300d70070286b89acc03016ab4b806b80400010f0081137096c055a0608d8053802ac03da0200e008b00d6bb00870f4980602e06e30000804c01038db681cd80bb49808b85a5c039b8204e0ed740ee009d01ba3c029c1dae8701070767806b83804f405707608e009d813a027006e0700ae87008e9700803b027005e87009e808002e2e0700c07a5c025c02b8b80400003d0e015c0e011d0e011d01b802b50400009802f43804000000381b8d4e02020ec740ee008e010700c0f7409e00d8411b6d0001cdb68000e7036da0c0002ed000100b5da2d03017036da0c0002ae06c06da08065aad031b6d16800100ab4022c04042db68181b007600cd415c01360181b60174fc401d80804d80408036c03042c0001ec000101a6bb00d6a34026c045a81126a250ec16038e160164f4410200cb5d80806026c16020216010030046cb449a894330000eb8038d96830146cb58006381b64f45a11410b4c9e8b422ce36810216cb45800055b017601adb27a2d08808da64f45a11727a2091161d820049aec02434d429aa0021a8176019c013c1d4e81807405e0080f004000f0740803c5c0e01807804069f842f083e107c20ac01e9f842f083d else (if j<23 then 0x10002080405e108000800807c21009800a8c161486021820104384230800204020004a8520007b30005b30005b30005b3000400201000200040000200200010001000008061c005d205a408005cc1b9d48a01f40179b4027982f305e6d00ba00f4016802d007a0081a107a4100b02500ac60e9413402000d004d008006ccc410e32e044808f40401c3d2201dcc159829007669009200ecd20115b67500de9b3a8071006200b5b6613d366102011c03b36804b305e80bd36614d419a83b368045602dd26626cc101ad100b671009ac057a2cc401ad500b67500a200c401681402d9d402d9d402d9d41a0195c12b3d0a019e2ae332809563add033c55cc250100036608078ab80ca021e366500c0a030810b30007578805578805330666500a6b7308e79008f062080abccc2b9e402b998b201b5c1713402c834026b2d5e8180b57a040000189a013cc179989a01b58101ac080d67a2cce62642a010000e32fe1e809e1e8043890c403f08207841f0f40259f85201f87a01486201487a1100cf157f0f4043c15fc25010f15730f40a02f8413c55fc219e0c2500f439008f0a1e80673d0a843d0e40250e402d0e402908321e80521c8540390f4025a82d00407d008a00ecc102ecc2044d5660012ab730867900a2e08117a98573c80590072090092cd57a0600003d220125de8d3198990880400190040b0c402b0e422018061c8051707671009a00ad5e616cc1012c000bc401e807e104c40dcc041000552a01552a015ccc2000ec3500ac3500ba861e80761a80561a8056130f40301c20b841d9b84001ecdc20100080802810002018c4610008000400203e1d8056206c5b00ac4098760100000001e2f0cc03f178660194e60156010282001b30410b300060005260800354103014e00010060e07201560ed950cabe108b1970224048bad2201b632e900d2e96ea24046c25d2018005018403632e0348089799a403aaf4c26c0c02cb557a99012abd40b2d9008b197f0ec04f0c4026c65fc21f8416c484601c5fa7100c02a827404e00f86e01786e01184e0115413803700004001415980024c1d2201e62af100f3073880798ab8498c0c403cc606201e62e011c016abcc2b98203c017982040567900007700405983d4f085d4b9984002750c21662c2610d2dd4f1784002e5ba9e2f08996f10043f0826207c20dcc0413841036608200016cc10203b3708003d9b840200100a0400060803188c2001409d0081006e80795000408f1787a0278803d00fc20dccc4e1008973010405ccc3d0000961280461e8056128056130f403b9c8c22982530646080038417082e12004e1309003681002f0f402f08264e8044823740324340801923a0400fa0400ae9502006612005e107c24009e9e16807b3708003d9b84020010100602000424118c461200006200002 else 0xa2091b0a10051071046090c91090c9108220dcc1b9820204000f454012914016cba2a00fa2a00948a00b65d1500600173e8855190055190055106400c801d9380401d801b003519005519005512884c4076209441040082d900ba21800168a442b98c8401dcc4016c81190802000b98cbc020105066ba18041459ae96012e7b20b513319680402cc8c014cac01044119809a22010000dcfa215444013cc199544c01d4423600c65512886060401980f42180010004902050402080010740080a007a5e0096a0f4a4011801f002e004a5e00aa40c8013002049da9120e6b920ba4080050004049c193c802e978025983e007c00f801e948029002b3b01803f002e006400c801701802b003e004ea52f007d2300452f005d23004783394833ad482b3826004073b8023aacca41eccc016cfa4610fa46008033f84c018005040c90200001e978023a83d230046004cf93290606cd2416cd2414cf2415001a002c0044f15e9200403a5200a400f49401680129033504f08008039e8025003a004a5a0096ad209c00e8017028025a8207494014cc1ba4cce61ecc12902080004001d2010043e0820504019820507660800100001a4080d204002a408052040032408e366120c71b3092004b38392700404cc0415d066164810007002e67a0cc300001c0600b2560080020206000400003c010005e10ba4010800003080020002000400002001d405e60b51e61351e613cc119784201ec8119684201800040100008033230e403799c82b90402b9040200e410082008401799c82390272080410040d9023301085a02000004c20800100001a4f009e0080010002024810274ba01f8400100bc21748021000100001020004000800100a00820a602208802e084030000080)))))
def g63H6 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0xf900003c0132060f0d080001226b40dc000000000926da235a010380880001b1570000000000000411000005a6a1419ca0eb303e332c64c63a1de00007220f41dc00007056d8293833181b7d018024d78add802c24cfe82dcd043e9980000015ff489ba137147d40028825fe0c2000000000000000000000226f00000a0f1507d2424c000061bc20942078d40aee188103200000000001be000000001c172000050af8250302fff47080acd06ec0000d137c65b987d9c1cc0123c007ba60a5233e00894d598561433da88200002252d00ea61f0b049643f0043a08ea789684622e8fd819f807a4821a80f3420814e4324f80000ccad7486124ddc4754ca4f072500bc0000000000005d264d1261417d4360219502860000000000000025600000000292be444f0044c4c42a5e009898140601b607880000e02d00003854fe08c000000000160081000000000000000e1ee0000e48150478024a224a284424446684c6219e0679a2e2528d005cb100127104136012414b56059984a3f03660c67085002b400000000402b100f7818000000000383af816c1469b276e90d2000074c180002c290e85650a600002024021f9f0cb805bc045dacd464eb5a0db049da22158b30303fd0e7e07180ed524b5c2ee00000000288380001447244a980002c04d20aa000000000000024b40000000000a2a000076560000014000000c0feea27742a9e63090708a5980001090910c7183db43ff8cc42063b80bb03bb0178243bfa5f880c789124013e0011896420db0000181ead025c637605af0555039230f80000485840000a14f64fcf47e1040de1e461008000342ac68d5e0fa1051442c6000090270000000000000047d80000000060620413000000000000016d7fa7dc00000000e08d1034989560000da49c32abc8a1296b544780003c412e091c03520233c05221e600001800f21f5a1a6d8a10c7e482320000411c0000000000000e8bb881d0000000000000000000001a1c0e84500001d20f008b7033da80400000000305b42231596a21e1d08ee879c10c30176111b9a4f693d8000000000000143d800007126292a40000c6530000684700000a1f30261800000001c01e90a89907c00002d6850420a84060c00006040820c0ec94161420e020408c0048b81005800e00001050400c08001450504042170009b0d04008aa023c1801400120440208a00081050e1808038380a80054307240c98c003c995122c1020200403021c1931200006000021f0c008825200428000418c321088002180002604286163400a060c1070a005800044100020010300081981e34006061010902000000ccc2000a18080080070300140090214126001c0002e14302001400a22000020000301080028108042010e200180400204020c4083014080040000102006840e24001 else 0xbfa1b80000486e40000650f000049206924a00007020800000000414b80c5f06cc00010894d0ef8a6800001a122642cd82080001496f9107800034020813e000068924000142488089800008205e01670d10000141a7a0e334f98000090e011680405507640001686be0328000093b400001049d9081c9040000e063121f8000000005024581b0d95f44a62ad2925c4000000b4542ae801c00000000e07980003847cc10b00004258800000000505580002d346e146b0d04266a417741e0c0dd304ba09bc0000105020862c37b81090012f85a982d201f776106a5480224a0b86065800000001717850c180003d969c24111206013700a6514df0090000152d8a89c30c6a815829110069000020214a1164118f025a82cb513d00a2d0b7082394867c18f0000681cf84400000460dc22140001a4a30046e837510a8c22a0000508a243a2615740745833400002015809a1a178c17da0feb04e800000000888df60500000000041d4a4ad8000000000000000000002438c00770000305ec0000c20204e17191c0000000034d5000000000a006b083e0650406600001838800000000000000000000000000000801ea2268000000000000202a6021d140aa439000000000e1b0465978828c11fc0490000315f8000000000000000000001f47c0000232ac81f6e16b00007074c59de0000f072d8329040e0000a4e5ca570c2a0000020e54c0e400012819000000002d40400000000781448138000010eae522a0496417e04bb99263825a000054f40000000000141a437a90d381a340efe030b8074000001e80000000000000a839c28e40711c00a0000101a00003422a000061299b2a7414a0000c6d16d1c4827ad47901215861c0000a0761440a21740001001400007224051f8c4ef0000000000000c12612543040c0000000093206217c0000a0fcc0ce980fc530880d6b0e7786a48264000000003938dd2ab003e48c38000010b4000000000000109660000a6eb8051f4aa6209a14d2d827c000000000000000000001610d6488800039284d11600000000052ae0000a022ea2100000000070f70261fc41ae058710b00000412021cc0a3d908ff194be23d0000423dc000000000000603dd4215e210c071084a5412c685b000000003d0f100e9c4a6f806000017125000000003c1300000006ba08b5427e0000000030626c208284214bb4306000000000b09a8000350d1c06d00007a7f000000000c10a981f510fff189a848e84d88960a9700000000000000417c64fa80226895c00007058c88b2a10e000030207d1e80000d136508b00002d3130866a821000000001015db8b7a07480000000054e6e303780427070000000001413389810000308900000414ea037323e0c25861312253ea48c0000614ad0e7a8708000000000000103ca8284401ad4) else (if j<3 then 0xe4c534ef800000000022f0000402f182c46165c11cf80d40000e4b10000505e504a8e1aa00004a73943e3686e70bd20128834f486030d880003432db07b700bc0451621350fb44c80522e12fe2c1ee029000018272025200000000000000000881a800000000000000007a7304b0b609e0000000000005e105e0620000000016ca3a0b800001438e405400000000382e800000000221f2903a205e00000887d8243e2260000220d40000000000000000000000000000072222034800000000222e40001a18500004885c0001488600002849e0057e1910000641e80000816420daea44103146c09505d52684d98b019336d3dc1fa88a381bf90b0500dc129400000000184c38193a03ce050818e200e5889200005256550eb68790219408cbc44a7037642b8000090c901eb000042600000000007256b04ee108c2088b252692dc00000000000000000015140ff5121da73fd06e2dba0000600c80000201108a8ea0ad8408000000002843e19b40000d119f274e41aa000060b400000c22e00001060182ce0072a0d050ce785b5d368c9c0106d407bd4275285c3475c01bc133c4000a088f806f4019e081b005800018434e1f53440787ee812fe1b674c6000000000c15b66718000000000000543d8000000016a04202e8000000014038a02f804040333e17360e680000000000005229fb2a2c28860cc0000200704873a4da10582a3980000000030f970169137160460000706c9017e4236000000002c29a00000000627d810e27038ea4880002d1fa4cb39057007e0000081c3000030527c309a1750000086d2c108c2450000000000000201fe0618000000000000e06f0000141eb6250343180003d0700000443d608c383d304ac608f8816c000161db00000000303fcc047c011800000000e4841053a520f40f1c0fd11269205cd28b64310000286b4931d61d6966c80000c3ca000041112218ac0d1213831028000102bc00000000492a80406a9f80000032c0000120bd0000101fd035fe1a8243a42246195da86a8a43b207c81b2000050768000381ce000000003019b408600000000380c4000000000000144e041d549549076711fe6106000020e43a7d389b2d5a6a0c08000112d12087625a8000000010cd80653c841943dba23c84338000000010234010e00003001b00f80000724e000000000507c8000000010244550180001d9be0000000000000000000000000606574356822338918000000000000000058431627c455bc041a871400000000a4a888363435d44d4c027f082c00008167e00cb031582780000544a8037e8002000050c13279d842309a60000000000000000000000000000000000405780002c48c0000c08469363843c0028584c800000000f119325b701324436000000007a79b09 else 0x190ec00000000000038418000000000000041e0000034148000143b0a1ac48aa8000382b80000a0955803a43f5e1c100000000320f80000d2c818256008461d070be80000000005860000000000000a1332109c21600001403a701200003c1900000000048299c3340000302ab04038336a8430000000020476803b165b00003c2a5202a412780000000101fc0000000008114000000006804d81280000d252800000001e1a3000004092d987811b381d0000100b349a9d81dba67451138186e821907a81130000000003b379913200000000185c8e0f3d1769115a86400001e86d00387a70cd32c00000000481af10486212000074502194d283bf0700830580a00000f41d221f44463c82a72b2801f8000020d4b0e5e88a402e380a3b0ee00001032561a5000000002048ec916000))
def g63D7 (j : Nat) : Nat := if 23 ≤ j then 0 else (if j<11 then (if j<5 then (if j<2 then (if j<1 then 0xc751cd624432f1d07358910cdf731cd62443375cc7358910cfb701cd624432f1d253589108ff8754d624423f21d5358910abc8454d624432f1d15358910cbc74d0d624423fa1c43589108fd8710d624429f6144358910cbc7410d62442be6004358910cfb85dc1624433e6177058910cfa84dc1624433e2137058910cfa54dc1624433ee0f7058910cfa83dc1624433e60f7058910cf883dc1624433e94f7058910cf953dc1624433ed0f7058910cf843dc1624423fa1f6558910aef82595624434f1d77458910daf72dd1624432fd947458910cbd651d1624434fdd47458910d3c751d1624429f6166458910cbc7499162442bb60a64589108fe8719162443379937358910cdc64dcd6244357dd77358910d9f74dcd62443671d37358910cdf651cd62443375947358910d5f751cd62443571d47358910d9c741cd624423fa1f6358910c7f75d8d624432f1d36358910c7f7598d624432f1d26358910aed8298d624429fe156358910c7f7558d62442af2116358910cbc7458d62442bbe0963589108fe8718d624431fdd46358910cbc7418d624439bdd76258910e6c75d8962443abdd36258910eac74d8962443b3dcf6258910ecc73d8962443731cf6258910cfb65dc1624433e5977058910cfa64dc1624433e1937058910cfb63dc1624433e98f7058910cf963dc1624433e18f7058910d7b75dc1624435e1d77058910dbb74dc1624436e1d37058910ddb73dc162443761cf7058910deb72dc162443bad8b7058910df371dc1624433e60376549109f980dd9524431fa1776d0910c7d85ddb424432fa1376d0910cde83ddb424433760f76d0910cf980ddb424426fa1376d09109ed82ddb424427e60376d0910abe84ddb42442bb60b76d0910af980ddb424423fa1a76d09108fd879db424433ee0176d09109fb805db424432fa1076d0910ced821db424423fa1876d09108fe871db42442afa1076d0910aed821db424433be0976cc910cfb805db324427ee0176cc910ced87d8b32443b360f62cc910ced76d8b324423fa13764c910cf980dd9324427e603764c9108fe841d9324432fe18744c910cbe861d1324432f618744c910cbc861d1324436b608744c9108fe861d1324423f618744c9108fe87991324423f21e644c910cbc7499132442bb60a644c9108fe87191324423f21c644c910cbc7419132442bb608644c910cf161dc151cc32e19170d0530cf3615c3414c32b9d27299110cea725c2644433c5c57099110a3d859906444237e1d6318d10a5f8558c634430f5d46410d10c7b70dd5624430f1d77458910cbb70dd1624430fdd47458910c3c751d16244317dd77358910c9f74dcd62443271d37358910cdb70dcd6244317dd47358910c5c751cd62443271d07358910ccc73d89624433ad8b70589108be84ddb424423e60376d0910 else 0x5990644438f6166419110eae8299064443ab60a6419110eb98099064442cf6166419110bb980990644423f60a7695110cdf835da544433720d76951108ff825da544433ee0176951109fb805da544432f5d864951108ff865ca544423f21972951109ed829d3634427e60274d8d10a7d8599363442bb60a64d8d10af980993634432f9d064d8d10aef8259663442bee016598d10cfb655c2634433e5957098d10ddb635c2634429f6166458d10cbc7499163442bb60a6458d10af980991634433b9937258d10cec64dc9634433e9937058d10cf864dc163442bbe096518d10afb805946344277e1d6318d10b5f8558c63442f6e016318d109bc845c8634423f60b7654d10cf980dd9534427e6037654d108fd821d95344337dd86354d10d9c7418d534423fa1b7254d108fd86dc9534423f60a7610d10cbc845d8434423fe097610d10cfb805d8434427ee017610d10cbd8719043443a760c6410d10cbd76190434434f5d46410d10cdd76d8c434433be197210d10cee865c8434433b6197210d10cec865c8434423fe197210d108fc865c8434436e1917010d10ddb635c0434437ce057010d108fe87953624423f61e54d8910cbe7495362442bb60a54d8910abe84dcf6244337dce73d8910cdd731cf624423fe1d53d89108fc8754f62442af21153d8910aef8254f624423fa1c43d89108fd8710f624429f61443d8910cbe7410f62442bb60843d8910af98010f62442bb60b65d89108ff87597624423f61e64d8910a7d85993624432f9d064d8910aed8219362442bb60b63d89108fd8798f624423fe1d63d8910a7f8558f62442af21163d8910aed8218f624433edc37558910abc845d562442b7e0d7558910adc835d5624433edc17558910a7e871d5624438fdd77458910e3c75dd1624429f6167458910c7f759d1624431f1d67458910abe849d162442b7a0e7458910add839d1624433edc27458910cbf851d1624432f6147458910cbf831d1624432fa0c7458910cbd831d1624432f20c7458910cbf751d1624438fdd47458910cbd751d1624438f1d47458910c7f751d1624431f1d47458910cfb701d1624423fa1e54589108fd87951624432f1d25458910cdf75dcd6244397dd77358910cdd75dcd62443971d77358910e9f74dcd62443379d37358910cdc74dcd62443a71d37358910c7f75dcd624432fdd37358910cbc74dcd624433edc37358910a7d859cd624431fdd67358910c7c759cd62442afa127358910cbc749cd62442b7a0e7358910cdf739cd624433edc27358910a7f855cd624431fdd57358910abc845cd624432fdd17358910cbc745cd624433edc17358910ade871cd6244337dd47358910e5f751cd62443375d47358910e5c751cd62443a7dd07358910cde741cd62443371d07358910e9c741cd624431fdd47358910c7) else (if j<3 then 0x9732442fbe0965cc910bfb8059732443bbe1762cc910eed85d8b324437b61f62cc910ded76d8b32443bbd9762cc910eed65d8b32443f360f62cc910cfe84dd9324433f213764c9109fe84dd9324437e603764c910cfe841d9324433f210764c9109fe841d9324436fe18744c910dbe861d1324436f618744c910dbc861d1324433fe18744c9109fe861d1324433fa18744c9109fd861d1324433f618744c910cfc861d1324433fa1e644c910cfc87991324439f616644c910eed8299132443be602644c9109fe87991324427f21e644c910cff76991324433f1da644c910b7d85991324436f1d2644c910bed8299132442fe602644c910cfe87191324433f21c644c910eed82191324427fa1c644c9109fc87191324433fdd8644c910cfc76191324436f1d0644c910ebe6419132442fb608644c9108fd82dc56095337dcf7158254cdc73dc56095337dcd7158254cdc735c560952bee0171582549df874833154ef5e0520cc553af980dc76054e3fe0971d8153af982dc56010fae2117158043edb835c56010ebee097158043ef3715c56010e3f60b7158043afb805c56010ebd60473d8550af581dcb615434f9d674d8740d3d759d361d02afa1363d87408ff8758f61d036b9d272d8740de5719cb61d033bd8d72d8740ced635cb61d036b9d172d8740cfb635c361d033e58d70d8740d7a755c361d035e5d570d8740dba745c361d037a9c970d8740de9725c361d023fa1f6358740abe84d8d61d02bde0563587409be84dc961d023fa1f6258740af78158961d02eda136158740bf180d8561d02bde057558730af7815c961cc23f60b76547308fd86dc951cc23fa1d62547308fc8758951cc33bdc96254730abd82dc4644c3ae6037119130abf825c4644c3addc57119130ebb815c0644c3ae6057019130ebb715c0644c3ae5c57019130abe84dc4644c23fe0971191308fd829d3614c2bd60474d8530af581dcb614c23f21172d85308fd829db414c32fa1076d05308fd821db414c33d60476d0530abe841db414c2bd60476d0530eb581193414c23f21972d0530cbc645cb414c23fe1f62d05308fe87d8b414c23f61f62d0530ced72d8b414c3ada1361d0530cf8765c3414c3ae19170d0530ef3615c3414c26f21172d9510c7d75dce64442bb60b7399110af980dce644431f5d57399110c7e75dca644431f5d77299110add83dca64442be6037299110aed879ca644433bdce7299110ced739ca644433be0d7299110ced835ca644433bdcd7299110ced735ca644431f9d57299110c7d755ca644439e9d57099110e79755c2644433edcd7099110cf9735c264443ba9c97099110ee9725c264443bc5c57099110dae749ca644435e9d57099110d79755c2644437a9c97099110de9725c2644437c5c57099110aef825cc64442bee017319110e3e8 else (if j<4 then 0x62443bbd0f6258910eec43d8962443dbdd76258910f6c75d8962443bbd976258910eed65d8962443ebdd36258910fac74d8962443bb9936258910eec64d8962443f3dcf6258910fcc73d8962443bbd8f6258910eee63d8962443bb58f6258910eec63d89624437ee177058910df985dc1624437ed977058910df965dc1624437ea137058910df884dc1624437e9937058910df864dc1624437e9537058910dfb83dc1624437ea0f7058910df983dc1624437e20f7058910dfb63dc1624437e98f7058910df963dc1624437e18f7058910dfa53dc1624437e54f7058910dfb43dc1624437e10f7058910dfb75dc162443dedd77058910df975dc162443de1d77058910efb65dc162443be5977058910fbb74dc1624437e9d37058910df874dc162443ee1d37058910efa64dc162443be1937058910dfb73dc162443f6dcf7058910dfa73dc1624437e5cf7058910df873dc162443f61cf7058910efb63dc162443be98f7058910ef963dc162443be18f7058910feb62dc162443fcdc77058910cfe83dd9524433f20f7654910df980dd9524433fa0c7654910cfc831d9524427fa1e6354910cff7698d524433f1da6354910bf98098d524427fa1c6354910cff7618d524433f1d86354910bed8218d524433fe0f76d0910cfd83ddb424435fa1776d0910d7d85ddb424436fa1376d0910dde83ddb424437760f76d0910ded82ddb424437e60376d0910e7e85ddb424439f61776d0910ebe84ddb42443b7a0f76d0910edd83ddb42443bb60b76d0910ef980ddb42442efa1376d0910bdd83ddb42442fb60b76d0910bf980ddb424433fe0e76d0910cfd839db424427fa1a76d0910afd879db424427f61e76d0910afe869db424433fdda76d0910cff835db424433f60d76d0910dfb805db42443bee0176d0910cff765db424433f9d976d0910bfb805db424433fe0c76d0910cfd831db424427fa1876d0910dbe841db424437b60876d0910afe871db42443afa1076d0910eed821db424427fa1c76d0910afe861db424433fdd876d0910cfe761db424433f5d876d0910bbe841db42442fb60876d0910afe86dcf42442bf61b73d0910cff76dcf424433f9db73d0910cfd76dcf424433f1db73d0910bbe84dcf42442bfe1973d0910afc865cf424433fdd973d0910cfe765cf424433f5d973d0910cfc765cf424427fa1f63d09109fd87d8f424433fddb63d0910cfe76d8f424433f5db63d0910cfc76d8f42442fb60b63d09109ff8758f424427f21d63d0910cff7658f424433f9d963d0910cfd7658f424433f1d963d0910bbc8458f42442fbe0963d0910bfb8058f424433fe1676cc910cfd859db324433fe1576cc910cfd855db324437be0976cc910dfb805db324427f61f65cc910cfe76d97324433f5db65cc9109ff87597324433f9d965cc910cfd765 else 0x4436fdd47458910f3f751d1624436f5d47458910f3c751d162443afd947458910ebd651d1624435fdd47458910d7c751d1624439fa166458910e7d85991624439fdd66458910e7c7599162443af1d26458910eed8299162443be6026458910b7d85991624436f1d26458910bed8299162442fe6026458910afe87191624433fa1c6458910e7f75191624439f1d464589109fe8719162443af99064589109fe87951624427f61e5458910afe8695162442bf61a5458910dbc7495162443af1925458910dde64dcd62443771937358910ddf75dcd62443d7dd77358910ddd75dcd62443d71d77358910edf65dcd62443b75977358910f9f74dcd62443779d37358910ddc74dcd62443e71d37358910ede64dcd62443b71937358910d7f75dcd624436fdd37358910dbc74dcd62442bf61a7358910b7d859cd624435fdd67358910d7c759cd62442efa127358910dbc749cd62442f7a0e7358910ddf739cd624437bdca7358910bf9809cd62442bfe197358910b7f855cd624435fdd57358910bbc845cd624436fdd17358910dbc745cd62442fee017358910ddf651cd62443775947358910bde871cd6244377dd47358910f5f751cd62443775d47358910f5c751cd62443b7d947358910edd651cd62443e7dd07358910dde741cd62443771d07358910f9c741cd62443b79907358910edc641cd624435fdd47358910d7c751cd624436f1d07358910ddf731cd62443775cc7358910def721cd62442bfa1f6358910e7f75d8d62442bfa136358910ebf74d8d624433f1d36358910ebc74d8d62443b71cf63589109fe87d8d624435fdd76358910dbc74d8d624439fdd66358910e7c7598d62443af1d26358910edf7398d624435fdd66358910dbc7498d62443b7d8e6358910bed8298d62442fe6026358910e7f7558d62442bf2116358910ebf7458d624433f1d16358910ebc7458d62443b71cd6358910b7f8558d624435fdd56358910bbc8458d624436f1d16358910bef8258d62442fee016358910afe8718d624439fdd46358910e7c7518d62443af1d06358910edf7318d624427fa1c6358910d7f7518d624436f1d06358910edd6318d624436f1d253589109ff8754d624427f21d5358910aff8654d62442bf2195358910bbc8454d624436f1d15358910edc6354d624436f1d343589109fe8710d624427f61c4358910afe8610d62442bf6184358910b7d8510d624436f1d04358910ebc6410d62443b7d8c4358910bed8210d62442fe6004358910eef85d8962443bb6176258910eef75d8962443bb5d76258910eee84d8962443bb2136258910eee74d8962443bb1d36258910eee54d8962443bbe0f6258910eee83d8962443bb60f6258910eec83d8962443bbdcf6258910eee73d8962443bb5cf6258910eec73d8962443bb94f6258910eed53d89))) else (if j<8 then (if j<6 then 0x2bf61e64d8910cfd87993624439fa1664d8910e7d8599362443be60264d89109fd8799362442df61664d8910bf98099362443af9d064d8910eed82193624436f9d064d8910ebe6419362442fb60864d89109fe87953624427f61e54d8910afe8695362442bf61a54d8910dbe7495362443af19254d8910bed8295362442bfa1b73d8910bbe84dcf6244377dce73d8910bf9809cf62442bfa1873d8910ddd731cf62442bfa1363d8910cfe74d8f62443b79cf63d8910bed82d8f62442bf61e63d89109fd8798f62443b7d8e63d8910bf98098f62442bfe1d63d8910afc8458f624433f9d163d89109ff8758f62442dfe1563d8910bbc8458f62442fee0163d8910edd7318f62443b758c63d8910bed8218f624427fe1d53d89109fc8754f62442bfe1953d8910afc8654f62442ef21153d8910edc6354f62442fbe0953d89109fe8710f624427f61c43d8910afe8610f62442bf61843d8910b7d8510f624436f9d043d8910ebc6410f62443b7d8c43d8910bed8210f62442fe60043d8910e7e83dd5624439f60f7558910e7e859d1624439f6167458910e7f759d1624439f1d67458910ede839d162443b760e7458910ef9809d1624433fe0c7458910cfd831d162443afe147458910ebd851d162443afdd47458910ebd751d162443afe0c7458910ebe831d162443af60c7458910ebc831d1624439fdd47458910e7c751d162443af9d07458910afe8795162442bf61e5458910ebc7495162443b7dd77358910edd75dcd62443b7a137358910ede74dcd62443b71d37358910ede54dcd624439fdd77358910afe84dcd62443afdd37358910cfe74dcd624433f1d37358910ebc74dcd624433fdd67358910e7f759cd624433f5d67358910e7c759cd62443af1d27358910edf739cd624439fdd57358910afc845cd62443afdd17358910cfe745cd624433f1d17358910ebc745cd62443b76147358910edf751cd62443b75d47358910ede741cd62443b71d07358910ede541cd624433fdd47358910e7f751cd624433f5d47358910e7c751cd62443af1d07358910edf731cd62443b75cc7358910ebc7494d62442bfe1d5358910afc8754d62443af1d15358910edc7354d624439fdd74358910ebc74d0d62442bfa1c4358910afd8710d624439fdd44358910e7c7510d62443af1d04358910edf7310d62442bfe197558910bbc845d562442f7e0d7558910bdc835d562442fee017558910b7e871d562442bfa1f65589109fe87d9562442fbe096558910bfb8059562443cfdd77458910f3c75dd162442bf61a7458910b7d859d1624435fdd67458910d7c759d162442efa127458910bde839d162442f760e7458910bf9809d1624436fe147458910dbd851d1624436fd947458910dbd651d1624436fe0c7458910dbe831d1624436f60c7458910dbc831d162 else (if j<7 then 0xba0a6419110fad8299064443ee6026419110ebe64dcc64443af9917319110bef825cc64442fee017319110afe86dc864443af9937219110ebe645c8644433fe0a7695110cfd829da544427f60a7695110cff825da544433f6097695110ddf835da544437720d76951109ff825da544437ee017695110ebf8219254443af6086495110dbd76192544427fe197295110cff865ca544433fa197295110cfd865ca544427f2197295110cfc865ca544435f61674d8d10dee829d3634427f60a74d8d10ded829d3634437e60274d8d10e7d8599363443bba0a64d8d10afd8299363443bb60a64d8d10ef98099363442df61664d8d10bed8299363442fe60264d8d10afd82193634436f9d064d8d10ebe64193634427f21172d8d10cfe645cb634433f19172d8d10afd82d9663442bfe096598d10bef8259663442fee016598d10cff655ca634433f5957298d10dfb855c2634437e6157098d10dfb655c2634437e5957098d10dfb825c2634437e6097098d10dbf821d1634436f6087458d109fd821d1634439f6166458d10eee8299163442bf60a6458d10eed8299163443be6026458d10b7d85991634436f1d26458d10bed8299163442fe6026458d10afd8219163443af9906458d10dee84dc9634437b2137258d10dee64dc9634437b1937258d109fe84dc9634433f9937258d10cfc64dc9634437ea137058d10df884dc1634437e9937058d10df864dc1634437ee0b7058d10df982dc163442bf60b6518d10aff8259463442fbe096518d10bfb80594634433fd957218d10cfd655c8634436f2117218d10cff82dd9534433f60b7654d109fd82dd9534437e6037654d10cff821d9534433f6087654d109fd821d95344377dd86354d10cff86dc9534427fa1b7254d10cfe86dc9534427f61b7254d10cfd86dc9534433f21b7254d10cff829d8434433f60a7610d109fd829d8434433fe097610d10cfd825d8434436f2117610d109ff825d8434437ee017610d10ebf8219043443af6086410d10dbd87190434436f5d86410d10f9d8319043443775db6310d10def865c8434437ba197210d10ded865c8434437b2197210d109ff865c8434433fe197210d10cfe865c8434433f6197210d109fc865c8434433f2197210d10dfb825c0434437e6097010d10cff839d3624433f60e74d8910ebe741d362443bb60874d8910afe8795362442bf61e54d8910ebe7495362442bfa1373d8910cfe74dcf624433f1d373d8910cff759cf624433f5d673d8910edf739cf62442bf21173d8910cfe745cf624433f1d173d8910cff751cf624433f5d473d8910edd731cf62442bfe1d53d8910afc8754f62443b79cd53d8910afe8710f62442bf61c43d8910ebe7410f62442bfa1b75d8910bed82d9762442bfe1d65d89109ff8759762442fee0165d8910afe861d36244 else 0xb7119130ebf72dc4644c3afe097119130ebd825c4644c3afdc97119130ebd725c4644c3afa137119130afd82dc4644c33fdcb7119130cff825c4644c33f6097119130aff825c4644c33fdc97119130cfd725c4644c3bddc57119130cff829d3614c33f60a74d8530afd829d3614c3af9d074d8530afd821d3614c3bd60474d8530afe84dcb614c33f9d372d8530cfc74dcb614c3bd60772d8530ef980dcb614c33fa1172d8530cfc845cb614c2bf21172d8530cfe745cb614c33f1d172d8530eef725cb614c33fe0a76d0530cfd829db414c2bf60a76d0530cff821db414c33f60876d0530ebe841db414c2bf60876d0530ef5811db414c3afe0864d0530ebd82193414c2bfa1b72d0530cfe76dcb414c33f1db72d0530bbe84dcb414c3af19372d0530bf581dcb414c2fe60372d0530cfe865cb414c33f21972d0530afc865cb414c33f9d972d0530cfc765cb414c3af19172d0530aff87d8b414c33fe1f62d0530afe87d8b414c33fa1f62d0530afd87d8b414c33f61f62d0530afc87d8b414c33f21f62d0530eed72d8b414c3bde0b61d0530ef582d87414c3bddcb61d0530ef572d87414c37ee0970d0530df9825c3414c3be1d970d0530dfb725c3414c37e5c970d0530dbc845cb6544377e0d72d9510ddc835cb654437ba0f7259510dec83dc9654437ea0f7059510df883dc1654437ee0b7059510df982dc1654439f5d77399110afd82dce644439f5d57399110aff825ce644439fa177299110e7d85dca644439f9d77299110e7d75dca64443afa137299110ede83dca64443b760f7299110cff73dca644433f5cf7299110ef980dca64443bbdce7299110eed739ca644433fe0d7299110cfd835ca64443bbe0d7299110eed835ca64443bbdcd7299110eed735ca644439f9d57299110e7d755ca644433fdcd7299110cfd735ca64443bbdc97299110efb835c264443be60d7099110efb735c264443be5cd7099110efb825c264443be6097099110efb725c264443be5c97099110d7d75dce64442fb60b7399110bf980dce644435f5d57399110afd86dca644435f9d77299110d7d75dca64442f760f7299110bf980dca64442fb61e7299110def739ca644437b5ce7299110def835ca644437b60d7299110def735ca644437b5cd7299110d7e755ca644435f5d57299110dfb835c2644437e60d7099110dfb825c2644437e6097099110f7a755c264443de5d57099110dfb735c2644437e5cd7099110dfb725c264443fa9c97099110df9725c264443fa5c97099110ff1715c264442bf60b7319110aff825cc64443afa137219110cff73dc8644433f5cf7219110cff835c8644433f60d7219110cff735c8644433f5cd7219110eef725c864443afe0e6419110ebd8399064443afe0a6419110ebd8299064443cfa166419110f3d8599064443e)) else (if j<9 then 0x7158043cff725c56010f3f5c97158043ef7715c56010fbee017158043afd829cf61542bf60873d8550cfe73dcb615433f1cf72d8550ef581dcb615433fa0d72d8550cfc835cb615433f9cd72d8550cfc735cb61543bbdc972d8550dbf819d363d036f60674d8f409ff825c763d027f60b7158f40dbf839d361d036f60e74d8740dbf829d361d036f60a74d8740f3e759d361d03cf5d674d8740afe86dcf61d035f5d773d8740bbe84dcf61d036f9d373d8740bed82dcf61d037d5c773d8740bf980dcf61d035f5d573d8740dbe745cf61d037d5c573d8740e7d75d8f61d03af9d363d8740afd82d8f61d02efa1363d8740dbe74d8f61d02fd60763d8740aff8758f61d039f5d563d8740ebe7458f61d02bfe0963d87409ff8758f61d036f9d163d8740afe86dcb61d035f9d772d8740d7d75dcb61d02efa1372d8740dbe74dcb61d02f760f72d8740bf980dcb61d02fb61e72d8740fae749cb61d037bdce72d8740ded739cb61d03bbd8e72d8740eed639cb61d037be0d72d8740ded835cb61d037bd8d72d8740ded635cb61d033fd8d72d8740cfd635cb61d03eb9d172d8740def735cb61d037b5cd72d8740eef635cb61d03bb58d72d8740d7e755cb61d035f5d572d8740dbe745cb61d039f9d762d8740e7d75d8b61d03af9d362d8740ef581d8b61d036f9d362d8740bf581d8b61d037ee0d70d8740df9835c361d037ed8d70d8740df9635c361d037ee0970d8740df9825c361d037ed8970d8740f7a755c361d03de5d570d8740fba745c361d037edcd70d8740df9735c361d03bed8d70d8740ef9635c361d037edc970d8740fea725c361d037e5c970d8740fe9725c361d03bed8970d8740afd82dcd61d02bfe097358740cff83dc961d033f60f7258740cff73dc961d033f5cf7258740cff735c961d033f5cd7258740eef725c961d03bde057258740aff865cd61d02bfa1f6358740afd82d8d61d027fa1f6358740bbe84d8d61d02bfe096358740bf78158d61d036fa137258740cff63dc961d033f58f7258740bbe84dc961d02bfe197258740afe87d8961d033fa1f6258740e7e85d8961d039f6176258740ebe84d8961d03be60362587409fe87d8961d02efa136258740bf980d8961d03bde056258740bf78158961d03dda176158740f7585d8561d03eda136158740ef763d8561d03bd58f6158740fe682d8561d03f960b6158740ef762d8561d03bd58b6158740ff180d8561d02bf60b7558730aff825d561cc33fe177258730cfd85dc961cc33fdd77258730cfd75dc961cc33fdd57258730cfd755c961cc3bbdc97258730ef7815c961cc3bee017258730cff82dd951cc33f60b7654730cff86dc951cc33f61b7254730cfe8758951cc33f21d6254730ef78258551cc3bd6096154730dfb82dc151cc37e60b7054730ebf82dc4644c3af6 else (if j<10 then 0x1ac00d5746a7435131a740d324694c346f1a1e0d03467dc33b719c40cd546674332319800cb64657432a319420c994649c3237190c0c80463b431b318c80c5c462ac3137188e0c41461d430d718520c21460c4302f18080bfd45fac2fa717bc0bd545e642efb17640ba845ce42e53171c0b8345bcc2dcf16d60b5f45ab42d37168a0b394597c2c9716340b104583c2bf715ec0aee457042b6715a60ac6455ec2acf15520a9f454942a2b14fc0a774537c299314bc0a564526c291314780a304513c286f14220a0344fdc27c713ce09dc44e842717137009af44d44267b1326098944bdc25bb12c4095544a4c24f712600923448bc241f11ee08e9446ec234b119008b844544226b111c0881443a421a710be085444254210710760831441442083102e080e440241fe30fde07e343ecc1f3b0f8807bb43d741e8b0f3a079543c741e170efa077443b2c1d6f0e9a0741439dc1ccf0e5a0724438dc1c470e1806fe4377c1b8b0daa06c9436041ae30d5a06a6434dc1a470d12067c433b419af0cc6065a4328c19230c7a063743174189b0c3e06174306c181f0bf405ed42f04173b0b8a05b642d5c168b0b2a058942bf415bf0ac4055842a6c14fb0a68052b4290c145b0a1a0503427cc13bb09c804da4267c1313097404b042504124b09160483423bc11bb08d20462422c41133088204354215c107f08340412420640fff07ee03f141f540f9307ae03cb41e040ee3076203a541ce40e530718038141ba40d9b06b6035041a4c0d13067603344196c0c9b063e03124183c0bf305e202e6416e40b4b058e02c0415dc0ac7055802a5414f40a630524028a4142409fb04ea026d41324096f04a402494120c08e7045e0226410e408530414020040fcc07cb03da01e740ecc073b039201c440ddc06d7036001a340cd406530310018240be405bf02cc015a40a840513027a012f40924045f021a010140794039b01b200c84060c02e7016200a84050402630124008a4041401eb00e2006a40324017300ac004f4023c01030074003340154008b003800144007c001f00003b74877358254edd211cd609533fe0b7158254cfd82dc560953b7dcf7158254edc73dc560952bf60b7158254cff72dc560953b7e0d7158254edc835c560953b7dcd7158254edc735c560952bfe097158254cff725c5609533f5c97158254ef7715c560953bee017158254ddf874833154ff5e0520cc553ede83dc76054ebf60b71d8153cff72dc76054fbe60371d8153cff825c76054f3f60971d8153aff825c76054f3fdc971d8153cfd725c76054fbddc571d8153efb82dc56010fbe60b7158043efb72dc56010fbee097158043ef9825c56010fbedc97158043ef9725c56010f3fe0b7158043cfd82dc56010ebf60b7158043cff72dc56010faf2117158043edf835c56010ebfe09 else 0xc9f464d33262192d4c93464873240191b4c8bc644b321a19074c80c63eb31ee18f24c764639b31c418d94c69c633b319a18c94c62c62ff317618b64c57c62a7314c18a04c4dc624f311818864c40461df30de186a4c334618b30bc18574c28461233084183b4c16c609f3044181d4c0d460533022180e4c05c601b300217fd4bfcc5fd32fe217eb4bf345f832fb417d44be545f0f2f7e17bb4bdac5ec72f5a17a84bd1c5e732f28178d4bc545e132f00177c4bbb45dc72ed817674bb0c5d772eb217554ba845d2b2e9017444b9fc5cef2e6e17334b96c5c9b2e42171c4b8bc5c4b2e1e170b4b7f45be72de616ef4b7545b8f2dc016dc4b6ac5b372d9016c14b5ec5ae72d6a16ae4b52c5a772d2c168c4b41c59ef2ce6166c4b33459832cb416514b23c590f2c80163b4b1c458cf2c5a16294b12c58872c3816164b06458032bf415f14af6c57a72bca15d84ae8c57232b7815b34ad4c568b2b3a15964ac6456232b08157f4abcc55db2ae6156e4ab5455932ac2155c4aac455532aa4154b4aa2c55072a7615364a98454a72a4a15214a8f454672a28150f4a854541b2a0414fd4a7cc53cf29da14e94a70c537329ae14cf4a654530f297a14b84a59452ab294e14a34a4e4525b291e14854a3fc51df28e2146a4a30c516b28aa144f4a25c511b2880143a4a1a450bb285414244a10c506b282c140f4a044500727fa13fa49f944fa727cc13e049ed44f5727a213cd49e444efb276e13b149d7c4eb3274e13a349cdc4e5f2724138e49c544e1f270a138249bf44def26ee137349b844db326d4136649b144d7f26b6135849aa44d3f26901340499e44ce3266c13334996c4ca32640131c498c44c43261a13084981c4bf725f212f54978c4ba725ce12e3496dc4b5f25a012cc4964c4b17258412bb495ac4abb255612a94951c4a7f253412944946c4a1324fc12774936c49a324c8125b492bc493f24981244491f448cf245a1223490e44867242c12114905c481323fe11f848f9c47bb23d011e148ee4474f23a211c848e0c46f3237211b548d8c46b3235411a748d2446832334119448c84462b230a117e48bcc45db22e6116e48b44459322c2115c48ac44553229e114748a1c44f7227411334896444932240111b488ac443f221811094882443ff21f410f64879c43b321d010e54870c4357219610c0485bc42bb2148109748474420b20ee106b4831c416b209c1046481d440af204010174808440231ffa0fef47f3c3f7f1faa0fc747e043ed71f520fa147ccc3e471f0e0f7e47b743d871ea60f4b479d43cbb1e500f20478ac3c371e040ef64775c3b7b1daa0ec7475f43ac71d540e9f474bc3a331d040e7347334396f1ca60e4a471e438bf1c500e1b470a438371c0e0dfe46f84378f1bb00dcc46e0436d71b600da846cec364f1b1c0d8646bcc35bb)))) else (if j<17 then (if j<14 then (if j<12 then 0x712238651c148dff46f8237851b848d9f46c6235b51ab48d374696234651a148cfb466e232f5193c8c8f463c23165189c8c3346102303518048be745f022f15175c8b9b45c622d95169c8b3f459422c6515f48adf456a22b15156c8a9345342292514748a274508227e513b489c344ce2262512cc8957449a22495120c88ff447a22365118488b74452222751134888b4440221e510dc88534420220c5102c880743f421f650f9487ab43cc21e350efc876b43ac21d150e44870b437c21b850d9486b3434e21a050cdc86574322218d50c4486134302217e50bd485bf42d6216750b0c857742b0215250a6485274286213e509dc84e34266212b509348483423821155088c843742122102507fc83e741e820ed50734837b41b620d7506948337419420c3505e482df416820ae5053c828b413c20985049c823b41122084503fc81db40e020695032c818340b820575028c8127408c203e501bc80c340522025500dc805f4020200d5002c80073ffc1ffb4ffc47fd33fe21fec4ff247f873fb81fd44fe847f333f8e1fbe4fda47ebf3f4e1fa24fcec7e5f3f241f8b4fc3c7e0b3efc1f794fba47dbb3ed81f664fafc7d6b3ea81f4e4fa447d133e841f394f9ac7cc73e581f274f90c7c633e261f0f4f8447c073df61ef24f75c7b9f3dbe1ed84f6a47b3f3d961ec44f5dc7adb3d641eae4f5547a933d3a1e954f4647a0f3cf61e734f354798b3cb21e504f23c790b3c7c1e394f1b478bf3c521e204f0e4785b3c1a1e074f00c77ef3be61dea4ef3477833bb21dd24ee6c77173b821dbb4edac76bf3b4a1d9a4eca4763f3b1a1d884ec1c75fb3af61d744eb4c75773ab21d504ea5c75173a801d3a4e9b474cb3a5c1d2b4e934748f3a3e1d194e8ac74433a161d064e7fc73e739e81cec4e71c737739ae1cd54e694733b39981cc74e61472f7396c1cb24e55c729f39441c994e4a4723739161c874e42471ff38f81c784e3ac71c338ce1c5f4e2dc714b389c1c474e21c7103387e1c3d4e1d470cf38601c2c4e14c708f38401c1d4e0bc705338181c044dff46fe337e41bee4df2c6f8b37c21bde4deac6f4b378e1bbd4ddc46ecb375e1ba84dd2c6e87373c1b984dc7c6e1f37081b814dbe46ddf36ec1b704db3c6d9336c21b594daa46d3f36961b464d9f46cd736621b2b4d92c6c7b36341b154d8846c1b36001afc4d7c46bd735e41aef4d7546b9f35c61adb4d6bc6b4b359e1acb4d63c6b0b357a1ab64d59c6ac3355c1aa94d5046a6f35321a954d4646a23350c1a814d3ec69c734dc1a684d304697334ae1a514d244690b347c1a374d19468af344c1a1c4d0b4684334181a084d01c680333fe19fa4cf8c67b333cc19e14ceec676b33a819ce4ce3466ff337619b64cd8c66b33346199b4cc9c662b3306197a4cb8465a732c8195e4cabc654b329e19474 else (if j<13 then 0x170e81010afac0be9a7c5c3a04ebeb7a69f168280010aeade9a7c5c2a03ebeb7a29f170e80fafade9a7c4c203a0200052bab7a69f170a80011afac4be8a7c5c3a0004ebeb7a69f130e80e11ae0c0a09a7c2c203a05040302827170e8280013a7c4c3a0a000369b080e808000caeada6a0002baa9e828000a11ae0c0a09a607c5c2c203a00068403028269a9f170e82814aeada6a000292a9e80008b12f2be8a7c5c3e0469f130b8000ba6c20220002ac2baafa2a4989f170f8382818b0aeabe927c5c3e042a09f170a80b30ae0daa0a09a607c5c2e000669f130b8000ba6c20220002ab836a82826981f1017080b819304c8ac9a687c5c3604cc04133269f13170b0d8101730104cc9a7c5c360404cc1322b269a1f13170b0d8164caa8bc9c5c2603cc044b836a8269f1017080d8001b30112e0c09a7c5c360005036a82826981f1017080d80018b12e0c0a09a607c5c36052c040b9342d269c1f1709817b12f2daa0ba8a7c585c38361204072c036a82826981f170d80016b12e0daa0a09a607c405c203606ac040b930b6ac2d269c1f170d098100821b12e0aa7604034b32ea79a950f80e8eadcbe9e7a542a0463eb72fa79a950e810aeade967c5c2a03ebeb7a39f150e80fafade9e743a034b8b3a79f170c80e302fe9e7c5c3e039b4aba79f170f80e2caae9e747c5c321004db5a69f130f80ce9a7c5c3602dbdb7a69f130d80e6ce9a7c5c36033c3a69f170d80c70ece9a7c5c3e03bb7a69f170b80d71e9a7c5c2e035c7a69f130f80d6eed6ae9a7c5c3e045bdaba69f170f80f6be9a7c5c2e032baafa49f170f80fe9c543e022bab7a69f170a80fafade9a7c4c3a03cfa027cc53e349f074f7c27ba53d8c9eab4f4c27a153cec9e674f24278c53bfc9deb4ee8276f53b5c9d9b4ebe275653a7c9d2b4e8a273d539bc9cc34e582728539149c774e3227105385c9c0b4dfa26f8537749b9f4dc626dd536a49b3f4d8a26bf535c49ac74d5826a8534ec9a5b4d20268b534249a074cfc26775338499a74cc6265e532c4994f4ca2264d5324498fb4c7626355317c98a74c48261d530ac983f4c14260352fec97db4bd825e552eec97674bac25d252e64970f4b7c25b552d8496b74b5225a352cf496634b2a259152c6496134afe257c52ba495b74ad0256152adc95534aa2254c52a2494f74a7425355298494b34a502523528e4945b4a2025095281493f349ee24f052764939f49c024dc526c49353499c24c5525fc92f3496e24b35257c92af494a249e524c49247491a24865241491fb48e6246f52344917748b424545225491174882243b521b490c748562428520fc906f482e24155209c9043481c2405520148ffb47f623f651f948fbb47d623e551f048f7347b023d251e7c8f2b478823be51dbc8ecb475823a951d348e734732239451c8c8e374 else 0x5a69f17091716c6a0b69a7c56041c047a69f170f83810ed6ae9a6a7c4c5c2c3e0e05ba69f170f80a7010ece9a7c5c2e041c043a69f170f80e6eede9a7c5c2e039bbb3a69f170b80e6eed6be8e9a7c5c2e04fa69f170b80b6eec0d6a69a727c545c343e1606dbdaba0269c9f15170d0f85819706d6be969a727c545c3426061bdb3b1ada3a69c9a9f1513170d0b0d83822706eec6ae9a7c5c2e04dc5bdb5afa5a69c9f1513090f8581d706d6b69a727c545c34251b02da0269f17080106d6a0b6809a607c405c203e00069c041b0342da4269f170b817706d6b69a727c545c34255c1b9b035a82da69c9f15170d0981d700c6be809a607c405c2036000684031a8269f170d80012106c0c6a0ba7c5c3610055c041b5ada2269c9f15170d098001d110c6a0b89a7c4c3610053c3b3aba29f1313810f0eceae9a7c54242e04bc3bbb3aba69f15090b814f0eeeceae8a7c4c4e04bc3b3aba69a9f1313812f0eceae8a7c4c5e0e04bc3bbb3aba69f15090b814f0eceae9a7c54243e0e053c3bbb3aba29f1313812f0eceae9a6a7c4c5e0e053c3b3aba69a9f131783814f0eeeceae9a6a7c4c4e053b3afa3a69a9f1313812106c0b6809a607c405c2824203e0007cc1b036ada4a2989f170e818001af16ee9a7c5c3603dbdb7a29f170d80ef06ceae9a6a7c4c5c2c2605bc1b3aba69a9f17090e9a7c5c3602bc3a69f170d80cb12e6daba7c5c361204dc1b5ada69c9f17098080017b12f2daba9c5c3612060005840302826981f17090d80017306eece9a6a7c5c2e04cc043b1aba69a9f170b0b816e9a7c5c3e029bbb7a69f170b80fe9a7c5c2e02bb4a82ba69a9f13170b0f83818ed2ae9a6a7c5c2e043a69f170f80a70e9a7c5c3e037a69f170b80a700c0a09a607c405c28242020069c2b031a69c9f15170d0d817706d69a727c545c3426052b5ae9c9f170d80e6d6b69a727c5c239b9a82ea2989f170e818001670106d2ba7c5c3a041c2b69c9f170d80e7010ad2ba9a7c5c245c1b8b839b5a69c9f170947011ad2ba8a627c5c3a0600061b831a826981f10170a09080801aac0d6a69a727c545c3436059b5ada69c9f15170d09814ace9c5c3e16033a7170d808aeade9c5c2e0a060004fa7170b828180cabe9c5c3e16032bfa7170f8580caeabe927c5c3e03bc3b3aba69a9f1315090f83818f0eceae82809a6a7c4e053c3b3aba69a9f138080014f0eceae9a6a7c4c54242e05bc3b3a69a9f1315090b81410eeeceae9a6a7c4e04bc3b0a82ba69a9f13812eeeceae9a6a7c4c54242e05ba69f150f8580ce9a7436023bbb7a69f150b8080013e9a742e0602fa69f150f8580de9a7c543e16037a29f150f80be9c543e160e037a69d090f858380fa7c4c2e0002e9b08088000a11aeac0ce9a7c5c3a04ebba0269f170e80eaeade9a7c5c2a0004042beb7a69f)) else (if j<15 then 0x30b838b29f170880e2cabe767c5c3210042b29f170e8482800108c0ac847c5c3a080424234afa32713170b0e82016908d2ac9c5c3a08042302fa3211f13170b0e820160d2a0a096607c5c3a0005034a82fa025981f1017080e8001a2f2be9c542a0803eb0afa79f15090e828132bc6c4054243a180a08050402da0269817080d80014100a09a607c405c20360005841b5ada0269a120980015106c0c6b68a627c585c383606069c045afa69f170b810706eec6ba72631c5b1afa69a9f170f8126c0b6809a607c405c2020059b02da02698170808012106c0d6b0b6909a7c585c382e069c041b035a2989f16170e09818100c6be809a7c405c20360006031afa026981f1017080d800186c0c6a0ba7c585c38361005841b5aa269f12170a09800170c6a0b8868a7c585c3836100606c31a82fa6269f16130a0d840186c0c6b68a627c5c3a060005841b02da026981f10170a09080f8001e116e0c0be809a607c405c2824203600082c5b9b036aaa69f16170e0d8481a6e6c2d6aaba7c5c26020005ec1a9a29f170d848180014701068a627c5c3a0600051b831afa026981f10170a09080f8001e0d6a0be809a607c405c2824203e0007841b035acaaa69f16170e0f8681a10ad6b2be9a9a7c585c382a061beb1a829a2989f170e8180019716d6b69a727c544c243e16065c1b035a69f170b8180014706c0c6a0b69a7c5c3e051c041b031ada69f170f815716d6b686809a7c56049c1b0369f170f838116ee9a7c5c36033c5b9b033a69f170d8136ee86809a7c5c36041c1b5ae9f170d80e106c0d6ae9a7c5c36049b9b7a69f17098001070116c6be9a7c5c36049c041bdb1a82fa69f170d817716d6b69a7c56060004bc1b3aba69a9f13170b0d816f06ceae9a7c5c360604bc1b3aba69a9f13170b094f06cebe8e9a7c5c3606053c1b3aba69f1709810f06cebe8e9a6a7c4c5c2c36063c1b3aba69a9f13170b09816e9a7c5c3602bc1b3aba69f1708ef0e9a7c5c36031c1b5a9a69f170d810f0116ae9a7c5c36045c5b5afa5a69f1581170106c0b6809a607c405c203600070402da0269f170d8001370106d6b6809a727c545c342600073b1aba69a9f13170b0f83816e9a7c5c3e029c3b3a69f170b80e70e9a7c5c3e031b83bb7a69f170b8106e0eece9a7c5c2e045c3b1afa3a69f170b813e9a7c5c2e029c3b035a9a69c9f15170d0f8581b706eec0de969a727c545c342e00075c1b5afa5a69c9f15170d09819716d6be969a727c544c243e16069b031a82ba1a0269f170f81670116f6ba7c5c36045bdaba69f170d80e6e0e6a0be9a7c5c2e0600059b5ada69f1708c70106e0e6be9a7c5c3e051c1bdb1ada69f170d812116f6d6b69a7c56041c041b035aba1a0269f170f81871a7c5c36029c045afa69f170b8180015706e0d69a7c5c2e045c1b839b else (if j<16 then 0xd800154e6866a5c36060004041a59a9097098001190ce0dca0a0967a405c202e0006d46383028239e9017080e800188eadcba5c2a0003e38302fa0239e9017080e800198ea5c3a0a00032b72e970a8000d8e0ca5c3a0003438b290170e0c808118e0c0be8096607a405c203a0006a38b42fa4a59e94970c0a808198e0c0be8096605c203a0005d4046383025981e97080e8178e0de809660605c203a0005d40463d22a692970d0e814ad25c2a0002eb72b231e910e80ed08eadcbe9e7a54302a053463eb72fa79a950e813b1a967c5c229c4bab59f170e80e70112fad6be8e66607c5c3a061c044bfa79f110e8080014712eac0d6a69e767c545c343a1207044bdaba59f170e810712ead6b67c5c3a041c042beb7a59f170e813afade967c4c243a0200056beb7a7170e8280ef0aeace967c5c3a043c2beb2b3a5981f13170b0e8281af0afacaceae9c4c5c2c3a0a063c2bab3aba713170b0e82816f0aeace9c5c3a03bc2beb2b3aba19f13170b0e8281a11af6ae967c545c343a12059c6bab5a9a59f15170d0e84819aeace9c5a12033a79f168480af0ae6a0ae8e7c5a043c2beb3a79b9f110e813afade8e7c5a1203fa39f168480bafade9e7a120a03abab7a59f170a80faee943a1202ba79d0e8480bafade8e743a1203fa39d0e8480bafade9e74243a120a049c4beb5afa39f170e812712f6be9e7c4c3a044b8b3a79f170c80f2ee9e7c5c32034bcb7a39f170c80f2ee667c5c32034bfa7148080b2ee9e7c5c32034bfa30c808112c0ba808e7c405c203a00062b82ea79f170e80eb010afa9e7c5c3a04046b82ea0239f1017080e80019a9e7c4c3a0a0003f9b080e808000c2c0caaa7c5c2203844b0302ea5981f170e80016100ba96607c405c203a0005cc4bdb6afa7170d811312fe9e7c404c36042c4b9b032a79e9f16170e0d8481bb12f6d2da8a7c585c383612066c4bdb6a79e9f120d812b02e2d6966a7c5c260200059b6ada4a7170e80e0dab69a7c5a033b4a82ba79b9f110f83814ed2a0ae82808e7c4e04ac0af9d0f80ab12e6da7c5c3612042c0b9b4ada59f17098080017b12f2da9c5c3612046c4b8a82ea69f1581130aeecaae9c5c2e044c2bbb6aaaba19f170b0b8173010aee8e7c4e020004cc2beaba79b9f110b813306dab6928a7c585c383a05cc1b6ada79e9f120e812302e2be9e7c5c3e040c041b4aba79f170f81230112f2be9e6c23cac2fa59f170b80e112daa0ba808e7c405c203e0006ea79f130b8000d31e6c202200034c044b02ea0239f10170808018ada928a808a7c5c240c042b4aea79f1709812112da96607c405c202005044b036a5981f1708012100d2a0a08e7c405c203a00062b4afa79f170a80e0d2a0be808e7c405c203a000679f130e828000d2be6c203a020003cb0b2afa79a9f170c80814b12cabc5c32 else 0xc9f0e810102bc21844b8a82e9c9e80e31c2201944b8a82f0e8080f2e2a0bc3a02844bcb2b0a82da2a49c8152d6927c3a1203044bcb0a82da49f0c8132f2d6927a120309f0852fc22019410e800080ce809c2e02ac033a0229f08cb00ce809c22ac033a0229f08d2aa7c5c2269b0b808080b682809a7c230302da0a02708c300c29c221302da0a026989f09127c210c0302da0a0249f090302daa2607c231369909008b0aae81ac2aba06ab27c21aac9f1708830aa10c2a8527c2170b80006aae8a7c2e00030470b808000ac2e0201aba9f0b8000aaaa7c2e00028409f0b808000caae8a7c2270d80431c2601aaa9f0d8084c8ac8876028c70d80611604018c70d808081160401a2a1d806b011a6a6202ac040b2aaa69a98eb049201ec4baa81c80ba7204018409f0d808000c2c2a2827c3603045a49f0d808000f6927c22022c70d84808316927c2402ec4b8af0c80a432040184080410aba76026c2a81980811c360200028af0d807c22010449f0d808000c3127c2402299005b02bc218402f20239d9016880f00016d06bc9e76765a323c140533e37279d9d968c8f05014d1c9496765a3c140433e35259d968f0501051c9e66764a223c040005647322f2025989e9615888881991cd8bc9892723a04640463727999d92888980016118c0bc808e76405a2020059362829a3999d91968f01016cd8be9e764c0403f37a79d928f03010104d8a0be868e6676465a3c0406599968f05030100e0d8a0a08e76405a203c00059362829a7999d9192888f03010001d506a0bc866a425c3e0600059af259a909709800114ee9e7a5c340353933a79e970d00e704e8d2ba9a7a42405c2c05f303028201e9017080f02010001acecde967a5c2c03f3f37a59a970f00ef0cfcccceae9a4a5c3c053c33f3333aba19e92970b0f0301acecd67a5c2c033c33c30a82ba39e9704014f0cfcd0c2ae8e7a54243c100673daba6950f0500f6ae9e7a543c1403b3935afa6930100fcfcd4d6be8e7a543c1405535afa39e950f050114e0c0be809e607a405c203c0804000793a34afa6a79e9e970e0b0201870114fcc6866a425c383c1804000733b359e97080b00e11cc0c0be8096607a405c203c080400081c1a59a90970e0f060100016cecde925c2c0373f37a79c930f00e6c0c0b6866a425c2600051b02d9897098000f2d4a0ba808e7a405c202005cb32ea5981e9017080f80016ad4a0967a405c203e00052b5282825981e9017080f800180d4a0ba9a5c34340a04e4040b12fa1a3999d9197090e81b904be9e764c242a04040b72929a3999d9197090e81865c2c3a120a02038b12ba79b9b95090c808142d4ae8e6e5202038b12fa3a79b9b95090c8142d4be8e9e6e6e543202056423ab0b729a19d9197090a808001d8e0dca0a08e76405c203a00065383028239e9708))) else (if j<20 then (if j<18 then 0xf6b6927c230c4aea2989f0e8081070312ba9a62643a06049be9a806aca9a618c5bab6989a6a010c1bc9a9886ba607c2a06031c5af087716bc21ea29e807706d6b69c228a8a69f0880a700d6829a62607c22048c0b034aca1a698981f0e816302d2b29c3a031c0c0b4aca69e1f091706dc21cb4a6807706e2bc220b1a828a698981817080d80818302c29a7c22034c4b0aea09f090c81130712c2a0ba9a62607c3206060c0b0ae9e1f0d84810316b692745c34220004cc1c0b4aea498d2c2ba927202cc4b0aa1f0c80d312c2ba9a7864561204ba2a6806e8a827a022b3a2a5808aca86960e02aba804aee0a01ba38281808e0a0601abaa3828000aaba0e01aac989e808aa27a01ac49e806ab6011c2baaba58380caa6ae960e02abaad806b0aae8a9a10032ae8403808aeaae0a0002aaba3130a8000cad27c360249f0d807a12012a09e84808aead27c2202c9f0a81808aee8a02022ba80806ab27c36022bc9f0d808aba1201aac989e8480aaae827a120e0349e84806ece9a6a7c4c5423ba69d09088ece9a703202bb3a0a69a9c0c80fa74242e0269a9f13150b80ce9a6a702e020369c0b80808eda702e0002bc69a9f13150b80fa742421e9d09086eba6a7c4c54233c3ae9c0c80af030eba6a703203bc3a8aba69a9c0c83812f0eba703202bc3b3aba69c0c00ef0eda70300e033c3be9c0b8000ceae9a6a6c502e00043b3a69a9d0d80ce9a7c5436028a69d0d8380ba743601bb3a69c808ece869a6a720369f15098080ae9a74260202e9a9d0b8180ba742e06023a29b818080ae02013c3ae9a9d0d80da7c5436020c3a69d0d8380c2ae9a74360e033c3ae9a9d0d80da7c54360269c804f070eeeba6a7203bc3a9aba69a9c83810efa7201a9f150d8380ba7424360e02ac0402f088b0100bc2230b80806b0100bc222c0402aa29b170b0b8133010ac2c0c4bc238c040b02f08bc2090900410ac2c0dc228c02f08630102c0b2927c23eb0a708610aeac0ae82842b8286302dc218a7085c22010c7084302bc21f08805c4c2a02021403680649a0169a8000651a011412e807a0a0001e80005a7c2a020270e805c3a0201f110e8000810ae0aa7c3a0a03842b82a9f0e8280fc3a0a01f0e82807c5c2169e804aeace9c3a02842b82f08810aeac0ae8a7c2a0430a80806c3a0001abab3a3170b0880fc3a0001b090e8000810ae0ba02042b82a9e80bc5c3a0a0270a80807c2a02019403129229e8280ea000129a80006302c2a28a7c2a03e9f0e806aeace8a7a0a0003f0e80807c3a0170a80807c3a02018c4b9282f0e80d2e4a0bc3a02844ba31282b20d2fc3a01f082112e4a0ba028bf08806512e4a0ba02cb9282e8000a112e8c4ac9203044b9282c9f0e84810112e4a0bc3203044b92c9e8480c312e2c2a0a2805c2024cb8a82f08810ac2aa82044b8a82e9 else (if j<19 then 0xab806100d6a696029c5bdaba580a700c0ae8680960e041c045bdad80b716b68e021c041b82da580c716ae9602041b82b818000d706e6d6b682841b1a82da3a38180013700e6d68602dc1bdada380a70ece8e021c3b3a0670ece8e023a3804e00843b3a380870ec0d6a0ae8680841c5bdaba087010ec0ae8e031c045bda89716ae019c1b8470106e0ae8e035c1b5ada200a706c0c6b68686039c1b035a1a180d706d68802045b5a5808716e896025c1b9a80086c6a0a68264443606049c1b1a829a58180e6d6a8927454360384035a9a49d150d810716b69274542003841a82da49d150d8102d6869a62607c2e02048b5a69f098080c2c2b69a7c228c0b5a69f08a2d69a642602030b69f0b8086da6a019b5a6981f0a8180f302d28a627c3a02044c1b0b4a698990e81812e9a7c218b69f08627c36060200030a69f0d809c208c0b69f089a7c22018c69f0d808302ba7c3602e990d818080ae9a6a7c36029b3a69f0d8180c6ce9c219b3a29f088f06fa6a7c22bae9f0d8180af0e9c26023aba69a9b170b0d8106ce9a6a7c22ba69f0d809c20e9f0d806e9a72019b3a69a9c80ba727c360269c9f0d808b12e6da7612034b9a69d8480aa927601ac1b0b49d80b6926602024bcb2989d848080f2f2da9a6a720603cbe9f0d8480b6927c260202cbcb2989f0d84808112f2da9a626432060469d8180808a660201aa69d806b02da760269f0d81808000c2e2da8a66020303698981f0d8080e302a29a7c22034c4b8b4a70c80d30712e2c0c6b2869a62607c32069b0a7088000b302e2d28682ba29f0b809c2e013b3a69a9f08ae9a7c21f0b805a7c213b4aba6988ed2ae9a6a628be9f0862ee9c21e9a9f0b809a7c2e01cc4aba29b80b312ba6e021c5ae9c9f08b706f6ba727c235c5ae9c9f08a702e2ba62607c2e02048b0a9a0a69f08c31a7c360269f0d8062ba7c260202da69f086302fa7c225a69f0d80830a7c36020b8ae99098080c306ba62607c2e02040c0b1a0a69f08dc36010c69f098080a2d69a7c220bda708631a64260202bb3a69f088ece9a6a7c228c69f0b808ece9a6a7c22ba69f08631a7c2e020c69f08630ece9a620c3b3a69a98ba7c213a69f087a6a7c2e0269f0b80730e8a6e024c69b806716ba727c229c045ae9c9f08d716ba727c22e9c9a9f088e9a7c2e025aa989f08871a6a01ab2a6986ac6d2ba869a6264442a0600065c0bab698970102aa0600035c69a806702f26a621c6981f0a8180c716bc21dc5af08670ad6aa9a72630c045bab5ae9c98f716ba726a028c041b82e9c98c716bc21dc5af087a927c3a020aa989f0e8080d302ba9a62643a06041c2b5aaa69c9d80e10ad2a6a0ba8a03dc0bab1b5ada69c99813700e6d6926a6066045c1bdada69c9a80e70102e0b69a7276041c0c4ae9f0e80c716b27c36028c4aea69f08b702 else 0x9a643612060483cb6a39a99981c8102e2caba9a6e6602042b99f0b808aeabc2e022aba70b809c2e0103d98981f0b80caf2aaa0ae86632b83d9c99981b808111142e01c42ab150b80b3030aeaae8e702e0204cc2bc0b8080b10aae6c5422c40c39d0908a300c0b286808e66040c046a82b9a999819131abc219b6ada10980ab0ec0c2966672038459c99981c80db167c22022aea2a3981f0b80fa8e607c2203398981f08b31a8c2e0202aaaa3981f08a302caaa8e606c5c2c2e05030a8a398981817080881430ac29c5c22a2a259b009c5c21035991f0882d67c5c22035991f0888a89661ac3981f0e8280cb0ac2ae8e606c5c2c2a050c0b028a3989818170808816e607c3a022c2b3a3981f0e828112bc5c2a0202b98981f08b2ac3a0a0202ac2ab9a9918aaaa6461aaf0c8062eabc320270c8042bc5c2202717084b1c3a0a022c2b3a70a80bc5c3a018ad9f170880b6647c3a02a459e82008908cc967a08030ad9f170e80a0b6647c3a02e4428a82b9f1600f90b0e6c7c4c580a04041b82a9d80a106e0ba760603180360601031a58060c2611b1a1800080ae06000203e9b81808106a0ba6e060003843b0286700c0ae8680830402c9860a26e060002841b9a82c9b81800106e0f26e021c0302ba1a020c10e810402a9860c2611c031a6988116ca619c02d8060a2611c5a9800082d6869a62607c2e02048b1aa989f098080e6826a019b5a698981f0a818106da64260209f0d81808000d6060201d818046c09a03a660169f0d81808000da7c3601e9909806602012989d818080bc260201a99804a627c3602028a70840da6260605c20360403698981f0d8480e706a6827c229b0a21f0980a2c6926a6862030b21f086306ba62607c2e020469f085c20e99104702ba62607c2e020469f0846e6d2a6a0a68264442e0a0584038ae9c9a981b81812100ba6a620c2989f0880a6a26a019ae981f0a8180d27c21699098066a26a0189b82818000a6e6d6926e0a0600041c698981f0a8180e71a7c21e9f08471a6426020402e9a988a60a989f098080a700da6260605c20240a70846827c218c034ae98981f08e71a787c224b49a9a188302c87c220c69f0d8086a0ba62607c360382e98981f090d848107027c260269e1f0d8480a316a87c26029c4ac9a9a1880c2b27612020aa1f0c809a786456021c033ada1a29b130b812706c0ceb686831c1b5806e869601ba5804706d6019c5804706e6b602581804106e0b6023c041b9b02ba180e6ce96019b3a5818086ce96019b3a5806f06f601bc3ad81808f0eae960602baba29b130d80ce96011b5804e86011b03581808706c0c6b6869606041b5a1a0008ece813b3a3806106e6ae8a6c4c2e041bba38066ee013b42ba3808716ae81841b9b029a099110b8180017706f6a184039aba380b70106a0ae060003dc5)) else (if j<21 then 0x6966460742461708806502d69672685c342470e00807d04b844203a180384021046104599181f0e80c11664606802b29185672685c22680201459e806102616802102610312925990e80cac8aa88221409e806cae6a6c3a0a031439e80650ace8e6a6c3003b9a9c006d18ee61b463b2b9b1a9280ed1a543a02345284d14ac61ea59f088082ba967c220c6a59f088b0eba96666c5c2c242c6a2a59f08b0ceb424222c432a31508b0ca8e6c5422c30b39d0908a712f6ae9662844b82b999818c712f6ae820402b999818a70ac2d6623a1a5986712ead6624bba598766a02019c5984706b661844b2b1a82da3a599981952c6b6966259a80806f0aeaceae82bc2bba86f010ae0a662842b82d9a80af0aeeb66662d9a804f0aeaceae96633c2bbad988ad6613a5984f0aeace8662842b9a82d999818eaeac662023c2bd090e80aaec5a0a023c2b1aba39c80cf0af201b990e806e6c5a0a022bab3a3999c80ce72011c4bd9f0e80a306627c3a029c0c4b90e8080c712f6bc3a12035999f0e82808000e312fc21cbf0e8063167c3a025990e80809c3a0a01bc2bab3a70e80cf0aeebc3a0a033c2b99f089c3a0a01bc2bab3a708af0aeebc3a0a0359f0e8480967c3a12023c2bd090e80ac543a0a0239d090e808e6c543a0a02ab50e84808e943a12023c2b0aba39d0e84810f0af43a120a032bab3a09d0c80d43a1201b9d0c82808e743a120210e84828080ae66606202cb82b99981e8080f66a0201841a82d99981e80eaeace867a0a033c042b82d9998c10aeac0ae966a03bc59998610ac6a0ae9666606a0499c808062e2caa6ae8e72039ac8042e2ce8e6a667203b999c8062dc3201f0c805c320119f0c806c3202018b9ab9a8082c6b6966e6a0203f0e804712e45a0202d999f0e82808000f6666a0199a80806a8e607c2a028b2a3981b170b0a8100c28e6260605c202204ea3981f088b0afa8a8e607c2a044b0af17088312dc5c2203398981f08ba8c3a0a02028b6a2a39a9918c2da84618b7170c8082d67c5c22035991f0888967a08022432a259a00bc5c21035991f0e80a31aa29c5c36036af170d8092ee7c360200036a89f170d80b31c4c403602ac4b9a07b12e1044b838ab9a9998191b12e661ec4b9806b12fabc3602ec4beaf089b12e4360602ec040ab9a9c81800102ca7c2602028bb998060f662607c2e0303ba59c999818d2aaa0b66662030c0402b9a99981981131ab286808a634c6af087306c2dab69284260404030a4999818cb00c661bb3a509088b0e8c54222c3b4aba40c80cb0ed2a2a28e7032040ab9d09088b0e6c54222ab9f086e7c2601b9f0d808000ab12faa69a761203ec4bcb6aea58480fb12f2da8a720600046c4bcb6aea19d84811b12caba9a761206042c4beae9f0d8480eb02f2b6967c2602046c4bcb6aea70c80fb12c2ba else (if j<22 then 0x84ce8e740402b9a930d0094040113695006e9a5c34020c539ae909017030001367a5c018c13e910000a4c2b6966c028c1989e9700a2b6966a5c028c53e91090000c714f6ba52543c0393dac950b00b714ea425c029c53daaa69490c4f6a6b24802e34a9a82ea298c304e8d2ba9a7a425c240513da8ac970a00c31a9a6a425c00039c53a0074ea940193a010078da8a6660629c53e90100f02010104f6b4280402d999e9090170300010314fa5c0253f00567a44000213935a09b00a3167a5c0259e91090000ba5c0c01e970b006cce9a5c023c33bae92930f00ef0ceeba4a42b3b004f0cf6667a4c3c03d9e92930f0300cf0ceebc3c02bc33bab0f0300cf06724a4042bc33c99981b00d67a4c01b33a697008f0ceeba4a4c3c03bc33bac9e9290ccf26c01d9e949700967a525c0259c930068d67a52422a59e949084d696667248036349a909200a4d696627248036349a90970000cf0ce2b4243c03338aa970300af02ba4a5002bc33e910c0300ce643c01b9a9703008cce8e626a543003b3695006e9a5401e9301006cc2ae8e7a54033c339a8ae92910d010f06ba4a5002c03004cecce827402e9705006e6a5401b9e95006cce8e666a500302b99981e9090c0ae66606242843382d9a9300c10ce0b662041a82d999818d66c2c01e950d006106a0b666607a542c340c0599a9100766a5c3c0c04030c539ae9090170301000146a24801a99981e9090a714e2ba405c3c08040493e97090092a6a0a2420c290970000b67a4c200259c9998188cf6724a404c036910856667a42405c0c00041989200767a4a44021302680e91005a440159e9090170f0201011a440169309006a424801a90970000925c1801c970600724c08019c59c909400acf6700c02497060066725c1802333a1989400a67001497060300808e66607a424302399981890a0c8ae80966a43033a0259880c68096666063345984514213414031a02599981d0926742601d9f0b81809664213981b806e606a4c2202b0040c0a4618328040c0a26192ea398690ada8a8e6a6c23e4244332aa39b1a911910ccae6232ba3999d970b08ee66765c2252b2b999d91950b090e6661243999a808cae6c2199d919068f6465c2c2a0203b981d9190168080f4aca66076464043b981d90690e60764a02b981d9190168080ecb641399981d919010c64c3a0202243981a908e60613981e95818000c600b981895818000d4ea5c36060281b81800094ba5421d2b29981e950b818001366a5c2e0602d9e910869166a4e0002d9b800076607a424e060003d99981b818000ccb66119c91806e607a01ab3a3981a930e82810100c48e646060443a000563ab32ba3981b08f8ee6061a3f0a8000810e64607a02e3a970a8000acae6a7a4a582c23c4140469608a1166460605c243a0004cb5a50a008112ccb else 0x10ae4a21c43928868ce60764a22b981d91908cf65221b4594886e607646405a222404399981d919010cce6b65a223414596888cf65a21b4596886e607646405a2223d453d239e88b50d14ecf48c86607646405a261968a89009c964a3c0c040302d9e958898a25621925968a888e607646405a2223d2321981d91901689091c964a2e06033981d919088ce60764a22b981d9190168888ec8e76465a22b99981d919010c65a3226023999d906e6676464c02b999d91908e66765c0234333a3999d970301150e76540254343999d9195030108ae60764a22b981d91908e607646405a223c0404b99981d919010d65a2c04025968a8b0100ae607646405a223c045439e8d00950d06607646405a340c051968a8f0100b6464a3c0c040304399981e9090c10e66606242d269508650100b48c9666607a54257259a970b8180cd0108c0b66a43340402d98850100b66660633259846724601c3aab970b0d00c310ee5c34040339d9090170000ce7642405c000313a930d0)))))
def g63H7 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then 0x380d22000058bce683b80000000068650890500001e5c4e0e3240ad800006233800000000000000000000014aff22401c2ff00000000000001030ada5ee803080001612600000000078f8942c280000000000000546f583eb60a370f60000018d620000304ff81f0da42763c0f8ec2000008a1a00001093ee3c88000002d9c14ec00d02015603c1cb50e838940b82840c88792257ea0ac03698ea4220000621ba4117d0f640000000010283d06b20257e2299817d0000002e842674227a9088020ed40e2b813118ee8a91e084ed020fc05760346a06f240d980000407eb93252004d864f61f7000000955c011d40eb44331a3e2fa29243d34884140bf8000101617247560c3a0dcee09330b954007587bf81956085ce109009fd083a98502233c80000c1a500000c077023e782ee2aae8000000000a34008bd0890b0000060373952d233198c6c605a505cf4d52b040e00000063a2149e0796034d3951749147c32d2047802600000109d70044c827400006b4fe20627894200004243f80430000188f2ea189c12bab2b460e380000000030a90ca4300001636e800009010d0628000282c0023c2830343d12067684b0202011b40450004061931b08089824c7018306041001a280ad39a000d021c28928291111b6c0020014700562ce9404001870c5c50c1a280020445403181430e08382923418018362c19b0c5409c142c00436240120404001000088f00141030e241023a1031b00300030400f820551b81101c090001050200115010010c002600f00dc081380040396128d1a01c1c001022c0871c8c28a0e143871a100062a180022e5801a0c0008b0608b821264187000019f2630a8602141a2001818e2a244102a28002062cd010454702080428b1ae070d1c0001303d0400000c78904040820c3010202000022a1c4831848f8f0001881000a1000041a8b7604b8a1414007302c00400043806654e8b022060002005850a0c1010650384022c08610086b408298010050186020c01a3201000062810004b0001aa0428b888c300002468008445050408b8f029429e140c00c0c60189162198c0a1cb050a603030428a930008100000058000201830204181040811a280008908040831010202080011202a808006c4304160408b0004080223000806041011600000000030d02040841a00081001d186021420f0018008020028c3404c8500201800408106004a202000029802201830a0018600201021a001000800d870c0000114087883600082561c48c000c018021c001001018e026818206500861e004000804f000018105004c105068c10816205850c34097400c3881608983021c60b069c0830a00121189828608540050cd8000000801b0604200000c5810008108023840156102000e0c782280c5840e144a6063008d081008a1410286 else 0x40000048989082298a04e00a108ee6041181f4e0fc6045bc1a6e8e3c88b26212a4142b8626cd6312442000078c5ac9297a0c3003f28b9800006a0a0000060bbd82c48000080bb70e9361f608b100000407fa000042bbc224558908c1b6800010209e820d6230a0760a54fb06b4000038860000000001433480000491da2679c1ba8000061eada894000060ad400000000000000000000000847200004870a80e02abf863dbd350a441050e50000048bf9e06d102d600005158c00000ab9aa1ddd8cf8a1808000060baaa70aa1b0e8c8122ea78d89c11b800014114882c9102a28551b22a000000000508f8a8e4ba7cec79b80000a00380be5e2e46078fc249b061a81ce7b5f908e6c831a0922c05ada19310d9c434d800000541b8b3ae36400000c8053850101e600000a2b3948e8a12130e2c0000000000302e80e0a913489bf028a28081417078bec039d0000101890000162b100001e0e5088780000109c8610492976000000001612980001a1a630642000000000e08ae0077a159a89f400005806043938a9f5e36158d3bc3a7e8064a1c3b8975e0d6f052a00002220f604d687b8a185395c8a323b865c00003a134a192a8cc4c286295374891e09e9c3898000000003049122f0588a8c8f8205b1808a7046c00002abc1c1df20e01822b0000103926a0b2832d00610e32280000000000000000068376c3dea31a5033268acce0263ab6b231c00000000000000023a186c182bcd202a23a5eb5500000480a8c11f2c0e0881f088eb23887b500213958abe51f44285908eab2a92a09e206c5680430c0f01ac18c98e2d2434ec0c71e0dcc0000180e2a3dc50a9a43d5d01f9c0f9085cae9042aa89621fe8842c080c896ae16fe4332e0ff903ae038fb89f181d788bee08a0d0a73806950509c007c04bb6395e0dfa039e984b3c082c103a83970000000001088f28cb80001055380874e18d40f336d703352b41ebb1061613e704d988c15a6f763a0e0ea18571189d0a06830c2e000038eec000000000880e90515421190931c3bdd078280b098599002ac0adc0000401b2000040596e337a07486132f2035c2362a0b167554806983aaf2691439918ede0000786f702cb00000000068bcc000028e22c38200000000000000434780000026508d6c0000706400000383a4000000000e23998812a9210207340ccb29960000405860000135084169683092d3908e1ecdac2812000000000141f4700e8000040ccab1fa800006238000000000280a4eadf881cd824bd836000000000103512098720f3b03f20000505ea28483871e00000850e000000001854a1495e2298000000000000005518d03cde25c80000000000000000038445635f00001405d0000000005c013219e9b4f8833eb8b3463bf1054b4d4568950c10c1d3cce0f6b0b0f520fa9f35c3b) else (if j<3 then 0x7ac83231ad01c02053b9dae00002892a00003210e0000302f84b032a227827b0000101235827f43a06a14781e5182e7e884e3518000000001c3b079e2bc26ae8230e1cdd0b20631808f8340ca820e52a52cca8e0357e830202dc10a7b60d160aff2090d0d0443148478e604090eb5605a90e3608b6f2c5300ae08f37c0c5e243b228e18f1d548b0000181dc80001a2c0000016a9f000000044609d36d7f515498372088c000001ab4e0000201e041ded8cec0000606200000681b05255e89c0a03600001e3e17104481f21863183d8f08bce13cd84e0e22cfabf6000028048000000b420279602ba000000000c1269235d82a4a051042df800002d3a18bf600000025e0000000000000515f8a905d037e000000001e1060000060188000000004014160a4106a8804c82133d47e3821bc315c018340b310a69818588562229580000a36680001e32f38e28608001058c294800019119c2496000050038000000001418e50530000000000ca468a101a37d00000a069ba55b812c0000161b7800000000302b483a9a09fa0235c8d75a34f689b9c2978046200005026dab0c80000205b9809c02558896c016cc0eba407f80001835878a3e0000205922265f9540286980ef24b0e32030002ee894d2adf60d4ee02f80000637a00001a90a88a63424d8043dac1230c380000708bb6150e84860000304800000601440000000000000583f4000000001ed3ce0e346112f082c000000000000000000000000000000068c8400000879a0000286be00007005feada0000081c2223e3c08180000000000d060000786720000231de00001ac35054ba0c598123a289ea08580000000012a73228280000000000001a247d0cda000000000000000001a2d28000000007a79f009af8c2009c22a95b60969a29700258000000005a3d6e13f023d48c9d9353109d648ef5c0b56021149e3103f60000084b763ca80001e0b9587fcc0f108b28e360786c9c1add0b5da241b0edc00000000163c2b2b5c408828f8622ccf2033423d58e5f62d4e8d71874950c066ae320ca301e100001e133d0f3b426b80000000070365a1af40ad2000072a4ca18bf8a00122540f0e0000000006d50b0a16000000000217e5aa00622480000c1bf00000431e800010260183bae2be18c9d007980000638500001480f000002056000006313000000000623b86163d8dd6000012434000019a46000025470000000001eb13288eda0b7205f00000294fba269da22c00000000000007076caa15409cc0000487e2e232725b000003a58eb11cd82940000786ac41860249de12750cfe0000000000000040fc0000682676155d03bc00000000080b780001ed3f39e120000452da833ad971601d56068e6329e244fa8fb814f5e8e700000684528f6c635400000000000001407180000751a50e else 0xa4400004855e0000000010aa98000049090000142c62951400007546f62a380001609280000e01b1055b01b700001a0fea83685472f0b8cc8fab2b1902aaa0459f3158000089b76067e00006044600000000180058000163d038d10c33500180e15338d40c8da6300803bc522cac9262060f0348303240000482fc00ec082bc02cc00000a3da00000a2c8f31d6e8cc283f800005803fa917a0205a3710000148c1c071800000873d218aa4093038ecaaa94d5508483c0e7e2998000040be620a1e23b5ec800000000004aa57a39a315fd2163000010a5448bd761b38813e01622150fe1ccdc348a8eb2b1d2a03112c8800007232c000030d25a1fb8000163c500001016078bb743c680ef8e22080001604f5abb600fa58660e166c800aa33a2954b007f0000000000000100d3181b921b89a13be037c004fe381007d5838e30dfc2903dc8100000500260365c0bfe8061ba3298850507a0216998c2483234873ee0852ab86a0f018172a07462326639688894c339b82cbc8e3f059f423da878c000000001228bf85c7290bca4ae1264d02fb09897b54c21f1494ffc1f018d5da19da09d4c40fd8398000010335c2d7fa3010229f834682ac0089bc179d9f26e1d000000a3cd401900000302898254d2b5e000000001435ab20d5aa57187dee0b040a3de04580001237e607f9802480bc922522091c80df352ac40c658ec800000c465224f6043600007027a00003a231c2f880000f10a60eea000060eb949cc28465e29e10804c9561072b691ed8ed9a0efb21c80216f08b80000423c7203488d95435500001013bda0e0002d00001282a3150260e2b9e1b29029ac30c176da7b4000000001c33d0000049254243981a0988100000684896289a29bce83b0000000000000062378240c8549903c800006876200003279042f500a034327b87fe41d2e8e9bc212f814de07c0867c00005a4294148f8bf3a17f00000a30b22576c0dcaa9f192470a3a2c35a630614381d95c1a77df82ce0000129558a80ba7bee12e580d04ad9800000000607b274ae80b600d71c8b0c09187a47f6afcc8402816a889ef4248b8e90208eaab0ca25bd835e691702c7e81462002d422462b60a26900001e3b420dd403a3f2893d4a0987a7206e80000000020a11034a1841ac2369a9480000005f3a37b689a821bd324368a53c077e00002a4ada5cae8d4ae91018b6f90cad0f72000072cc80000000000000787d783a6723a60000525b3e0c308e94000000001c21c00000000070070000030396232199038000020eb301a480001c24048905611a9098461992a3d20000034efe1f2e151de219e8084ed87800cdc0f41c3cc000013523213a00000002b3a68e00003080600002b00d410778cd9ccae7951a6548403fc000000000e55c923b600000000000004abf4a0a38000000)) else (if j<6 then (if j<5 then 0x20a86000012028615f58d76a00be2b1fc84162b78839648d4800548019c0000720ce000000000604c400f048fc587cc000020821ab1210e786342b2c8fe35ba87bc0000501a301dc789d903cbc84dc000000000684b80000e9169b72aa03fa0582e23c5b51e02c7e0223aab9303830095c0bb18a2a58022c2713886a000000001215778e8ae39b88c7c00002056802c16abd6479a3847521cbd0605a3daf880cc245e29928aec18c33492f00000613d88e7fc0ec90ca8023f924e22a3a00000000060c04000058262000010d3021f92007e0000226c1c07600000a914c8e600000000000000182e000001a0fcaa3e4c78d0ae3e838487853a9252240eab53428db0ad622c1f02d0000040de2037d88791c10208834e19b000000000080bd4d5480000125600001a3b508558000038c4a81a7900f243df8000000005813a00000000000003485e6b1280000000000c08000072412a542d2395416800001a16b800012099586a4a10800001a36f800012000607ac000000000000000000000008433e2a20000000000000000006053c41c1586a2000038aa10b22e821c00000000000002d2d5e1b9000000ae7c8b5a012d20adf0aa36017c6045701d78affc0db600000a47ce587a068b8c9ebd1a8000000000000000000000040dd20000000016287e00460385a066f6d3df09598197f0f520000082d9a107b8a75824c8000003c10000168ccf011b8285184f08061396b1c306c1551c8c200000000008757c187902ee821780000207d8000123766016ceaa64a3e4000000001215180000a218a0b44000060f2800005805601434808da0d2083d94213d150003d100000000068687c0665a0b4000068886000000001a8ebb887ac1c578779422d0000000000000048ff92ab400000000040de00000000038dca0000485a8812780000000010b6c62b962bcfc22230bca0000000000000724b2000000001c124e0b3d40cd8000182ad38f808d4f1894774b58952a000000000a1c98000163953060601d400000000030de4000000000e2c20000000002aafc000060b76000000000000058a6d67cfa84d2f4f6584ebe1eda2068000048afc692ec8aa200002304660e82076bc3ab80000802880000000020961c2ca8000000000222be212000016d3c00000a3a20000003c4286e6e0084890a000020b7c000000000000023714e115f8a2043290a95e85394a83ea9f43aab603d09a69368bff8775a08fd88b6000008f3960e33105641550b546887a4350dca38123a40acdd828a0000223ce000062c360000020a428fcec463899380000000052012000000000438480a6fc391000006368e950800002a3cda134704aa60af923da4748d816702f6800000000000010132320d6000000000000078be068ff38e18a0f7f963bc53e0a430491100000000030 else 0x10087a09cf845069236843f019680000000069663e014c0544000000000000000001e3346828000003b524000040b9702648000182a038eefc840ba7942a55a8c02e5465029842be8000121ae48a85235c9878781b800001000d800012205f03dd09b870c22e2d1800000000000018c15e0151569d5814b6aaec8bde4b36e96efe3001885200000057903b4c8aac6ab99873b816e0000080722c79041bbb8dc72041d829fa0a49278aa036f036dc0f0883ca0000128b2eafec9d80000040d33a31e02c05c2ed00001aaab68a98c34700000c2e928acbcb2100000428c52bb466910000083aff274e000000000000000000000018911853a2881a000010ad943cfd01c3a056c0363a3b680000000000000000048983eaf1485f6425f8000062f1584e7289a8086c0000401f3d47b40868e058003edc2d90354549065a4b003b85044e00245818b61417a2d4b1121044862ae3a18bb51b00001226c0d1a621d480f74a80e386ab430c00000000028f1e0000000010182800000000785d7439af80ae00007a68a0000408a382344294ce27f885380000000000000686d8000035368c3beea677a872fa73ca01080000000029d4c201b8029b0a508000000000000081a312c1a8175000000000084044753a0f5f63adb0939ea9d5a43c0000000016309800006b1e8000000000a48020dae0c63c01418a32032bb23f4c32ad0de7453cf244a00002809a000041048000000000903e00000630500000000000001a0b480001092180001c273e00c0000002b8b4ade8000000003a48fe1b5722dda3d98000003396853b223880000e29a9004a000000000000000000c20b9b4e62a9d90e4c0000489b282fa20a66000060a8200007005d00e4000000000085346d4110df140bc80000000000000e09df1e17a8fde953102a7607ec0000000000000000014356624b72d4e58cce000040f7828f100000023f20f312200608aec06beb00340790000042484882a403e00000817b00b8600006b04200000000122b9b0b380571d0f24e3518000050f61291d837ac8899c3a700000e101bb5f6000008ebc000068d260000606d60000000002191231da81b29057082dd48ee7c550d01da01cc1851e81a1207f3c2c6e8b1c21c1f23ba6310f2ade0000000012ac700000000052b1a206ffac43f11c0000116958000000000000000001a2d7609730daf4184b02b2202250259229652a5e000011062277e1c0cf61bf80000ad4eb89980000108fa432ea8c180000128c80000583a9cb201b04a0000240e40363eaa62c0bc00000889854d3689d0a0cc2204ab0da0000018d56632810553884680000000018b2fe39c0ac0b453f20f49a05538de0e1152a3bdc2e680000000068236000000001d11a20efec356801ab886a906fa8262800000000000000) else (if j<7 then 0x8e8c000060352000000001311b80000e023b4014000008b92000040828202cd06ccab234b53600007831f018a00001c27c800000000423fb40f800000302c60af1e9160000000000000000000000000003a4460000000000000000000000535c36aa518d87608b00001236098969a12880001d49af86374aacb821e0000286a17249000018216000000267a093bc00ae0c17e25980000a9f1b075dc2de12b85c26378bfac80f8aaea000040dc368ec603abc0dc58410a55510db800004a39e000000001d1f1e0bba00000000082acb0d16218cbb238000015202a20e800010aeeb2349409240528634e0000000006818fa1c68000080057a49208fe0000000000000000000000000000000000005879d68fa2087d8d53b0b80031b8000130cb80001700418a2c000060d2e000000000c04db8ab74031f0f2d41ca2060cf2028000083b5804d56222a0f7d000e8000000001097c0000000018168a96cd202c0000008f000000822c00000400d4063e00006865361fd70e52000060d3e407a5801a00a1702500000080e6000035b7a000040d8d455350818831c888c6e135f87a22292f8781004a10ae20000200cec24b7866b0221000008311009df888618176000000001009180001e9a310a46000030725c86f00001631db2399225c3a092615b00000000038a3a00003aa8e0b1880000000000000000000000000018b59200450019c3c670bdca33c0046602e7782a0000008a1cc14c80001c01348b240d4a0000000000000108ef8000180020000000000000000004a8b8e28880001a23300000000068b02433000001c8e292c86000000001c2fd380ee03c300001c0a08000000004248800000000000005874d40c170a48614b72810c03900001a05740414e0cbf0eca4a02ea3c8492e609ca61458000101004035100e2005ee00005831cc8a3c86ec420c0000000005a32b499a60a9e0000484be000040daa00004880e000038aea00002861da37c80000000000001687b781ebe10980000205c10c3a632400000000078712000010662020c800008a2600001e14978c67e0d2807f60000000008900e01b6457dfa02c000000001cb0ef230212b20000000002a35e0000309e722c598e6c621c8842200004847841d9e8bac00000010bc906f9e2e00000000149bc80000000000001a027cab02006480000c3a8c033800000000000000000000e180000000000000000000000218b000000000684e3653be00ea00000000028e5f08dcc0dbfb04d201ed84a928f428a7c62902a41cc91ae833daa6160bb2000030241c0a99827c80f9800000000000010aec8000000c4186e800005b52dadc4f057e000028ead63a920d7f6d45fac5600004042c003e88ddc000000001806580001a5488000000000000021eef09180000605e400005090c00000 else (if j<8 then 0xf2ac9e3048006600007823c00000202e6d50335c80000488d2e2d88000121cd18a54a0aba835942b828711c12f3065600005814601fa22233c278f82f528ecf02dba2668005800000000000005003140578842accb480000e25e0000000003151e083f80000aa1780000000000001231a400b6c01a80001c784706f00000000000000122d8000000b5100f8f019e00001807de3d640941c3d6e0f466326884a080f560aae0000100956a3f8884522097a958213ea032042a36352f02279275681960c85463190000022e3a89dc0000305e9038b8000160b1e0a96c38c68b9e61a278dd000003aaef03c04881e61e7f08a4e3c4a955383868000000000000003a1000008b1ba8b89e0f5dac5163d410bc2cae9ca408a324c84cd813d08809caf080001227e6494222fc2890f6d71730586d98981940000602a2000000001e0321a906000030836838430a5d23779005428448000122d338adab256e09340000202e8c3cf2856a205230c74090810033e92d00000416eb05b5219988e774399c490701d962432000000000e03d087ea000060138e1ab8000001a9aa7eb42940853e000000000e36491f73c00f78c35e32b000000000481a9f6aa29da200002a1a8c10d30e0b22050000042b1800000000000000000003b8000000000000070040436f30f5cc53dd8aec20de800012d3eb0270431190702000030c5ecb3028a4ec30f80000e20f482b0000000001833f29715351cbd28e4b0f820670907d02320227488540000701d2000078a34c21beb0254094b056162d580000000000000c1d61895a82da9839c639f0829620fbe050600005020f88f638d9f7512234f40000287c6e1c80000082c9d8e1dc34b42202000000001eaf8000016333000000000688aa000000000000000000000040165e9278000102eab044343ddd04a4000038abdd2e39807501e9080a00000000000000487d34aafc05cd61c5e084d62f6285e000007953c423280000000000000a1923a1a0a35e00000000000001833ba00a6e1b4c01c5887e78876c11de8d0c214dc85c30313804c6622308122a36d3a4072258888231022e800ca2cd80001a2bbe0b7b2d4f80000000079047c8e838674000010cf723c9b05fec0b10000120e4fa0a200001820800002871c0000000000000314f0e2eb800000ab8a2c4e830788ce2000008e02c8e360a0901d10000161f3922bccc10000012dc598f080000000018551f8f4e8d4192457a1e280000a3c58000065430000180e6c0c3c8122801d581d6e01cf292a80000000018696e345608f28398c8c94ca2d80000000050e4a03b922c3d41763019ac08e0000162e2bab98e1ec4a062000000000c25d9904a000000000433808d03e03598470e34248cb8c354a054f21136057408f780000000000000604b180734802926d0a403b008a else 0x22896842e000070bc60000000016a95000000000351abc2682894400000000000003c328454900ecc000068dc08177603c6c228007a9e08d70838a0cc58c11606f50db3c215c0307626de0219ad8e98cb20cd99a03740352899d28f760438000040245a0c0336ef4570e43268362ec95c09e3b005b28f0c810fc1aeda701e0c2a8213007b88ba6c0a953573e11ee0ec4948ab221be1c030ac34268e195202d3e80020322014e342fae032c000018c50c1251a2bb4d4099e0d207b489ada0d3c9949e1ed70cdc810318e42234af85e3a102e8e47603b0000021300000083c848a43014700000a1d180000206b435260000603428a6080000e27db92384c8a2d464c37bb85faa0ca60b15e136b88976146f8520a15b8899101b478315c1f6b033a0000309c247c7304dfc34480000a0e8d081d60899072c000000000000078dff68fb50327111b78da7a912595452001da86d629dfd1bbe359706c600001847f60cfa0461815eb07e000000070c00897031361650000122d0509b4e11758bd20000105b78a3cb8ea800005895c41fc385de000020a7e8a9e1495400000000000001a0f9c99c888d5611010690a36900001212b0000000003800422994094fd1ef8000141d080000b50a62404c15210d4c60bde8c374032c8db0c2ba5076e218f20354000028d4240e98000000001c8f2000000001401108c28000060cbf200968b8422e88000120f4d8eb00020a8143026e8898ef1e480001e10a0351c0000000000271e8a2a439cc0929a09a78dac00005017bc15ca01de81591b51ac0edf8d19c01e3b521a3b1800000000000000000109126063714e76db330da80000000002383e0b68000028f4a00007a18c68e43a2adc2b400001077bc0109c54178a0cad7ed8aba817478af4827818a5b835ed8b73c23958d66025532b704312785d2481e40323a05f80af7c2d5086710b1018a07831048ee3e32c6894a225950469c31ff8c5d2376a15394093a85c8010e80000000002b3821be0059da164181e3041098e87c97b68a70619e088c561500c78a00004a256e38300000418070803cd5252c54000000000a21960125a24920769c2a980000501f480b9e0a708a944c11189bc225e8000000000012e000000000000038a8b409bb022e0000484164b1f00bbe605e0000000003812641f9802aaa095306460000002e222a950b3e000000000000000000018278aa9e03dc0356000038722e0d7202acc0588153a616f2052f2335c080ac79c68d9800001869de4134058ac1a06078943d500000030700000c8ea2aaec00004851360dd68c820000306234171000000000054662293006698125baa7ae130e8d0f42b25091b607280c0c4915188bec284a81008325f0c54000020850c04662bbe2276aa1f5c1d3b02a8000079e0f832d))))
def g63D8 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then 0x37e3b682985fd72d0530dfec5a0a61fe5c3414c2feb96ca885ff7259510dfee732221bf5ce644437fb94c8886fd7299110efceb32221df5d664443f7394c8885fd7299110fdae532221fe5c2644437fb98c8886fd7319110dfee432221bf5c864443df320c8885fd7219110bfced2a2217f5da54443de324a8885fd7295110bfce9b1a21bf993634437e326c6885fd72d8d10dfecb31a21bf59663443efb1cc6885fd7298d10bf8e8b1a21bf991634437e322c6885ff7258d10dfeca31a21bf59463443eeb18c6885fd7218d10bfeeca9a217f1d953443ee31aa6885ff7254d10bfcec21a217f5d843443de32086887df6310d10bfae421a21bfdd7624437ebaec4886fe74d8910df8e9b1221bf953624437fb9ec4886fe73d8910dfae7b1221bf1cf624437f29ec4886fd53d8910dfe87b1221bf10f624437fb2ec4886fd65d8910bfce9b1221bf993624437e326c4886ff63d8910dfcc7b1221bf58f624437e31ec4886ff7558910dfaeab1221bf9d1624437e3a2c4886fe5458910dfee6b1221bf9cd624437eb9ac4886fc7358910dfca6b1221bf54d624437fa1ac4886fc4358910efeeab1221df1d5624437fb2ac4886fd6558910f7ee8b12217f1d162443de3a2c4886fe6458910df8c8b1221f7dcd62443ee39ac4886ff6358910dfcc6b1221bf58d624437e31ac4887ef6258910ff6e0b12217fdd952442fe3b2a4885ff76d0910dfeeda12217f9db424437f3b684885fd76d0910dfaeda12217f1db424437e3b684885fe76cc910bfaed99221fbd8b32442ffbb264885fc764c910bf8e899221bf991324437e32264886df7358254db8e6b04a93fdc5609527eb8ec0a9efb7158043df2e2b00873fdc56010e7eb96c2a85be74d8f40b7ce9b0e817b5cb61d02fcb86c3a04ff72587409fee4b0e613fdd951cc37ab0aa3985fb7054730d7ee232261af5c4644c27eb88c8984fe74d85309fae5b0a613f9db414c27e3b682986bc64d0530deec3a0a617e5c3414c2f7b92ca885fb7059510cfceb322219f5d66444377394c8884fd7299110ddae532221be5c264442bebacc8885ed7299110bf2e1322213f5c8644435f320c8884fe76951109faed2a221af192544436fb1cc6885f97098d10afeeab1a216f1d163442f7b92c6885fb7058d10dbac631a213fdd9534427e3b2a6885bc7454d109fcec21a213f5d843442beba886886bc6410d10bdae421a217e5c0434427f3a6c48867f7558910cf8eab1221afdd1624427e3a2c4886bc7458910dbee6b1221b71cd62442bfbaac4885bc7458910bbee6b1221771cd6244377b12c4885fb70589109feeca92213f1d9524427fbb684884fe76d09109faeda12213f1db424427f3b664884fd76cc910ddec5992213fdd9324427e3b264885bc744c910d72e0322613b5ca644425e3a2c4884fb7058910 else (if j<2 then 0x3934b24be46048588fef1eca3a1c6cd8ccb17f62bcc4f588e30f621adc2e584fb088e0cfc122814b00a1fd5bf197d54f941ee63d6b79f8f251e0f3bb676aaebedd50ba1d7378e551c79b892700ede7db94b6ba6c96d71da9e34a3684cce3598bb29a642cc5f586eb0605fb8bcd5766ae7a5c4eb7516af2cef590eb0b55d82b33556ca8c94de2985528ea34542da8164f4e9ddd37d26844c9a98592d3a52a496890f91f923bb46b48bad14c224543ac859d08320a540887f8cfbd9f1a3d8e7998efb9d6c39de7190e0f9bd336f26c7cd5f1a64340666a4cae991f31d06270c1a17d32ef25c7cb62966b2c2256dcaa414e028e250409d0933225944a4c92011f4236c45fc88b90d9212841748130fda1f003cd07628e6b1c0636dc6b20d1819b4325461d8bef172a2cb45660a6b142226f84b209111152210440187c50f001c9837b06b80ce6190c30d05ea0b6615b829804d608dc106c1d6034b05d40a2411781e30304044c05c808200a400a40007ff73d8740ffae7b0e81ffd8f61d03feb1ec3a07ff72d8740ffae5b0e81ffd8b61d03ffb9ac3a07fd7358740ffec6b0e81ff58d61d03ffb92c3a07fd7258740ffec4b0e81ff58961d03ffb9682987fd72d0530ffee732221ff5ce64443ffb94c8887fd7299110ffee632221ff5cc64443ffb90c8887fd7219110ffcc9b1a21ff19363443ffb2cc6887fd6598d10ffcc8b1a21ff19163443ffb28c6887fd6518d10ffeebb1221ff5d762443ffb2ec4887fd65d8910ffce9b1221ff1d362443ff326c4887fc64d8910ffca9b1221ffdcf62443ff39ec4887fd73d8910ff8e7b1221ffd8f62443ff31ec4887fd63d8910ff8c7b1221ff94f62443fea9ec4887ff43d8910ff887b1221ffdd562443febaac4887ff6558910ffacab1221ff9d162443fe3a2c4887fe6458910ff8c8b1221ff95162443ffb9ac4887fe7358910ffae6b1221ff1cd62443ffb1ac4887fe6358910ffac6b1221ff18d62443ff29ac4887fd5358910ffe86b1221ff10d62443ff31aa4887fc6354910ffeeda1221ff9db42443febb684887fc76d0910ffee7a1221ff5cf42443ffb1e84887fd63d0910ffecb99221ff59732443ff32264887fc644c910dfee2b04a9bf5c560953ee90662a9eff71d8153dfae3b02a7bfdc56010f7eb8ac021efe73d8550df8e7b0aa1bfdcb615437eb96c2a85fd71d8f40bfee2b1e81df9d761d03bebaec3a07be74d8740dfec7b0e81bf58f61d03f7396c3a05fd72d8740fdae5b0e81bfd8b61d03fcb86c3a06ff7358740dfae6b0e81bfdc961d037eb92c3a06ff6358740dfac6b0e817fdc961d037fb12c3a06fd6258740feec2b0e81bfdd561cc37ebaac3986ff7258730dfae4b0e617fdc951cc37eb12a3986ff7119130dfae232261bf9d3614c37e3a6c2986ff72d8530dfae5b0a61bf9db414c else 0xc3c2819204160d96a73c7490f0c06482d952f469cd9b2c28681920416cbd1a7366cb0d020647ac1b2f409cc1b2c340019213b60d97a04e60e902c2058003e408ce1b2f408ce902c2078003a3d60d942f409cc1d205840d0007c7ac1b285e813983a5840d0354080e5b2c5e9539d3a40b0c1207a8111eb06cbd2a73a648161a000fd11eb16ca17a64e78e921a040eb05aa33c58780f60b06a9cf12103c08002dc08ae58334e78b0d02ab9668139e2c3408af5ba33c58680e22bd60c17a046788161034001d5eb74660f161a0457add39e2434080026b9669cf161a03d7add19e2c3407af5ba73c4840d02000a115eb060bd0233c58680030b966bd39b3c5848002ac08ae582d409cc1e205840d0007d8115c2d409cc1e2c340019604172d56a04e74d1e2c24001c60bd62bd39d3c5878145ca85e9cf12103c08002cc082c1aab4e78b0f028c08abd39e2c2c083022bd5e8cf161e0498115eaf4e789081e04001860bb62bd39b3c58781460b550b50273078b0f0006182d542d409cc1e205840f00071810583558b52273c78b0b036b062bd02730788161034001a22b062bd0273078b0d0006160c542b4e78f161a100b105aaf449ce9a3c58480032b462a17a64678b0d0805c8ad18a85e9939e3c4090d0807086ed8305e8129e205840b0007360cd0253c587810e0406694f161e04370ed8374a78b0b0244376c182f4094f1616000ce94f1616000670202f4a78b0f0204370ed7a53c58781259a53c58780dd29e2c2c0531d29e2c3c062e57a53c58780f57a54c58785060009e94f12103c080022c082c16a04a60f161e000cb020b05a812983c40b081e000e115eb060bd0253c58681622bd60c17a04a60f102c2068003c457ac182f4094c1e2c34001a22bd60c17a04a7881610340d2e18af4094c1e205840f0006882e18af4094c1e2c3c001822bd5e9509e2c3c281462b86aa17a04a60f161e000d315c3550bd0253078816103c001e60426ab17a64a70f161606164bd39f242407af5ba62c3406e94f161602f4a7890f017bde7777ee3bdb47b4d7671ec4bd767ad1756bea3fd3bfa5ff488e8b1d0179e0737be67bcc1b96ef2b4e4c3c8ff90b71d1e327c58f88f70bde0f1c0eb801efdadf47bdb37a1ef1addf1bb3f7536e68dc7fb7eb6e1eda1dad5b5076856cd3d90fb0ef5fb6ba3d6d9acf3582eac0d52fa9bb514e9f2d34da5bf49c6908d195a24f42767fbcf899dab38be6bdccab987b2ece5b0cb1d95cf2ac6528c9c7927b229640dc7918e2b1a9e2ebc4f9881b0d66152c1d58227010dfb9beb17bdef39ddefbb477596e93dca3b84d6fbedb95b34b56f6992cf3d971b205626ac07d761adc95982ae0555fa9ef525aa1753cda6af4b6a935d1fca31b44b286950719fe93e167764e619be535f26834c9e98432f025a8cb0c95ab2a7a510c9e)) else (if j<5 then (if j<4 then 0x6083810d9a85e8d2993c48b0a1e0c0f7021bb66a17a34a78916143c181ee04366a15a04a64f14245860a1e101824e04360cd42b4094c9e2848b0c143c20304dc086e1db066a17a44694c9e2848b0c142c002ad83350bd2234a64f14245860a1600117061b06aad5a14094c983c509161828785060ab830daab56852993c50b0c1e14182061bb62c57a14a64c1e205840b020011b0e1bb62d55af4a8d2993c50b0c160412b0e1bb62d55af4a8d2993078a161828581000ab81159b352a17a54694c983c509161828785060b37acd9a85e951a53278a16183c283045c08acd9a95e951a53278a16183c283049c1810deb366a17a54694c983c509161828785060bb86c19ab4094c9e245850f0607386c19ab4094f161e0c0b70ddb35e8d29e2c2c0016e1bb66bd1a53c5858002dc086c1a2b56812993c48b0a1600107021b350bd1a53278916143c181ee04370ed9a85e8d29e2c3c181ce04366a17a34a78b0f06063810dc3b66a17a34a64f122c28783045c086c19a856812993c48b0a1e101822e04360cd42b4094c9e245850f080c117021b876c19a8588d2993c48b0a16001210d83350bd2234a64f122c28580040b34294f161e03b83059a53c587810e0c36aad5a14a64f122c2878506083830d83556ad0a04a64c1e2c341820dcbb62dd29e2c2c0930ddb162bd0a53260f161604001fd29e2c2c080d61c176c5aab5a8d2993078b0b020011b0e0bb62d55ad4694c9e2c28581040c15e94f161e03982fd29e2c3c077022b362b51a532789161434181ee0c086f59b350b51a53260f161a0c117022b366a542d4694c983c58683040c37acd9a85a8d2993c48b0a1a0c10abd2a13c5878506040ae94f121e0c080f60c160c56a14a64f161e040db060b062b50a53278816103c081e62bd62c57a14a78b0d02d457ac192f4494f161a0598af58b15e852993c40b081a040f515eb064bd12530789161434001e62bd62c57a14a64f161a040d515eb064bd1253078b0d000698af58b15e8529e205840d035457ac192f4494f122c28681a5cb150bd0a53278816103c081c60b962a17a14a64f161e040d315eaf4a84c1e2c3c281660416aa57a14a64f161e040d3020b552bd0a53278816103c081e60ba62d562f4c8529c3278816102c10104ec082e98b550b51253078a16182c0823604174c5aa85a892983c50b0c142c10104d4278c17273e547012a04278cd7273e547015a04670b9398365440e000648111b2e4e60d95103c0019993450bd1a7366ca891c080d5199345e8d39b36547020333068a17a04e60d951038001ba04460b919d205840f0006180e9aaf4e7cb0a0005274dd39d2c2800119f374674b0e01f3e60c57a73a48700028467cc182f408ce902c2070003a3868a17a04674816103c001a592d409cc1d205840f0006564a16a04e74c902 else 0x8519930748902c20700046c38cd193556bd2a34664e912c3070404ac38cd193556bd2a34664c1d2240b0c1438202059c67cdd1a73664b0e0808001ad83450ad0273674896143c181ca1b068ad0273674b0a1e0c0d8eda285e8d1983a44b0a1e0c0e511db45e8d1983a5850f060696ca16a44668c9d2844b081e180821583250b50233464e902c3050f0a0811911eb16ca97a34e6cd902c28681f20447ac5b2f469cd9b205868103e4084edb2f469cd9d225850b0007c84ed92f469cd9d2c285800364364bd1a33074b0a1e0c0c9021b7468cc1d225850f0606a8111eb06ca97a24e68e902c286800454088f583654bd1273474b0a1a07e8111eb462d942f4c8519a3a508961034201055447ac1b2c5e951233464e902c3050d0009e88f58b654bd3273c749081a040fb060b15a850233260f102c20781042c182c56a1408cc983c40b081e04107020bd62cd42f469cd9e2c340e7020bd62cd42f469cd9e245850d0208b8ae5eb166bd1a33078b0d035c57ac59af468cc1e245850d0207b8315cb34e78b0d026bb429cf161a03d7add19e2c3407315eb162bd0a33260f102c206810008d7add1993c5868115eb74e7890d020438105eb166a17a34e6cf122c286820e0417ac59a85e8d39b3c5868103dc57ac59af468cc1e245850d039c57ac59af468cc1e2c34081a5cb35e9cd9e2c2409315eb162bd0a33260f161a04001f60c572c18ad429cc9e205840d020858315cb062b50a73278b0d020758305cb55a8539d3678b090007589060b652b52233464f102c206840209182ed8b552a17a14e64f102c20581000958105c3b62c56a34e74d9e285860b020958105db16aa542d469ce9b3c50b0c142c080054c082d54a85e851993078816103c082221b550ad0a73a6cf122c287850608186c1aa856850253678b0d060718105eb150bd39d3c58781960c082e58a85e851993078816103c0824604176c5aa950bd0a73278b0b020011b020bb62d54a85a8d29b3c585810008d82e1db16aa56a34e74d9e2c28581044c082d54a85e851993078816103c082261b06aa15a1409ce9b3c509161828785060a086d542b429ce9b3c50b0c1a0c0f3020bb62a17a73678b0f032c18105cb150bd0a33260f102c20781048c160d54ad429cc9e2c3c081a60b06aa56a14e64f102c2078103cc08ac56a14e74d9e2c28783038c082d16a4428cd193c40b081c0410ac58a85e853993c40b081a040e3158b150bd0a73278b0d0206982d57a34e74d9e2c24001862b150bd39d3c5850d0206568c58a85e990a33464f102c206840209386c19ab4094f122c28783035c360cd5a04a64f122c28783039c376cd7a34a78916142c001ae1bb66bd1a53c48b0a16000d7021bb60d15ab4094c9e2848b0c142c0026e04366a17a34a78916143c181ce04376cd42f4694c9e245850f) else (if j<6 then 0x8961c06384f19ad4a7490e0405274cd1993a5807664e912c02c64d51a332748961c0538309da95a44b0a1c05184e56921c0807709dad2258700ee0c276a569124381014cc9d2258100ccc9d2438100c99a33a44b0e01d993a44b0e01b4282cd199385850d0805e850cd193858684025c182e58ab46786812e0c176a570d0204172cd1993c3407664f0d0202982e570d015c182e59a9568cf0d0205b32786808cc9e1a0405b060bd52ad19e1604d8305ea95c2c081061b55685308c61b16aa55a1467849b060b96aa56a34a6cf0b0206d82e5aad4a78581024c362d54ab42984830daa9568cf08e59a14a78456c59a14a64f08ed8b34294c9e11db34a64f08b4c9e160405a78581011a53278580b4c9e1604056c5a9c3278581020c15a78580ae0c352b4c9a2c28497061a95a64f08e60ad3c223830d4ad32784770d6993c22b86ad2993c2c077061a95a64f08ee0c366a55a53864f094e0c362c569c32785814e0c372f4e193c2c096a55a53864d16142c0816d8b34294c9e11cb34294f0b018c3668529e1a03986c59a14a64f0d025a53c2c080b4c9e1604052e5aa34a64f0b0204972d529e160407305db16294e1e16040a7061a95a64f08e60b95694f0b01cc15694f0b019c182ed4ad32784870d4ad4a78680ee0c352b52993c34097061a95a8d2993c341816e0c35a94f0d01dc186c59a9568529c3c340c7061b162a529c3c341816e0c372e58ad4a70f0b0206182cd4ad4694e19345850b0207181158b252b8473022b164a54a13c24972cd30d0169e2c3404c5868074f0d00d4182e570d0194182e94a93c340812a0c174a56993c34095060b964ad09e1a040a4c5aa956890a53c24a62d54ab4494c9e126c18684f0b040408b0609e1608080fa14678cd727366c8151238101da14674f19ae449cd9b205470203f3268a1724448cc9d28449891a0c1091192e449cd9b20547830324088d939b3640a891e0c0ccc9a285e8d39b3640a891c080e5199345e8d39b3640a8e0406a81119a85c9cd9d225850f0607281119a85c8939b3a5850f0607685119ae448cc1d2c287830374288cd7233074896143c181a623e60d54a85e85399364481610380024623e60d54a85e85399364481610380024e0c674c19a73a5870159d33429ce961c04274dd39d2c280010e0427cd193352a16a34a6ce9120587024e13e68c99a95a8d29b3a44b0a1c0811cf9ba33a58700e633e60c57a14664c1d2240b081c0011cf9ba33274b0e022c38cd193556b51a33260e91205870239f3266bd39d243810002dc084f993350bd1a7367489614381022e0427cc99a85e8d39b3a5850e040838cf99335e8d1983a44b0a1c080f719f3266bd1a33074b0a1c080e709f3464cd4af4a8d39d367489618382026e0427cd193352a17a5469ce9b3a448161828704040c18cf98315e else 0x309d31568ce96021c184ed4ad22487012e0c278cd4ad4a74)))
def g63H8 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then 0xdc0000a05f8434a0000343458453843175044c000026a48d4afa0995c4ed4130102f7e0b7ac1d13075d82f140a1245ca00001014ab02e8000060e155490010e3c1a9c04b5458aa1624409c604240000a0ba8cdcac0f234088403c7125a0413d8de20000303250000142962060103def124680a886833832f449f1508710d880000852bb428f1098d00301112c11e961031504cf367484ba9069a41d9c01bd416a20c00549166a3ec391a100905aa6617a804b10753843448e466831d1250030d50611d235004adc23780b76831ae068f018630bac0991b0768029790a1b84d321745c30b001ec80493200ec3da412a903e67093b421080da285b5000434145613e6058806a41c02d412429a12301f445a601318c12071324108fd13c5425170988807e408c3cd1a90a990468f124dc4ff112349438aa89bc3967146bd428017084983e14bec046707ee809f000df425640c54809d72182cd4410a5141b5a12c59049400cb44a4d14d8034c942278229b11a8041ce536a43c344001400f517a592497016a057c602ca4035b02f70cf5c15e304a8840c5806370038829b20ac083709101b8571f09e04096e0b19c150652a84218a49b501d661142c3330687b0d4060102d00d0402c002400817c98194223948008c040154b2e43b048a1414317804103000118842040000c0d4d806010030d02d05c740105c0d901094860707041813879a70b86b0083c39c482cc356d02302d4c00c0f048a05481615c29120001981702c2e094600302f01c2700c1458422000027bc0203c020e8b70d02d0d02d0d061390050344a0308d1b403058474741117800000050104602865118001f0171dc0d01c000e44113c570b8030600202800000ae0e800034306c05e030300041909c191680649c2d0045b0000119011028161b424244010680121c0d03c04028100140018000000000006d034161400012c150ac0200831058030480600c46000011d8020700b048060c40003c261b400004120140402413018940b40a08c090ac000001b0200f10490008ca0440701009018980001506832004000d4eb0a83601c00018451380303c592bc060187200c0000c0806c000002f0504f1f0100644a0083701011000030340b0103a0e81c01c0b0f0010d8282a8000940704cbb0004e1001506c050d80900434000000240e1100106803010070101500000014001bc010bc5f1b8001901b13c020183302845078170080505034058280640005c2e01018000020fc000d00309c1900875040031540f0240b06829000000240601c00018200340006c01054120d807004020000001c0a1540d05801014000680313805020010040003c7d0cc390000401c01004030542d0f402014091800003c7307c04020160000812c1c0000203c60048030302c028180000c01c0a000030003e else 0x3fd006644841112b00b330b8a40fc00b674020c40e750306023440af10e3a840930f5b0d78c131d427cd07d584987058884375162d51f716090c470a106f05ccf02164082d0e56c59070553c22bf11e283ac36821400850ca384a1516fe403f10cac050d14d2a50e6907d3c1e641601c5c4f51a081d5104de05d216fe9439b533d8448c44d16d155d096b03fdf0809c56c704bb4158f14d6434d5344a4112d08a0182680a494d3796215c2887089e5860b1358028a70c090474f08f745e1608f281f31013ec2af60283005eb0096822a60f4e05ace01d542e98115604c3715cd42cd0351941927128243c6b0762835440f408172404090028d0d46c0a9a09318204606cb41a0d0dea02bc6a12a45c0a0227055d6033ac26dc1750c1d2e16f5c14d80a60d48c8047284052043582902048a9455d073b5939e09a88266612d28241f0b6941cb151e1c3ec90a354331e154ecd5001547019630893448100002030e444ec0000d13c2020cb1055855b0827c03e2000020156835800177b0db383f7b0fc2421d304f842b16139342fdc416c81c99455241b7916d1455ff15690281921854024c054f418ef063043aab12ce843f442b983d53070440279166984f6f1791c4753414543a304999c417a2a7b013c34993c0c3810ab406c94536846fa1209d12620f0285e06350113bf604a6100760b60842f0088081bc70141c059d149f03cdc0b8642a5e1759823f407e9c2b8e0b4d41eb61149503dc153bc0fb213d1c48a013a64270a0e5e81a5a0bb68054f0362112911718418de0cc8c39f1131685010496d00d27073d4db31024183e1510e9816320e9644a7c06fec239242294166e019c83e810f6d83e0204119a93e04e40004201f0139a30bbac4ea7146140c2b071dc58e8057240e421423c0bc40f45cce460979c1e140c5394d9214fe826f01389d2272354e83ad9077543d47043f45e850a00436b712db44fce13bf457730b2c43b070ea6587ca161c50557161444af00002145240a66c356b4778c548411d80304304280136f032f039804b2bc183c0c188095213f7407a7095c0000226d5da9f4133ac02e8109ec1180137f40e8414564001e07e4c01650728c981f1136c318716bc434bd0378c54cc0dbf13ae40e8612682017c854610aedc2b40674a0d961173a915670d19d9173117b9442c0e68822de177c52713524a029c900cc1056000038274149a682a3f04c905b2b44b4c3f41086f04d0e094f8327f12b18394000024276d143340c8d0053c03c10b2bc4a3f351e42f300001cbf680df8436ad10b7004e90351814ef1307c52610ce3446d80b1c42345034dc05dd0e028423512640000612b940c1209b142a020a84e094f0d21809ae07f74076d01980000f067c8100c17640000c07920361f1109420b1153740f7560a1c3f290369c5ecc07) else (if j<3 then 0x8c6c0a4a2a6e44f8f01e683abf15a14123b452145b1c4549016b00000000011132c16790370027250c8103e5e0783033a10137433e0000293b53009902e5b14010565816e105525495383c4a000e8a94909a00000c0d924447b6a780000f48989a0a0000000c780531024d2497cc01e611f744964508683c241512812c90e0c9260400750206b4037456d9004482fcb0cde846000001056700003443e80d018431952c6c3b500c73d408105c00000210c8000020cc201ad74c83405b62609046290ee4c49be11b000004014740f494cedc1f11179c85b00000045a4d106651436078d4355f057e8454c535983b16168201f8c0eca40cc502b9c248812698072b0f1d83ba41771853af52b402f0e010c40e5700bc8566744f3014820479c4c890547815725482028b80c14407f30addc143c488d418fa05d8c3923026d42ab70bb3c5c9f0b4ac5e300000c08af092a02be8400b8592a45328a9ae0fe7c060915ca40074099000004144c1a1150d824885511c984207087e04447810f44d200000c40fa6083402170f60020a80e7bc03aa0c33838aa0e640000e10f5427a000018160015ace160b17ac00000000284cf410a402c98147d053bd07f1010871037c56e80cb182f400a771120215880000b454684ee0161b05daa3784450500001d25800003031eb15248435b0689c17c0000103cb10d3a8077e0ff08047502dc0000601b905baa6186c45dd07238d451096c000040f7e8dd2e49ec835ed03e144cc30f1580d1410f2420800001417a10dfdc410750680000c0c0740d0b0d0c847c90cf212f25499f45b31509e44bbc00e4853e000014141215530285d115ddc1170c4bc2447052d0352b6421c17140102822f00003c3d7c0be7c149a03fa0a8e00002c0e15090ac1bb717160036710ac00c4c0a4c848ed0737c11b202aec0f6441484056e01174041d16960246a04a38133c03bd8528a13284277a3504805cf1562c576c0e9f01f0c14494403714c34421f14840217100abc0650000043e9b02b00000c0f9ec181616570366c08044165516534282f0b728d76e1555c58340070000000000000000003c27e74506851b209c7808e903c88269d0e1a514bc03c1c3fba008cc4a9000018503793be40e90000250577108bc31020155458480b47429f4074c83dc00003d03aa0d1e43bee454e54d770bee10f30000100a3909cdc01791336c06b368341133a121d148e615679136351d04492a0049852ef11f80353340ac85e58416203110218800006013044b2c136c445f70e2c433fb07fa04b5049de801b7102c012552a4604a670aa05a0f005d204bf9038e05a700cb449b80147641b4802f8c0c904136c5643166ec1c5606504121a06791803e14798087c07024155f0b33c09ed35d4408f842d102a43104f055c644b8dc15403cdc1d030d260d else (if j<4 then 0x15d20d12c5254076d896fb0efc456140c67c5ddf15a7851cb6a5004c2d0f24813571633c24f20fb94502e07fe43076095181313083982c3510a104433403f5278d163ec0f970f2a109fc04c2c3b890aa64115e03ab8350911a70029d077cc17f70b9842a280f8dc509fa8d5857aa038245744164c437d806b384452062f846b22600110554989403e052fcc4f7a0f04c4e15145ac2ffe1635c4d750e2443888529c683ac00f6d448b6a6a04b9b35ce832a003d452be7066bc1c6311e702b990c20d44330980453c314e102fe5036c041d00003c17d509f743fa549764002049bb0575510690d74b084801b1c11580000c02940000549871123013a0c5d5c05e31256e06e903bb00ab305ea3020400001091c0015212f0c3f66a0ae844fc041643b6a2fdc899590e0480e7000000000000000000f07b400009050b04f2a033e545a10df245a3f0625d113e08f8000000000000010e414596a02da8083b056a04776128ac1b3f132fc4de00001c44ef00c58267d4954c1aa003744a8d70c76c1f69160602f2410020080a217e010ea047e84e7e08d443a0204e1124fc003400bf103b3836390cd8820061272c2c2801d3409810a7a84530070b81a800002c2f5f13fb923c70bbfc0aa0000184be00003839c70dce400bb0193441800564c36de088994a1526de8524005a5047324054000096a3943a6544190185a145f4359235b15822713758107d084400000018644d95014a819cb1004416fb116801b690ef3031f5080c44d570d5d43b4d0b83d4acb0690000080b6c000000003409100002c4bd9064c037400001825216430d26be0014050be02c3030ff1644c4fa66a4400cdf04590439411b9c324205d4c39df00e064d6000000000813440000f2175049fc2a64000020219c4f36083e812a708db93d8406fa019d115a88009b05b941b9311eec2aaf44740000f089b45cbd438b020560fcdc3dd6066e82d56416805d7f0c9bc28c00fe2c10100003c215b0ea3c3ed70e12814770beadc617024e5125d01cd00bb61464086600000c41600001443b00000000000003125c20779c58220b200000000000000c0edf0365c090d600000003404850e35042e208ea85de10365457bd173485be00003c4b03037d04070000083efa054a43bd9016082ba1618bc9a4321ac85ae937a240b4b06094a8fc088e054770fd60433e109800000000012590000085c8461ac0000e10480000f119f0459e08e102e4d044000009127b0000e153c0000a0b0544b820444c53de1124440a00000c50731202c295e06c0c36e6081c487c411234232410c25324d150ec4eba015f035d00002d0536119545b634e44c3a4e0d08016400dc680e6703180000b136881efc155a0219a12ddc250615155c63134d80000f02d6d2f9f0d6a45a970f93002220450408cf0492047f40 else 0x142c096429420d315fd0341701c7c0a7f06b9825d80662c511210514464a1106448900d7c43d2a3546c3798035a800a20b5c426e940a845db012b6c144115400542e1380d81fa0e4d813fc09fe432120e33030ac08cf5094c14b5859770b5bc2b5f1276c2bdb0f67c0a1e1010033be1044403b60b8e4287c0ecdc52970128c466c48c741ab713b24216410b3c3cf40be283ff8073303ea40c4e057e60917d434f16ec81e2c07b0459da068684e54138c0000d02480000104f6817340de243eb35235826140ebf4126616850372509d6814f215bf806ae0957854110a68000000108d3d2f0e09c36780267c0a6500b28485114cd4103201b6409430b3f8283749c10579008514a9f70924c0b91524f4de76152bc0ed86ff10a93d43604534a0b395059203fc000000001059e615f6c3cc71666d112d42f0d13040e3d44e6d1799c01f0000040c08178a91ccb617d822e413100335c02e30334b44bf0309b1220033d849bf00ca0079c9a8d40e8b126a0000241af9447102bf841538495a123f411dd07a1125e3111bc5d000000c1881118485abc057a049760068c0ee7155e024b10ba1852b7065704ab10354057031670c37bd0ab9c44081580c5a860111c52cd0da481ea7367011655495d05bc50cb9c197b0ca4185dd432fc28e1004f03f1807a4000060712034fda0f418669064400005066602b2409ad01b8c04bc8240e05860279d6a64a00d5414000000000385d3e038a013b00002d08814f3d40a2911c40000a0f3b0408000000000000008563d0ffb94abe0c58410600002832230b528377000028187c4128c5add09719043e056c835cb0d6e8540f02b484d40107f1253d03e9c436301a6421330894000041440000020ebb9160535dc0a92c5486c4a5302c6904e46759047a54a8b029100001c31bd1361c034305e4018a0077211c470643c209304300000049b2016c252c100c5504670140749da29ccc37048358000028537314800000a14280000d116285c7414e6052a00033c1bd204d3c5b90070f0d42a338242d01096480785103b010b513d4c55e614c9c3759107b44fbe122e05988022e4424e07940000993c643230000000005121ac45c0000003878168800008173f8084c014c000000000c5b7849978ddfd0ad9085ef152c0000a0dd8807020c0d400680a9c021a70ab7045bb07c800008137000007018ae4ee6088500ebf09eec168f498dc2e7f82d004510000011f1a0acf046300000417bb046a82895069ec018f148f49b600ce7c21cf170fc2c400003852200003c514c4103148f605b70127b1095c2df4035dc504436ca85060000085d800000450e103f782f6b6a6c0000e120e050f3170581173097ec146908b2802be04e8806880961859fe2a43423b014c4c097a07ba82c5808784)))
def g63D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6081e61951745334f24a180f6081e61951745334f24a10600116279865745334d20a180d6279865745334d20a106000f586945504ce34d20a1070810428207586945d245338d34828414004d85865541334e20a107040e616195504cd38a1c103185d65745334e285000c617595d14cd38a105000d6085d61a55541338d38828414004982175951745334e20a10704106085d6545d14cd38a1c103982175951745334e287040e6085d6545d14cd3882841c104182161951541338d3882841c20412608586545504ce34e20a10708104982171d6195174914ce34e20a1050014216195174914ce34e20a10500116165745130e20a107040d6165745130e287040b6085869555044c3882841c20411a185d61a55749144c3882841400497996545d245130e20a1070810458217996545d245130e20a10708104e82271859330f209106000e985904cd3482c51c103081a5904cc3c82441c00366185d04cc3c82441800368206164cc3482841c003489e6185d04cc34a106000e1c61741330d20a107000d2075869741330f20a105000f2271a5d04cc3482841c003885d6185d04cc38a140c2175861741330e2841400388185d044e20a107000c2061741138a1c002881a5933cb1408185533cb1807985d33c91807225d33ca1407e70e04db0d50ceac72c18bcab7cb28ab6a509f699c9368c48527d47687146cc6605ee58250a4b046240e3ba36630c2b82581fe1b01561080c6090060030000ffd8f40ff58f40ffd8740ff58740ff54730ffd0530ffd9510ff59510ff99110ff19110ff95110ffd8d10ff98d10ff58d10ff18d10ff94d10ff54d10ffd0d10ff10d10ffd8910ff58910ff54910ffd0910ffcc910ff4c910bf58254f7cc553bfd8153bf58043bfd8550bf58740bf58730bf19130bfd8530bf99110bf19110bfd8910bf58910af191539f59443be58043af19130
def g63H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x1320f6122420ea80c7a0050000a10520ee4400e128a34f7136a0e5f07d669f40be90743031f448b14c9026f61fb0bcf09354360000b12020fe112910776253134b40f01114d10be0b7b135d050d0efd0ad000000000000f13950a80000a10300001149e102f00200002256506c806922d9c03a004ed46bd0f1309940370000112710fbb144d22fe0582083e0cd20a940e2d008e60b50d1009f812c902c409ca0181112e02b02e1f0480000a14e50d7913bf66320f9a1085148000002ee10d3110df141000050ebc07300000003c02f000b13556011f21e70b8c08d014df8d0d012e2f9f4332017a01d7029c8daf025813780b9314009483117e11aa2d8904300f80001e10f7071000080a73070603500000000f0fde12f341030d2402a110cb428f066c02840f3f03c8131905c20bdd0f7308c44c2e1246086607e0000303d0221b0c152cf703e000080c0c13a0000f34e304c72f40000f024e2e3702d00000000e0340000000070ddf052c0960000804b301c212e3065b0c6b0300000d0230000142cf0ff20a0625230c350551119a14300009075e0e8f24076a4006a31333155000080ca4088c05fd01e71040000902090409157c00d16b80087801f0000805ac43cb11bd667e0b670cb801500008158908f9949b0ba0000a0bbe0a6b130e085000c0000000090560000f064c0f4804a0000207b0000800910c9f0140000f1510000000040e780a410d510722154000021158082a7075150903f7116604df07c565aa01b30548608000060db212a50070611b05951107142000060b1d604b047511e343e50b2400610b5512540193063f0929041b12b7246607f100f7013a004a25444ced0b01624309b210a5245f0d660da000090d080afc0a30000405e609590d4714660c400001078b06180391606312200006000b068505150aa90ed9098e0217022900a0000908ef1210000109000006147a036006ed13f704410b3710110ab0000b0e9811ca03bf067d0790000a0e10000704290a58057b0f2d032008a909dd11d308be0f522fba0cf80380000614f90ec42f392e450e4907aa00e301a70600145b14b306ff0e66094e15660dc80a1d091711882fff06bb2fc960f2046315232223076e10e7049e153013e0045000090800000210951060000c2efd3564081e123d0c840ce2132413ca097403322fad0d9306df706a100f13d90b4511170e0b0fa72474027e226524170c5065b000060df3089b0ae525551267062f21130de11070000205df11f01908740a060144823328602241000001c16608144189028246f050200c0201042d42a0000004022d0310c0200008bcde01054541e0d0180c0a0000008020c2285c1805020143200010601a0611828004a008500000008380615000340a0009a185608000040017030fc1601040200a050001c060a else 0x50fc90e350a2401032feb0cc00bfe0d8f0ac3138814a712dd41e902ef04fa053f134f09a80c2909ea2d7d05bf6218016f084e1)
def g63D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8398a498e428840620c524c72144300188314931c8510c00620e62d0931c851080d3168498e4288405a0c524c72106002d073168498e42080c398b424c721060031073168498e420c006a0c5a1263106002e4d82dc960945420c62103d003fca9fe53fea9ffd0ff887fd50ffa07fcc3fa61fd10
def g63H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x170e000223a496a2990ca856c38464c0a4b6400068d000002a949c17202735c418e1b0006006520066a329023434000611234543ba1ec2d709184bed2926197d902f25b52b0480014d8000191d805603d10500103f206913a4051be124610c96480e00b469e026c1aa2326a6844c95c16b080441c50c26a0c0000000848f09e95e8b070d407519c001405000103f5b401b17025098900024857818b071e50002
def g63D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4321017f
def g63H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1642908000009080180071181800730f0200000000888a8dc4d845000011100750b60961824582100e02
def g63L : Nat → Packing
  | 4 => (1,7,4,0,0,0,0,g63D4)
  | 5 => (597,6,4,0,0,12,0,g63D5)
  | 6 => (1990,5,4,0,0,16,0,g63D6)
  | 7 => (1517,4,4,0,0,17,0,g63D7)
  | 8 => (345,3,4,0,0,15,0,g63D8)
  | 9 => (42,2,4,0,0,12,0,g63D9)
  | 10 => (10,1,4,0,0,10,0,g63D10)
  | 11 => (1,0,4,0,0,0,0,g63D11)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g63H5
  | 6 => lookupWord 251 1487 7 17 10 3 g63H6
  | 7 => lookupWord 699 3821 7 18 11 3 g63H7
  | 8 => lookupWord 464 2011 10 18 11 3 g63H8
  | 9 => lookupWord 104 479 9 16 9 3 g63H9
  | 10 => lookupWord 19 89 7 13 6 3 g63H10
  | 11 => lookupWord 5 29 5 11 4 3 g63H11
  | _ => fun _ => none
def g63 : Forest := ⟨63,11,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P4_0 : block g63 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B4 : block g63 4 0 1=true := g63P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_96 : block g63 5 96 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_192 : block g63 5 192 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_288 : block g63 5 288 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_384 : block g63 5 384 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_480 : block g63 5 480 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_576 : block g63 5 576 21=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 597=true := (@block_merge g63 5 0 288 309 (@block_merge g63 5 0 96 192 g63P5_0 (@block_merge g63 5 96 96 96 g63P5_96 g63P5_192)) (@block_merge g63 5 288 192 117 (@block_merge g63 5 288 96 96 g63P5_288 g63P5_384) (@block_merge g63 5 480 96 21 g63P5_480 g63P5_576)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_96 : block g63 6 96 85=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_181 : block g63 6 181 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_277 : block g63 6 277 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_373 : block g63 6 373 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_469 : block g63 6 469 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_565 : block g63 6 565 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_661 : block g63 6 661 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_757 : block g63 6 757 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_853 : block g63 6 853 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_949 : block g63 6 949 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1045 : block g63 6 1045 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1141 : block g63 6 1141 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1237 : block g63 6 1237 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1333 : block g63 6 1333 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1429 : block g63 6 1429 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1525 : block g63 6 1525 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1621 : block g63 6 1621 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1717 : block g63 6 1717 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1813 : block g63 6 1813 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_1909 : block g63 6 1909 81=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 1990=true := (@block_merge g63 6 0 949 1041 (@block_merge g63 6 0 469 480 (@block_merge g63 6 0 181 288 (@block_merge g63 6 0 96 85 g63P6_0 g63P6_96) (@block_merge g63 6 181 96 192 g63P6_181 (@block_merge g63 6 277 96 96 g63P6_277 g63P6_373))) (@block_merge g63 6 469 192 288 (@block_merge g63 6 469 96 96 g63P6_469 g63P6_565) (@block_merge g63 6 661 96 192 g63P6_661 (@block_merge g63 6 757 96 96 g63P6_757 g63P6_853)))) (@block_merge g63 6 949 480 561 (@block_merge g63 6 949 192 288 (@block_merge g63 6 949 96 96 g63P6_949 g63P6_1045) (@block_merge g63 6 1141 96 192 g63P6_1141 (@block_merge g63 6 1237 96 96 g63P6_1237 g63P6_1333))) (@block_merge g63 6 1429 288 273 (@block_merge g63 6 1429 96 192 g63P6_1429 (@block_merge g63 6 1525 96 96 g63P6_1525 g63P6_1621)) (@block_merge g63 6 1717 96 177 g63P6_1717 (@block_merge g63 6 1813 96 81 g63P6_1813 g63P6_1909)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : block g63 7 0 26=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_26 : block g63 7 26 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_122 : block g63 7 122 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_218 : block g63 7 218 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_314 : block g63 7 314 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_410 : block g63 7 410 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_442 : block g63 7 442 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_538 : block g63 7 538 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_634 : block g63 7 634 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_730 : block g63 7 730 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_826 : block g63 7 826 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_922 : block g63 7 922 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1018 : block g63 7 1018 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1114 : block g63 7 1114 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1210 : block g63 7 1210 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1306 : block g63 7 1306 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1402 : block g63 7 1402 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_1498 : block g63 7 1498 19=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : block g63 7 0 1517=true := (@block_merge g63 7 0 730 787 (@block_merge g63 7 0 314 416 (@block_merge g63 7 0 122 192 (@block_merge g63 7 0 26 96 g63P7_0 g63P7_26) (@block_merge g63 7 122 96 96 g63P7_122 g63P7_218)) (@block_merge g63 7 314 128 288 (@block_merge g63 7 314 96 32 g63P7_314 g63P7_410) (@block_merge g63 7 442 96 192 g63P7_442 (@block_merge g63 7 538 96 96 g63P7_538 g63P7_634)))) (@block_merge g63 7 730 384 403 (@block_merge g63 7 730 192 192 (@block_merge g63 7 730 96 96 g63P7_730 g63P7_826) (@block_merge g63 7 922 96 96 g63P7_922 g63P7_1018)) (@block_merge g63 7 1114 192 211 (@block_merge g63 7 1114 96 96 g63P7_1114 g63P7_1210) (@block_merge g63 7 1306 96 115 g63P7_1306 (@block_merge g63 7 1402 96 19 g63P7_1402 g63P7_1498)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_0 : block g63 8 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_4 : block g63 8 4 85=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_89 : block g63 8 89 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_185 : block g63 8 185 71=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P8_256 : block g63 8 256 89=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B8 : block g63 8 0 345=true := (@block_merge g63 8 0 89 256 (@block_merge g63 8 0 4 85 g63P8_0 g63P8_4) (@block_merge g63 8 89 96 160 g63P8_89 (@block_merge g63 8 185 71 89 g63P8_185 g63P8_256)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_0 : block g63 9 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_4 : block g63 9 4 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P9_17 : block g63 9 17 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B9 : block g63 9 0 42=true := (@block_merge g63 9 0 4 38 g63P9_0 (@block_merge g63 9 4 13 25 g63P9_4 g63P9_17))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P10_0 : block g63 10 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B10 : block g63 10 0 10=true := g63P10_0
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
  · exact g63B4
  · exact g63B5
  · exact g63B6
  · exact g63B7
  · exact g63B8
  · exact g63B9
  · exact g63B10
  · exact g63B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem fullLower : Impossible true graph 11 instanceInputs.toFinset := by
  rw [show graph = targetOf g63 by decide +kernel]
  exact root_index (g:=g63) (top:=11) (i:=0) (before_sound K59 V59) g63G g63T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_12144

open PEqualNP.Outside.L_meta_12144 in
theorem PEqualNP.Outside.L_meta_12144 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276682240 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276682240 * 2 ^ 32 + 4269860864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
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
