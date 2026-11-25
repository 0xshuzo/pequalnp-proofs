import PEqualNP.Defs

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_670
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
def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
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

def supportPairs (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (selected mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))

def graphPairs (m hints : Nat) : List (Sig × Row × Row) :=
  (selected m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
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


abbrev Bits := BitVec 768
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 768 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 768 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 768 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 768 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 768) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 768) (j : Fin 9) :
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
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 768) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (graphGoal m) = (liftGoal m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (vertex m j).getLsbD (asRow v i).val = ((if m.testBit j then v j else 0) : Bits).getLsbD i.val := bit_vertex m v i ⟨j,hj⟩
  simp only [bit,graphGoal,liftGoal,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]
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
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
    if (rs ||| column d z.2) != BitVec.allOnes 768 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 768 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 768) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 768) (hq : chartSamples m q = 0) :
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

def forestHints (tab : Packing) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+packedAt data (start+i*ow) ow
    getPairs data cw d (packedAt data pos 5) (pos+5+marker)
  else
    let off := denseRowStart d raw dict + num*denseRowWidth d flags
    let pairs := off+num*ow
    let pos := pairs+(marker-1024)*(cw+d)+packedAt data (off+i*ow) ow
    readSortedHints data pairs cw d (packedAt data (pos+5) 3) (packedAt data pos 5) (pos+8) 0

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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 768) &&
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
theorem extendKnown_ok {u old L m carries} (previous : Known u old)
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
def lanePlace (v : Nat) (upper : Nat) := 2^769*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^769 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<769 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 768) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (769*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^769)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 769*(i+1)-769=769*i := by omega
      have ge : ¬769*(i+1)<769 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 768 = (a==BitVec.allOnes 768) := by
  by_cases h : a=BitVec.allOnes 768
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^768-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^768 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (769*i) =
      (f xs[i]==BitVec.allOnes 768) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^769*u+x+(2^769*v+1)=2^769*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^769 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬769*(i+1)+768<769 := by omega
      have di : 769*(i+1)+768-769=769*i+768 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 769) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (769*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 769) (i:=i) (by simpa using hi) _ ok.2
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
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 768 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 768
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
theorem listPieces_all {α f xs d} (h : @listPieces α f xs d) : xs.all f=true := by
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

def witPairs (m : Nat) (rs : List Nat) : List (Sig × Row × Row) :=
  ((selected m).zip rs).map fun x => (x.1.2,Fin.ofNat 512 x.2,Fin.ofNat 512 (x.2 ||| (1 <<< x.1.1)))
def fullOK (m : Nat) (rs : List Nat) : Bool :=
  let xs := witPairs m rs
  checkEssential (graphGoal m) (varsX m) xs && (xs.map Prod.fst == vars m) &&
    properB (graphGoal m) && decide (varsX m = vars m ++ [typeWord (m/512-1)])
theorem full_split {u} {m : Nat} {rs : List Nat} (ok : fullOK m rs = true) {k : Nat} {S : Finset Sig}
    (h : Live u (graphGoal m) k S) (sub : ∀ v ∈ S, v ∈ varsX m) :
    S=(vars m).toFinset ∨ S=(varsX m).toFinset := by
  simp only [fullOK,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨ess,alls⟩,_⟩,hX⟩ := ok
  have rest : ∀ v ∈ vars m, v ∈ S := by
    intro v hv
    rw [←alls] at hv
    obtain ⟨r,s,hd,hi⟩ := essential_ok ess v (List.mem_toFinset.mpr hv)
    exact raw_required h (varsX m) v sub r s hd hi
  have mem : ∀ v, v ∈ varsX m ↔ v ∈ vars m ∨ v=typeWord (m/512-1) := by
    intro v; rw [hX]; simp
  by_cases hs : typeWord (m/512-1) ∈ S
  · refine Or.inr ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨sub v,fun hv => ?_⟩
    rcases (mem v).mp hv with hv | rfl
    · exact rest v hv
    · exact hs
  · refine Or.inl ?_
    ext v
    rw [List.mem_toFinset]
    refine ⟨fun hv => ?_,rest v⟩
    rcases (mem v).mp (sub v hv) with hv | rfl
    · exact hv
    · exact absurd hv hs
theorem strong_full {u} {m q cap : Nat} {rs : List Nat} (ok : fullOK m rs = true)
    (e : graphGoal m = graphGoal q) (ev : vars m = vars q)
    (a : Impossible u (graphGoal q) cap (vars q).toFinset)
    (b : Impossible u (graphGoal q) cap (varsX m).toFinset) :
    Lower u (varsX m) (graphGoal m) (cap+1) := by
  have ok' := ok
  simp only [fullOK,Bool.and_eq_true] at ok'
  intro p bank hr ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live (proper_of _ ok'.1.2) (essential_plain ok'.1.1.1).1 (essential_plain ok'.1.1.1).2 hr ha
  by_contra! small
  rcases full_split ok run hs with h | h
  · rw [ev] at h; rw [e,h] at run; exact a k (by omega) run
  · rw [e,h] at run; exact b k (by omega) run
def g15d3 (i : Nat) : Nat := 0xf
def g15l3 : Packing := (1,0,1,0,0,0,0,g15d3)
def g15samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe47473,0x173652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe97a7f,0x8c829),(0x1f8f9c,0x21714),(0x168de0,0x1de8e0),(0,0),(0,0),(0,0),(0,0),(0,0)]
def g15columns : List ColumnInfo := []
def g15autos : List (List Nat) := [[],[48,33]]
def g15levels : Nat → Packing
  | 3 => g15l3
  | _ => emptyPacking
def g15index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def g15 : Forest := ⟨15,3,fun j => g15samples[j]?.getD (0,0),g15columns,g15autos,g15levels,g15index⟩
set_option maxHeartbeats 0 in
theorem geomg15 : graphValid g15 (boundsBefore []) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg15_3_0 : block g15 3 0 1=true := by decide +kernel
theorem allg15_3 : block g15 3 0 1=true := sg15_3_0
theorem tablesg15 : checkedTables g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g15 0 0 0 = true)
  · exact (rfl : block g15 1 0 0 = true)
  · exact (rfl : block g15 2 0 0 = true)
  · exact allg15_3
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low15 : Lower true (vars 15) (graphGoal 15) 4 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g15) (i:=0) rfl rfl (before_sound [] baseKnown) geomg15 tablesg15 (by decide +kernel))
def known15 := extendKnown [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid15 : Known true known15 := extendKnown_ok (m:=15) baseKnown low15 (by decide +kernel)
def g31d6 (i : Nat) : Nat := 0x11a20bf
def g31l6 : Packing := (1,0,3,0,0,0,0,g31d6)
def g31h6 (i : Nat) : Nat := 0x30be670208000065000016357504004755c084
def g31d5 (i : Nat) : Nat := 0x40828fd20fd10
def g31l5 : Packing := (2,1,3,0,0,3,0,g31d5)
def g31h5 (i : Nat) : Nat := 0x300
def g31d4 (i : Nat) : Nat := 0x5dd4520
def g31l4 : Packing := (1,2,3,0,0,0,0,g31d4)
def g31samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd15d16630b273,0x11525c6a12412),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe90c286464e7f,0x2c2d009524869),(0x18c06d986cd9c,0x1290662058794),(0x27e6c59e90980,0x2166995b04820),(0x3ebbb2079b000,0xe892284e92c0),(0,0),(0,0),(0,0),(0,0)]
def g31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]
def g31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def g31levels : Nat → Packing
  | 6 => g31l6
  | 5 => g31l5
  | 4 => g31l4
  | _ => emptyPacking
def g31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 5 15 3 9 1 4 g31h6
  | 5 => lookupWord 1 3 1 9 1 4 g31h5
  | _ => fun _ => none
def g31 : Forest := ⟨31,6,fun j => g31samples[j]?.getD (0,0),g31columns,g31autos,g31levels,g31index⟩
set_option maxHeartbeats 0 in
theorem geomg31 : graphValid g31 (boundsBefore known15) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_6_0 : block g31 6 0 1=true := by decide +kernel
theorem allg31_6 : block g31 6 0 1=true := sg31_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_5_0 : block g31 5 0 2=true := by decide +kernel
theorem allg31_5 : block g31 5 0 2=true := sg31_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg31_4_0 : block g31 4 0 1=true := by decide +kernel
theorem allg31_4 : block g31 4 0 1=true := sg31_4_0
theorem tablesg31 : checkedTables g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g31 0 0 0 = true)
  · exact (rfl : block g31 1 0 0 = true)
  · exact (rfl : block g31 2 0 0 = true)
  · exact (rfl : block g31 3 0 0 = true)
  · exact allg31_4
  · exact allg31_5
  · exact allg31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low31 : Lower true (vars 31) (graphGoal 31) 7 := plain_low (hints:=8449) (by decide +kernel) (index_root (g:=g31) (i:=0) rfl rfl (before_sound known15 valid15) geomg31 tablesg31 (by decide +kernel))
def known31 := extendKnown known15 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid31 : Known true known31 := extendKnown_ok (m:=31) valid15 low31 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (vars 47) (graphGoal 47) 5 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known31) (before_sound known31 valid31) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known47 := extendKnown known31 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47 : Known true known47 := extendKnown_ok (m:=47) valid31 low47 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (vars 55) (graphGoal 55) 5 := plain_low (hints:=257) (by decide +kernel) (cut_root (prior:=boundsBefore known47) (before_sound known47 valid47) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))
def known55 := extendKnown known47 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid55 : Known true known55 := extendKnown_ok (m:=55) valid47 low55 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (vars 63) (graphGoal 63) 8 := plain_low (hints:=8449) (by decide +kernel) (cut_root (prior:=boundsBefore known55) (before_sound known55 valid55) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))
def known63 := extendKnown known55 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid63 : Known true known63 := extendKnown_ok (m:=63) valid55 low63 (by decide +kernel)
def g111d6 (i : Nat) : Nat := 0x7213f
def g111l6 : Packing := (1,0,2,0,0,0,0,g111d6)
def g111h6 (i : Nat) : Nat := 0x8000
def g111d5 (i : Nat) : Nat := 0x17e51
def g111l5 : Packing := (1,1,2,0,0,0,0,g111d5)
def g111samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffad506dc8c692839f653,0xf04d190d4828112652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9aa3b7e53917e26487f,0xa02a6201004224829),(0x544c503731eb1c38f9c,0x1449d09c60531818514),(0x6d8c223200ec1fc0fc0,0x6bb62f6391ac07c0ac0),(0,0),(0x71d0482cce001fff020,0x70fb0c6f2b181eed020),(0x7fe3c2000ee7f040020,0x7f5fd599feffb040000),(0,0),(0,0)]
def g111columns : List ColumnInfo := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]
def g111autos : List (List Nat) := [[],[32,83]]
def g111levels : Nat → Packing
  | 6 => g111l6
  | 5 => g111l5
  | _ => emptyPacking
def g111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 g111h6
  | _ => fun _ => none
def g111 : Forest := ⟨111,6,fun j => g111samples[j]?.getD (0,0),g111columns,g111autos,g111levels,g111index⟩
set_option maxHeartbeats 0 in
theorem geomg111 : graphValid g111 (boundsBefore known63) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg111_6_0 : block g111 6 0 1=true := by decide +kernel
theorem allg111_6 : block g111 6 0 1=true := sg111_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg111_5_0 : block g111 5 0 1=true := by decide +kernel
theorem allg111_5 : block g111 5 0 1=true := sg111_5_0
theorem tablesg111 : checkedTables g111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g111 0 0 0 = true)
  · exact (rfl : block g111 1 0 0 = true)
  · exact (rfl : block g111 2 0 0 = true)
  · exact (rfl : block g111 3 0 0 = true)
  · exact (rfl : block g111 4 0 0 = true)
  · exact allg111_5
  · exact allg111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (vars 111) (graphGoal 111) 7 := plain_low (hints:=16785665) (by decide +kernel) (index_root (g:=g111) (i:=0) rfl rfl (before_sound known63 valid63) geomg111 tablesg111 (by decide +kernel))
def known111 := extendKnown known63 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid111 : Known true known111 := extendKnown_ok (m:=111) valid63 low111 (by decide +kernel)
def g189d7 (i : Nat) : Nat := 0x163441bf
def g189l7 : Packing := (1,0,3,0,0,0,0,g189d7)
def g189h7 (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0
def g189d6 (i : Nat) : Nat := 0x420a3fa41fd10
def g189l6 : Packing := (2,1,3,0,0,3,0,g189d6)
def g189h6 (i : Nat) : Nat := 0x18000
def g189d5 (i : Nat) : Nat := 0xb7d8d20
def g189l5 : Packing := (1,2,3,0,0,0,0,g189d5)
def g189samples : Array (Bits × Bits) := #[(0x1da64108012bd832f47c,0x1d85960021199906a42c),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffac458a9750042f2dc84f,0x4c61e4544061425c84a),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9958e417a60021ce0f8f,0x1909e00a3a18e18a0685),(0x67780400a62f50f10f70,0x627201f4c42600710950),(0x52c2796909d080fbf080,0x4042684f5e8240f95000),(0,0),(0x7b3dbae059d52e010080,0x3b3981b0a179ab000080),(0,0)]
def g189columns : List ColumnInfo := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]
def g189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def g189levels : Nat → Packing
  | 7 => g189l7
  | 6 => g189l6
  | 5 => g189l5
  | _ => emptyPacking
def g189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 9 13 2 9 1 4 g189h7
  | 6 => lookupWord 1 3 1 9 1 4 g189h6
  | _ => fun _ => none
def g189 : Forest := ⟨189,7,fun j => g189samples[j]?.getD (0,0),g189columns,g189autos,g189levels,g189index⟩
set_option maxHeartbeats 0 in
theorem geomg189 : graphValid g189 (boundsBefore known111) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_7_0 : block g189 7 0 1=true := by decide +kernel
theorem allg189_7 : block g189 7 0 1=true := sg189_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_6_0 : block g189 6 0 2=true := by decide +kernel
theorem allg189_6 : block g189 6 0 2=true := sg189_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg189_5_0 : block g189 5 0 1=true := by decide +kernel
theorem allg189_5 : block g189 5 0 1=true := sg189_5_0
theorem tablesg189 : checkedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact allg189_5
  · exact allg189_6
  · exact allg189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (vars 189) (graphGoal 189) 8 := plain_low (hints:=536879876) (by decide +kernel) (index_root (g:=g189) (i:=0) rfl rfl (before_sound known111 valid111) geomg189 tablesg189 (by decide +kernel))
def known189 := extendKnown known111 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : Known true known189 := extendKnown_ok (m:=189) valid111 low189 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (vars 127) (graphGoal 127) 9 := plain_low (hints:=16785665) (by decide +kernel) (cut_root (prior:=boundsBefore known189) (before_sound known189 valid189) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))
def known127 := extendKnown known189 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid127 : Known true known127 := extendKnown_ok (m:=127) valid189 low127 (by decide +kernel)
def g191d10 (i : Nat) : Nat := 0x8201ff
def g191l10 : Packing := (1,0,5,0,0,0,0,g191d10)
def g191h10 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a
def g191d9 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40
def g191l9 : Packing := (12,1,5,0,0,10,0,g191d9)
def g191h9 (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016
def g191d8 (j : Nat) : Nat := 0x1f80354899e077b024a9159a24b911ac077e0465c892708574212ef090d670221e053c214e043b8235cc808a67d091c046f022c0a32623f7049522d15433a6477b08ce033e84719314e04222c097484381b79046f2083ea431f521b80ae446e02b90c91ffb0022ff500273ff780227d009160ad1a2b008a388648213e1129ec123701bbc02b6031f108e812788527a1372fef00a370177821af58220f98488d80ed11b79e031029f81224fe00116e08ea457911b013808784866ffa009e7c49103fc0098ee0495c8319f848269f5444bf2292df046e02b7ba00a2fc6c027b211cfe48667a04ad80ec912592247ef00ae68147aaa443fce6009d00860143e0495227c608ef0062ec24c9e99123806bc62448287a25ec8251c78110a11258898fc215345209610e8c3700843000414019102020c60a121c5c5ec5844fc4543ec3542cc25c1bc12409bfebf43e8be1bd8bcf3c73b9bae3a7b9eb9838f383b7d373369b6035934fb46b3ab3432bb24b1b311b072fcaf62edae72dc2ce2bf2b02a2294a8da83a7ca70a66a5ea54a4d24423c233a2aa192102069fa9ed9e61de9d29cd1c09b21aa1a399a99498e18397416815a14f94493712b11e91590f1000f10e88dd8d18ca0c08b70ab8a209508407d87606b86505b85104203883182501880d00042a470a82c2e250b1c428051315c2a4b0980c2c730b01c220f0b9942c37098142e430883428431b894240f098cc2a090881424370b12c240d090ac4e43090cc6e650994426530b0d44651090d4242f0b98c2a490b0242c570b1542c490b02c2408c3891ae246b94ba4107b92b6e24e8849aeb66b881ee82a983aa6486b951ae707b831ae0c6bad364307b893a2047b92324287b8ba6e867bb19ae0e6bb51ee2a7b909ae2c6ba49aed66b9c9ae607b8b1ee088a159ae50e9811ee4ea9821eea8c98c2a60c6b921ae086b8b9ee467bb29ee62e9849ae346b8d9ee647baa9ee0e6b993a4146b8caa64e6ba41eea67b89b2a286b959ae4e7bb216e242b9c86e87ffff7f7efefbfdf6ef6f902308821058d53501314c12044020
def g191l8 : Packing := (113,2,5,589836,68,12,1057,g191d8)
def g191h8 (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000
def g191d7 (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163
def g191l7 : Packing := (116,3,5,0,0,11,0,g191d7)
def g191h7 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a
def g191d6 (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110
def g191l6 : Packing := (12,4,5,0,0,6,0,g191d6)
def g191samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffda8e80efa31334f8b77110a294fa2c140112476e217263,0x1a8204e622010a10823154424006181028000900212202),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe550613dee46b171e50184200e13000163a237ccc4483f,0x2550c011dc22916965caaa243f59e4c1d3e726bcc44879),(0xb8767821ad46b844808258e2a3253cf6ea13881040d8c,0x287218002942c96181045804080031c00109841008504),(0x2669d07e8c08ca07a98c101ac024d2c2804ca411f909a0,0x2428c05eec0a4201a424385293645c4328c32710b10ae0),(0x1554139111eda5cf49d49289dc948100804cc031fe5240,0x154130111e4b5ce49ca82ad2c98a38c923cd0654ed000),(0x253ba84144b4c40e1226cad10169ac341018648a03a410,0x2509e8114094c4ae18468a9400a0a6cc00bdf6de028450),(0,0),(0x38f01e2cfde810414683fb572913092a5d010800038410,0x1870162cbd68114126a930633d5f5823ff420120010200),(0,0)]
def g191columns : List ColumnInfo := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]
def g191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def g191levels : Nat → Packing
  | 10 => g191l10
  | 9 => g191l9
  | 8 => g191l8
  | 7 => g191l7
  | 6 => g191l6
  | _ => emptyPacking
def g191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 16 41 5 10 4 2 g191h10
  | 9 => lookupWord 67 277 6 13 7 2 g191h9
  | 8 => lookupWord 100 251 6 13 7 2 g191h8
  | 7 => lookupWord 4 19 2 10 4 2 g191h7
  | _ => fun _ => none
def g191 : Forest := ⟨191,10,fun j => g191samples[j]?.getD (0,0),g191columns,g191autos,g191levels,g191index⟩
set_option maxHeartbeats 0 in
theorem geomg191 : graphValid g191 (boundsBefore known127) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_10_0 : block g191 10 0 1=true := by decide +kernel
theorem allg191_10 : block g191 10 0 1=true := sg191_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_9_0 : block g191 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_9 : block g191 9 0 12=true := sg191_9_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_0 : block g191 8 0 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_3 : block g191 8 3 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_39 : block g191 8 39 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_70 : block g191 8 70 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_8_106 : block g191 8 106 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_8 : block g191 8 0 113=true := (@block_merge g191 8 0 106 7 (@block_merge g191 8 0 70 36 (@block_merge g191 8 0 39 31 (@block_merge g191 8 0 3 36 sg191_8_0 sg191_8_3) sg191_8_39) sg191_8_70) sg191_8_106)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_0 : block g191 7 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_13 : block g191 7 13 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_49 : block g191 7 49 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_7_85 : block g191 7 85 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_7 : block g191 7 0 116=true := (@block_merge g191 7 0 85 31 (@block_merge g191 7 0 49 36 (@block_merge g191 7 0 13 36 sg191_7_0 sg191_7_13) sg191_7_49) sg191_7_85)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg191_6_0 : block g191 6 0 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg191_6 : block g191 6 0 12=true := sg191_6_0
theorem tablesg191 : checkedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g191 0 0 0 = true)
  · exact (rfl : block g191 1 0 0 = true)
  · exact (rfl : block g191 2 0 0 = true)
  · exact (rfl : block g191 3 0 0 = true)
  · exact (rfl : block g191 4 0 0 = true)
  · exact (rfl : block g191 5 0 0 = true)
  · exact allg191_6
  · exact allg191_7
  · exact allg191_8
  · exact allg191_9
  · exact allg191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (vars 191) (graphGoal 191) 11 := plain_low (hints:=536879361) (by decide +kernel) (index_root (g:=g191) (i:=0) rfl rfl (before_sound known127 valid127) geomg191 tablesg191 (by decide +kernel))
def known191 := extendKnown known127 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid191 : Known true known191 := extendKnown_ok (m:=191) valid127 low191 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (vars 251) (graphGoal 251) 8 := plain_low (hints:=1358970881) (by decide +kernel) (cut_root (prior:=boundsBefore known191) (before_sound known191 valid191) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))
def known251 := extendKnown known191 8 [(251,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid251 : Known true known251 := extendKnown_ok (m:=251) valid191 low251 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (vars 255) (graphGoal 255) 12 := plain_low (hints:=553656577) (by decide +kernel) (cut_root (prior:=boundsBefore known251) (before_sound known251 valid251) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))
def known255 := extendKnown known251 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid255 : Known true known255 := extendKnown_ok (m:=255) valid251 low255 (by decide +kernel)
def g383d12 (i : Nat) : Nat := 0x1840804ff
def g383l12 : Packing := (1,0,6,0,0,0,0,g383d12)
def g383h12 (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109
def g383d11 (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10
def g383l11 : Packing := (6,1,6,0,0,9,0,g383d11)
def g383h11 (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410
def g383d10 (j : Nat) : Nat := 0x2ff45022545810b0ebed2a0a0caa9a4a646170118bba1216fab28127d3e208a4fd3025756808373fd0139d909a4f77fc6205153e0263c3e095f7f520157b044d77c804c7e9c8080acf700959fa41af7f15139e7a243e4b049e3e72549ef82c4149a9b213cd771046be348414dff0820a1d72484df882050f8046fdd00eb5019eb3818801d311052ae460a7bcd01029a02900f738439afc1100200b730408c90182a2e28830c2c20863024850e8b0a261b081c11808f861e128c0d842217820e140a0933257c918e31461a4187eaf6de1ba2708d81a3b2d618bd16c2b1532a053124b45a834f71d2366648b895627049c860f91c23445d09f1081b43084b06209c0e800eb8beb9aeb83eb98e398eb9cf41aeb8df389e982e39ce41af982fc0bf40bf38de98ce98df39cf18dec0beb89e389fc1af98cec1ae40bfb8dbc23cb858c1a8c0d8c188c1d8c0c8c098c3dcb839c0b8c1c9c1a54180c316c156c104c183c23ffffefbeffbeef7bbebf8c2104c1100c010
def g383l10 : Packing := (47,2,6,524294,51,11,1060,g383d10)
def g383h10 (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720
def g383d9 (j : Nat) : Nat := (if j<1 then 0x90c4083f321d6cc55f504646019c44204dfc10cf28937f0432053910ce223b02400980bbc34c65818045e5f095406f016f31822b00f789912c221f5c0114f24249ce0e08c5fc120656c06b2083990d70859f22264171411812e90b633045ad93564ac98ac1927756b1df4473c74045ae40c7bc4213fdaa08c1dec4c97b82425ed04f3d690c2f0864391ec72208d390a7d7c922807c0191010fa1911e02bfb8240e4c43990d011c06bd692267e463b811dee091ec041cc873e3c9046de215e623de216f1097a08640ab2623f9804abea9226f20245bf630932fde02207c2399086b88877f60496e239ac50c021f5491180a7108bc843247a20643ec231f50022efe0c114fda0958225a38918c18c308840c70fd088c0683056b01e8ec1e8cc2c288d0b416286c21c0109148e1a828738784a282029c20384833040b05c2684e0814120e020441e0b05549d41d33d27d1c513d084fe4f74f14e5cdecd84d14ca4c34bccb4cab49f497c8747fc77c70c66c60c57c51442437c2fc26c1ec1440dc02bf9beb3e4bddbd73cc3c23b73b1ba83a139739238c37fb78b73b6635fb58b4ab44338331322317307af72efae7ade2d5ac72bcab6aae2a129328a280a74a6ba5d251a49237a29a1f211a061fb9f29e39dc1cc9be1b89ac1a519918f98618097996c96115894e14513b92b1229191109080fd8f80ef0e18d48c70b88aa8a109788d88187906e06905c05604e04083302901a80c00049718e4c0b36e11290e6d2997424c0b9261cf970e52b97315cb95261d8532e4ab97614cb9ca65cf532e6a997744cc1735c271330008982c5cc02266041130937948c5c8c8266017b0528b970cfc91846550c2628b983612c82e3e58513308c2711a9cabe265d58302aba833c4cc325e51382e23159451dc19c266176322389989d3c83c2e5cc7ce6137946d3c830e65c3372688b976da48ace60cf232a4259095ec14c2662673060a5900054c162a612172f0bd97886cb3afa462c1268bd9189c4b86f5cc2173103d8201fb9848644e7b050369159bc8acde1134322bd78445bc222c61857b271159411bc2251e61f1f2d03d829e140aac6188772e19f924dcc19226608830280998704cb8c2e6194b213c5837e0c0bc2e5c62f2853784553c8182661d7306eb784512c83aca4477f2460998808ca9a4654e3f24c3a970dec13d8cc513f24f0b9815f4bc574c555b0f009973ddc194de1106b22b0998943c9180e51b07291ff6febfbff77deefdbff7f6fddf7bdf77ebfcff7feff5fdbf77def7ddfb7f3fe7dcefdc6309c6308c63061e3060e3060a30606305c6305c2304c630cc6109ce1060e10606105ce104c6101ce10e1130e0530a0530605305c5305c13020530e0d10cc110a0d1060d105cd104c11020d109c43061830604305c4301c43060c10608105cc101cc10 else 0x23fc480cb7845bfa208a1e04c73d81137085d8158ef1090e22602dc5c887112c08e223888e2258134029f023bd8325d2859f446065d28576447019d81200235c08603afc001907c8877046f6022e212f4)
def g383l9 : Packing := (136,3,6,1638440,86,12,1083,g383d9)
def g383h9 (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804
def g383d8 (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630
def g383l8 : Packing := (53,4,6,0,0,9,0,g383d8)
def g383h8 (i : Nat) : Nat := 0x834601a000
def g383d7 (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30
def g383l7 : Packing := (2,5,6,0,0,3,0,g383d7)
def g383samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe383f541a14f4a486b2153ac6cc220d9a4c042882144400812c1a03824014a3e21f653,0x3835041a0c802027c003361601060690134460c209508104109022004008a24212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc798b2d38f019ccd955a0208a2083da20800120c010a1d5456e25c86f4208c8c6481f,0x1c288328053019888301081491048f8080c08110c302d0c88414008862440588c44809),(0x7f70482928ec6864892a7808c5443041003000306a901d5cd20440308a310f1078f9c,0x3d70482108ec6035cd2a7ca2c536061530706a304a029342b68660288a31871038514),(0x80a735fca4439b2e3869d91109444066714241006ab062288005b03d09cb601f80f80,0x8003b598a4030a023055011412c961ea430201c00594401409011095010a200b00a80),(0x167c86b44125c70c20a80cbc7ec00400020c06c00546400210005cf480fbe001fff020,0x147c84a44125c50d00a80c8e1ec30880424881e00722b16ebe406cd4a0ef45014ed020),(0x183c3ab81e2a648807c2c202060a2405bc40004ff800180a32b78004109b53fe000020,0x18382ab81e02648903c2c012072c9614fe40a0d2916af00796b6a00c309b74da000000),(0x119338998a1ec23330ce50600f619822183bd9200010a002102fddf75f600000000040,0x11338919a0e423320c650636e78101b5b3e708c0079280753abfc771d20a800000000),(0,0),(0xfc4c4e66431b5758c1c33431509592059bbf857fc041ea02010020410640500000060,0x6c4c406603181449c382f0c900368e000810f216e8403f82840020080440100000060)]
def g383columns : List ColumnInfo := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]
def g383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def g383levels : Nat → Packing
  | 12 => g383l12
  | 11 => g383l11
  | 10 => g383l10
  | 9 => g383l9
  | 8 => g383l8
  | 7 => g383l7
  | _ => emptyPacking
def g383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 8 37 4 10 3 3 g383h12
  | 11 => lookupWord 48 123 4 13 6 3 g383h11
  | 10 => lookupWord 79 299 8 15 8 3 g383h10
  | 9 => lookupWord 39 99 5 13 6 3 g383h9
  | 8 => lookupWord 1 5 1 8 1 3 g383h8
  | _ => fun _ => none
def g383 : Forest := ⟨383,12,fun j => g383samples[j]?.getD (0,0),g383columns,g383autos,g383levels,g383index⟩
set_option maxHeartbeats 0 in
theorem geomg383 : graphValid g383 (boundsBefore known255) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_12_0 : block g383 12 0 1=true := by decide +kernel
theorem allg383_12 : block g383 12 0 1=true := sg383_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_11_0 : block g383 11 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_11 : block g383 11 0 6=true := sg383_11_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_0 : block g383 10 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_6 : block g383 10 6 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_10_19 : block g383 10 19 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_10 : block g383 10 0 47=true := (@block_merge g383 10 0 19 28 (@block_merge g383 10 0 6 13 sg383_10_0 sg383_10_6) sg383_10_19)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_0 : block g383 9 0 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_3 : block g383 9 3 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_39 : block g383 9 39 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_75 : block g383 9 75 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_111 : block g383 9 111 8=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_9_119 : block g383 9 119 17=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_9 : block g383 9 0 136=true := (@block_merge g383 9 0 119 17 (@block_merge g383 9 0 111 8 (@block_merge g383 9 0 75 36 (@block_merge g383 9 0 39 36 (@block_merge g383 9 0 3 36 sg383_9_0 sg383_9_3) sg383_9_39) sg383_9_75) sg383_9_111) sg383_9_119)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_0 : block g383 8 0 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_36 : block g383 8 36 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_8_44 : block g383 8 44 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allg383_8 : block g383 8 0 53=true := (@block_merge g383 8 0 44 9 (@block_merge g383 8 0 36 8 sg383_8_0 sg383_8_36) sg383_8_44)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sg383_7_0 : block g383 7 0 2=true := by decide +kernel
theorem allg383_7 : block g383 7 0 2=true := sg383_7_0
theorem tablesg383 : checkedTables g383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g383 0 0 0 = true)
  · exact (rfl : block g383 1 0 0 = true)
  · exact (rfl : block g383 2 0 0 = true)
  · exact (rfl : block g383 3 0 0 = true)
  · exact (rfl : block g383 4 0 0 = true)
  · exact (rfl : block g383 5 0 0 = true)
  · exact (rfl : block g383 6 0 0 = true)
  · exact allg383_7
  · exact allg383_8
  · exact allg383_9
  · exact allg383_10
  · exact allg383_11
  · exact allg383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low383 : Lower true (vars 383) (graphGoal 383) 13 := plain_low (hints:=12901687553) (by decide +kernel) (index_root (g:=g383) (i:=0) rfl rfl (before_sound known255 valid255) geomg383 tablesg383 (by decide +kernel))
def known383 := extendKnown known255 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid383 : Known true known383 := extendKnown_ok (m:=383) valid255 low383 (by decide +kernel)
theorem validF : Known false known383 := known_down valid383
def x31d6 (i : Nat) : Nat := 0x1a230180fd10fc20
def x31l6 : Packing := (2,1,2,0,0,4,0,x31d6)
def x31h6 (i : Nat) : Nat := 0x104451000a0200202082101c0c0071400
def x31d5 (i : Nat) : Nat := 0x613110000e3d4507e48110bea9a217d53082faa4885f54420
def x31l5 : Packing := (5,2,2,0,0,5,0,x31d5)
def x31samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffec04a3a21f673,0x2a912c2212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8a05bac6487f,0x56291cc44829),(0x2f8585078f9c,0x309c463038514),(0x135b045f80fe0,0xb41b88b00ae0),(0x3507a41fff000,0x142e4354ed000),(0,0),(0,0),(0,0),(0,0)]
def x31columns : List ColumnInfo := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4)]
def x31autos : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]
def x31levels : Nat → Packing
  | 6 => x31l6
  | 5 => x31l5
  | _ => emptyPacking
def x31index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 8 11 1 11 3 4 x31h6
  | _ => fun _ => none
def x31 : Forest := ⟨1055,6,fun j => x31samples[j]?.getD (0,0),x31columns,x31autos,x31levels,x31index⟩
set_option maxHeartbeats 0 in
theorem geomx31 : graphValid x31 (boundsBefore known383) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_6_0 : block x31 6 0 2=true := by decide +kernel
theorem allx31_6 : block x31 6 0 2=true := sx31_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx31_5_0 : block x31 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx31_5 : block x31 5 0 5=true := sx31_5_0
theorem tablesx31 : checkedTables x31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x31 0 0 0 = true)
  · exact (rfl : block x31 1 0 0 = true)
  · exact (rfl : block x31 2 0 0 = true)
  · exact (rfl : block x31 3 0 0 = true)
  · exact (rfl : block x31 4 0 0 = true)
  · exact allx31_5
  · exact allx31_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl31 : Impossible false (graphGoal 1055) 6 (vars 1055).toFinset := plainA (q:=31) (prior:=boundsBefore known383) (before_sound known383 validF) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1567 : Lower false (varsX 1567) (graphGoal 1567) 7 :=
  strong_full (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (index_root (g:=x31) (i:=0) rfl rfl (before_sound known383 validF) geomx31 tablesx31 (by decide +kernel))
def known1567 := extendKnown known383 7 [(1567,[]),(2079,[50,65]),(6687,[50,33,16,64]),(7199,[66,16]),(1703,[115,67,100,83]),(4263,[114,33,97,82,50,65]),(7847,[115,50,98,83,66,16]),(12455,[113,97,82,32,65,48]),(2361,[131,115,65,50,98,81]),(6990,[131,115,100,50,33,16,80]),(4963,[130,33,113,99,82,65]),(9571,[130,33,50,113,99,82,16,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1567 : Known false known1567 := extendKnown_ok (m:=1567) validF low1567 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42527 : Lower false (varsX 42527) (graphGoal 42527) 7 :=
  strong_full (q:=1055) (rs:=[2, 1, 2, 4, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl31
    (index_root (g:=x31) (i:=1) rfl rfl (before_sound known383 validF) geomx31 tablesx31 (by decide +kernel))
def known42527 := extendKnown known1567 7 [(42527,[]),(44063,[50,65]),(47647,[50,33,16,64]),(52767,[33,32,65,48]),(57887,[16,64,49,32]),(42663,[115,67,100,83]),(44711,[114,33,97,82,50,65]),(47783,[114,98,83,33,16,64]),(54951,[113,97,82,32,65,48]),(68775,[113,16,96,81,49,64]),(44345,[131,115,65,50,98,81]),(60217,[129,113,33,98,81,48]),(53070,[130,114,99,49,32,65,80]),(60238,[129,113,98,16,66,49,80]),(42851,[131,50,66,116,99,82]),(44899,[130,33,113,99,82,65]),(50019,[130,33,50,113,99,82,16,64]),(53164,[130,50,116,49,32,97,80]),(60332,[129,50,114,48,66,97,80]),(69548,[129,116,50,97,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42527 : Known false known42527 := extendKnown_ok (m:=42527) valid1567 low42527 (by decide +kernel)
def x111d6 (i : Nat) : Nat := 0x1040a3fa21fd51
def x111l6 : Packing := (2,1,1,0,0,3,0,x111d6)
def x111h6 (i : Nat) : Nat := 0x40000
def x111d5 (i : Nat) : Nat := 0x102de54110
def x111l5 : Packing := (1,2,1,0,0,0,0,x111d5)
def x111samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa1c017c36792839f673,0x6456218245928112652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdc38e7cc981ff26487f,0x1021104810085244829),(0x627e830e1e31c78f9c,0x474a42a0e1430838514),(0x207083f01fc1f80fe0,0x38b5bd5f00bc1780ae0),(0,0),(0x21c0103ffe001fff000,0x1ba9de7dba001eed000),(0x5818003fffffe000000,0x6fdeefb7eff7a000000),(0,0),(0,0)]
def x111columns : List ColumnInfo := [(96,0,15,0,4),(1,32,78,0,4)]
def x111autos : List (List Nat) := [[],[32,83]]
def x111levels : Nat → Packing
  | 6 => x111l6
  | 5 => x111l5
  | _ => emptyPacking
def x111index : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 3 1 6 1 1 x111h6
  | _ => fun _ => none
def x111 : Forest := ⟨1135,6,fun j => x111samples[j]?.getD (0,0),x111columns,x111autos,x111levels,x111index⟩
set_option maxHeartbeats 0 in
theorem geomx111 : graphValid x111 (boundsBefore known42527) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx111_6_0 : block x111 6 0 2=true := by decide +kernel
theorem allx111_6 : block x111 6 0 2=true := sx111_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx111_5_0 : block x111 5 0 1=true := by decide +kernel
theorem allx111_5 : block x111 5 0 1=true := sx111_5_0
theorem tablesx111 : checkedTables x111 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x111 0 0 0 = true)
  · exact (rfl : block x111 1 0 0 = true)
  · exact (rfl : block x111 2 0 0 = true)
  · exact (rfl : block x111 3 0 0 = true)
  · exact (rfl : block x111 4 0 0 = true)
  · exact allx111_5
  · exact allx111_6
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl111 : Impossible false (graphGoal 1135) 6 (vars 1135).toFinset := plainA (q:=111) (prior:=boundsBefore known42527) (before_sound known42527 valid42527) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low49775 : Lower false (varsX 49775) (graphGoal 49775) 7 :=
  strong_full (q:=1135) (rs:=[2, 64, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=0) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known49775 := extendKnown known42527 7 [(42683,[117,80,66,96,16]),(47806,[114,83,48,33,97,64]),(69498,[129,33,97,81,16,114,49,64]),(69557,[134,81,114,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid49775 : Known false known49775 := extendKnown_ok (m:=49775) valid42527 low49775 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42607 : Lower false (varsX 42607) (graphGoal 42607) 7 :=
  strong_full (q:=1135) (rs:=[2, 1, 2, 4, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl111
    (index_root (g:=x111) (i:=1) rfl rfl (before_sound known42527 valid42527) geomx111 tablesx111 (by decide +kernel))
def known42607 := extendKnown known49775 7 [(44155,[99,83,64,32,16]),(44219,[115,50,32,83,66,96,16]),(44731,[117,80,66,96,16]),(52926,[114,83,48,33,97,64]),(54974,[112,48,50,33,97,64]),(42711,[115,83,67]),(47838,[101,117,50,33,16,64]),(52958,[99,115,83,48,33,64]),(42739,[82,98,115,66,16]),(44787,[83,80,96,115,64,32,16]),(53054,[130,114,98,49,32,81,64]),(60253,[128,80,117,32,16,98,65,48]),(60282,[129,33,97,81,16,114,49,64]),(44981,[134,81,114,50,65]),(48071,[83,133,115,67,32,96]),(53212,[82,50,133,98,49,32,113,64]),(60408,[49,50,83,48,130,113,64]),(69624,[81,80,48,50,130,113,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42607 : Known false known42607 := extendKnown_ok (m:=42607) valid49775 low42607 (by decide +kernel)
def x63d7 (i : Nat) : Nat := 0x344640ac3f865fc10
def x63l7 : Packing := (2,1,2,0,0,4,0,x63d7)
def x63h7 (i : Nat) : Nat := 0x1520079d85d46b7171000680020c0000f391436008009b010
def x63d6 (i : Nat) : Nat := 0x1108482000804c8462023211880840401f7cb4e4b74a0b44658480fb48032fd4c410bf58032bf58c10bf590109f59432be580329f59410bd58432bb58810af59010b758c10
def x63l6 : Packing := (12,2,2,0,0,7,0,x63d6)
def x63h6 (i : Nat) : Nat := 0x24f9400060ba8030352
def x63d5 (i : Nat) : Nat := 0x108421184210872a1e50a03e498240196e52058432cea62b2821b54c1610cb5a98ac8086e53158810
def x63l5 : Packing := (6,3,2,0,0,6,0,x63d5)
def x63h5 (i : Nat) : Nat := 0x20034000
def x63d4 (i : Nat) : Nat := 0x3b04813058432
def x63l4 : Packing := (1,4,2,0,0,0,0,x63d4)
def x63samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc87d813f01c73e21f673,0x765c43000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe10600dd66a4c8c6487f,0x3601a1ac64a488c44829),(0x238268c08738f1078f9c,0x9aa0e13831071038514),(0x16807e00f83f01f80fe0,0x125451e4502f00b00ae0),(0x1c109622ffc001fff000,0x2d89a218afc0014ed000),(0x690100fffffe000000,0x3f89a3bcfffdda000000),(0,0),(0,0),(0,0)]
def x63columns : List ColumnInfo := [(1,32,30,0,4),(6,0,57,0,4),(40,0,23,0,4),(24,0,39,0,4)]
def x63autos : List (List Nat) := [[],[65,50]]
def x63levels : Nat → Packing
  | 7 => x63l7
  | 6 => x63l6
  | 5 => x63l5
  | 4 => x63l4
  | _ => emptyPacking
def x63index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 7 21 2 9 4 1 x63h7
  | 6 => lookupWord 2 9 1 8 3 1 x63h6
  | 5 => lookupWord 1 5 1 6 1 1 x63h5
  | _ => fun _ => none
def x63 : Forest := ⟨1087,7,fun j => x63samples[j]?.getD (0,0),x63columns,x63autos,x63levels,x63index⟩
set_option maxHeartbeats 0 in
theorem geomx63 : graphValid x63 (boundsBefore known42607) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_7_0 : block x63 7 0 2=true := by decide +kernel
theorem allx63_7 : block x63 7 0 2=true := sx63_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_6_0 : block x63 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_6_7 : block x63 6 7 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_6 : block x63 6 0 12=true := (@block_merge x63 6 0 7 5 sx63_6_0 sx63_6_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_5_0 : block x63 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx63_5 : block x63 5 0 6=true := sx63_5_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx63_4_0 : block x63 4 0 1=true := by decide +kernel
theorem allx63_4 : block x63 4 0 1=true := sx63_4_0
theorem tablesx63 : checkedTables x63 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x63 0 0 0 = true)
  · exact (rfl : block x63 1 0 0 = true)
  · exact (rfl : block x63 2 0 0 = true)
  · exact (rfl : block x63 3 0 0 = true)
  · exact allx63_4
  · exact allx63_5
  · exact allx63_6
  · exact allx63_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl63 : Impossible false (graphGoal 1087) 7 (vars 1087).toFinset := plainA (q:=63) (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6719 : Lower false (varsX 6719) (graphGoal 6719) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (6688,0,6687,0,7) (by decide +kernel) (by decide +kernel))
def known6719 := extendKnown known42607 8 [(2143,[101,66,16]),(2425,[128,80,84,66,16,114,97,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6719 : Known false known6719 := extendKnown_ok (m:=6719) valid42607 low6719 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1087 : Lower false (varsX 1087) (graphGoal 1087) 8 :=
  strong_full (q:=1087) (rs:=[16, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (index_root (g:=x63) (i:=0) rfl rfl (before_sound known42607 valid42607) geomx63 tablesx63 (by decide +kernel))
def known1087 := extendKnown known6719 8 [(1087,[]),(2623,[50,65]),(1119,[101,66,16]),(6303,[117,101,67,32]),(11423,[117,101,33,32,65,48]),(6319,[116,100,83,32]),(13487,[113,97,82,32,65,48]),(1207,[115,84,99]),(3255,[114,81,98,50,65]),(1255,[83,82,114,99,66,16]),(18749,[129,113,82,97,48]),(11614,[132,116,84,48,33,96]),(18782,[129,33,114,82,16,66,49,96]),(18798,[128,64,116,49,96]),(1395,[131,84,115,98]),(18809,[128,80,84,66,16,114,97,48]),(11708,[132,67,84,48,33,113,96]),(3555,[83,80,132,115,96,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1087 : Known false known1087 := extendKnown_ok (m:=1087) valid6719 low1087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low11327 : Lower false (varsX 11327) (graphGoal 11327) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 16, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (index_root (g:=x63) (i:=1) rfl rfl (before_sound known42607 valid42607) geomx63 tablesx63 (by decide +kernel))
def known11327 := extendKnown known1087 8 [(2719,[117,101,67,32]),(13495,[115,84,99]),(3389,[132,116,65,48,80,97,32]),(8542,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid11327 : Known false known11327 := extendKnown_ok (m:=11327) valid1087 low11327 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1599 : Lower false (varsX 1599) (graphGoal 1599) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (1568,0,1567,0,7) (by decide +kernel) (by decide +kernel))
def known1599 := extendKnown known11327 8 [(1599,[]),(12463,[113,97,82,32,65,48]),(1719,[115,84,99]),(2365,[132,116,65,48,80,97,32]),(9582,[128,16,113,65,49,33,96]),(4979,[130,50,81,115,98,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1599 : Known false known1599 := extendKnown_ok (m:=1599) valid11327 low1599 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low47679 : Lower false (varsX 47679) (graphGoal 47679) 8 :=
  strong_full (q:=1087) (rs:=[2, 4, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (47648,0,47647,0,7) (by decide +kernel) (by decide +kernel))
def known47679 := extendKnown known1599 8 [(47679,[]),(44127,[101,66,16]),(52831,[101,50,33,16,64]),(42671,[116,100,83,32]),(68783,[113,97,82,32,65,48]),(47799,[115,84,99]),(68791,[114,81,98,50,65]),(44349,[132,116,65,48,80,97,32]),(60366,[82,50,133,115,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid47679 : Known false known47679 := extendKnown_ok (m:=47679) valid1599 low47679 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42559 : Lower false (varsX 42559) (graphGoal 42559) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 2, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (42528,0,42527,0,7) (by decide +kernel) (by decide +kernel))
def known42559 := extendKnown known47679 8 [(42559,[]),(42591,[101,66,16]),(47791,[116,100,83,32]),(54959,[113,97,82,32,65,48]),(42679,[115,84,99]),(44727,[114,81,98,50,65]),(60270,[128,64,116,49,96]),(60281,[128,80,84,66,16,114,97,48]),(69497,[128,81,67,112,97,32]),(48078,[83,133,115,67,32,96]),(69603,[81,80,128,113,98,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42559 : Known false known42559 := extendKnown_ok (m:=42559) valid47679 low42559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52799 : Lower false (varsX 52799) (graphGoal 52799) 8 :=
  strong_full (q:=1087) (rs:=[2, 1, 8, 4, 1, 1]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl63
    (cut_root (prior:=boundsBefore known42607) (before_sound known42607 valid42607) (52768,0,52767,0,7) (by decide +kernel) (by decide +kernel))
def known52799 := extendKnown known42559 8 [(44719,[116,100,83,32]),(54967,[115,84,99]),(60239,[131,115,100,50,33,16,80]),(50014,[132,116,84,48,33,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52799 : Known false known52799 := extendKnown_ok (m:=52799) valid42559 low52799 (by decide +kernel)
def x189d7 (i : Nat) : Nat := 0x8151108090c808420380cd31101fd30fe887f0c3f821fc20
def x189l7 : Packing := (5,1,3,0,0,7,0,x189d7)
def x189h7 (i : Nat) : Nat := 0x74308515c76e77000000818435800000a71f02000000828c06fa8001025909670038579507803705e0482024814000001004000000
def x189d6 (i : Nat) : Nat := 0x10842000421000040820b764a0f19283c280fe48130bf58910bf58430fe54030fe48110bf58930bf594209f59420bb58830bd58430
def x189l6 : Packing := (10,2,3,0,0,7,0,x189d6)
def x189h6 (i : Nat) : Nat := 0x700009040000000000ddd0800002
def x189d5 (i : Nat) : Nat := 0x104208141ba541620c36698ac4186f15058430
def x189l5 : Packing := (3,3,3,0,0,5,0,x189d5)
def x189samples : Array (Bits × Bits) := #[(0x98543c01121d833f4fc,0x1e6c550011215802a4ac),(0,0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc268201f82067f2cc8cf,0xa9854a582041528c8ca),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe6400c361c3861cf0f0f,0x146729421c3060870605),(0x25004de0e03f81f00ff0,0x219082bde00e81700950),(0x18979200ffc001fff000,0x9328e7ca8001fd5000),(0,0),(0x103ab009fffffe000000,0x35648318357bea000000),(0,0)]
def x189columns : List ColumnInfo := [(33,0,156,0,4),(24,0,165,0,4),(12,0,177,0,4),(132,0,57,0,4),(17,0,172,0,4),(160,0,29,0,4)]
def x189autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]
def x189levels : Nat → Packing
  | 7 => x189l7
  | 6 => x189l6
  | 5 => x189l5
  | _ => emptyPacking
def x189index : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 23 29 4 12 4 4 x189h7
  | 6 => lookupWord 2 11 1 10 2 4 x189h6
  | _ => fun _ => none
def x189 : Forest := ⟨1213,7,fun j => x189samples[j]?.getD (0,0),x189columns,x189autos,x189levels,x189index⟩
set_option maxHeartbeats 0 in
theorem geomx189 : graphValid x189 (boundsBefore known52799) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_7_0 : block x189 7 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_7 : block x189 7 0 5=true := sx189_7_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_0 : block x189 6 0 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_6_3 : block x189 6 3 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx189_6 : block x189 6 0 10=true := (@block_merge x189 6 0 3 7 sx189_6_0 sx189_6_3)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx189_5_0 : block x189 5 0 3=true := by decide +kernel
theorem allx189_5 : block x189 5 0 3=true := sx189_5_0
theorem tablesx189 : checkedTables x189 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x189 0 0 0 = true)
  · exact (rfl : block x189 1 0 0 = true)
  · exact (rfl : block x189 2 0 0 = true)
  · exact (rfl : block x189 3 0 0 = true)
  · exact (rfl : block x189 4 0 0 = true)
  · exact allx189_5
  · exact allx189_6
  · exact allx189_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl189 : Impossible false (graphGoal 1213) 7 (vars 1213).toFinset := plainA (q:=189) (prior:=boundsBefore known52799) (before_sound known52799 valid52799) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2237 : Lower false (varsX 2237) (graphGoal 2237) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=0) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2237 := extendKnown known52799 8 [(2237,[]),(18109,[82,48,66,112]),(2395,[130,114,98,33,81]),(12774,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2237 : Known false known2237 := extendKnown_ok (m:=2237) valid52799 low2237 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1725 : Lower false (varsX 1725) (graphGoal 1725) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=1) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known1725 := extendKnown known2237 8 [(1725,[]),(17085,[82,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1725 : Known false known1725 := extendKnown_ok (m:=1725) valid2237 low1725 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2749 : Lower false (varsX 2749) (graphGoal 2749) 8 :=
  strong_full (q:=1213) (rs:=[32, 8, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=2) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known2749 := extendKnown known1725 8 [(2749,[]),(11453,[117,67,32]),(1371,[130,50,98,82,115,33,65]),(6630,[115,83,82,130,99,66,16]),(13798,[66,114,50,132,99,32,80,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2749 : Known false known2749 := extendKnown_ok (m:=2749) valid1725 low2749 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43197 : Lower false (varsX 43197) (graphGoal 43197) 8 :=
  strong_full (q:=1213) (rs:=[20, 9, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=3) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known43197 := extendKnown known2749 8 [(43197,[]),(58557,[82,48]),(64189,[83,114,64]),(43823,[135,50,65]),(46427,[130,50,98,82,115,33,65]),(48475,[135,101,50,33,16,64]),(49638,[115,83,82,130,99,66,16]),(55782,[117,130,99,32,64,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43197 : Known false known43197 := extendKnown_ok (m:=43197) valid2749 low43197 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44221 : Lower false (varsX 44221) (graphGoal 44221) 8 :=
  strong_full (q:=1213) (rs:=[16, 8, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl189
    (index_root (g:=x189) (i:=4) rfl rfl (before_sound known52799 valid52799) geomx189 tablesx189 (by decide +kernel))
def known44221 := extendKnown known43197 8 [(44221,[]),(44733,[84,115]),(52925,[117,67,32]),(54973,[116,83,32]),(58045,[82,48]),(60207,[132,65,48,80,113,32]),(42843,[130,50,98,82,115,33,65]),(44379,[130,114,98,33,81]),(58203,[133,117,101,33,48]),(48102,[115,83,82,130,99,66,16]),(55270,[66,114,50,132,99,32,80,16]),(69606,[80,132,99,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44221 : Known false known44221 := extendKnown_ok (m:=44221) valid43197 low44221 (by decide +kernel)
def x251d7 (i : Nat) : Nat := 0x60bfd31
def x251l7 : Packing := (1,1,1,0,0,0,0,x251d7)
def x251samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0021ee01fffe490e402109fc2670e40ff27f,0x208080808080490a402108a80450a401222a),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe488e110001fe0033fcc6313cd9833fca4c4f,0x156067666666600212cc63114910212ca4c45),(0,0),(0x1000fe000071c380f83e331e1c38f38f8c,0x66caaaaaaaaa718380f82c321e1838a38b0c),(0x1000fffe0181fc0f003fc3e01fc0fc0ff0,0x199355555555580740f001341e007405c04d0),(0x1b761ee000001fe000fffc003ffe000fff000,0x1036e0f1e1e1f24000a948003fba000fed000),(0x488e11000001fffff0000003ffffff000000,0xa9f989999999ffded00000036efded000000),(0x1b74000000001fffffffffffc000000000000,0xfc91f0e1e1e0dbfff56b7ffc000000000000),(0,0)]
def x251columns : List ColumnInfo := [(88,0,163,0,4),(8,0,243,0,7)]
def x251autos : List (List Nat) := [[],[115,84],[65,99],[65,115,81,99],[81,118],[81,99,65,115]]
def x251levels : Nat → Packing
  | 7 => x251l7
  | _ => emptyPacking
def x251index : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def x251 : Forest := ⟨1275,7,fun j => x251samples[j]?.getD (0,0),x251columns,x251autos,x251levels,x251index⟩
set_option maxHeartbeats 0 in
theorem geomx251 : graphValid x251 (boundsBefore known44221) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=0) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx251_7_0 : block x251 7 0 1=true := by decide +kernel
theorem allx251_7 : block x251 7 0 1=true := sx251_7_0
theorem tablesx251 : checkedTables x251 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x251 0 0 0 = true)
  · exact (rfl : block x251 1 0 0 = true)
  · exact (rfl : block x251 2 0 0 = true)
  · exact (rfl : block x251 3 0 0 = true)
  · exact (rfl : block x251 4 0 0 = true)
  · exact (rfl : block x251 5 0 0 = true)
  · exact (rfl : block x251 6 0 0 = true)
  · exact allx251_7
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl251 : Impossible false (graphGoal 1275) 7 (vars 1275).toFinset := plainA (q:=251) (prior:=boundsBefore known44221) (before_sound known44221 valid44221) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low48891 : Lower false (varsX 48891) (graphGoal 48891) 8 :=
  strong_full (q:=1275) (rs:=[2, 80, 16, 10, 1, 2, 32]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl251
    (index_root (g:=x251) (i:=0) rfl rfl (before_sound known44221 valid44221) geomx251 tablesx251 (by decide +kernel))
def known48891 := extendKnown known44221 8 [(59646,[116,100,49,81,32]),(43479,[115,83,133,99,50,66,16]),(55773,[99,132,84,48,33,112]),(46581,[67,80,100,131,112,32,16]),(58874,[84,100,49,128,113,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid48891 : Known false known48891 := extendKnown_ok (m:=48891) valid44221 low48891 (by decide +kernel)
def x127d8 (i : Nat) : Nat := 0x1948817fd30
def x127l8 : Packing := (1,1,3,0,0,0,0,x127d8)
def x127h8 (i : Nat) : Nat := 0x8e80
def x127d7 (i : Nat) : Nat := 0x24c269243a037eb0261df54530
def x127l7 : Packing := (2,2,3,0,0,5,0,x127d7)
def x127samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc30c1fc403f090d9a33c9401c73e21f673,0x3301d20130c00091222c94000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc4b18000fff1632604c0ff66a4c8c6487f,0x8d421c20c30420400804264a488c44829),(0x30400032fc098c38470f188738f1078f9c,0x2322c82492498838470a18831071038514),(0x3842603b000e0fc0780fe0f83f01f80fe0,0x1ccd1659659407c03005e0502f00b00ae0),(0x9026ec9000ff0007ff000ffc001fff000,0x3229a68a2bf0004dd000afc0014ed000),(0x20c1104000fffff800000fffffe000000,0xcfe2dfecf3fff6e800000fffdda000000),(0x4b18000000fffffffffff000000000000,0x372bde3df3cfbdfbff7fbd000000000000),(0,0),(0,0)]
def x127columns : List ColumnInfo := [(20,8,99,0,4),(96,0,31,0,7),(16,0,111,0,7),(66,0,61,0,5),(34,64,29,0,4),(1056,0,1119,0,8),(49,0,78,0,4)]
def x127autos : List (List Nat) := [[],[16,66,101]]
def x127levels : Nat → Packing
  | 8 => x127l8
  | 7 => x127l7
  | _ => emptyPacking
def x127index : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 1 6 1 1 x127h8
  | _ => fun _ => none
def x127 : Forest := ⟨1151,8,fun j => x127samples[j]?.getD (0,0),x127columns,x127autos,x127levels,x127index⟩
set_option maxHeartbeats 0 in
theorem geomx127 : graphValid x127 (boundsBefore known48891) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=1) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_8_0 : block x127 8 0 1=true := by decide +kernel
theorem allx127_8 : block x127 8 0 1=true := sx127_8_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx127_7_0 : block x127 7 0 2=true := by decide +kernel
theorem allx127_7 : block x127 7 0 2=true := sx127_7_0
theorem tablesx127 : checkedTables x127 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x127 0 0 0 = true)
  · exact (rfl : block x127 1 0 0 = true)
  · exact (rfl : block x127 2 0 0 = true)
  · exact (rfl : block x127 3 0 0 = true)
  · exact (rfl : block x127 4 0 0 = true)
  · exact (rfl : block x127 5 0 0 = true)
  · exact (rfl : block x127 6 0 0 = true)
  · exact allx127_7
  · exact allx127_8
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl127 : Impossible false (graphGoal 1151) 8 (vars 1151).toFinset := plainA (q:=127) (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2175 : Lower false (varsX 2175) (graphGoal 2175) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (2080,0,2143,0,8) (by decide +kernel) (by decide +kernel))
def known2175 := extendKnown known48891 9 [(2429,[129,82,113,48]),(7038,[129,98,82,16,66,49,112]),(9598,[128,100,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2175 : Known false known2175 := extendKnown_ok (m:=2175) valid48891 low2175 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1151 : Lower false (varsX 1151) (graphGoal 1151) 9 :=
  strong_full (q:=1151) (rs:=[16, 4, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (1056,0,1119,0,8) (by decide +kernel) (by decide +kernel))
def known1151 := extendKnown known2175 9 [(18814,[129,98,82,16,66,49,112]),(11742,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1151 : Known false known1151 := extendKnown_ok (m:=1151) valid2175 low1151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low52863 : Lower false (varsX 52863) (graphGoal 52863) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 8, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (52768,0,52831,0,8) (by decide +kernel) (by decide +kernel))
def known52863 := extendKnown known1151 9 [(44925,[129,82,113,48]),(50046,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid52863 : Known false known52863 := extendKnown_ok (m:=52863) valid1151 low52863 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44159 : Lower false (varsX 44159) (graphGoal 44159) 9 :=
  strong_full (q:=1151) (rs:=[16, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (44064,0,44127,0,8) (by decide +kernel) (by decide +kernel))
def known44159 := extendKnown known52863 9 [(44159,[]),(47743,[101,66,16]),(69501,[128,84,66,16,98,113,48]),(74110,[128,100,49,112]),(48094,[82,133,99,49,32,65,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44159 : Known false known44159 := extendKnown_ok (m:=44159) valid52863 low44159 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43647 : Lower false (varsX 43647) (graphGoal 43647) 9 :=
  strong_full (q:=1151) (rs:=[10, 1, 2, 5, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (index_root (g:=x127) (i:=0) rfl rfl (before_sound known48891 valid48891) geomx127 tablesx127 (by decide +kernel))
def known43647 := extendKnown known44159 9 [(43647,[]),(46455,[131,84,115,98]),(51063,[131,100,115,82,16]),(43901,[129,82,113,48]),(46461,[128,84,66,16,98,113,48]),(48510,[129,98,82,16,66,49,112]),(51070,[128,100,49,112]),(43423,[134,117,33,32,65,48]),(58811,[84,133,80,66,114,96,16]),(59900,[82,48,66,129,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43647 : Known false known43647 := extendKnown_ok (m:=43647) valid44159 low43647 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42623 : Lower false (varsX 42623) (graphGoal 42623) 9 :=
  strong_full (q:=1151) (rs:=[2, 1, 2, 4, 1, 1, 2]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl127
    (cut_root (prior:=boundsBefore known48891) (before_sound known48891 valid48891) (42528,0,42591,0,8) (by decide +kernel) (by decide +kernel))
def known42623 := extendKnown known43647 9 [(42623,[]),(60285,[129,82,113,48]),(60286,[129,98,82,16,66,49,112])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42623 : Known false known42623 := extendKnown_ok (m:=42623) valid43647 low42623 (by decide +kernel)
def x191d10 (i : Nat) : Nat := 0x28270019312920f8e91910020841c00602403e3031e1d18e0d8d0c8c0b8b0a888028504c483c3844400101e1c1a180e0060b0a090807003030282018100801fbb98bdd7a82ec539c87a00ff503fd43ff54ffd10ff083fc40ff0c3fc53ff18ffc31
def x191l10 : Packing := (10,1,7,0,0,9,0,x191d10)
def x191h10 (i : Nat) : Nat := 0xa49b3289cfee0003c11e62e10c1e4000235000513996000090c91cf0a000013a78dac3f26c00039c5cb8000000000204a000000452c001633e0e551fc80b152f0f95a89a255e23881a8be81b938018248c665c070000000000b3bc9a800000031700028c3072b06ecfafc98375010470c01e16716e074d6b0bf948ee3ac9600036e0054814054a5d5892c4d40b354401d8907a8d086167486866b2610135be1dd11650170cee09f0f01bcb5800000010d202243f318eef1419c646e0a9a0079430db52928c52c5193c564cb39a6900028ec0012280375062865214c24898f806a2a5df5d43e1d42ba11a4fe586827629805dd992be81c8003761a6d0ec800000000072b8000c8986beae00000018581727cae660c1200068bc0011c561f0148000b8c0000001cb4c5e711000138985d121316f8741ed000000000000000009074020000004d29b7e000c0d671818d8a3e1049165c75b693b0000000c7511c313d41fc131606bb107a0d043607013300102070000030000000461000006da150300000025000000000210610700003013010000000a0020130090060020020100100240030000015000100100020072001010001104000000010000400000000001011
def x191d9 (j : Nat) : Nat := (if j<1 then 0x4670b12533d10c75e8c8b58478714c78518d7ffe317a00012a9ac91478d191b210c32553e54c93f89481224ccae8c8db6fde254791fe4e848fbc887bfd7bf91489036fde2547dcf8012e849566e24b9fb14c8811a0e059e352b5153447cbd4232d7f49221033d272641407a231b409789c248c37effc18880013340f091678851c118ebe79ab9993d531d8dc499a05bd0c116be4b20866cfc8181973f508195bdbb50994f7c60a504f0c8428b9e9121c0ac4fc46a1120e04a60f4453fb885004944e5f860055bc6ff42c4127799d428024a1e7ce7ac1704adc7e20451ffc4244651f5f0228486f4f0a1954c1e8977ea4a053be12443c9c3c6580589afe03afe94c94489efffa830090fdb8d0417f449000ce5f928a32dffc2d0614d27f807b0a67cf1f4d91f647d4208fbfe3700101096bf0781268499f1f02000903ffe01040482fca44652ffe289a4fc122aff8d4941804bdf23604101297c7e2140124af7ee811a7f861011d78f7002c80953e381127d8e0211e7f299142fbf18650920df8cb8019cf270f30e0547938798702a5ebf9031120250f9f5818890128f270f30e05400fe351d6404a258208d1b924507a3c1d8e86f1d841349848218d86b128212494478f110820c0a8e62006815047c230948a42161f9088a0318c9c0a1707c9404221c0c881288b0503b15130a240108fc04381b1a0844030838cc0801088b84e07148944900150b4582b1787c010b2846416a08101e7fcbfa1f92fab7c5bddde64f0b778bb55d82e9e73db929c58e0c6f43739b5ad886b9b591a7ed1d68533b5996cb263d319988cc2b606af8d78aba05bcad9566ab10570ab25534a8d52fa8ed41e9ef4eba72935296e4a92505254906477a3591928ae444219908c8224009f80f6c78e3c09da0e727113711ad0d0066031e1840bdc5d52d89660ad254f29413e49b64b1247919c87c4161f88ef472036519c0c605f42df15609f849e22e105076437c19a0bf054424c0f9066025c0c4035000524114a83d264f4b885240f4b93d2a234983d2a4f4bb3d2e6f4b24d2813498352c034b1852c6d4902d242d4b93524094884d284d4aa3d26334a0bd2a614b0bd2c13498852eaf490352c734b1bd2a274b13d0e4f4b01d24134a13d2403499352e334b09d2407498b522014a8c52e2f4b08d2c114a84d26134ba4d2e8d4aa3528334b9b52e61498052c054384d0e4d4a0352a434a9152a474b84d282d4a8bd2c0f498bd24014a002ae4cab8c32846eb1caae10ab883282eab84aae22a393ca40cabb0c282cab91aae4aa3932ae0aab8caae2aab982aea4abb128e132983aaea6ab913a610ab8a3a612aba32ae6cabb1aae26abac2ae4eab822ae42caa3aaea2ababaae048b8a1ae462ba9a2e260bb192e660bb0ffffdfdfbfbeff7dbdddebf3f54d435011018c53100310c020 else 0x2a514f996be52268663fe3f325000b13ca8643f53090a16b2b1c08e6b231fc5008b7c382938e31a32317b310ffc6068f40910413efe1f6c01485ee44d9b654c87a249bf13a091bbf9e4f32ae0e4e3d3a92ab09fe26af3c9e651e04e8247ae7089a62f4408edf4ca44663e5120b04991818324)
def x191l9 : Packing := (122,2,7,720906,68,13,1115,x191d9)
def x191h9 (i : Nat) : Nat := (if i<1 then 0x8d2114ec42d555274bd2a00000161bc698a2be56e421c83e4eb400028745174e28a00000000000286640b140300000000000000029000001258a89ff00992fe0002b3da039c601254b5a7f81c0000a2dd89140da00006de2a4c59326092843a17450c9f98641eb8a6b0f032194d57899800010e20001c2208b800000002805000000000000000585b4e2b828d9a9b073f668000000008cd0000ca8dc8ad2baca4800000006ec3000060efc281810153c0000000217ef0d083fe87f00000001a1b8000781ec09a000246b324e0000a18c00039010001415c9baeb4c41fa947800010ac718343a800b516940168a70089713c725c00019a69eb0a0e0430e88f585868e0660223a8000a20e09dc8435154e1a3a209844215f52428c1cc67013432ca00034b5802270ffe195659f02531b064907608000e55761ca05e994bc50c000024e80003a02817f18688f76221a3d7d8af0df90eba87909b1876f302c105aa780000000000000060c0e190431ed5c5ec7000063d08b774286a09c1800006874a10ac3148761ac93451490187128de904f03084bb0000a1760000000300806afc2d7193f6fb0001841047b1299605400e8ea3fab29decc4b4cb3f14996518be8037c8c662106570000523a41e200014bda0cb8046d9e082a6aa400000259c4890f3613a227b440214710bd222cc55f95a52ee000384b99090001f43ac0db05dc2c380b606a4018e2c7c29000020e0b2c1c36d592581d405720e2070800051e58148179e57ec06e29fd94ff1596e576499887e93d52040000000000000000000000795500018280000403f0001612c0000000d17805980000000115f98a2c6b8000311dd8c356120d5b0c303bf0199866f08fe41a48e86705255e23385c8000b199fa7000050bf517da340801104c12de04508900000b134e067c961c1421cdc609488c1179277c579c8b767531636558089d347628365a2ca9e67f39dc94eff59cd5e90d481580b63f30a091557c001e97ce0ab2092d9b9923c13184648424ae092a2000251800e365b6ec4f892fb1b00c5dc12c482812e2f0e3ac0000000dd56a4e1cbce14af06045e8559b8202a28aa3599f78a280094d6254a491b0a46e5c4126684e456a0000c079b020000034f4b950b30000428604a800000012236482a88a00000000000000050ee000255e0000d1f600034aeaabb506cd2c00000502a8681003000e00140330401a0204c8b1a0000181040800456140030441602023011024280ba0254000865c1840010380140418f100c0150e04008001d0071a100802810081021810300000813204004060008e000c00e000c78710080080004291040029d2a44b0600006020a004820600003002c0042e002800c1808804104021e0c1810804080000440006000881824381004010402081091e001882208203 else 0x1b4a50500001d9fb975a15d240d09f665ca19400010148000d1120470000302ea103812ad92800041b8000000718e4000169580000000ec7a54fe07d532f9ea60000000191fd235ab94000005ceede82b68ac114331d200000002c309023e0d6a8e255930f60000c3e469200000000000300c89e400018b2000032dae49dca328dd0000a33c802b87e00000002020487dc8f05b1242c8cbf3068ec0c87758a5e2ae00033b16092dd50a395c36506b110702c1017c118ae2964af86cfc2179248c7f843873f929c843749a8d53e0a64b7917a78aa300f619f11a0a6c8001a2da47e4e380c952035c3c914c125e79dcb032d7fa52532f204a38c452e64523c2d6831f0269d1e3b6000046b502a1432594f8042e11bfb571400000a50987ce83cb1f0000031980004d6a0001094d53200010bf800016ed000074c40006015000000021b6800000000a15c1ea832e2e1639ec13384f000000004985c7752fb3484c94632b82150298cb54f6700000000000084291da000200d009f000000010a20000000144eac4c90ba0127cce6836cb09b02f9c9c5737045411fc4dc83c51313029e144400d939d939a26f84e6069a63962ca054f61f393ca2d000fd)
def x191d8 (j : Nat) : Nat := (if j<1 then 0x6525d9a24904d89415292e2f4660a546a02949804e92e6012580e3841401982aa92a4d525c84a4901d496028e285512442340a129793064f2c6e9261e3aea93e49204ef2a521754a9a4b94249760e92407125d43a4bb2b5160ad12a2b066119c4a8b94954511aa4e1c508d249035714182e282f524812a4b9398d2068910f412482ca4b09d49727c92a44de58dc44409749204d1ac0e125825c4b0d4714236e2a8d866008a4c28e79317092e42925d820cc2b55d52a91ac2e1e4c2a24ba8349730292e8cd25d4224a8b6496366330539261d244a8ad8d845292e6cd248118cc2b4198224a2c03125ca7c6900b49406692e4f622063a4b954498244330ce125465bc982c4971871a60a52614a24a0598d2071110341e4c27a4b0351983511102dc6619a3cb1d44976583306a525c8424b88279537092407dc551724b0cb19855e92e42dc502a46c1a98d2034f2615d2614e82c1220487860b0e18161e182c33629523e090efd5551e8243be05821e0b06a0e5cc30243d75952a27ac274e480f36aa380580b20b0ec98212890b09039730a230754e20e282c14d05836682c270d50a6b4a0c20581408a4094160a314a94d05870a4302408585002c22821602c0b0ad8e4c260ac0b105802ceaa6e1048119ec01d05823e53047ca54878243b94572707b0a74858081c985904879e7ac0741604f9ca89e3d72328ae6a5b505c02c3ba40818a52c27ce548f02c14e21524042c0801605b20a0a861429052a538121e81aa12005849c130d38121d91aa11c4d63aaaaa50016013bea12935423eeac6e1654ab34a0ae21514082a2d0a480fba98504171307ae429a505c9cb1d805859882c0701606702c3835954ac52a23c848081cb09e05818c6ae500e580f20b8830487a6824070e4c268243ad41863882a471358ebb4a12f5554a70a82a41604810c0a005822a0b0ef0d5c9db2a117418538090ec0854483a904804878452a27c360600243b121204042a441d4c5c20b88929813e72e60ca580f9ea89d29522a8a40881604796a11e1d4240030d389508f98a11cffbfdff3fbfebf7fdbeffbbedfafe7f7fd7f3fbfedf7fdfb7ddef77dbf6dd9f5fd3f3fcbeffbf6f7bbebf9fe3f5c5535c1535915358d535815350553501534c5534c15348153441531c1535d5435c5435c14358143545434c143481435d5405c94058d405894058540581405514054940545405414050940505404c9404c5404c140481401c9405d1105cd105c91058d10551105091050510501104c9104c5104c11048510481101c9105c8635c4635c063480635c4535c053480535d8405d4405cc405c8405c44058440580405484054440480405d8315d4315c8315c03158031548315d8305d4305c8305c43058430580305483054430480305cc2058c2054c20500204c4204c0204802044020 else (if j<2 then 0x91681d011002a0fd070f4380c4270111f8940107c110cc0787d000a6000b8000b02b0bc2deb07517a69d25e8cf4179efcdae64f2cf94fc90e4271bb8b3c3fe1870a3833c0bdfe6fc77c5bd4ddceeb7743b8ddc2ede76c1b4bd966c7761faf6d6ceb0f569a9fd4aea174f7a6ad2de93b47ba2fd10e8273fb9e3ce566b3333987cbc65b32bb94cc9c64b72258fac6fe34f1898b1c4f625b101868c27e10b06d81fc065fdefc77d5be45ecaf3178dbbcddaeebb73eb925c2edf36ecb70db42d836b3b53da62cff673b2ed93ac8962fb0ad80ebe75dbae756d2b41595abed5d6adb553a9dd482a0b4eea6552be94f491a3cd19a883430a12503e8013f39f44f627953ac9cace1a6f135a99fccce63b30d97a4b9a5a52c29554a7650f27d934c97a49923a912c8624051e38e3c6ba34518e8c2c5b22b514289d448220b0f486b43261830ae84b421e0e506282b410e06701d807400dff6fee7f03f55f8efb77d5be7df2af827b83d89e9af367943c55e14efc7773b51d8ceb97513a4dcfce7272f3941c8ae39711b855c12df26f5377dba2dc56dd3689b18d776b5b579aa4d4769a34a1a2cd0a67933999a4cb6655b27190ec6c62f312186cc186052ffd7cebd25e12ec5740b8d5b62d3566ab28586ac0d5e8ae456a2af5556a9a53ca98d480a26503a7cd3cc9da4e026c534c98c4bf25b92b894749ea4892068ee46a231d1688a744821d90cc85341c20910207f43ef1f1cf5e79b3bd1d80e8c7383901c34df46db3659ad0d3869033f19acc94637311981cbe85d42dc16b8b445922be1574aa654229a9450a024ee26992dc94e494242117c87c42e2098fe07c43cf1d20e507043611a38ce864e31c1830bb05a42bd1508a0c4e425e12788fc456212101079c3a21b20d206342f81680aa84d424a10b079839016c08e03080cc00033031d25c9fc4b0bb71429292e21a3481924c3a1198262a2c111261e824b88549208c92ead525c6ba4904c71425e92403d2618e38a1188d20aa9304963481aa490228d2062f26142254578cc336198086910518660670cc32c71422ef2415925c8c0cc10c492096f24121248104440a45161831a413d2486324bb038d4253110284660d9a4b881498366330269c549dc4a8d249765a92e22925cd48cc22971418712a2ac6605224b09f493066baa501e4c24a4b94171423292c07466050a4b013893154e284c62204438a0c449529692e4dd25d5a0cc2b689525ee240edc551ca4bb2e1980191a4129754a4a4ba8289515d1a41046608da4b88b4920b092e22125ca224a9b35d529f12a20e25059bc9932198074930c4de4c5d46a8b849709e3305246601946902d49765e92e4312548a28b09a79609033012525cd50cc2ba89516a92e46521ca324c30d49202092c13125d8138904081207e3303112549a44408189516892e2 else 0x340a25a5322c508f112816314116c3de54064dca108c686c049ec18d808de0829e121cf18c88708802c913c053686908722a6065d5041b011814e2218030127c898cde1045fae0190e111e05df2863ef912326700c746877788680cc210053a42a3435615f2106c359147a03199093c85065f40630ff70992f091d6cc53108c84e116c50b5450d0144be0640f4a63c9700c86421c8b2da1d9923005f190e3e018ddc2106b41602dfc0867848d7a886ba887591588b5e282f71020d80ad4a19e0559147cba06417d1a0f6f8489bc215585808f90aad09a45a83b90a7f0488c046f0415a234057a887dfd531a78c4bc06dec8c6e021b3e9127810e9087b431800047f00c7de40c60f0020f47e8220fd0436fdb422651f810880159731d7a031d65625ffab00233cc0d8084f486748b682409780cb036fe60190bc0319c22c6073a780648790506c05730922f2153c2a0cb619e0431942af60636810f5886012d7219028958b78421d6a1d5867f443cfe000c8bfd44885f4a63302cf06200c7ca18cf2238fe26300e70020d7d79221ec0f3a78064581005af232f2863a703ba14336236020e0c4c7433e221eb8140400d02388980dc450684604c040147262de108b61677416403630d86eb91d21ac8ab222fc898de02581278463a3433d243d41da143b88a90981133c492c0a8147286300a43ec0a81521cf6663e2e18d7c486a05b415026026708d80bb262602ef806360213a43af362642048e06e1848ef10a0ee22a4c495ba625fd0811550340590e2c735843be223b11e6989f6022fe810118edf1613b79231b00efcc312a023810f888f88a78e219c84766235fd020232f848796c3d05967c0844edb498cb6e848c034039f021107021024fc218de029a42be08e62a86016d509453b7c584f35843ce68191c057109120798c18cbf80639a424ecc590e8190cb090cb0923c10193b3263ce48c75e24c72c904bfa04046ce68192fc402678083e018ee2121fa230fe404c97845b65511bc218cc0b78424ecc49dbe08655bc09b50863c8508bd0d8b035c91977fa0910023023e03ada98cedf16138047e0370147d309195f6021f023c8740c85fa44c97c44fb010b8133ca8100ccbfa0404698428f448c990e81917c2434ecc45fb1482819e690ad5245fd0202367340c96223e446808af9249f021127c08449ac21d72923227ca48c8bc4232c24ac467c0679c46be80443e039f5a089b2b221f790c26780b3a1319b810cb092f91187e1d0321f01b7ec0c7b59288708829e5ff3e22a9c6fd08248df7fcca0824053cbfe7c454be30c6f1a092a21088340e91013c2805841913414844b4961d8042140842076168d1128a002041230830042241c581bc54308404e071228552789d4186d154a02409604480450c))
def x191l8 : Packing := (387,3,7,2359386,103,13,1105,x191d8)
def x191h8 (i : Nat) : Nat := 0x4048000b050c190000427c0b6c0ae0f8000000104ef11dc59702504c0002c1800020759179d2161bfc05f1f9c566d19c76b1d2c3080d1a07c04df1a00000003098000c08207790bc000d109d3bd0a68070018000312ec6ee1e603900c583a64be435318e5361509868521b480d14000061f544fe9a2085606fc212022422905f08741ac0000003c0b40dd01e10ec84011cbc52b0e0f51a123465808c85a1c0444660f4c1561b5c0ce444000812a82800f105b000286710ca054a1b085800014600000000307c483404304d4074c330000000c1ff0841038000484ec36f1c287a81ef449f20986a315ec62200000070b948101a6f5f2222844000041c0000000500a40d0002025706b864214c0000002043000145c203f51d0003c61000342b211600150a8000000000011e000081cc00059ff03f0001b45b17c01611c5424e00c00014dc05d0000b5a6c4444144b2c2c0147c7cb0440007013866515700a404048b3520eb08aa5695d0a755101400104110500d38b50100a080
def x191d7 (j : Nat) : Nat := (if j<1 then 0xcf10e13bf579aec5c2b756a2cd588b015e2b6560ab1536a0d39a634a690d19a21422804f49c9362684c39772ce52c8d8f91d23645c8a911e1d42e84d06608c057f4fc9f53da7a4f1ddfbb775ee8dcab8d6f6dadb1b4f684cdd9331961ac05792e65acb0d5baaf538a293f2744d09812aa464768bd13a0d40a7d4ef1cf38e6fcd91a933863cc39772de570aa1422684908e10b1f43c86f8d71922d85309b1242183e8710d0170268420660940d00f0001330942649c6ca0b0c541874ac3246645536a94785422c1330a026430ea90069c914e9a40da95064209034752033292241b508ce49842a9637a7930252481b8cc8a5119128790335f508906c899c930be52a544f206b8ccc250991c3ba413cf245206c91ad9417cfa844e250869e40a6d94158510f54e21ec0ccba19d601211318dc244b7098566d423052a54195806b2b08b85421213235e250829e48a9199501128433450821443dd6d4238c92274264a284c9533c984a1324d21480f4e48a38d510312e219f5088c4a0b128878cb28475b508dbea1145161327ae22275457b6ba8715911d324039c545ccc903919921b12c3136505704c95c6d422e2b243cf545598a11b7d730faa40d46644588c915454195192245b508b70984189710e2b303d9244164a0bfe52066bac251858471e40a230876ab2847cf206cc89857b154787b0eea2508518aa408942123930b784c26489014b952a942c983348192aa11dbd209c01300c1261290a952b520b6013080921f134a116348396f284470505d9643daad30bd028427fc7f4fe5fb3f57e9fd1f9bf2fe4fc5f6be97cef8dedbd6f87ef9debbcf76eebdb7b5f69ecfd8faf75de9fd2f9ef3be6fcbf95f1fdf9beb76e7ecfb9df3ae6fccf97f1be1fbf95f6bdd77abf1fe3ec3f4817154d635915321d6454d5458d535014154d54501535494054c87501535493054c844c15361d2054d304815321d2054c81481535491054d204415321d1054d861c1536107054d811c1535493050d424c14361d2050c8148143205725018158d405056250161581405c954501525454021d5150172505404c532501544c54054531500874c54058d30501614c14058130501524c1404c5305008148140549734408758d106095444181551105095444087551105494144142505105d94044184481105cd20441424811050520441404811060c72441541c9106017218d205c4634817018d87480634817114d825c0534817014d87480532052014d525d84054576101425d84048176101825d44060575101615d44058175101525d44054575101205d44058573101605cc4054973101515cc4048173101805c84058572101605c84061971101855c44058171101525c4404817110182584405096110142580405c5511008148040549760c1205d8305cd31081714c420 else 0x2a743e6105ac2095c0d7b8c6c040101078c50c0aaf41113c18a9815e610c03b2626c097a420000b213210020464200000000000100005023e22502001a0800026c21860c6f60300003e2200701380b50401682016424080000f88801808000004a0c3020152b14d2100078314584812e909c056432837488c866108be314a080073625f90ac8501b2100205748980990802c7a4880134853f090ee910000548802e02701004e210003762005e9093613e2200dd2168d08034c218058442710cec0e90804c8402c04016023244c04c91260748690992206610100a2784ed04271200030d019507a0004620e00c830008f90124ec020b004a828120fd1662d4548002c43e0b80002905e0ad0002dd73ac74e689ced99f28e46c7d8)
def x191l7 : Packing := (137,4,7,3801188,103,11,1064,x191d7)
def x191h7 (i : Nat) : Nat := 0x247800a1c00085000a0de22d610c00000272000f1bc2ec1b90725c1d40191e0508b44d01001a1400000c080000000000042841210
def x191d6 (i : Nat) : Nat := 0x2c08168400e410815871042002c08000003504205c102f02d800181687ab67230efab6722e19d5c1ad9985712ce84403d49524c087481538fc2a520605544430dd636408759153de85089850520443f40a1481524c153f6848171509601039a92021d4255110f4a4814258175103d2542245205d4409dc6949850520443d8542245205cc40fe0509302052050f9a542261205c440f2950891481761039d1302048748153f625092058173103d6151481525cd10b0729d645516354e07ca9549861c153
def x191l6 : Packing := (19,5,7,0,0,8,0,x191d6)
def x191h6 (i : Nat) : Nat := 0x81900
def x191d5 (i : Nat) : Nat := 0xa3390a134a4c28290221e50549302048748153
def x191l5 : Packing := (2,6,7,0,0,3,0,x191d5)
def x191samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc402ee4723402700821075b301c73e21f673,0x516b7a00004108082102532000224212652),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9401c100011c87330c6249c366a4c8c6487f,0x38c8481ffffae3330c6248c164a488c44829),(0x133511089c9ec04010038e7c8738f1078f9c,0x4321b34000011cc010010028831071038514),(0x235800308c800883e07c0f80f83f01f80fe0,0x24960cb3b52cc103e0580f80502f00b00ae0),(0x604a2032204028fc007ff000ffc001fff000,0x5a69404c4ad32e7c0027d000afc0014ed000),(0x8800ec54221107fff800000fffffe000000,0x52a908506683ef6a59000000fffdda000000),(0,0),(0x8a410885023507fffffffff000000000000,0x2c5644af997c0015a6feffd7000000000000),(0,0)]
def x191columns : List ColumnInfo := [(24,0,167,0,7),(2,0,189,0,8),(6816,0,6687,0,7),(1538,0,1725,0,8),(43010,0,43197,0,8),(44546,0,44733,0,8),(54786,0,54973,0,8),(160,0,31,0,7),(17922,0,18109,0,8),(1664,0,1599,0,8),(42624,0,42559,0,8),(47744,0,47679,0,8),(16898,0,17085,0,8),(1544,0,1719,0,8),(42504,0,42679,0,8),(47624,0,47799,0,8),(2208,0,2079,0,7),(1,0,190,0,7),(2050,0,2237,0,8),(44552,0,44727,0,8),(54792,0,54967,0,8),(2688,0,2623,0,8),(2562,0,2749,0,8),(12304,0,12463,0,8),(42512,0,42671,0,8),(44560,0,44719,0,8),(47632,0,47791,0,8),(54800,0,54959,0,8),(68624,0,68783,0,8),(1560,0,1703,0,7),(1696,0,1567,0,7),(42520,0,42663,0,7),(42656,0,42527,0,7),(58370,0,58557,0,8),(58016,0,57887,0,7),(57858,0,58045,0,8),(44568,0,44711,0,7),(47640,0,47783,0,7),(54808,0,54951,0,7),(44192,0,44063,0,7),(44034,0,44221,0,8),(35,0,156,0,4),(4,0,187,0,7),(9,16,166,0,4),(19,0,172,0,4),(129,32,30,0,4),(36,128,27,0,4),(20,8,163,0,4),(42500,0,42683,0,7),(47617,0,47806,0,7),(25,0,166,0,4),(14,0,177,0,4),(44036,0,44219,0,7),(13320,0,13495,0,8),(68616,0,68791,0,8),(64002,0,64189,0,8),(56,0,135,0,4),(7704,0,7847,0,7),(12312,0,12455,0,7),(68632,0,68775,0,7),(11296,0,11423,0,8),(26,0,165,0,4),(52738,0,52925,0,8),(54785,0,54974,0,7),(134,0,57,0,4),(2592,0,2719,0,8),(52896,0,52767,0,7),(13328,0,13487,0,8),(3080,0,3255,0,8),(168,0,23,0,4),(4120,0,4263,0,7),(1152,0,1087,0,8),(6160,0,6319,0,8),(47776,0,47647,0,7),(44548,0,44731,0,7),(152,0,39,0,4),(1032,0,1207,0,8),(6176,0,6303,0,8),(162,0,29,0,4),(164,0,27,0,4)]
def x191autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x191levels : Nat → Packing
  | 10 => x191l10
  | 9 => x191l9
  | 8 => x191l8
  | 7 => x191l7
  | 6 => x191l6
  | 5 => x191l5
  | _ => emptyPacking
def x191index : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 177 223 4 13 7 2 x191h10
  | 9 => lookupWord 185 697 7 15 9 2 x191h9
  | 8 => lookupWord 39 199 6 14 8 2 x191h8
  | 7 => lookupWord 11 35 3 11 5 2 x191h7
  | 6 => lookupWord 1 3 1 7 1 2 x191h6
  | _ => fun _ => none
def x191 : Forest := ⟨1215,10,fun j => x191samples[j]?.getD (0,0),x191columns,x191autos,x191levels,x191index⟩
set_option maxHeartbeats 0 in
theorem geomx191 : graphValid x191 (boundsBefore known42623) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_10_0 : block x191 10 0 10=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_10 : block x191 10 0 10=true := sx191_10_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_0 : block x191 9 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_7 : block x191 9 7 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_43 : block x191 9 43 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_48 : block x191 9 48 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_84 : block x191 9 84 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_9_120 : block x191 9 120 2=true := by decide +kernel
theorem allx191_9 : block x191 9 0 122=true := (@block_merge x191 9 0 120 2 (@block_merge x191 9 0 84 36 (@block_merge x191 9 0 48 36 (@block_merge x191 9 0 43 5 (@block_merge x191 9 0 7 36 sx191_9_0 sx191_9_7) sx191_9_43) sx191_9_48) sx191_9_84) sx191_9_120)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_0 : block x191 8 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_5 : block x191 8 5 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_41 : block x191 8 41 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_77 : block x191 8 77 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_113 : block x191 8 113 32=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_145 : block x191 8 145 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_181 : block x191 8 181 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_217 : block x191 8 217 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_253 : block x191 8 253 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_289 : block x191 8 289 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_325 : block x191 8 325 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_8_361 : block x191 8 361 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_8 : block x191 8 0 387=true := (@block_merge x191 8 0 361 26 (@block_merge x191 8 0 325 36 (@block_merge x191 8 0 289 36 (@block_merge x191 8 0 253 36 (@block_merge x191 8 0 217 36 (@block_merge x191 8 0 181 36 (@block_merge x191 8 0 145 36 (@block_merge x191 8 0 113 32 (@block_merge x191 8 0 77 36 (@block_merge x191 8 0 41 36 (@block_merge x191 8 0 5 36 sx191_8_0 sx191_8_5) sx191_8_41) sx191_8_77) sx191_8_113) sx191_8_145) sx191_8_181) sx191_8_217) sx191_8_253) sx191_8_289) sx191_8_325) sx191_8_361)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_0 : block x191 7 0 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_17 : block x191 7 17 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_53 : block x191 7 53 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_89 : block x191 7 89 36=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_7_125 : block x191 7 125 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_7 : block x191 7 0 137=true := (@block_merge x191 7 0 125 12 (@block_merge x191 7 0 89 36 (@block_merge x191 7 0 53 36 (@block_merge x191 7 0 17 36 sx191_7_0 sx191_7_17) sx191_7_53) sx191_7_89) sx191_7_125)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_6_0 : block x191 6 0 2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_6_2 : block x191 6 2 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx191_6 : block x191 6 0 19=true := (@block_merge x191 6 0 2 17 sx191_6_0 sx191_6_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx191_5_0 : block x191 5 0 2=true := by decide +kernel
theorem allx191_5 : block x191 5 0 2=true := sx191_5_0
theorem tablesx191 : checkedTables x191 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x191 0 0 0 = true)
  · exact (rfl : block x191 1 0 0 = true)
  · exact (rfl : block x191 2 0 0 = true)
  · exact (rfl : block x191 3 0 0 = true)
  · exact (rfl : block x191 4 0 0 = true)
  · exact allx191_5
  · exact allx191_6
  · exact allx191_7
  · exact allx191_8
  · exact allx191_9
  · exact allx191_10
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl191 : Impossible false (graphGoal 1215) 10 (vars 1215).toFinset := plainA (q:=191) (prior:=boundsBefore known42623) (before_sound known42623 valid42623) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6847 : Lower false (varsX 6847) (graphGoal 6847) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=0) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known6847 := extendKnown known42623 11 [(6847,[]),(1887,[133,117,101,33,48]),(14175,[131,67,99,116,50,33,16,80]),(8059,[128,64,116,81,96,49,32]),(17275,[130,114,98,81]),(17390,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6847 : Known false known6847 := extendKnown_ok (m:=6847) valid42623 low6847 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low18111 : Lower false (varsX 18111) (graphGoal 18111) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=1) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known18111 := extendKnown known6847 11 [(14143,[135,50,65])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid18111 : Known false known18111 := extendKnown_ok (m:=18111) valid6847 low18111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17087 : Lower false (varsX 17087) (graphGoal 17087) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=2) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known17087 := extendKnown known18111 11 [(17087,[]),(9535,[133,117,16,64,49,32]),(4959,[133,117,101,33,48]),(2415,[128,16,64,100,80,113,33,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17087 : Known false known17087 := extendKnown_ok (m:=17087) valid18111 low17087 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2239 : Lower false (varsX 2239) (graphGoal 2239) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=3) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2239 := extendKnown known17087 11 [(2239,[]),(4927,[131,65,50,114,81]),(6975,[133,117,16,64,49,32]),(2399,[133,117,101,33,48]),(9567,[131,67,99,116,50,33,16,80]),(4975,[128,16,64,100,80,113,33,48]),(7023,[130,33,113,98,66,16,80]),(2427,[130,114,98,81]),(9595,[128,64,116,81,96,49,32]),(9703,[67,132,99,82,16]),(12782,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2239 : Known false known2239 := extendKnown_ok (m:=2239) valid17087 low2239 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2751 : Lower false (varsX 2751) (graphGoal 2751) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=4) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known2751 := extendKnown known2239 11 [(2751,[]),(1343,[135,50,65]),(18751,[132,65,48,80,113,32]),(1375,[135,101,50,33,16,64]),(18783,[132,67,100,84,48,33,112]),(1391,[130,50,97,115,82,16,64]),(18799,[128,97,65,49,33,112]),(1403,[130,50,81,115,98,65]),(18811,[128,80,81,67,96,113,32]),(28135,[80,132,99,112,32,16]),(6638,[50,117,131,49,32,65,96]),(28142,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2751 : Known false known2751 := extendKnown_ok (m:=2751) valid2239 low2751 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1727 : Lower false (varsX 1727) (graphGoal 1727) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=5) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known1727 := extendKnown known2751 11 [(1727,[]),(2367,[135,50,65]),(7007,[135,101,50,33,16,64]),(9583,[130,50,97,115,82,16,64]),(4987,[130,50,81,115,98,65]),(17341,[129,82,97,48]),(14318,[50,117,131,49,32,65,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1727 : Known false known1727 := extendKnown_ok (m:=1727) valid2751 low1727 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42687 : Lower false (varsX 42687) (graphGoal 42687) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=6) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known42687 := extendKnown known1727 11 [(42687,[]),(44351,[135,50,65]),(47967,[135,101,50,33,16,64]),(53087,[133,117,101,33,48]),(44923,[130,50,81,115,98,65]),(69499,[128,64,116,81,96,49,32]),(60349,[129,82,97,48]),(69565,[129,80,48,50,114,97,64]),(42983,[115,83,82,130,99,66,16]),(45031,[84,117,80,132,96,48,32,16]),(53230,[50,117,131,49,32,65,96]),(60398,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42687 : Known false known42687 := extendKnown_ok (m:=42687) valid1727 low42687 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58559 : Lower false (varsX 58559) (graphGoal 58559) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 36, 1, 9, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=7) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known58559 := extendKnown known42687 11 [(58559,[]),(64191,[117,67,32]),(51007,[133,117,16,64,49,32]),(54079,[135,50,65]),(46431,[133,117,101,33,48]),(43887,[128,16,64,100,80,113,33,48]),(54127,[128,97,65,49,33,112]),(48507,[128,64,116,81,96,49,32]),(43951,[113,129,97,82,32,65,48]),(43453,[129,82,97,48]),(64445,[129,80,48,50,114,97,64]),(49646,[64,132,49,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58559 : Known false known58559 := extendKnown_ok (m:=58559) valid42687 low58559 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58047 : Lower false (varsX 58047) (graphGoal 58047) 11 :=
  strong_full (q:=1215) (rs:=[2, 1, 2, 16, 8, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=8) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known58047 := extendKnown known58559 11 [(58047,[]),(47935,[133,117,16,64,49,32]),(69439,[132,65,48,80,113,32]),(44383,[133,117,101,33,48]),(74079,[132,67,100,84,48,33,112]),(50043,[128,64,116,81,96,49,32]),(58235,[130,114,98,81]),(69102,[66,114,132,49,32,81,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58047 : Known false known58047 := extendKnown_ok (m:=58047) valid58559 low58047 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44223 : Lower false (varsX 44223) (graphGoal 44223) 11 :=
  strong_full (q:=1215) (rs:=[16, 1, 2, 4, 1, 1, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl191
    (index_root (g:=x191) (i:=9) rfl rfl (before_sound known42623 valid42623) geomx191 tablesx191 (by decide +kernel))
def known44223 := extendKnown known58047 11 [(44223,[]),(44735,[84,115]),(52927,[117,67,32]),(54975,[116,83,32]),(42815,[135,50,65]),(44863,[131,65,50,114,81]),(53055,[133,117,16,64,49,32]),(60223,[132,65,48,80,113,32]),(42847,[135,101,50,33,16,64]),(50015,[131,67,99,116,50,33,16,80]),(58207,[133,117,101,33,48]),(60255,[132,67,100,84,48,33,112]),(42863,[130,50,97,115,82,16,64]),(47983,[130,33,113,98,66,16,80]),(60271,[128,97,65,49,33,112]),(69487,[128,16,64,100,80,113,33,48]),(42875,[130,50,81,115,98,65]),(44411,[130,114,98,81]),(60283,[128,80,81,67,96,113,32]),(74107,[128,64,116,81,96,49,32]),(44989,[129,80,48,50,114,97,64]),(69095,[84,117,80,132,96,48,32,16]),(69607,[80,132,99,112,32,16]),(48110,[50,117,131,49,32,65,96]),(55278,[66,114,132,49,32,81,96]),(69614,[80,84,132,49,113,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44223 : Known false known44223 := extendKnown_ok (m:=44223) valid58047 low44223 (by decide +kernel)
def x255d11 (i : Nat) : Nat := 0x4c88f1a284060808057fc10
def x255l11 : Packing := (1,1,6,0,0,0,0,x255d11)
def x255h11 (i : Nat) : Nat := 0x83800e3000c4814a28004c8280a80000001288072170108490827828b80af
def x255d10 (i : Nat) : Nat := 0x45e30d8a0c818140206a241064060040e1d00022e2050212800011103640685c1c10c04820d80802c260c58342c08544800504d78c021e1c0400087480d0b4609048382010050c640685848241c10080283c30342c27180a0c10040161a18161413918d06080200bbeabda425b7f9a15910f2e85d003ff5cc10ffd30043ff55010ffd42042ff60810bfd83042ff61010afd86042fb60810bbd84042f760c10
def x255l10 : Packing := (11,2,6,0,0,10,0,x255d10)
def x255h10 (i : Nat) : Nat := 0x202000000380606397c47943e48901800297152608243b403c8700800082947f118001c3285b90ec41920000002c8c93c003182c4b157140c72130003050003410000003d1e537c6746e01704d44505c06907602c00110950282796c162857834001c1c40e912986200108200000514a043340004082000000144000
def x255d9 (j : Nat) : Nat := 0x5e531855aca28df80d3485b10aff144a303b08ac2279015e40503fc243f74904e6f88cfe84131fd4095e405a6492532492f60487f42099e4055ba01ef5025bee9209cfec0916e8073ee9209c7a808879e449669080ff091d4057d0116e807bd81208116988c51b8c1680a003e0241874390b410783414020482f090886c0001070642100bd2d8b0ab2a8e8a9f66f9864f8f625819f3761bf6b59860d6e54d414ad153dcdf324ab2487719c4f0f42b054002c92cc12c983ca94cb84cc11eb80cca3ca134aa60cad8a94ab9b89846b856a15aaa38cbc0cbc4a168b846cad4986aa134b9e6c95a9836b9d0c958b9c8a146a956aa58aa46985aca3ffdbff7def7ddfafeffcff618106101060c10608105cc10550104c010
def x255l9 : Packing := (36,3,6,524295,51,10,1055,x255d9)
def x255h9 (i : Nat) : Nat := 0x4200118060050390014553e041769a0
def x255d8 (i : Nat) : Nat := 0x190040e18320081c3064010386000418002029b9673502d1e1900abf6897361810afb6a57360810ebe5c13061810efa5c13060810eee5c13061010cfb649825cc10aef68973610108f72a54260c10
def x255l8 : Packing := (8,4,6,0,0,8,0,x255d8)
def x255samples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff981017018004f68c0077c4481d3200821075b3090d9a33c9401c73e21f673,0x7892404800340000422904481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff848d107200410000f6f7c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x30db990d14ace6f3090c0004081330c6248c10420400804264a488c44829),(0x6401400c52820973fe802081863c4010038e7c98c38470f188738f1078f9c,0x2c32446006102010020520810028401001002898838470a18831071038514),(0x260480809b801730000070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x50c43b9c31a55a2554aa470c07c003e0580f80407c03005e0502f00b00ae0),(0x1a6008010938f6000000380ff8007c007ff000ff0007ff000ffc001fff000,0x7298423ce4aa5daa954b803e8007c0027d000bf0004dd000afc0014ed000),(0x112a780a404008c01083ff000007fff800000fffff800000fffffe000000,0x469af34f68936130486f2a000006a59000000fff6e800000fffdda000000),(0x8c00720041000000003fffffff8000000000fffffffffff000000000000,0x7cf2466f2eb53190cf6f3fffbf7e8000000000fbdfbff7fbd000000000000),(0x6102a0847602080009083fffffffffffffffff00000000000000000000000,0x5384108b0966c9ecf9780d5effd795a6feffd700000000000000000000000),(0,0)]
def x255columns : List ColumnInfo := [(2,64,189,0,8),(33,0,222,0,7),(1048,0,1255,0,8),(1184,0,1119,0,8),(17,0,238,0,7),(52800,0,52927,0,11),(54848,0,54975,0,11),(58432,0,58559,0,11),(64064,0,64191,0,11),(43010,64,43197,0,8),(11266,64,11453,0,8),(52738,64,52925,0,8),(57858,64,58045,0,8),(58370,64,58557,0,8),(145,32,78,0,4),(64002,64,64189,0,8),(73,16,166,0,4),(162,64,29,0,4),(41,16,198,0,4),(1096,0,1207,0,8),(148,8,99,0,4),(160,0,95,0,8),(12,0,243,0,7),(177,0,78,0,4),(54786,64,54973,0,8),(59393,0,59646,0,8),(52801,0,52926,0,7),(78,0,177,0,4),(193,32,30,0,4),(90,0,165,0,4),(84,8,163,0,4),(54849,0,54974,0,7),(0,128,91,36,7)]
def x255autos : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]
def x255levels : Nat → Packing
  | 11 => x255l11
  | 10 => x255l10
  | 9 => x255l9
  | 8 => x255l8
  | _ => emptyPacking
def x255index : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 5 23 3 10 4 2 x255h11
  | 10 => lookupWord 27 69 6 12 6 2 x255h10
  | 9 => lookupWord 2 13 4 9 3 2 x255h9
  | _ => fun _ => none
def x255 : Forest := ⟨1279,11,fun j => x255samples[j]?.getD (0,0),x255columns,x255autos,x255levels,x255index⟩
set_option maxHeartbeats 0 in
theorem geomx255 : graphValid x255 (boundsBefore known44223) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=0) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_11_0 : block x255 11 0 1=true := by decide +kernel
theorem allx255_11 : block x255 11 0 1=true := sx255_11_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_10_0 : block x255 10 0 4=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_10_4 : block x255 10 4 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_10_7 : block x255 10 7 4=true := by decide +kernel
theorem allx255_10 : block x255 10 0 11=true := (@block_merge x255 10 0 7 4 (@block_merge x255 10 0 4 3 sx255_10_0 sx255_10_4) sx255_10_7)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_9_0 : block x255 9 0 27=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_9_27 : block x255 9 27 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx255_9 : block x255 9 0 36=true := (@block_merge x255 9 0 27 9 sx255_9_0 sx255_9_27)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_8_0 : block x255 8 0 1=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx255_8_1 : block x255 8 1 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx255_8 : block x255 8 0 8=true := (@block_merge x255 8 0 1 7 sx255_8_0 sx255_8_1)
theorem tablesx255 : checkedTables x255 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x255 0 0 0 = true)
  · exact (rfl : block x255 1 0 0 = true)
  · exact (rfl : block x255 2 0 0 = true)
  · exact (rfl : block x255 3 0 0 = true)
  · exact (rfl : block x255 4 0 0 = true)
  · exact (rfl : block x255 5 0 0 = true)
  · exact (rfl : block x255 6 0 0 = true)
  · exact (rfl : block x255 7 0 0 = true)
  · exact allx255_8
  · exact allx255_9
  · exact allx255_10
  · exact allx255_11
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl255 : Impossible false (graphGoal 1279) 11 (vars 1279).toFinset := plainA (q:=255) (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2303 : Lower false (varsX 2303) (graphGoal 2303) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2112,0,2239,0,11) (by decide +kernel) (by decide +kernel))
def known2303 := extendKnown known44223 12 [(27127,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2303 : Known false known2303 := extendKnown_ok (m:=2303) valid44223 low2303 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low17151 : Lower false (varsX 17151) (graphGoal 17151) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (16960,0,17087,0,11) (by decide +kernel) (by decide +kernel))
def known17151 := extendKnown known2303 12 [(17151,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid17151 : Known false known17151 := extendKnown_ok (m:=17151) valid2303 low17151 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2815 : Lower false (varsX 2815) (graphGoal 2815) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (2624,0,2751,0,11) (by decide +kernel) (by decide +kernel))
def known2815 := extendKnown known17151 12 [(18911,[99,132,84,48,33,112]),(28151,[67,80,100,131,112,32,16])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2815 : Known false known2815 := extendKnown_ok (m:=2815) valid17151 low2815 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low6911 : Lower false (varsX 6911) (graphGoal 6911) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (6720,0,6847,0,11) (by decide +kernel) (by decide +kernel))
def known6911 := extendKnown known2815 12 [(17403,[118,130,81])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid6911 : Known false known6911 := extendKnown_ok (m:=6911) valid2815 low6911 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1791 : Lower false (varsX 1791) (graphGoal 1791) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (1600,0,1727,0,11) (by decide +kernel) (by decide +kernel))
def known1791 := extendKnown known6911 12 [(17405,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1791 : Known false known1791 := extendKnown_ok (m:=1791) valid6911 low1791 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1279 : Lower false (varsX 1279) (graphGoal 1279) 12 :=
  strong_full (q:=1279) (rs:=[16, 4, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (index_root (g:=x255) (i:=0) rfl rfl (before_sound known44223 valid44223) geomx255 tablesx255 (by decide +kernel))
def known1279 := extendKnown known1791 12 [(3579,[99,81,115,130,65]),(18941,[82,129,48]),(11774,[117,99,49,32,65,128]),(18942,[100,49,128])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1279 : Known false known1279 := extendKnown_ok (m:=1279) valid1791 low1279 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58623 : Lower false (varsX 58623) (graphGoal 58623) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 36, 1, 9, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (58432,0,58559,0,11) (by decide +kernel) (by decide +kernel))
def known58623 := extendKnown known1279 12 [(58623,[]),(46559,[118,133,33,48]),(43517,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58623 : Known false known58623 := extendKnown_ok (m:=58623) valid1279 low58623 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low58111 : Lower false (varsX 58111) (graphGoal 58111) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 16, 8, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (57920,0,58047,0,11) (by decide +kernel) (by decide +kernel))
def known58111 := extendKnown known58623 12 [(68863,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid58111 : Known false known58111 := extendKnown_ok (m:=58111) valid58623 low58111 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44287 : Lower false (varsX 44287) (graphGoal 44287) 12 :=
  strong_full (q:=1279) (rs:=[16, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (44096,0,44223,0,11) (by decide +kernel) (by decide +kernel))
def known44287 := extendKnown known58111 12 [(44799,[84,115]),(42975,[118,101,133,50,33,16,64]),(58335,[118,133,33,48]),(60383,[99,132,84,48,33,112]),(48119,[115,82,98,131,66,16]),(69623,[67,80,100,131,112,32,16]),(45053,[80,48,50,114,129,64]),(58365,[82,129,48])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44287 : Known false known44287 := extendKnown_ok (m:=44287) valid58111 low44287 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42751 : Lower false (varsX 42751) (graphGoal 42751) 12 :=
  strong_full (q:=1279) (rs:=[2, 1, 2, 4, 1, 1, 2, 4]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl255
    (cut_root (prior:=boundsBefore known44223) (before_sound known44223 valid44223) (42560,0,42687,0,11) (by decide +kernel) (by decide +kernel))
def known42751 := extendKnown known44287 12 [(42751,[]),(47871,[117,67,32]),(42999,[115,82,98,131,66,16]),(60413,[82,129,48]),(69629,[80,48,50,114,129,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42751 : Known false known42751 := extendKnown_ok (m:=42751) valid44287 low42751 (by decide +kernel)
def x383d12 (i : Nat) : Nat := 0x5a2c1286c92b8843c484150a450271300c12251208c44210334401f0f074381b0d06430170b05402080a04c24110803c1c0d065c160a048200e063014080301004006f6f1294761d803fe887fd30ffa81ff54bfe087fc30
def x383l12 : Packing := (6,1,8,0,0,9,0,x383d12)
def x383h12 (i : Nat) : Nat := 0x146100000004baed31538440c1ffdeb0f6183e06000a8c0b07e49b14e320002839810909504c00050a76d4868c1000068bfa4c000000000083709a00000028a800190dc14911063a64efd100000000007aed45560ed2b90b0000000c289281131c40021b72000000000000020b2031241808c49c032807502389b83e000b92e08c0009128422147ccdc24b299c6cd4889ec33b15a259e00915b38a81356660ac43d82820ca83712145fe1b30b939f002000f12fa0743b0039c1d0b445d640f035b1000194c0000001045e02d07502ddb960a713a47c0008c3e89f81470c20450413471001400820430050b11c35410032cc082000283
def x383d11 (j : Nat) : Nat := 0x6ffff64904012a7fcc020224b7f64e130f024d2bfafe40a032481e0294604de32d22ffc68564541281bff0144081a63d8b819409fff785350254fffe02f017139c88000001547ebf703c5804a327e1f3e4c0082f1cf1be89c1b0004ec7062909778125ffe0ca5ec0085e09fb70ef058a20000dc5fff81aae0670005ffd7000400fcfea2002aaffec8001025157aa85702d1ae1e9c8400000003ff3fc7f8990414d7fe7f00184005c15620000af597d0ca8a688f6fe300022685f554114bff14d63033dff85f00ccb9c800caef024afe865044340378275f91338fb400f3f404a0073c6fbb0870004c004ff0178007139c9224a93c6a8dbca09400dffea8819f3f0e0085a338ff5f0360058d98227afe40ec8c00004fe7ff61784cbbc09000001f000000138ffe14e3f504e40cc185538033003cfc0464a86819c66172268a04d84e148820c8404551112469184211b10d424450f4fc3981c641855454d52428511404f1394b0a82900c2809c090941f0c00486a170520e0086017c5e16e06490464743a41c6518c6289d565552c42c2487612872188442d0320f8340b1303c1762a1695855d3d4084844d304b51c082018260882e2d96540436024cd324c51488e038120a0bd2b11e2c86d204404a88a210da2550438caf100d43b0f8371270f0b8348900001c0697a94f9158e38c58a386e83a81a7e378274c7106d06b169b6616155e45835535255044aa44941c3e83ca39b3563403132e32b02a526c2151e51b618713f11d0dc0c607204902300090414ae2e57352b8391cd48e6253032c3c90c14ae12560729829619cae3248352c189609ca632570329859605cae2647132a8b9589cb06a48172c0994c04a40d98306c1a32059b060c8126c3c36199b0251862641a8481c2e0d5418ec107482830c498202c18ffffefeff7fbfbfbfefbbdebf549404c1100c010
def x383l11 : Packing := (48,2,8,655366,67,12,1166,x383d11)
def x383h11 (i : Nat) : Nat := (if i<1 then 0x46d2ef6d0e6207b000048f90000000054c6c4bb48ca6097d01f000000000000000000000000000000000c5ec8a4109c785902e500e5a00a0101c8f8501720d3781340b4e400a0ec00008421a0f450b500000000000000fe0000e073000050bcc298100850520000700e000020f098d1782814190000208e000062400000d60b0000b0321898c03bd8fe000072fc2033a028302eb0e1687968e540e720fca88a06d5d26d8087ea25b007a092e05b2009000000d5000008cb789a508ad0a1146feefc007882b700cd901988f070b8b0b9e0e320cb00d9e02a02cd80f500009039d00b0000000000003018c0eac65e48cd88655081d242041520ed982788a5fc223a4bc702a3026cd5d06d3084b0a4205624eb3ec6220b200110e47053b0d4d0ef8e90501120aec0756088e429327e20294067fa66306cc042f0f26098e03754c58ced6068122500437409000090bed0c8609500a9701428e870bf207fa08b00007072c0c790c3606a22c5a2e2d825a090d0e8da83f0699884f07a0000a0890000e047000000000000904d000000000000f071e05700000000361a000048375015302d30201025d010f410b8d8006240fab0ac0000000031020000b03e000014ca280300008079a8bec065d016e013104a000084180000dec50000385a000020abc8c6705050e0d87c282e5658a038d0a030dbe866b816ec277c0eb026303500e92005bed2d02356216076e0042d00b08f92226427686228b3e03a70307609e226a02f80d040aaca6c00baeac5064d065c528fe25c205de0b00000e0120849a027e09a204ba836c0589830486896dbb0550000000068a30000001d0000602c00000000000000000000f0bd9618b04e5021b083208d10700000f6960000000060cf0000206e000000000000f0c4589e9692e0b6f05aa0c0c8b1c886d2d792212a9b0415c004021000008902a0400000000c20c000a01b00000c0130001800000c40000c33002800420000000001c014000500000000004000008000000b00130e1800000060060820015021c00802000002810040000000004000120000000c10000000000000c03070000010000002400000002800800c70006810000440520401810000000020001c00030000800020c00010830040420001800002040c10010800800440000802800000c10010490c900000004000004000100000000000000b00000000d00000700108410000000d1400000010020000050400c00030000c00800000000030800c000a0800000000000800000010000cd00000000000100000c0020000080800030400000000000010000000800000040020071000010020000000031400000840000000000000000000060000002000800000000000000010802000000000000400020000000001c00000000030410000010000c0000000000 else 0xc2d40000e85f900d000010d80000a0d684eec100e44c70cef0de20021022603fd43900000000809908f2000000000000000000003811109f82992cda18eb909bb49b00a764c760c6304f0000c29400000000d47a00008875220e5622802ba8a0ec6c489f80bb08350000f0a5a60fc01a40df507d26e70a21b0c9e03d820c882df0f800000000000000000000e09e2091c2acc060c6f87031929ca074f422e0630cd022391e9be01ef05ffe6fe490bc9280820a90e890040b84d760d7e041f8f3383da210100fe252de2c9049a8316096d0fb70f644fc28531502da98a6da24e7f8b4a0f3540190cc407e5048b05e50d2429090347405206f000000000000000080fd0000804c229b70cabeeb80c5dcf8c05c40dc1287b84b2860626600001894a897407c9c2168da2000000010240000e0f1e8faa0f9d0ff0059fae56054b09314e2c0a3f0e24afc08f12b00e0ddb0c140a64061e09d0000600c886fd08508d65094d8c1e0ebd82140f7f682e06b1040682ca869c0af64205876442c203c60662086b08038290000d0b2cc83701b808c30ad00a2841e0000783300000000204420b1c077f8d500000000000000007e21dacd0000e8f49006b8920000b858000000000000000080ee401c203600000000a8f70000e885e046285120c280b3b045205120da8064000000000000760e70d15848000020b7f0a810031)
def x383d10 (j : Nat) : Nat := (if j<1 then 0x53d58f2b3c28eb83a90e78393ce293768dc436c0d91359cd2233fccd432b8c9b31e8c563090c122ff0be22e5cb622d3cb392c18ada2a50a812994a3427f09d626f4992261496024dc8fa233c89b218c82b20607d21e947751d3c7121bb86c21a9467a198461f17d85bc162455014a050a13844ce128c480117842b0fd83d40e4037d0d102f70b4c29309a022507f01d106b417a053c118039c0da031c0b40284066016404600cc020003400095304255c6295717a5661894973e525d195317a5661095313e55c9595714e564629597725641695724a561d695654e55c4f94875a52618959072564df95718254c5595987e554d394918a55c5c95935255cd195515a55c9495315e565d4959872560569531825589795985a5641f95716a5662295656a55c0e9487565641894874652610949772558d394937da61d9688739a5cd169970da26102d9034b6622716559f4c5d698305a4c602d983645897698724b65d12d974a45c0f69516e45c012d9179a6055698744b261691604cb64cb68970cb641c91874e154d568972634c21716356164d490985da24e0688746364e17d9775a661669814da261f2d977235c9391206da649b699181a65d169811a154da91935da609490815da5c112d976a4605791725cb65cc7d7174b659391706da6608912060b655291315e45c1a698750b2614689744b65ce68816da65c969875a45c132d926da21d985313db5c5e689862324992d9649a605a7d4179a615369534a465d32d9169a61da698159a262269916da481b688169a6622689871a6155699381a4c112d987244857697180b646068874a154d3698121a604769706e421d3698569a24602d9189f64dd69816da21da8d718646593698704b644f69826e35c962d916cb64927d4181a6095698559a245b69874e35c9a90814e365e191514da66182d9131a61c769985245953716555a61c391814c465d11198004261035870c4660421932d765c21098604660d259784465c519954a04c571197384660f3d861cf604a81534c464d23d8618464e015963196053618120f644a59900d665c3119548a640d89724ca640051877595c1b5d8205625c3259235760805d820c42614119039764c23d8621d54611d9411e4c5d49850c465d2893085461017553844649b119820f244a59700d26141119180466223d86049648b019715061434d8408c61c305954816545458508264d2398609560830d9217ffffeff7febfbff6fdffb7edfbfeffbff7f6fddf7bdf79eefdd7b7f6ded7d7faef3fe77bff7fafddf7bdf77edfcff9f73de6fc7f4c1524815261d405c5405c140505404c5406193060930605305c5305c130589305813054530481302053060d105cd104c11020d101cd100c1100411061830604305c4305c0304c030204301c43060c10608104c0101cc10 else (if j<2 then 0x294b87d9e18125a4c0d94ff1102129ffd080042d275fc88cc7d08e32d5a4ca1d3e240ca037fc0042243d78c55d1318fe00895fff0e105d3009081b01d1fd4e20010e7b410dc82500e01ff0000d08c5060b310c019f4978ffef011359ed040b978a3df8cc2818025730485f341944407c3d214551e90632fde35400ce503bbfd64a14479ebd08198bf837d44a8044d40dfc218819dbe3fb489689a11fd4cfa8410a203b8c33a15081a8f482827f7a6d123c1044da94fef4220672ff8fda88267aebe1881981af92c46490191206189cd483f27d448490174c4a3c749363910d1e90630ef8780361ff911abdb383b610b5f13eba1b0203547ec9e824206907fb855000c14449c5d78852e1c8ad47cc58b8f0853da088ff1343221a0f764452011fdd10858604791431a4bbe9cd63940d22e1078c2057cbebd8aa49a3359ed0427c0af2080034400017c0bbe142f9501b60af51a91d3e015c308f48d5aaf7fb0e401527fcb0c8f4880466b0029f743c2871a470e26782bd46a479fea3fe0240932f282e30219bffe705d071346fc66140c0128a067b410f6821ed040efce05fa1e10d25033da087b410f6821ed04281c0e41a23c2e3080f21c82d0944b4cc4ab92ce2024c969130ec472814036174444546487c211c18800fa1ed3c6140189d9240742621c03786b6b0562abd2aa65822014464402444813026719d05a6686b1984442810b1861861dc22c9108c4700420840a0a125175b8d0fa8491844c10c39881a022281e0f2a006d41e96524896817824458500ca4084731d22819a8e88710c116154208188740800f0dc18d0622c43623134400c041dc3ab410e64af12e2d12b4c795a0211a4c89017184ac703384681383b00e220c8188a0d08a490d1a151cc378b28a70f0bc1ea0a42d09180e0385108e88686e0fc0813f0686165689024b11a661a3108784014819060ac461ff0584347c17695a070700e43604a0d216e0307c8499649f2066215043f30f06e0d2881070d40f81d83606a0bc2683ac4801c0004c00c0ba6cd9a72682994e633984a5e997565c39642569950a523942e4f4936a4c0925246e917643e908e4048f223ad8e4e3788d5a32f8c462db8aca27f895e23f88aa204874a1ba866e175854e13484520f9833a0b682ba09281f205780ae00f7fc9fd57ecdf9e7e21f357c11ef47b11ea87959e2c7871dfa7741da57601d607501d0e73d1ccf728dc83718dc4870b9c0b6f8db9f6dfdb596ccdb046b9dac76aa1a8a69c1a3267699c26695979652991363e18c86259878611981b5fd17d85eb57775d2d7275c216be5a8567e598962858455e256a558f559d51e53ad4d2529d49851f1456510541650013d74ead37c4d3d3384c4d2ee4b052a149c5249489120c47b91ce46bd18e455112744210ea430108b413901e402cfe43efcf8 else 0x2f02307bc14abdfc307b7cc69f38145081a23fe881901ef881084fe013a08547682bc08c9d1ec34420438ffa252847172f00810a97f7d114b9618fbd23190f884c4f4813469ff92003369f84009499a625fde088bd9571903cb803233ffc88b000204443891835f70913be00324f1dc2c8dded86c01980f500a327ffc4d185021e1eaea8810aefea20a20021c3a7c2c0199718110f88498f25040429bfca5410010e5d2cc70e2c3a137e3d9104747e100211bfe003255f98051aff1044a87d89218cffb7184019ca08c87321269f5983a927e8501b41251f09a0f6b1888a174c4a3578cfd210bcc0c3ed2197fffc5a3080e0854206d53f4482041535911d8fe7e60441647c503243e1da8c958204200811a1fe7da913334029feb118511ff95848330f73e7400488bfa10023cf83f022cfaa80230379971f140d0bd62a22ffcc0411b7fe140a09234f15091b7a4be1159fe903cc780896fed48a13dfa9b0021400d7b0dd44fa02228de1002133aacb806633f2003a90193ffd31033c7db499213760a107c56322af8e408a3437a247fe881e00c000d411ff87d00ad07f708804df7f90499f420643be040300a502e0cffc28cfdb7f8547a889a4efe012ede01555805373f061200010e3fa8822a3a7aa090010e1ff850001986fd2c68238d7c222ebfff2a428517fc9ba8410a1f71f44c041257e97c411b32a943297ffffd6190000804d75e700646fe1268cb5ff104ccfcff9208000445cd025064fff4c40ce5fc1be9a60a06959f41125d9df21a1483f1fded08000440da5ff84202501a17fb00de7c02061295c0253e904197a409b4cc798240ffe02840cc6e4128bfc82002175fe9da0021adfcfcc2a1437bfa24010219fec02de721f20a0b1e1050cc027924e7086cfd42065dbea0a2100a657b3a1c08577de82042d61ab1a8fe008b97fa808bb9e8091a5dd54108077c7d86cc024403fc56420a194fc88518f58c28b9e184a8033f3ff4214410a1e9ff6e9016358512bd7c54440093b110c3e3680033698595029012ff94541840888b876c06054c5fe564c819b9f40090801ff67a58611f58220371f4120e0af50952483fd0610217de28040850fffc0150dba624048da7c412d9a924df302a3bbec500))
def x383l10 : Packing := (259,3,8,2490403,102,14,1251,x383d10)
def x383h10 (i : Nat) : Nat := (if i<1 then 0xa087405c06c402f82ba83696c9af3800020581025c55122e2801908bb4a8000000010279141156dc2ea0bbe97b882043dd877c927e075027bc12c0b20000c016c9d214d30d80000000707200000000814000000000000000d18472f34d40000000141af8c80100a06ee07884c906413302cbad3f3a040001ae40000402d0000804382d35bc90b84270000000000000000000681fc17870980000000bb43422000000000000a2dfe230820e832a09a03edc80b169224400040122194e0c0000287fd0fc00000000000c2fc0066246c696615920d2807000080e051ead5198540000e26380880000000413941e80006b680002444e038214461a9a16103679540003456d853a85c0003c8b402b30923252c21f87c50cc00030140000615e41db244ea872034000083a461b0000000361c800000017177c2d8000713ba28f13bb09e00016c989b88095c8fb40600003132000000000004c17112c62370304c35b963604cc50a20cf77192b6d10e82a50f0631740ab2950001006d63651b4110921c40000000f2980000000000010742430000604d10a3d0b69457501415540fb0317108901300f1ca26ba6b88be0286581671518f8301a3a00000000f1eec2f0000804902c4e42645e5148000044038c3e0620eec85cb8165902a0d5e1c12bbd05e0184c438cb87943ad3ec2048a828787ab3655c4281941faef8ada8b374840002503606e46fd880104d7081c13778dcc2648bd60afae8f62d08a90000850800014517189001e8024846210400000007c65112471b40000000000000000347bc2107f6240000782c299202d9807d850c16ac016aa2590a10aa000000000000000000000000000000a08c449853210ebbae1437c85278ed02f9847369f1019400433e11227d0d60a563100bab4d2307d4428041e866819fd861848f089b0acc252897c044e037053e073a08b90a64000079818df30e02fa09fe0b0531d0591863ad48015abd1424360e4221b80e38a5b0ca72a4841bc7520f4801bc1df04718c7412d064b8c8000142fc44550ab00000003518383346af14c70608008d96be4c4639a02e0003040800000001001810020000001450c61532010002800261020800c000824d0002030000000c00430c020200600000000000108500038300004000100000000000810000000e04004100010d0801800c20000400400000041430010000001400000000010090000020000000010400020c000000000000000b0040020000010000000000000400000001030400010000000000430000000410060001000030870000000000800000000000400c6080080000040002040005082000080001000200000000042040040005080080080001000000040000000041000000040000001080006000001000001000000000000000000001000000000000000 else 0x2d08034fba781186efec4a1842490a80c8847a92012c1)
def x383d9 (j : Nat) : Nat := (if j<1 then 0x5a2c6b4e344b82353242352c282e4709b5145eb04a292e47c9b4afc2152e1f2e2a66aa76942a4e8cb494622e2e0cb491c9950529240a0c34b454330e5eae4cc9b511e6aa4717ae4989b4ed1a346149b4f20f341467a633e32a2c54130ed41512c234ebe2ae0e9632a5c9b4748215244f344d8f34cd8f152ddeae490e342ca7a831e12e485eae50cab46ad634460f34e654130a02352b89b517142604941317e12e300e344409b4375432ea54b2e5cf150dd62ca9cf34a69a302c4f34c68234c9dc30f354130d669536692e474f34268e344a89b4751b2a2d1c30f30234e9d41517d41312c9b42fdeb4e0e5aa7709b4af57b245cf150e423525e3ac079eae48dda635692e48272a27c13524c13449c1344e811503c135255ba63384b4d544b4e341353110b4662626160e942981352d013475d394318894318d34665332e1c19526c134380db44686349516a832933440863483049522d594060bb4a644b4e390b2b112350290b2a588344547b470972616d0aa69c8344f4834021ca630982e01a1ae2e0834424bb4ad90aa38252a271e241764aa47013509891511552a69c5b4b04b34761ba8320134c9d534661d263145b4a259ae01592e238db4464a34ed81352cc135314134e9cd342705b4af90aca9daae0105b4b0a0ae289e2a48de2e48c934154115359032a0202e2e001522c0b4408fb0c292b040642a470734024334a346b44243b4834534a244344342b4e351328011b0807ff3febfdbfcffb7f7bf6ff6bf5ff5bf4ff4befbe7fdfbdf7df3defdebdd3bfbbf7befbebbdfbdbbd7bbfbb7b7fb7baffafbaf79ff9fb7ef7eb7b777f77b75f5ff3ff3f73ef3eb3bf3bb3af37f36f2beffaff2feefeafdafbef7ef7af6eefedfabfebfabf6beebdebdabcebbeb7eb5eafeaeeabea7e8fe7fe7fa3fe3ee2fd984c15264530549714c15226130548914c15265d20549714815254d205495148152645875013161d4024d875009161d4064d71500985c54024d71501715c1405057050187505405c541501315054065d31501904c5405c531500984c54025d3150192619305c1864c15161930481864c09161930205864c1726093021d824c0816093021d814c1985c530641714c0985c530589704c1315c130485704c0815c13061d624c18558930605624c17258930595624c15158930261624c08758930615604c18258130595604c08758130609514c17254530261514c1964813061d204c18548130605204c172481305c5204c17048130595204c16348130581204c15348130545204c08748130205204c195205305c8814c1532053021c814c17360d105c183440985cd105c530440974c11065c834419161830245860c09760430619710c1941c43025d83041976081064d82041874c01061930041854c01060930041981cc1064073041821cc10 else 0x36285bf610c3eb16a0f78313259a16018b360a9f1020ef08ac84e1493586087710ef811806dc08f490f0c6a2601ae5091c1046648f7d2431b843c342afe64645d2134087bd144b9847522ee8c4dc189c047018f390d40b2e8594b1081edd0b3e0241dec472b4246af906806788830d068cb760514584df0120f2e850c1058f0f0212ae845fa09e01cca15e22d910c023488b22f7a20b6b88720e689161514304a0dbca8c60e8e20d8076910fd81107a90d80738421704153cc4838e04c75c018cfa233c22ea4d147229c443187434d85e01bbdd050c0a029f98a7213bd9053f810ce11201bc030704135d0af090ef113809617a19e1120378896350dbae58d7e021a7f93416538447e035025020fac5622cfe9244cb3f121cd550c7b8864c89013b01d795318f350dd01ba037a03b66826fc0477920b7f311117f8218f421cb2d5070ea9419d9157940032cf021d52c5bc14368113221798506e80d0127f446265d68920dec0680a3e0631c422051e818c991172c18eb8031da118bc40835e821bf00c4f086ce0733429aa12fec110fc119028f818f734260200e30411f80c9b234047fc04859147c0c63a843c721a0e384719239fc10ce05bef922003ffe3641203e90c6650ff58992bf5c4c93f1c110003813ff024e7f081932f1432f4d18f39aa643fe2240373ed140dcfb45df7c91013c18dcad880270dc441c26b480c20266c458909250d2e0e8874ac26092b88420217891a0d54742281b6482c81d0747281a198119450c3dc381a4a5e26c27825823e0d20001d02301746741d4c4443144021780780c17119a25e1755c6c3c25749010c0d501824c2079640e40f813e19f0901b344081825016c0035060181340e81fc01801f8901f81f01a81300bc0bbe2fdd3d87d57ce7cabc77c23bb3b73b43af3aa3a53a079e39a79538fb8c788382f7e378b73b6fb68b6476135ab55f52b4df49345f4273d33a335f3172e72a72371ef1ab13f10f0d304eff6fc2f52f0eebee42e02db2d76d36cfacb2c8ac52c1abc2b6eb0eab6a529ee98294e9168b286282e7ea79672a6ce67262a5ea59655a50a4ba4824463ee3b638e3423062ae2522161e61aa1561160c2086051ff5fb5f8df51f01ea1e45db9d7dd39d09cd9c8dc59bcdb75b21acda91a65a259c59719358f98b98698197c17516f56a563d5d55955154c547d4293f53b934d3112e52591f11ad1811290e90bd061024fc0f64f24eb8e64e20dccd8cd48d04ca0c54c28bd0b88b58b34ae4aa0a58a2c9cc99493c8e888083c7f87a076c7046505c85504dc4703b43402e82802181b81400c80600002353797ae57d433049fb027d634c6141314d634e609b4cf68ae2729ae26deae4b142e3814130f1eae4d18ae0ea2263428952709b4efa924178c34b714152d49b4cfdeae4949b4355b14ad)
def x383l9 : Packing := (203,4,8,5505121,119,12,1118,x383d9)
def x383h9 (i : Nat) : Nat := 0x23520a6010e441400000002b21a46000182e001301e1c617a1e0013ac000000208000000001c3062c000c03a1862803620c233810023c068ec35400191ca2600020efa5404820000a12000000224001208c05149e1
def x383d8 (i : Nat) : Nat := 0x178405e10350405c07c1001805c203f01a84000004004c083a83e24100bc3d2400300b8604c035080fc02f1013005c200233ae2400300b8804d00300bc7d2402600b87e2401708002f0170a33be2400300b88006017080981adaa4a4a73952358c21e86607809e3745a561967521434f905364ad238891a83104800bcdb6c54aa6902a5fd24c0a954d2054bfa4a9a40b92a2985779b72819520530cebaa6d3930a8a61e795c971609514c2bbc5caa2b2a40986bb5a7504984c540cfe152b8aa290261f78545715c9204c2f6cdb152a9a40987dd1315c0985c530afd172902e4a8a61ad754da12613054bfa4982a6b8a40a96adda64c49361d40fec2e2982a2902a58eb691a2660730431b6cab4443902985739b42819520530aeb172a8aa690261ed254d202613054a3bc5cb4a40ae098636da5689981cc108f736854aa29026155e6dca0654814c2bb4d9140ca902986f49526855348130
def x383l8 : Packing := (28,5,8,0,0,10,0,x383d8)
def x383h8 (i : Nat) : Nat := 0x2022120a00481835bb4200000707b100030
def x383d7 (i : Nat) : Nat := 0x390805c1eb5c2b99303f5054d515c57248130e5e1722a571545204c3792549b62a553481309739c42e551595204c35d254cb9481725453083b8c86d0a9545204c31c654db42a55148130
def x383l7 : Packing := (7,6,8,0,0,6,0,x383d7)
def x383h7 (i : Nat) : Nat := 0x78001b2d178400008
def x383d6 (i : Nat) : Nat := 0x3507340795054d722a571545204c22671b0e2172a8aca902614748da54cb94817254530
def x383l6 : Packing := (3,7,8,0,0,5,0,x383d6)
def x383h6 (i : Nat) : Nat := 0x1e0
def x383d5 (i : Nat) : Nat := 0xd41d1505c4da54cb94817254530
def x383l5 : Packing := (1,8,8,0,0,0,0,x383d5)
def x383samples : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff081210205f8a00b8028136002c6004203f193090d9a33c9401c73e21f673,0x1a6b048b813a54161041804002c6004202519200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc48c8065583220a4000393601008190c2c861f1632604c0ff66a4c8c6487f,0x5909b044884ab21e4880c201008190c2886090420400804264a488c44829),(0xc240015520000003083a40960f060704f181c98c38470f188738f1078f9c,0x2a0760dbb36254861b3092d960f0607047181498838470a18831071038514),(0x8601e9022015e0030942c9203000180701fe0e0fc0780fe0f83f01f80fe0,0x10e894240419815884476d0203000180000540407c03005e0502f00b00ae0),(0x137002048460b8004001c7c007e007fe000ff0007ff000ffc001fff000,0x25146b507ac42aa16bb812bc7c007e007da000bf0004dd000afc0014ed000),(0x3110400a858081500828000f80007fff800000fffff800000fffffe000000,0x2094b2646e818949ce866faf800055a9000000fff6e800000fffdda000000),(0x20a8060080600a44740400fffff8000000000fffffffffff000000000000,0x3a6c2460a71b145a0a47e3cfcba50000000000fbdfbff7fbd000000000000),(0,0),(0x3524888800519504f50488fffffffffffffff00000000000000000000000,0x503499b106462a431381010345aaa56fffabf00000000000000000000000)]
def x383columns : List ColumnInfo := [(28,0,355,0,7),(2080,0,2399,0,11),(2112,0,2367,0,11),(2064,0,2415,0,11),(2052,0,2427,0,11),(1,0,382,0,9),(49,0,334,0,7),(70,0,313,0,7),(1056,0,1375,0,11),(1040,0,1391,0,11),(1088,0,1343,0,11),(1028,0,1403,0,11),(36,0,347,0,8),(53824,0,54079,0,11),(53776,0,54127,0,11),(32,0,351,0,11),(4,0,379,0,11),(47648,0,47967,0,11),(52768,0,53087,0,11),(44548,0,44923,0,11),(69124,0,69499,0,11),(1568,0,1887,0,11),(4640,0,4959,0,11),(6688,0,7007,0,11),(9248,0,9567,0,11),(13856,0,14175,0,11),(18464,0,18783,0,11),(42528,0,42847,0,11),(46112,0,46431,0,11),(59936,0,60255,0,11),(7684,0,8059,0,11),(16900,0,17275,0,11),(48132,0,48507,0,11),(44096,0,44351,0,11),(44036,0,44411,0,11),(44064,0,44383,0,11),(43536,0,43887,0,11),(42512,0,42863,0,11),(4624,0,4975,0,11),(6672,0,7023,0,11),(9232,0,9583,0,11),(18448,0,18799,0,11),(59920,0,60271,0,11),(64,0,319,0,11),(42560,0,42815,0,11),(42500,0,42875,0,11),(50,1,332,0,4),(13,16,354,0,4),(4612,0,4987,0,11),(49668,0,50043,0,11),(59908,0,60283,0,11),(73732,0,74107,0,11),(43522,0,43901,0,9),(18433,0,18814,0,9),(59905,0,60286,0,9),(50689,0,51070,0,9),(9217,0,9598,0,9),(57,0,326,0,4),(69,2,312,0,4),(42524,0,42851,0,7),(42752,0,42623,0,9),(52800,0,53055,0,11),(352,0,31,0,7),(13888,0,14143,0,11),(47680,0,47935,0,11),(50752,0,51007,0,11),(49696,0,50015,0,11),(34,0,349,0,7),(73760,0,74079,0,11),(9244,0,9571,0,7),(2400,0,2079,0,7),(2050,0,2429,0,9),(50696,0,51063,0,9),(43776,0,43647,0,9),(46088,0,46455,0,9),(9220,0,9595,0,11),(276,8,99,0,4),(104,256,23,0,4),(6657,0,7038,0,9),(72,0,311,0,7),(49665,0,50046,0,9),(73729,0,74110,0,9),(4672,0,4927,0,11),(6720,0,6975,0,11),(9280,0,9535,0,11),(18496,0,18751,0,11),(44608,0,44863,0,11),(59968,0,60223,0,11),(69184,0,69439,0,11),(16,0,367,0,11),(44288,0,44159,0,9),(83,0,300,0,4),(65,0,318,0,7),(1036,0,1395,0,8),(18449,0,18798,0,8),(59921,0,60270,0,8),(9233,0,9582,0,8),(6705,0,6990,0,7),(46082,0,46461,0,9),(59906,0,60285,0,9),(69122,0,69501,0,9),(48129,0,48510,0,9),(1312,0,1119,0,8),(18498,0,18749,0,8),(42848,0,42527,0,7),(321,32,30,0,4),(74,4,305,0,4),(59909,0,60282,0,7),(262,64,57,0,4),(18,0,365,0,7),(44572,0,44899,0,7),(52801,0,53054,0,7),(44098,0,44349,0,8),(18436,0,18811,0,11),(71,0,312,0,4),(43600,0,43823,0,8),(53,0,330,0,4),(272,0,111,0,7),(44384,0,44063,0,7),(305,0,78,0,4),(44102,0,44345,0,7),(51,0,332,0,4),(52785,0,53070,0,7),(5,0,378,0,7),(273,32,78,0,4),(2114,0,2365,0,8),(290,64,29,0,4),(26,4,353,0,4),(80,0,303,0,8),(2118,0,2361,0,7),(8225,0,8542,0,8),(47632,0,47983,0,11),(47872,0,47743,0,9),(41,16,326,0,4),(18438,0,18809,0,8),(59910,0,60281,0,8),(4620,0,4979,0,8),(11297,0,11614,0,8),(4636,0,4963,0,7),(280,0,103,0,5),(260,0,123,0,7),(59953,0,60238,0,7),(59974,0,60217,0,7),(324,0,59,0,5),(49692,0,50019,0,7),(49697,0,50014,0,8),(44546,0,44925,0,9),(40,0,343,0,7),(102,0,281,0,4),(300,0,83,0,4),(344,0,39,0,4),(1344,0,1087,0,8),(78,0,305,0,4),(354,0,29,0,4),(92,0,291,0,4),(18465,0,18782,0,8),(284,0,99,0,4),(3138,0,3389,0,8),(326,0,57,0,4)]
def x383autos : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]
def x383levels : Nat → Packing
  | 12 => x383l12
  | 11 => x383l11
  | 10 => x383l10
  | 9 => x383l9
  | 8 => x383l8
  | 7 => x383l7
  | 6 => x383l6
  | 5 => x383l5
  | _ => emptyPacking
def x383index : Nat → Nat → Option (Nat × Nat)
  | 12 => lookupWord 35 135 6 13 6 3 x383h12
  | 11 => lookupWord 470 589 6 16 9 3 x383h11
  | 10 => lookupWord 338 423 6 15 8 3 x383h10
  | 9 => lookupWord 9 55 5 12 5 3 x383h9
  | 8 => lookupWord 3 13 3 10 3 3 x383h8
  | 7 => lookupWord 4 7 1 9 2 3 x383h7
  | 6 => lookupWord 1 3 1 8 1 3 x383h6
  | _ => fun _ => none
def x383 : Forest := ⟨1407,12,fun j => x383samples[j]?.getD (0,0),x383columns,x383autos,x383levels,x383index⟩
set_option maxHeartbeats 0 in
theorem geomx383 : graphValid x383 (boundsBefore known42751) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=4) ?_⟩,listPieces_all (d:=1) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_12_0 : block x383 12 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_12 : block x383 12 0 6=true := sx383_12_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_0 : block x383 11 0 3=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_3 : block x383 11 3 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_11_18 : block x383 11 18 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_11 : block x383 11 0 48=true := (@block_merge x383 11 0 18 30 (@block_merge x383 11 0 3 15 sx383_11_0 sx383_11_3) sx383_11_18)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_0 : block x383 10 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_11 : block x383 10 11 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_47 : block x383 10 47 23=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_70 : block x383 10 70 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_106 : block x383 10 106 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_142 : block x383 10 142 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_178 : block x383 10 178 30=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_208 : block x383 10 208 36=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_10_244 : block x383 10 244 15=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_10 : block x383 10 0 259=true := (@block_merge x383 10 0 244 15 (@block_merge x383 10 0 208 36 (@block_merge x383 10 0 178 30 (@block_merge x383 10 0 142 36 (@block_merge x383 10 0 106 36 (@block_merge x383 10 0 70 36 (@block_merge x383 10 0 47 23 (@block_merge x383 10 0 11 36 sx383_10_0 sx383_10_11) sx383_10_47) sx383_10_70) sx383_10_106) sx383_10_142) sx383_10_178) sx383_10_208) sx383_10_244)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_0 : block x383 9 0 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_16 : block x383 9 16 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_52 : block x383 9 52 36=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_88 : block x383 9 88 2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_90 : block x383 9 90 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_126 : block x383 9 126 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_162 : block x383 9 162 36=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_9_198 : block x383 9 198 5=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_9 : block x383 9 0 203=true := (@block_merge x383 9 0 198 5 (@block_merge x383 9 0 162 36 (@block_merge x383 9 0 126 36 (@block_merge x383 9 0 90 36 (@block_merge x383 9 0 88 2 (@block_merge x383 9 0 52 36 (@block_merge x383 9 0 16 36 sx383_9_0 sx383_9_16) sx383_9_52) sx383_9_88) sx383_9_90) sx383_9_126) sx383_9_162) sx383_9_198)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_0 : block x383 8 0 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_8_11 : block x383 8 11 17=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_8 : block x383 8 0 28=true := (@block_merge x383 8 0 11 17 sx383_8_0 sx383_8_11)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_7_0 : block x383 7 0 2=true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_7_2 : block x383 7 2 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel
theorem allx383_7 : block x383 7 0 7=true := (@block_merge x383 7 0 2 5 sx383_7_0 sx383_7_2)
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_6_0 : block x383 6 0 3=true := by decide +kernel
theorem allx383_6 : block x383 6 0 3=true := sx383_6_0
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sx383_5_0 : block x383 5 0 1=true := by decide +kernel
theorem allx383_5 : block x383 5 0 1=true := sx383_5_0
theorem tablesx383 : checkedTables x383 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block x383 0 0 0 = true)
  · exact (rfl : block x383 1 0 0 = true)
  · exact (rfl : block x383 2 0 0 = true)
  · exact (rfl : block x383 3 0 0 = true)
  · exact (rfl : block x383 4 0 0 = true)
  · exact allx383_5
  · exact allx383_6
  · exact allx383_7
  · exact allx383_8
  · exact allx383_9
  · exact allx383_10
  · exact allx383_11
  · exact allx383_12
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem pl383 : Impossible false (graphGoal 1407) 12 (vars 1407).toFinset := plainA (q:=383) (prior:=boundsBefore known42751) (before_sound known42751 valid42751) (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low2431 : Lower false (varsX 2431) (graphGoal 2431) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=0) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known2431 := extendKnown known42751 13 [(9599,[100,131,82,16]),(17343,[114,67,84,48,33,97,128]),(9711,[100,131,116,50,33,16,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid2431 : Known false known2431 := extendKnown_ok (m:=2431) valid42751 low2431 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low1407 : Lower false (varsX 1407) (graphGoal 1407) 13 :=
  strong_full (q:=1407) (rs:=[16, 4, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=1) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known1407 := extendKnown known2431 13 [(28143,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid1407 : Known false known1407 := extendKnown_ok (m:=1407) valid2431 low1407 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low54143 : Lower false (varsX 54143) (graphGoal 54143) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 34, 4, 1, 5, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=2) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known54143 := extendKnown known1407 13 [(54143,[]),(64447,[117,80,66,130,96,16]),(44015,[116,83,32])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid54143 : Known false known54143 := extendKnown_ok (m:=54143) valid1407 low54143 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low44415 : Lower false (varsX 44415) (graphGoal 44415) 13 :=
  strong_full (q:=1407) (rs:=[16, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=3) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known44415 := extendKnown known54143 13 [(44927,[84,131,98]),(47999,[101,66,16]),(53119,[98,82,16,66,49,128]),(58239,[82,129,48]),(69503,[84,66,16,98,129,48]),(58303,[118,133,33,48]),(60351,[114,67,84,48,33,97,128]),(69567,[117,80,66,130,96,16]),(42991,[83,114,99,33,16,64]),(60399,[80,81,114,66,50,129,96]),(69103,[116,50,129,80])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid44415 : Known false known44415 := extendKnown_ok (m:=44415) valid54143 low44415 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low43903 : Lower false (varsX 43903) (graphGoal 43903) 13 :=
  strong_full (q:=1407) (rs:=[10, 1, 2, 5, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=4) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known43903 := extendKnown known44415 13 [(43903,[]),(46463,[84,131,98]),(48511,[101,66,16]),(51071,[100,131,82,16]),(43455,[98,118,81,130,50,65]),(43967,[118,130,81]),(54207,[116,100,49,32,81,128]),(58815,[114,67,84,48,33,97,128]),(49647,[83,114,99,33,16,64]),(51183,[100,131,116,50,33,16,80]),(54255,[116,83,32]),(55791,[83,133,115,67,32,96])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid43903 : Known false known43903 := extendKnown_ok (m:=43903) valid44415 low43903 (by decide +kernel)
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low42879 : Lower false (varsX 42879) (graphGoal 42879) 13 :=
  strong_full (q:=1407) (rs:=[2, 1, 2, 4, 1, 1, 2, 8]) (by decide +kernel) (by decide +kernel) (by decide +kernel) pl383
    (index_root (g:=x383) (i:=5) rfl rfl (before_sound known42751 valid42751) geomx383 tablesx383 (by decide +kernel))
def known42879 := extendKnown known43903 13 [(42879,[]),(60287,[82,129,48]),(44991,[98,118,81,130,50,65]),(69615,[33,80,112,97,130,49,64])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid42879 : Known false known42879 := extendKnown_ok (m:=42879) valid43903 low42879 (by decide +kernel)
def xdd14 (i : Nat) : Nat := 0x16ad2728c1ee6b16a4a0e629062082fff
def xdl14 : Packing := (1,0,5,0,0,0,0,xdd14)
def xdsamples : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc020000000003000003fbc001bfc000003ffc4c10398cc00b1801080fc64c4481d3200821075b3090d9a33c9401c73e21f673,0x1c8e5425111515114115514111115115115104c10118c800b1801080946484481532008210253200091222c94000224212652),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd000200000000003cfc000000000003fffffe10a52610c040206430b2187c00061c3b30c6249c31632604c0ff66a4c8c6487f,0x200109c08e0a688e08e08e0ae48e08e08e08e10a526104040206430a218240004081330c6248c10420400804264a488c44829),(0x800010000007fc000000002003fffffc0000001c01f2583c181c13c6072081863c4010038e7c98c38470f188738f1078f9c,0x360c43c50c51450c50c50c50850c50c50c500000800a2583c181c11c60520810028401001002898838470a18831071038514),(0xa000fdc008000100003edc403ffc000000600607e0080c000601c07f8070e07c003e07c0f80e0fc0780fe0f83f01f80fe0,0x18091ac1a418c1a41a41a41841a41a41a41a460000540080c00060000150070c07c003e0580f80407c03005e0502f00b00ae0),(0x800000000b000000003eddbfc00000000380c7f80031f001f801ff800380ff8007c007ff000ff0007ff000ffc001fff000,0x2370a11a4ae22a4aa4aa0aa6ae4aa4aa4aa4b80c7e80031f001f801f68003803e8007c0027d000bf0004dd000afc0014ed000),(0x520da4003ff4800203ffc12000000000000000f800003e0001fffe000003ff000007fff800000fffff800000fffffe000000,0x16003c06c42c06c16c02c16c06c06c06c06c000000003e000156a40000032a000006a59000000fff6e800000fffdda000000),(0x3a5525a020000003cfc000000000000000003ff0000003ffffe0000000003fffffff8000000000fffffffffff000000000000,0x19783603707583703703303503703703703716a0000003f2e940000000003fffbf7e8000000000fbdfbff7fbd000000000000),(0x180005003b907fc000040122000000000003ffffffffc000000000000003fffffffffffffffff00000000000000000000000,0x3c9f380383382b83283383283783383383383ffff7ff5c000000000000000d5effd795a6feffd700000000000000000000000),(0x2e57dfaffc464800300000000400000000003fffffffffffffffffffffffc0000000000000000000000000000000000000000,0x2686c03c03803c03c03c43c03c03c03c03c0295fffabfc0d16aa95bffeafc0000000000000000000000000000000000000000)]
def xdcolumns : List ColumnInfo := [(128,0,383,0,13),(16,0,495,0,13),(64,0,447,0,13),(32,0,479,0,12),(2,0,509,0,12),(256,0,255,0,12),(17,0,494,0,11),(4,0,507,0,12),(42624,0,42879,0,13),(43648,0,43903,0,13),(44672,0,44927,0,13),(46208,0,46463,0,13),(47744,0,47999,0,13),(48256,0,48511,0,13),(50816,0,51071,0,13),(52864,0,53119,0,13),(53888,0,54143,0,13),(60032,0,60287,0,13),(69248,0,69503,0,13),(49168,0,49647,0,13),(55312,0,55791,0,13),(43072,0,43455,0,13),(58432,0,58815,0,13)]
def xdautos : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def xdlevels : Nat → Packing
  | 14 => xdl14
  | _ => emptyPacking
def xdindex : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none
def xd : Forest := ⟨1535,14,fun j => xdsamples[j]?.getD (0,0),xdcolumns,xdautos,xdlevels,xdindex⟩
set_option maxHeartbeats 0 in
theorem geomxd : graphValid xd (boundsBefore known42879) = true := by
  simp only [graphValid,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=3) ?_⟩,listPieces_all (d:=2) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem sxd_14_0 : block xd 14 0 1=true := by decide +kernel
theorem allxd_14 : block xd 14 0 1=true := sxd_14_0
theorem tablesxd : checkedTables xd 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block xd 0 0 0 = true)
  · exact (rfl : block xd 1 0 0 = true)
  · exact (rfl : block xd 2 0 0 = true)
  · exact (rfl : block xd 3 0 0 = true)
  · exact (rfl : block xd 4 0 0 = true)
  · exact (rfl : block xd 5 0 0 = true)
  · exact (rfl : block xd 6 0 0 = true)
  · exact (rfl : block xd 7 0 0 = true)
  · exact (rfl : block xd 8 0 0 = true)
  · exact (rfl : block xd 9 0 0 = true)
  · exact (rfl : block xd 10 0 0 = true)
  · exact (rfl : block xd 11 0 0 = true)
  · exact (rfl : block xd 12 0 0 = true)
  · exact (rfl : block xd 13 0 0 = true)
  · exact allxd_14
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem caseFA : Impossible false (graphGoal 511) 14 (vars 511).toFinset := by
  have h : Impossible false (graphGoal 1535) 14 (vars 1535).toFinset :=
    index_root (g:=xd) (i:=0) rfl rfl (before_sound known42879 valid42879) geomxd tablesxd (by decide +kernel)
  have e1 : graphGoal 1535=graphGoal 511 := by decide +kernel
  have e2 : vars 1535=vars 511 := by decide +kernel
  rw [e1,e2] at h
  exact h
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem low511 : Lower false (vars 511) (graphGoal 511) 15 := plain_low (hints:=13438558465) (by decide +kernel) caseFA
def known511 := extendKnown known42879 15 [(511,[])]
set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid511 : Known false known511 := extendKnown_ok (m:=511) valid42879 low511 (by decide +kernel)

def neighbor670 (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0
def absentRow670 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor670 i)
def presentRow670 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor670 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow670 i) graph ≠ bit (presentRow670 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow670 i) (inputs.getD j.val zero) =
      bit (presentRow670 i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 15) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 14 else 15) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 15 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 14 else 15) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow670 i) (presentRow670 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 15 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 14 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 15 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run

abbrev TransportEntry := Nat × Nat × Nat × List Nat
def moveEntries (rows : List TransportEntry) (base : List (Nat × Nat)) :=
  rows.map (fun e => (e.1,e.2.1)) ++ base
def transportValid (base : List (Nat × Nat)) (e : TransportEntry) :=
  (boundsBefore base e.2.2.1 == e.2.1) && carryOK e.1 e.2.2.1 e.2.2.2
theorem movedKnown {u base rows} (h : Known u base)
    (cert : rows.all (transportValid base) = true) : Known u (moveEntries rows base) := by
  intro e he
  rcases List.mem_append.mp he with hm | hb
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    have hh := List.all_eq_true.mp cert r hr
    simp only [transportValid,Bool.and_eq_true,beq_iff_eq] at hh
    exact carry_of hh.2 (hh.1 ▸ before_sound base h r.2.2.1)
  · exact h e hb
def transported : List TransportEntry := [(151,5,94,[48,33,133,118]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(223,9,478,[80,16,33,50,116,131,100]),(239,9,127,[32,83,116]),(247,9,478,[48,33,133,118]),(254,8,251,[32,83,116]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(350,8,95,[128,49,100]),(369,5,94,[16,82,131,100]),(371,8,95,[16,82,131,100]),(375,9,127,[16,82,131,100]),(381,9,127,[48,129,82]),(413,7,123,[48,33,133,118]),(440,5,94,[81,130,118]),(444,8,95,[32,49,128,81,116,100]),(446,9,127,[32,49,128,81,116,100]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(463,9,127,[16,32,48,128,100,80,116]),(471,8,251,[16,82,131,100]),(477,8,251,[48,33,133,118]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116]),(491,9,127,[128,81,32,49,100,116]),(493,9,127,[80,129,50,116]),(499,9,478,[32,83,116]),(501,8,251,[80,16,33,50,116,131,100]),(505,9,478,[16,82,131,100]),(506,8,251,[128,49,100]),(510,12,255,[32,49,128,81,116,100]),(1279,12,3579,[81,130,118]),(1407,13,28143,[32,49,128,81,116,100]),(1503,12,18911,[128,49,100]),(1527,12,3579,[16,32,48,128,100,80,116]),(1531,12,18911,[48,129,82]),(1791,12,17405,[48,129,82]),(1967,11,4927,[32,49,128,81,116,100]),(1983,13,17343,[48,129,82]),(2015,12,17403,[48,129,82]),(2039,12,17403,[80,129,50,116]),(2045,12,17151,[48,129,82]),(2431,13,9599,[16,82,131,100]),(2493,11,2239,[48,129,82]),(2495,13,9599,[32,49,128,81,116,100]),(3263,11,1375,[80,16,33,50,116,131,100]),(3391,11,1343,[81,130,118]),(3519,13,28143,[16,32,48,128,100,80,116]),(3571,9,11742,[32,83,116]),(4955,8,1725,[81,130,118]),(4991,13,17343,[16,32,48,128,100,80,116]),(5053,11,6847,[48,129,82]),(5111,12,17403,[16,32,48,128,100,80,116]),(5115,12,17405,[16,32,48,128,100,80,116]),(5117,12,17403,[48,33,133,118]),(6511,11,1343,[16,32,48,128,100,80,116]),(6606,8,1119,[16,32,48,128,100,80,116]),(6639,13,28143,[81,130,118]),(6654,12,18911,[80,129,50,116]),(7039,13,17343,[81,130,118]),(7150,11,6847,[128,49,100]),(7166,12,17403,[128,81,32,49,100,116]),(8166,8,1725,[16,82,131,100]),(8167,11,1727,[16,82,131,100]),(8175,13,17343,[32,49,128,81,116,100]),(8183,12,17405,[32,49,128,81,116,100]),(8190,12,17151,[32,49,128,81,116,100]),(8679,11,2751,[16,82,131,100]),(9702,8,2237,[16,82,131,100]),(9710,11,2239,[128,49,100]),(11710,9,18814,[81,130,118]),(11711,13,28143,[16,82,131,100]),(11773,12,18911,[81,130,118]),(12716,7,2079,[32,49,128,81,116,100]),(12719,11,2367,[32,83,116]),(12733,11,2239,[80,129,50,116]),(12735,13,9599,[81,130,118]),(12781,9,2429,[32,83,116]),(12783,13,9599,[16,32,48,128,100,80,116]),(13310,12,27127,[48,129,82]),(13806,11,2751,[32,49,128,81,116,100]),(14191,11,4927,[128,81,32,49,100,116]),(14269,11,6847,[80,129,50,116]),(14303,12,17403,[16,82,131,100]),(14310,8,1725,[32,49,128,81,116,100]),(14319,13,17343,[16,82,131,100]),(14333,12,17403,[80,16,33,50,116,131,100]),(14334,12,17405,[16,82,131,100]),(17342,9,7038,[81,130,118]),(17406,12,17403,[32,83,116]),(18429,12,27127,[128,81,32,49,100,116]),(18779,8,11453,[81,130,118]),(18815,13,28143,[32,83,116]),(18939,12,18911,[16,82,131,100]),(18940,9,11742,[81,130,118]),(27623,11,2751,[80,16,33,50,116,131,100]),(28079,11,1343,[80,129,50,116]),(28134,8,11453,[16,82,131,100]),(28155,12,3579,[128,49,100]),(28157,12,3579,[80,16,33,50,116,131,100]),(28158,12,18911,[16,32,48,128,100,80,116]),(32750,11,2751,[128,49,100]),(37374,12,27127,[48,33,133,118]),(42719,9,48094,[80,16,33,50,116,131,100]),(42727,8,42679,[16,82,131,100]),(42867,8,42591,[16,82,131,100]),(42943,13,44927,[81,130,118]),(42951,7,42683,[16,82,131,100]),(42995,9,48094,[32,83,116]),(43003,12,44799,[81,130,118]),(43447,9,46455,[81,130,118]),(44287,12,58335,[48,33,133,118]),(44415,13,58239,[48,129,82]),(44479,13,58239,[48,33,133,118]),(44511,12,68863,[16,32,48,128,100,80,116]),(44539,12,58335,[48,129,82]),(44541,12,68863,[80,129,50,116]),(44791,9,48094,[128,81,32,49,100,116]),(44915,8,42679,[81,130,118]),(45039,13,44927,[80,129,50,116]),(45041,7,42711,[81,130,118]),(45047,12,42751,[80,16,33,50,116,131,100]),(45051,12,42751,[81,130,118]),(48063,13,44927,[32,49,128,81,116,100]),(48079,9,42623,[16,32,48,128,100,80,116]),(48095,12,42751,[16,32,48,128,100,80,116]),(48111,13,42879,[16,32,48,128,100,80,116]),(48126,12,44799,[32,49,128,81,116,100]),(48635,12,58623,[81,130,118]),(49403,8,43479,[16,82,131,100]),(49643,9,46455,[80,129,50,116]),(49662,12,58623,[32,49,128,81,116,100]),(50047,13,58239,[128,49,100]),(50143,12,58335,[128,49,100]),(50158,11,58047,[128,49,100]),(50159,13,58239,[128,81,32,49,100,116]),(50167,12,58335,[128,81,32,49,100,116]),(50174,12,68863,[32,49,128,81,116,100]),(51135,13,54143,[81,130,118]),(51151,9,43647,[16,32,48,128,100,80,116]),(52991,12,44799,[32,83,116]),(53086,8,42679,[48,33,133,118]),(53183,13,42879,[32,49,128,81,116,100]),(53198,8,42679,[32,49,128,81,116,100]),(53215,12,42751,[48,33,133,118]),(53229,9,44925,[32,83,116]),(53231,13,44927,[32,83,116]),(53244,9,48094,[16,32,48,128,100,80,116]),(53245,12,44799,[48,129,82]),(53246,12,42751,[32,49,128,81,116,100]),(54206,9,43647,[32,49,128,81,116,100]),(54253,9,43647,[80,129,50,116]),(55039,12,58335,[80,16,33,50,116,131,100]),(55231,13,58239,[80,16,33,50,116,131,100]),(55279,13,58239,[80,129,50,116]),(55287,12,68863,[16,82,131,100]),(55294,12,58335,[80,129,50,116]),(55789,9,46455,[128,81,32,49,100,116]),(55799,12,58623,[16,82,131,100]),(58111,12,68863,[32,83,116]),(58301,11,44223,[48,129,82]),(58363,12,68863,[128,81,32,49,100,116]),(58814,9,46455,[48,33,133,118]),(60251,8,44733,[48,33,133,118]),(60380,7,42711,[128,49,100]),(60382,9,48094,[80,129,50,116]),(60396,8,42679,[128,49,100]),(60409,9,48094,[32,49,128,81,116,100]),(60411,12,44799,[128,81,32,49,100,116]),(60414,12,42751,[128,49,100]),(63871,13,64447,[81,130,118]),(69053,11,44223,[80,129,50,116]),(69055,13,58239,[32,49,128,81,116,100]),(69094,8,44221,[80,16,33,50,116,131,100]),(69111,12,58335,[32,83,116]),(69118,12,68863,[128,49,100]),(69561,8,42679,[80,129,50,116]),(69617,7,42711,[128,81,32,49,100,116]),(69619,9,48094,[48,129,82]),(69627,12,42751,[128,81,32,49,100,116]),(69628,9,48094,[81,130,118]),(69630,12,44799,[128,49,100]),(73703,11,64191,[16,82,131,100]),(73710,11,64191,[32,49,128,81,116,100]),(74214,8,44221,[128,49,100]),(74218,7,44155,[128,81,32,49,100,116]),(74222,11,44223,[128,49,100]),(74223,13,58239,[16,32,48,128,100,80,116]),(74238,12,58335,[16,32,48,128,100,80,116])]
def pri := moveEntries transported known511
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem vpri : Known false pri := by
  apply movedKnown valid511
  apply listPieces_all (d:=6)
  simp only [listPieces]
  repeat' apply And.intro
  all_goals decide +kernel
def moY : Array (Bits × Bits) := #[(0x42211f87e1e04110421091143f1f07818818818818818818818818818818818818dc1b39170018b5ca6660d41c4210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f031031031031031031031031031031031031,0xf87e1e00000000000001f1f038007ff8007ff8007ff8000000007ff8000000204a1100018072606050c1e80007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07000fff000fff000fff000000000fff000000),(0x844220882228bf0fc02f82f3e1013c821821821821821821821821821821821821a98a812091421946202a033cbe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279043043043043043043043043043043043043,0x3f0fc00f80f3e0001c7ff8000000000000007ff8000000007fffff8188004c29225000a12853a03e0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038fff000000000000000fff000000000ffffff),(0x13e1f0117fe07c20085f10f20423fe8043043043043043043043043043043043043014ca8a812f306ac46180c200421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0086086086086086086086086086086086086,0x3e1f0007fe07c00001f00f00001fe00000007fffff8000000007ff8007ff80000000608a211000060c400224514000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0000000ffffff000000000fff000fff000000),(0xfc8044ff84401042ffe40044bffe2400860860860860860860860860860860860861a62c0ce6c846e2101310342884208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc48010c10c10c10c10c10c10c10c10c10c10c10c,0xfc0000ff80000000ffe000003ffe0000000000000000007fffff8007ff8000007ff9e10044e608a002023318008800000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000000000000000000ffffff000fff000000fff),(0x2001ff2208047fff108000ffc84440100c00c00c00c00c00c00c00c00c00c00c00c0001182178046889c04243e13ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802018018018018018018018018018018018018,0x1ff0000007fff000000ffc0000007ff8007ff8007ff8000007ff8000007ff800000118211e04e889c04243e13ff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000fff000fff000fff000000fff000000fff000),(0xfffe004010087fffffffff00008080251051051051051051051051051051051051056902714880980109102b4c050842084210822109042108882108917fffffc00802010fffffffffe000101004a20a20a20a20a20a20a20a20a20a20a20a20,0xfffe000000007fffffffff0000000000000000000000000000007fffff8007fffffc4500424880180188032b16040000000000000000000000000000007fffffc00000000fffffffffe000000000000000000000000000000ffffff000ffffff),(0xffffffffffff8080200020081000010220220220220220220220220220220220220200000000108000808d68041e1084108421044213ffffff004001007ffffffffffffff0100400040102000020440440440440440440440440440440440440,0xffffffffffff80000000000000000000000000000007fffff8007ffffffff80000060100810400c011804d28041c0000000000000003fffffe000000007ffffffffffffff0000000000000000000000000000000ffffff000fffffffff000000),(0x410880002080210441084280000108014014014014014014014014014014014014002940000023040000701080ebffffff0002080003ffffffffffffffa108211000041004208821085000002100280280280280280280280280280280280280,0x7fffff8000007ffffffff8000000000000002284100003b040031fc9080ebfffffe0000000003ffffffffffffff8000000000000000000000000000000000ffffff000000fffffffff000000000000000),(0x82110884411142088210840021080006806806806806806806806806806806806800029564286214010988568933fffffffffffffffe084210008210004210422110882228411042108004210000d00d00d00d00d00d00d00d00d00d00d00d00,0x7fffffffffff80000000000000000000000001a092001630540058044e963fffffffffffffffc000000000000000000000000000000000000000000000000ffffffffffff000000000000000000000000)]
def moC : List ColumnInfo := [(0,0,511,0,15),(16,0,495,0,13),(6160,0,6639,0,13),(7696,0,8175,0,13),(9232,0,9711,0,13),(12304,0,12783,0,13),(13840,0,14319,0,13),(27664,0,28143,0,13),(42512,0,42991,0,13),(43536,0,44015,0,13),(44560,0,45039,0,13),(47632,0,48111,0,13),(49168,0,49647,0,13),(49680,0,50159,0,13),(50704,0,51183,0,13),(52752,0,53231,0,13),(53776,0,54255,0,13),(54800,0,55279,0,13),(55312,0,55791,0,13),(59920,0,60399,0,13),(68624,0,69103,0,13),(69136,0,69615,0,13),(73744,0,74223,0,13),(64,0,447,0,13),(1600,0,1983,0,13),(2112,0,2495,0,13),(3136,0,3519,0,13),(11328,0,11711,0,13),(12352,0,12735,0,13),(16960,0,17343,0,13),(42560,0,42943,0,13),(43072,0,43455,0,13),(43584,0,43967,0,13),(44096,0,44479,0,13),(44608,0,44991,0,13),(47680,0,48063,0,13),(50752,0,51135,0,13),(52800,0,53183,0,13),(53824,0,54207,0,13),(54848,0,55231,0,13),(57920,0,58303,0,13),(58432,0,58815,0,13),(59968,0,60351,0,13),(64064,0,64447,0,13),(68672,0,69055,0,13),(69184,0,69567,0,13),(128,0,383,0,13),(1152,0,1407,0,13),(2176,0,2431,0,13),(4736,0,4991,0,13),(6784,0,7039,0,13),(9344,0,9599,0,13),(18560,0,18815,0,13),(42624,0,42879,0,13),(43648,0,43903,0,13),(44160,0,44415,0,13),(44672,0,44927,0,13),(46208,0,46463,0,13),(47744,0,47999,0,13),(48256,0,48511,0,13),(49792,0,50047,0,13),(50816,0,51071,0,13),(52864,0,53119,0,13),(53888,0,54143,0,13),(57984,0,58239,0,13),(60032,0,60287,0,13),(63616,0,63871,0,13),(69248,0,69503,0,13),(1,0,510,0,12),(6145,0,6654,0,12),(6657,0,7166,0,12),(7681,0,8190,0,12),(11265,0,11774,0,12),(12801,0,13310,0,12),(13825,0,14334,0,12),(16897,0,17406,0,12),(18433,0,18942,0,12),(27649,0,28158,0,12),(36865,0,37374,0,12),(47617,0,48126,0,12),(49153,0,49662,0,12),(49665,0,50174,0,12),(52737,0,53246,0,12),(54785,0,55294,0,12),(59905,0,60414,0,12),(68609,0,69118,0,12),(69121,0,69630,0,12),(73729,0,74238,0,12),(2,0,509,0,12),(1538,0,2045,0,12),(4610,0,5117,0,12),(11266,0,11773,0,12),(13826,0,14333,0,12),(16898,0,17405,0,12),(17922,0,18429,0,12),(18434,0,18941,0,12),(27650,0,28157,0,12),(43010,0,43517,0,12),(44034,0,44541,0,12),(44546,0,45053,0,12),(52738,0,53245,0,12),(59906,0,60413,0,12),(69122,0,69629,0,12),(4,0,507,0,12),(1028,0,1531,0,12),(3076,0,3579,0,12),(4612,0,5115,0,12),(18436,0,18939,0,12),(27652,0,28155,0,12),(42500,0,43003,0,12),(44036,0,44539,0,12),(44548,0,45051,0,12),(48132,0,48635,0,12),(57860,0,58363,0,12),(59908,0,60411,0,12),(69124,0,69627,0,12),(8,0,503,0,12),(1032,0,1527,0,12),(1544,0,2039,0,12),(4616,0,5111,0,12),(7688,0,8183,0,12),(26632,0,27127,0,12),(27656,0,28151,0,12),(42504,0,42999,0,12),(44552,0,45047,0,12),(47624,0,48119,0,12),(49672,0,50167,0,12),(54792,0,55287,0,12),(55304,0,55799,0,12),(68616,0,69111,0,12),(69128,0,69623,0,12),(32,0,479,0,12),(1056,0,1503,0,12),(1568,0,2015,0,12),(13856,0,14303,0,12),(18464,0,18911,0,12),(42528,0,42975,0,12),(44064,0,44511,0,12),(46112,0,46559,0,12),(47648,0,48095,0,12),(49696,0,50143,0,12),(52768,0,53215,0,12),(57888,0,58335,0,12),(59936,0,60383,0,12),(256,0,255,0,12),(1280,0,1279,0,12),(1792,0,1791,0,12),(17152,0,17151,0,12),(42752,0,42751,0,12),(44288,0,44287,0,12),(47872,0,47871,0,12),(52992,0,52991,0,12),(55040,0,55039,0,12),(58112,0,58111,0,12),(58624,0,58623,0,12),(68864,0,68863,0,12),(17,0,494,0,11),(6161,0,6638,0,11),(6673,0,7150,0,11),(9233,0,9710,0,11),(12305,0,12782,0,11),(13329,0,13806,0,11),(13841,0,14318,0,11),(32273,0,32750,0,11),(47633,0,48110,0,11),(49681,0,50158,0,11),(52753,0,53230,0,11),(54801,0,55278,0,11),(68625,0,69102,0,11),(73233,0,73710,0,11),(73745,0,74222,0,11),(24,0,487,0,11),(7704,0,8167,0,11),(8216,0,8679,0,11),(9240,0,9703,0,11),(27160,0,27623,0,11),(27672,0,28135,0,11),(42520,0,42983,0,11),(68632,0,69095,0,11),(69144,0,69607,0,11),(73240,0,73703,0,11),(66,0,445,0,11),(2114,0,2493,0,11),(4674,0,5053,0,11),(12354,0,12733,0,11),(13890,0,14269,0,11),(43074,0,43453,0,11),(57922,0,58301,0,11),(64066,0,64445,0,11),(68674,0,69053,0,11),(80,0,431,0,11),(1616,0,1967,0,11),(12368,0,12719,0,11),(27728,0,28079,0,11),(132,0,379,0,11),(1156,0,1403,0,11),(2180,0,2427,0,11),(4740,0,4987,0,11),(42628,0,42875,0,11),(44164,0,44411,0,11),(44676,0,44923,0,11),(57988,0,58235,0,11),(144,0,367,0,11),(1168,0,1391,0,11),(4752,0,4975,0,11),(6288,0,6511,0,11),(6800,0,7023,0,11),(9360,0,9583,0,11),(13968,0,14191,0,11),(18576,0,18799,0,11),(42640,0,42863,0,11),(47760,0,47983,0,11),(160,0,351,0,11),(2208,0,2399,0,11),(18592,0,18783,0,11),(47776,0,47967,0,11),(52896,0,53087,0,11),(58016,0,58207,0,11),(60064,0,60255,0,11),(1216,0,1343,0,11),(2240,0,2367,0,11),(3264,0,3391,0,11),(4800,0,4927,0,11),(18624,0,18751,0,11),(42688,0,42815,0,11),(44736,0,44863,0,11),(320,0,191,0,11),(1856,0,1727,0,11),(2368,0,2239,0,11),(3392,0,3263,0,11),(42816,0,42687,0,11),(55104,0,54975,0,11),(64320,0,64191,0,11),(0,16,486,9,10),(55296,16,55782,9,10),(0,64,189,258,10),(43008,64,43197,258,10),(44544,64,44733,258,10),(52736,64,52925,258,10),(58368,64,58557,258,10),(0,128,347,36,10),(42496,128,42843,36,10),(46080,128,46427,36,10),(1,16,486,8,9),(47617,16,48102,8,9),(54785,16,55270,8,9),(55297,16,55782,8,9),(2,64,189,256,9),(44546,64,44733,256,9),(58370,64,58557,256,9),(3,0,508,0,9),(18435,0,18940,0,9),(52739,0,53244,0,9),(69123,0,69628,0,9),(4,128,347,32,9),(46084,128,46427,32,9),(6,0,505,0,9),(59910,0,60409,0,9),(8,16,486,1,9),(49160,16,49638,1,9),(55304,16,55782,1,9),(12,0,499,0,9),(3084,0,3571,0,9),(42508,0,42995,0,9),(69132,0,69619,0,9),(18,0,493,0,9),(12306,0,12781,0,9),(52754,0,53229,0,9),(53778,0,54253,0,9),(55314,0,55789,0,9),(20,0,491,0,9),(49172,0,49643,0,9),(32,128,347,4,9),(48160,128,48475,4,9),(33,0,478,0,9),(11297,0,11742,0,9),(59937,0,60382,0,9),(48,0,463,0,9),(47664,0,48079,0,9),(50736,0,51151,0,9),(65,0,446,0,9),(11329,0,11710,0,9),(16961,0,17342,0,9),(53825,0,54206,0,9),(58433,0,58814,0,9),(43080,0,43447,0,9),(43104,0,43423,0,9),(129,0,382,0,9),(48257,0,48510,0,9),(50817,0,51070,0,9),(130,0,381,0,9),(136,0,375,0,9),(256,64,189,2,9),(43264,64,43197,2,9),(58624,64,58557,2,9),(264,0,247,0,9),(44808,0,44791,0,9),(272,0,239,0,9),(288,0,223,0,9),(42784,0,42719,0,9),(384,0,127,0,9),(0,1,460,50,8),(0,2,440,69,8),(0,4,369,138,8),(0,8,227,276,8),(0,32,94,385,8),(0,256,151,104,8),(5,0,506,0,8),(58373,0,58874,0,8),(9,0,486,0,8),(47625,0,48102,0,8),(49161,0,49638,0,8),(55305,0,55782,0,8),(9,16,486,0,8),(6153,16,6630,0,8),(7689,16,8166,0,8),(9225,16,9702,0,8),(12297,16,12774,0,8),(13833,16,14310,0,8),(27657,16,28134,0,8),(47625,16,48102,0,8),(49161,16,49638,0,8),(54793,16,55270,0,8),(55305,16,55782,0,8),(68617,16,69094,0,8),(69129,16,69606,0,8),(73737,16,74214,0,8),(10,0,501,0,8),(46090,0,46581,0,8),(19,0,492,0,8),(59923,0,60396,0,8),(34,0,477,0,8),(36,0,347,0,8),(42532,0,42843,0,8),(46116,0,46427,0,8),(59940,0,60251,0,8),(36,128,347,0,8),(1060,128,1371,0,8),(2084,128,2395,0,8),(4644,128,4955,0,8),(18468,128,18779,0,8),(42532,128,42843,0,8),(44068,128,44379,0,8),(46116,128,46427,0,8),(48164,128,48475,0,8),(57892,128,58203,0,8),(59940,128,60251,0,8),(40,0,471,0,8),(43048,0,43479,0,8),(6193,0,6606,0,8),(52785,0,53198,0,8),(67,0,444,0,8),(69190,0,69561,0,8),(134,0,377,0,8),(140,0,371,0,8),(4748,0,4979,0,8),(42636,0,42867,0,8),(44684,0,44915,0,8),(161,0,350,0,8),(52897,0,53086,0,8),(257,0,254,0,8),(258,0,189,0,8),(2306,0,2237,0,8),(43266,0,43197,0,8),(58626,0,58557,0,8),(258,64,189,0,8),(1794,64,1725,0,8),(2306,64,2237,0,8),(17154,64,17085,0,8),(43266,64,43197,0,8),(44802,64,44733,0,8),(52994,64,52925,0,8),(58114,64,58045,0,8),(58626,64,58557,0,8),(260,0,251,0,8),(49412,0,49403,0,8),(42776,0,42727,0,8),(47944,0,47799,0,8),(416,0,95,0,8),(1,2,440,68,7),(1,32,94,384,7),(2,1,460,48,7),(2,4,369,136,7),(4,2,440,65,7),(4,8,227,272,7),(7,0,504,0,7),(59911,0,60408,0,7),(69127,0,69624,0,7),(8,4,369,130,7),(8,256,151,96,7),(14,0,497,0,7),(44558,0,45041,0,7),(69134,0,69617,0,7),(16,1,460,34,7),(21,0,490,0,7),(73749,0,74218,0,7),(26,0,485,0,7),(32,1,460,18,7),(32,256,151,72,7),(35,0,476,0,7),(52771,0,53212,0,7),(59939,0,60380,0,7),(42552,0,42951,0,7),(47672,0,48071,0,7),(74,0,437,0,7),(12371,0,12716,0,7),(98,0,413,0,7),(133,0,378,0,7),(44700,0,44899,0,7),(168,0,343,0,7),(256,8,227,20,7),(256,32,94,129,7),(268,0,243,0,7),(42764,0,42739,0,7),(44812,0,44787,0,7),(289,0,222,0,7),(53025,0,52958,0,7),(296,0,215,0,7),(5,2,440,64,6),(10,4,369,128,6),(18,1,460,32,6),(18,4,353,136,6),(24,4,353,130,6),(34,1,460,16,6),(40,256,151,64,6),(48,1,460,2,6),(130,1,332,48,6),(136,4,369,2,6),(160,1,332,18,6),(257,32,94,128,6),(260,8,227,16,6),(272,8,227,4,6),(272,32,78,129,6),(384,8,99,20,6),(11,16,484,0,5),(13,16,482,0,5),(21,2,424,64,5),(26,4,353,128,5),(37,128,346,0,5),(41,16,454,0,5),(44,128,339,0,5),(50,1,460,0,5),(133,2,312,64,5),(138,4,369,0,5),(152,4,353,2,5),(168,256,23,64,5),(259,64,188,0,5),(262,64,185,0,5),(266,64,181,0,5),(292,128,91,0,5),(321,32,30,128,5)]
def moA : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]
def moD7 (j : Nat) : Nat := 0x3fd1b7f07ff4127f4d341986d552605314c120
def moD8 (j : Nat) : Nat := 0x1c8800007030060b2c2315e8e1f83e034ff412034603454c2c960275b2ec4dd481dac660f4d0d5e4d5acd4f494f4750b9605514c12074cb9605514c120661b5605314c1206d552605314c120
def moH8 (j : Nat) : Nat := 0
def moD9 (j : Nat) : Nat := 0xcec5ac0901b01c604d03008002762960402682010c08d0690f6c215b10000000017f26403bcc4670103323099922e4110139818e02ed04899e60b3d94f1848c56461e0a1f8008a194f10d0604cf8526a3bfc2fd83828781ad226ee827e1a818ae8c3d1c3e0f81a8f46c04d00d181a7f412068b4f99c6e0ae966aed5685349647e2f097e3c5c6d164b05729e491fce05e248e05a1d068008e8e2c6a580ee5406e51ce8c5ce8c0cec3f05cbb2ea374e9b64e4328e42eae42906d9ca6d9e0e9160e910e6d8c66e098eb05ee9804e8dd2e8cd46cc96eb462e32e6e22826e26ecc22e6d9f6da99aea03be875f4ebd9d3f3a7a71afcbed97bb2f365becb5d7fc2fec5fd2bf917e6afc95dd2b9e95fd2bed55f6abeb4fba7ed477a8bed07fcba611545c12032d7350970481a96d8a954d202e4b869531481ba660954c52030d9860530481c154d524c1203255354930480ba54d524c1202e5b35453048182605514c1202e58154530481c62e5514c120710b954530481c32e5514c120661b54c530481b5605314c120661814c53048152605314c1202d5814c530480a5605314c12054d52601204419854d52481103295354920440ba5495148110
def moH9 (j : Nat) : Nat := 0x4201a40000000180000220000000000048040c200000
def moD10 (j : Nat) : Nat := (if j<2 then (if j<1 then 0xefb2ffc7ff1fec7f71fbc7df1efc77f1bfc5ff13fc3feffcbfeaff6bfd2ff3bfcafeebfb2fe6bf7afbebedaf77bbfadfeb7f6dfbb7dedf6b7beddfb76edbfb6fadb7b5debfeafeebfaafbabdfaf7abbeadfeb7ea7fe9fda7ee9f7a7be9dfa6fe97f9ffa7fb9fde7f69efa77a9bfa5ff97fa5fd97ee5f793fe3ff8ffa3ee87fe1fd61d73505602a573505602a5635056061d425056059542505602a5425056065592605302e992605302a592605302a552605306c8a9605306e092605306d49260530694926053065492605302cda466120691a16612028da1661206d8a36612069ca3661206c49864d2066153645202e553645202e995611202e5a36052065593605202a593605206c553605202e553605206dc93605206c493605206549360520611545c1202e9545c120551535c1205cd425c1202a5a054d206d8a954d206c4a954d206a4a954d206558450d202e99550520655845052061d8450520661a54c5202e5a54c5202e1a54c5202a5a54c5202a5a04c5202a1a04c520295a04c5202e9954c5202a5954c520261954c5202e9944c5206d8a94c5206d4a94c5206e0a54c5206e0954c5206d8954c5206cc954c5206c4954c520660954c520661a14c120549a14c1202a1a14c120295a14c1206c5984c1202d5984c1202cd984c120549914c12054d824c1206d5814c120661814c120549814c1202e5814c120295814c120255814c120605804c1204c5804c1206c5534c1202e5534c1206c5524c1206c1524c12054d524c1202e9524c1202a1524c120261524c1206e1514c1206cd514c1206c9514c120661514c120609514c120605514c12054d514c1202e5514c120261514c1206d5314c120661314c120605314c120549314c1202e5314c1202e1314c1202d5314c120295314c120255314c1206c4a54c120684984c1206d8954c1206d0954c1206cc954c120684954c1206999524d202a5a1609102a5a0609106cd95609102e9956091065593609102e993609102e953609102a553609106d4a9609102e9536011054d52601102e5a3549106e193549102e993549106e583549102e583549106c1825491068d825491064d82549106e1a54c910661a54c9102e5a54c9106a5854c91054d824c110549804c1104c5804c1102e5534c110609524c11054d524c1106a193481106959348110615934811054d804811054980481106a1534811066153481102e9534811054d52481106c9514811054951481102e95148110549304811054991604306a5526043065952604306c553604206a5536042066153604202e99854c20655a3608106cd95608106c995608102e995608106d5936081054d9260810651536081064d53608102e95360810651a3548106d593548106a1935481068d935481068d925481068d825481064d825481054d8254810 else 0x61d9719875476e9d064ca7470329c9c0a87222715c489c8700f32dacb8c96a8054da18cb968117159c29c5671172d98edc2663c7059845cb652f72194d9c4653a70d94f1c165866058df981633a70584adc1614c32980edc85d3b70574edc55c3b705718db15c3b70d6cedc15b2e3256974b95a2e3256574b959636e1618db3585d2e56174b956876c955f982557c2e55575c8532e7214c45c8531172d48cdc5523c705498db252866613ded984f866553e15524f862d53e18a54f7a2e538adc84d3a71534adc54d3071d30e1c24c3a7212ce9c84a3a7212539b5474e6e10c65c541197150064ca3f476e8f91cba3d19714f011c53c476a4e411c2381e328dc29c836472e8d465c83447328cd68b9312c324c168cb2f1032cbd1cb92e19720b11ccb2b0f32caa0553292b7089e0153265f6e095e198257832494b8cb221132c860d53201132c7c44cb1e32718760dc91c83720720dc01c6f6a0720d981c79660720cca1c83324721d831b3c70c64a1c30d1370ac1a0a9ae15716b405cba90b7029d0da7a31630e8849c7a14069e8119b09f0172a5821c1963f6a6553d9895506625128ba92037064474ca901371a3901a98d0132e1805c8851a71e0849c7821c71a084dc6821a71e047dc4812070a0481c28013719f805c87c406a5ecfdb77a406d9e901a9770932dcdfd537220709c118ba6f25719b8a9c36e2a705b5fd536c65329a5ccc36974661a1fd5368516e591f581632a32588c5c6612471985fd535f7f72579fdc15e7f32579fcba5e7f2a57960b959606cd6024cb575b2e55560b954097214d51c6530d7194d59c4535870d4c39c353586614560c9512a3254418cb50616d53df5984f726613e11524f5e6d5388dc74d317193491c64d377092cddc24a0e72d24c5c6493471124e5c1490e70d21519846586611125b6434a6d10d2db3434d6c50d01b84201714f005c93b03700ec05cb3a14714e859c33a01728c81ccb2f0132cb405cb2b7d604a024cb240132c9005cb237f60c7189b31b826946e09c91a8270c6a09b31a8268c6a09931a8260c6a08ba1a3571065fd5318187285c05cb16406e85515a91450660515d93140172c4cf5ba120532c4805c1114172c4105ba0f143283c9dc30e556cc3858ca0c173282d08ba0a432e82405c908426e01da9a8061672c1405cb0516720105dc803446e4099198026665c09a596026b65409b194026e728045dca017771405b9a301556e401ada9007565c01d994007764c0030cb8f3e6ddedc5984f023291401c111ffe3ff4ffc7ff0ff6bfd8ff5bfd3ff4befcfbd3dfcf7d7df3f76fdd7f74fdcbf56fcfaf3dbcf5f3d3bfaef6f9f3e7bf9ebe76f9d7e6ef9afe5ff97be3fb8fbdfeb7f8dfd37f2df5f7d3d7fb5fdd7f35fbd7df5f6d7d75eed76f5bed5ff4ffd3fb4fdd1ff3fecff33fbcfdb3eec) else (if j<3 then 0x710c5f885e1db492d30bc09e85f4c85a40a586804e58440c2742562171919c180b1c2e900610a74f8b814804ea867b18497123eb47bd22017d1a0e844f85c17f05f818f04b9c67499c0838a0f60e051f13af184a903a6a674da40941411014369d0044e253852019c181b15226715c7469320c690e1c2e2e0616e1779609433a0ce8b016001700b8074e83ac4485d614304d7a10d112c58d19f84478ba683000415c0243454056c183d27362e5a0f86d7a4017bd163c1804cee01d247601d85c1adc143a3bf079c5806b812d785f86171501a86113a26780417cd18418d04d3c08f0d41a3e8d81a7f07fc2f068ba09ac9aae9ab3eab0aa4ea78a942a28a8029d8a6c2982a56a938a49a90ca3d28d2a28e885a17283ba05a7ee9f1a7a89e0e7719d3e72e9c3e6fd9b7a6ca9ad669f9a12675998a62c985660697a25d496ea5a5964657995aa55094ce51593fa4e693464b7925a478917a452911641d90063ea8f6e3c78ec23968dce35b8d3a32f8c2e2f68b322ae8a52268894a230885e1f687961cd86ca19085b215c84fe127845e10783d20d882fa0a4823a07e818a04080a20127fb1fda7f09fad7e55f7b7da1f587d1df2d7c5df0a7bf9ee77b01ea97a49e7d7995e4b78d9e21780ddf3778ddc976cdda27639d767571d4474a9d1273e1cd67305ca9725dc85718dc567139c3e7099c196fedbe86f65bcc6ef1ba46e55b826d51b3a6c71b026bd1ade6b59ac46addaa96a29a7c69d1a6c6991a43680d9e2667196664f990063318ab61c983a60257e95ed97925e117565c756ea5add67358a95ec572159655b554054854fa53714af51f1444505d3e74ec138a4de13404c4d2e14b0d2a449f5246489921748211b74611161452512843d50be424105e4068fea3f14f9e3e0cf573cc0ef83b6cec03a68e673938e39389ce0f37d0dd836f0dad3680d8235c0d4734e0d0633b0cd13310c9e31e0c5130acc0c2ffcbd92eb4b872d68b3a2bc0ac22a84a78294ca2e27dc9d1264497c251492623dc8d622d48a2220484f20607ee1f187941d647371c306cc1aa467e194862f184c5ee170c5a015e854314784fa13804ba1248478117843810783fe0f603bb0e683790d603370c3c2e90af829909f8263090021d07cc1d006ac184055012f04280ca025006800b4000672a6c865c5b16d2a6bd1cbaac04716ad1dbaaa476a6a11da9a60472e9521b8a5476ea9149b8a4476967828cb9d2671a7065c39b197066c29c59a0a72e6465c5982d3265d719594476ea4d49b893536de4c65c18e476a631b4c48b297062865c8892972221b4ca88297261d1ccb860a32e1865c8850a7221465c98422702111cb984197220c89c882197220889c58219716086dc781227160485c281227220011c87f19721f865ca7d2b70df4b5c17d476e1e91da97a476a5e51da978596 else (if j<4 then 0x4404600d7f904100a607f200108383089bf9d804600cf478c4014dac00f6aec40220bfafdcc80670d3cf0d9801a004fffe05184200226bb61f949019e0bff100ca87fb80029063ec227dc1e91405299fea100a4d7fea4f40a00878f848325fd4c25ebdbc60290083f843043532e861107e0861c310e602233a208367cc083bcfe0257806d02bef2809ee623e78fc40042bc03e301cd0c8029a1d408324ded06c0383ea7502931369c4285a3f880014887f1061523b9e40847012327ea010ba6d4013a94a8c9fa8042b5f13084029400eec70e1ff004915982580e8b02e9f8e4399c14d1e1096d3c700e86b69da0742db4ed03a140cfff72780743d1c1e21d48001bfe9978e01d1338d43003de4e6af270f4ee14213a001120f4b4054b38d951f901d090750c8cfa1d08affff280874323fffc61010e870f96a82399c33ff6ab99a14c00f554e878fc02b8fd2c1cd31ff6073291f96078ea5063c14fe57080e89036ca9b48d606d818694000cfdc2696481652d26b881c1adcdfa06916f2c0b80d2e581701a4022fa806915f00016fb01c3a1e5d5129104fdd92101bf46343339d12900afe1c92141bf46306fd18c0f81444a406fd18d0d8f128c8f8d584a44d72a3205f3f71142f9fb88a17cfdc450be7ee22a3f251c24291f88b094977cc2047296cface09492337116466e22878f2d4650f1e5a8cb379b07a252878f2d4656dbf8ca32fbf62384852b7324d222a64dbf8ca32a6dfc6519400013c1ac8af9a2404f06300bc3874ff000200670005fac12788d100002df603866162634048c844f0a7201b05d6175804e67685c217099ea1706dc12868b84ecaa41aab066c42e10044efca6a274a960e2e3b280abc9d08f3b32215885050f90ca9c0189608fe518704a84ebe0024084eab1ac658d1c0c6709f5c8823c42830422a83ca0cc7413c7054e160a9771d7a1324372abd07e0f763c3674c857210c83c91cc8320f399c3c20150761083d88f639d09573aade3f78f4e17b8fee3da3fda83a8f515003d660bcb538c205741200c5ba2eb84ee0bc5408f9249995064e40e90638911061ea5f2abaa5daab1870a4e892504c746e8409e8303e5c1fd280e10ba0ca7d5a6869a71c0526e152e9a519c10313a64610408525450418a15b6c69213e68b43cd68be312aab01cf494d194177b25387be193047f0bbc0179d10fa0504950f242c74480411848bb892b19c4eb156dc59b2d74b58411175b271491259dcb54a0d0fe03ff0a214381446563aab04e213304d80f0999c1692a0d217496265830b8109c8101b632426905960617e805c61316093aa9d0e9003e9c9403cc2ec705c8f063fc139cac768325b6aae111055749d055044e6e58152f86714444f9e13c315b1ef0450537044f05fc30f065c44e8f7a12e244a67450c12fb1d414cc290150b07e9 else 0x5f867b100000ebe17c02b4f595cf11dc0fca3630345180037e2e9e6c51ac4ed8e9cdcc4f5cc6028c401dbfc0dc4e1cac928c4e182d0e4f317861a03d710064f19c31e90bba01e2dc03c2c184e1b0c05cc46c5462fde871460187c42ac4cdce6f61dd9d130a92d7f2120b127719fa0b106d3f8a32b630ad526f7c202b60be1d6f39870c003efd1eb7c205dcee8ef8c8e714863bd21bbad5835a061c988001affc8982a6eb85451687a89f8a3a6c82170c60e1e3054d904a7f14516863b3ee23314cd1ddf1514776668977330998704083d41d0c078f0fc91c3a3c6c0b88c85a055b82e21189a761546562e8a2d0a38c16ce9c2f710a0f8f60815262c9612d046f5a951e5c0f805223b60aae472000a5d3fa0a8e9e4283678337a42869f890de7c202c3d8f5714ec37570f878233c1840e9aa0e82fd0084cb67200a4bba122251d1c2a6e15dd0ddd0d7262c325ea3a9eaf0a7b1ee2939a8a6706cd17a8c012f4dc36a7d639e290f1fa834285ab58a0f82899fb0407fd45698171572629ba1d1e0d4fc18585ed1340a507eef5174ee6e02c4738544f7328ac8344e6e74429ce713bb20a6f34557e2151dce0dce08b95b062d5c136f06d3609cece8a7b10e2f3e8a2069360fcfa28802b3e221c463b0cdf3054b218590b1547c200a7c7618d04008e86a63b0868366ec4d1e69628343341e9c19194c2c7036c20a06ab24019c5b9f0b0baf58ca310e33893618b6a880035629a0b6c22785528d3610000000113ea6180000059fec068d43ac546f0c0000000022fe317a9d7240006056e20000e1e231006be0caa2eaa6a801cf1bd4328a6019bc36180019eb7bb66a9c001cffbc14f29d2a818046bed10f0e4d08061ff10111a9bde6fe1a10e2200003cec7e940000dbcaa1c74e001777a253e980032fe070953015ff778b62496144c3ffee9222105601a2b1ffe492800d6b888a67706a45bfa3dd0d1a9b9d9e31590b07002f730a5c5b9cb8737ec623291ef88ca300073b9f8528177f18a412a600093f65ca06a7bbd0c2ac152c172fcb1d3338197e51522b0a7a3d2eac290bc23c60072e0a10088e3c6e51005299f8476c9514def3204205f180a333ff2301482fac307ca40222bff01991302060547e0c72f178220)))
def moH10 (j : Nat) : Nat := 0x86545800001aa6258000000000000000000000000000000000000000000048400000000000000000000000000000061acc20000000000000000000000000000008028fc0000000e000000000000000000000000000000c3a01800312000000000000000000020f0000000000000000000000000000000000000022c12c0000000000000006000000001308000000af0380000000000000000000000000000000000000000195a060008240030d8000000000000000000000000000000000000000000000000000000485000002680000000000000000000320000000000000050000000000000005c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000b00093c1040000002a00039800000266460000000000041f000000006000000000000000182e3a000000000000000000000000000000000000000000000000000000000000000000493000b48000000000000000a00000000000c3c00204c6602800000000000000000008060114500000000000000000000000004ea00000608000000000000010440021c00004c002ca0000000000000000000000000001017100000000001000000000000046000000009f6000000000009100000025c21967e600013e90680000093400000000000002e1000000d0c20004
def moD11 (j : Nat) : Nat := (if j<6 then (if j<3 then (if j<1 then 0x679940b3add05326c828fb741009ba083ed1842068c1cdb2e087196043cca021f6e808137404c5b5023ed4011f68c0903500281a30112dc80206a401533000b597005ecb003265401a32800d9930082ba47816da240b6cef1d536994a913012e87c017407ffeffefff3ff7ffaffc7fdffedff5ffa7fcffdffeeff57f7ffbdfdbfed7f63faffd3fe97efff5ff7ffbf7debed5f3ff7ffbfbbffdfeefef7efbf5df7efb77cfbdfdebeeff76fbafdbfeddf5ffaf7cffe7f73ef7ffbfedfdefdf77fb7fcffe7fb3fb9fbcfbe7bf3bf9bfcbfe3fefff7febfedfeeff57f7bfb5fbefdd7bfbdf5dfedff5ffaff57f6bf75f7adfd5fe7ff3fe9fbc7fe37f17f69573581425c5605c570581635c16059542581735056058d4158142505602a54158192645302a1914c0a564530289914c1a060530649814c152605302a5814c09260530694914c1a224530660914c19524530648914c1a46612068598480a36612066194481a764d2069593481a164d2065d934819564d2061d93480a864d20295934809864d2064d91481536452026191480936452066184481956112061d84481a36052064d8148153605202a58148093605206898048131601206a174481985d12064d73481845cd2066170481935c12061170481735c1205c570481545c12054d70481515c12050970481415c1206a553481a154d20681534819454d202a553481a550d20655434818450d2069d41481985052065541481945052061d4148184505205cd4148153505206a531481a54c52068131481954c52065131481544c5202a531480a54c52025531481a84c12069530481a24c12068530481984c12065530481914c12060930481814c12060130481534c12054930481514c1204c530480a94c1202a130480a54c12026130480954c12068c98481a824d2069c93481a624d2069493481a124d20660934819524d2025493481a564d1068993441a36491060d92441a960d102a583441a96091069582441a36091068582441a06091065582441936091054d82440a96091068980441936011054d8044152601104c580441a35491068152441935491060d5244182549102a55244182541106a532441a54c91065532441854c9102a532441a54c11060930441814c11060130441534c11054930441314c1106a120441a54811068d2044198481106552044193481106152044183481106012044153481105492044151481105412044130481106a1910c1a960430689810c19760430659810c19260430645810c152604306859808153644206a581081a36042064d8108153604206a553081a854c20685530819854c2064d53081a564c106a192041a5648106a582041a56081068d8204195608106518204193608106498204153608106a552041a35481065d520419354810649520418254810 else (if j<2 then 0xd985d46cc2e23655711b50b631b85a46d42d2469d692b4cb48da55a46d42c236a15d1b4aae8da85646d2ab0c6e5551b64a88db35246d4a88c2e5451952a28da9504654a7a36a53919529c8dba4d18dd26a36a5351b749831ba4c46d4a6232e9302974988da94b0a5d25a32a52c636a948da94a18dca48c6c92029748e8da944185ca2236a50d1b748431ba4246d4a1232e90863728230b94174dca03a6a501d32681315340745ca0236d4f51b72788da93c46cc1e232e4f11b747631ba3b0add1da36a4ed1b50768da93a46dc9c056e0e02b62708cb93818dc9bbe604d6aaa66b55313570dc9a38660d1c1726831b93392a999946d4c9c3306415b3310adc18286a0c11b3060a1a82f18da973c660b5e3705831b82c78da963c6a0b11b5058f1a52c46d2963c660b1e32a58f1852c30dd15986e4acc3745461b92a78c994d8548a4c3745015ba2830dc940c6e4a0c37051358528aac194586e49dd3724f61b827b0d993d86a09d3b504f61a327b0cc13ba6609ec3264ee99327b0c193cc54c9ed3744d69b326b4d1935a64c9ad3064d68ba2650d412bc66095e3264a61b52450d4123c66092aaa64961522418d911a36c8891b72428da9215ccb90ae6e8811b743c31ba1e46d28f3a68879db4a3aeda21d76a90e856e8711b5238c1961c18d98da36e86863743431b81a76d88d236cc651b72308da91858cc0c236e85c63742e8da5170add0b0c6e458bb622c8da91658cc0b3864c591b702a8db11546dc8a236a4511b72268da91346cc09b864c4d1b742431ba1258d409386a045c37020e1b21074da87ba6cc3dd3701ce9b30e74d407236a0391b6a1a8db30d46d4862c66031732e18c1960c46dc85a36a42d633016b9970b60cb05b36542d1b2a16d5940b66dd05236e828637414cdb30a74d9053369429997414d5a50970dd040c6e821c36a10e1a50870d1843a6d41dd34a0ee9a30774a983a36a419732e0cd5940670c983052e8191b660a8db9040adc02236a411832c08d5940470dd01236e808637404cdb50270d401236a009c34604e9b80174d400ba68c05d37200e9a9004ed1803a64c0262a60070a9c73c54e3026cf1413658a09bac404d95e836ceec41676c1db6b404dd57066de983b6d4c09b39f045ccd842ea4a12e71f3d428e38db44876da2413631208b988045cc2822e5f01174f219b77738db3b876d9dc136aee88ba706e59b82b661b05b72d7215369165cb4136d59e9b02ce55b2641edb31116d1889b66c46d985f38cc2f1b69d68e34cb409ba5938d32c826c94c11749a08ba4c04daa5026cd2813667e09ba3b04da9c826e4e1cb264f2d5327aed9131b65c84e32c4209ba1e40d10f21694750b443a09ba1a14d88d1a6606013742e7d931304dd091a6a04811742421b81012d987896e03903501c69980b36cb859c6582ceb2a1 else 0x140b2d820596a502cb4681659340b25ca03d6e4f8cb667d71b03e52dc9e296e0f14b5278f5983c7add1d996e8edeb7076f5a93b52d41dbd660edeb5274a5ba377adc9bdc6c0dd4b4a6f59533732d91b3f608dae2a46b59b834acd91a566c4d14b7466f5b93332dc19996c4cdeb3067658233acc11956548cae30a5f71852cb8dd15dc6e4aee3665771ba2ab8dc955c6d4aae34a5571952ab8a994dc6e8a14b745171b9287adc945c6e0a0cb705171b028b8d414296a0a2e33050f59828b85d145c2e4a2cb704f65b3277ada8f3d6a471eb7434f5b81a7ad40d3d6e85deb6a2ef5a5177adc8b3d6542deb7414f5b30a0ad866a36633602cb970163cb20d8e5405cf288363928ca9c88ab2e3236a6fc29757e8ca9be46d4de856eaf06b71788da9bc4cd9dda3662ed1b31748d95ba46d45ca36a2e11b4b708da8b746d2dba368add1b4f6c50b3b646d25aa368ed519476a39b7b420db5a0c6c6d11b4f6831b1b346d457a3686bc63735a14baad18dad50c6c6a91b4b5431b9a818d9d38c6e298636b4c8dbaa418d8d2232ea911b5346b198a346d4d10c2e6891b5342b198a14654d08c2e6802b673e15ba9e1adc4f0e6de78bb633c8da99e58cc4f056c67429753830b99c18d8cd0c6e265732f32b9879918d9cb986c65c63632e61b89630d8cb3c6625a1aeb2c61b99586c9ca43612521b27270d8493a0c249186e644c3612335549130dc48586623ec2a71e61b38ea0c247435ce39a9691a8da98c185cc6232a6311b53168ca98b46d4c5106da246363128da98946dd438c6e21c63630ed59586465d42236ea0c6371068cba836acac10c6e605ab2b0031b97e6a5a3ea36e5f11b52f88d987c465cbe0c2e5f11952f8a1a87b50d2bdd564ded4152f68ca97b50543da8295ec2b74f48da97a0a5d3d232a5e91b50f231b87720db3ba36d5dc636aee8da97718dcbb166c9d8c360ec8da9760add3a906d9d49368ea51b3752ed8baa36a5d5e172e8a0a97450d439bc2e5cde330e4a1a87150d2b8bc661c6aaa6e3615271785cb8a82a1c5414ae2f1b37078d8b8282e9c1e16ae154b37078cc37a82e9bde330dd55536eb0a93728685b5e330da61ba6c30dcb63e661b16330d8f9826caaa9b658549b0c172d830b96c30d935be605aeaa62d755b96a18dcb5556c9aaab62d555b06aaa5cb5382e5aaa952d561ba694edd34856e9a6c366d259b169b0d834d86a1a6c330d349536998a9b4c954da6c174d360a969b05434d8261a4c374d061b968aad9b4586c9a1e330d1359568b4c0b45554da1e172d060b968aadcb3d56d59ca36acf55a56770cc33d56559ea302cf495267aa5cb3b82e59ea96acf54a567aa4ab3986e198c36aca61b26530d8b2986e190c364c861b16430dab1986cd8cc362c6a1a16330dc31186cd88c362c4a1a16278cc31246617d2b30bc8)) else (if j<4 then 0x297e294c292328f528bd2894286b2832280427d427a7276f272126f326c626892660261525e225b02571254a251124e324b0248c2453241623ee23bc2359231c22d52286224e221421dc21af216b2130210320d520a32071203a20071fc11f911f5a1f1d1ee61e9e1e711e3a1df11db91d701d2d1cce1c691bfa1ba31b531b011a861a4a1a1319e819bd196a192318be186a180017cf1790174c170416d4168c163f160a15c4157f152e14e1149e145c140f13c71375133512fd12c01274123c11ef11c011931153111310e110ab105e10260fe40fa80f6f0f390ef20eb30e710e190dda0d8e0d410d080cc50c790c390bf20bb60b800b340aef0ab30a730a370a0009c5098d0955091d08df08b50872083407f607b3076a072b06ee06af066f063705f305be0576053504fa04b7047a043a03e303b0036b031a02e302b4025d022901e60176013000ee00c1007f0045000088c3e6465973232c7991187c8a2c3e3196d70ccb718465b2c232dae0996cf014b4b80a5a3c052d1602928b00cb757ef5a9bf7acadfdb2c6fde9537ef5a9be32d95e996eaf0cb717865b5bc32d8de29696f1eb2b78a5b2bb52dadd196d6d1495164a4a8b15254583d2a2bde9515cf498ae52d456a9686b5eb315a65b7ac32dad6196c6b0cb715665b5aa7a5c54a96eaa1eb7350f598a87ac9d43d2e6a0cb634aa5a9a37ecc51bd6a685eb3142f595a17adcd05b6c6814b534065b89e32dacf3d65679eb733865b59cb8d84e4461e66230f3170b896b8cc4adc6e646e36123719391b8c248dc54e3a89691aa5a98c7a5cc6196ca2d4b4f16a5a28b52d0c5bd6a628cb63134595867a5c41a968e05eb3103459580a2c3c04461dfdeb72fcf5957e7a5abebd661f14970f8f5987bb85abda92a1ede930f4a5a8787acabc196d5dccb70ec65b07632dc3a996cdd5eb30eb70b86fb85437dc261bd4b4adaa5a16daca9b6dc6e9b2e372d8f5b96cb8dab6196d5b2e366d971b26c32d9365c6c1b2e350d971a56cb8d1365c661b1eb30d971956c7ec1365654db2caa4d970a96cb852b65c255b2e304d771816bb898b5d66e1aab364d559b16ab2dc34d96cda4cb66d365b16952d0b4d654da6c970d371b868b8d9b45c6c9a2e304d17098687acab3db6059eb170cea5b16152d8b0296c5754b30baa5a85a52dd2abd6e555eb2aaaa5a95152d4a82969541eb2aa0a5a54f52d1a7bd64d3ccb629ca5a54e52d1a72968539eb269cf4b94e7add26996e935eb669af5a94d7a5d26bd2a534cb7498f5a94c7ad2a63d655314b749765b24b52d4a5996d5294b748f71b04752dd23196cd18cb628d71b0467ac9a34e54d194b448aa5a94452d422296a10d4b4686a5a1437acc21bd64d0ecb04873953437add21196e909eb7084f5a9427ad4213d66109eb7282f5a94152d4a0d96e502cb668165b else (if j<5 then 0x9d839d599d369d139cf19cc79ca59c799c509c2d9c149be09bb59b989b6b9b4e9b229aff9ada9abe9a819a659a449a2d99fc99cb999f9976993f991d98f198ce98a3986b985a983c982b981797f497e397ba97919759973d971296f496c696b5968c966396529627960395de95d195c0959e957d953a94fd94e694ca94a9948994559427940093d993b9939c932692fa927a91fa918b90f4909d903790168fd58fa28f748f1a8ed48e9a8e628e468e028dbc8d6d8d138cca8c768c328be58b988b3f8aeb8a9e8a638a1389e989bd8981893f88e388a1885387f2879c8764872186ef86a08663861e85d4859585478510849e845d841983e383a5836a833382fc82c08285824e81f881b681858155810e80cc806c80407fe57fa47f637f137ed87e877e557e1a7dd67d807d417cfd7cb57c6d7c187be47ba37b5b7b2b7af17ab97a677a1379cc7991793d78fe789e7860782977e677917755770876af7672762a75d675967563753674f874d1749f7451741673dc73867357731b72af726f722971df71a571667140710770cb709b705d70086fc86f8e6f486f0e6ec16e956e5d6e136dcc6d866d506d126ce26c9c6c706c336bf26bcb6b8e6b4d6b0b6ae76ab56a8a6a636a3869fd69cc697d6948691268d768b3688d6844680367e267b367806751671066de66b9665e662865f765bf6593656b651f64ce64a0645e640963cd63866365631062d262a46254622461f461ba619a6165611360d460aa6084605060045fea5f905f315ef15eca5e965e5b5e215dec5dd65daf5d745d4b5d025cd55ca05c6d5c455c215bf85bc85b9a5b795b4f5b2c5b005ac85a8e5a4f5a1559db599a595a591158e058a95862581657d757935758570056bd56755634560b55e755bc5585554e551654db54a354625430540553b8537d5341530452d952b1526f523f520f51e051925167512750ed50a55072503c4ffa4fb94f844f474f024ece4e7e4e4b4dfc4dc64d854d554d094cb84c6c4c354c074bc34b8e4b524b124ac94a694a304a0549d4498f494d490848e148af4879482347dc47a7476a472b46e9469a4640460145b7455d450f44ca448c444d441543e043a64376432742cd428d424a41f541ab4193413f412240d740ba409a405c40223fe63fa43f663f1c3ef53eb73e793e503e233e003dda3d9c3d543d2b3ce13cb43c683c2a3bf13bb73b973b6c3b403b0a3aee3aa43a6d3a3239ef39aa3965392138c238803861384237fb37ba377b3754371f36c6368d3651362035d435863547351334e0349c3461342933e933b733853351331632e23299325231fe31c331853150311d30dd30a5306c30372ff92fc02f7d2f432f022ec02e6f2e2d2df22dbc2d762d482d1a2cf02cbf2c962c6d2c322c0a2bd22b9f2b6b2b3d2b002ace2aa82a762a422a1429dd29a6 else 0x78684c28b26192e5852c1960b082ca382061110b684f82ee4c4c5b055027e124e180db52ab85390429814b98a40b5a3fd47618984ec3cd2052b1a37a505d1746a53eeaad9281bec2685a0270c84b14c50f422074d0a68c62aac4a66ad118340c56624512e89a5430aa8caa945a3a074e83036a1b6193c1124b104f82631d19018924848424356a66853690029094349c850027a8c4555a5c68c609003393fa90a0eb2896244202c91a48c4f41eee9aa2619c347e6010c921602ed267e00863f82fc90c3a0160ccf610d1ce16790b4760ad454b8f72ac43a04eb095c2e822a54029a467733b20f4cea1751758381f3c670a0d1a70ad8c2e2c86228900f6a62ca4033b494c27b2204ce14cc26611e991a740abf222989a58e49530a908c75a22e8ba506550141a99c36f4702b8f1639aacc229cc4eb0a429072c060a556c7bd4851d28ea19bc2c619c2fec2e22c39d2ccf8a60d69a2c2e389407d615316ac50a402962cb014763852720a14a0500e1151f449023a63130f7456d41c54227265827d1a6834215b64e120d506c90b3a0673889888c2371d742ec440a8514296acb5c38300582f8480bdf06792388493a057386c13513a7210306c54c34611108819a0c2f2518c262ec282a40286181098e84827347ba2a68f4265a10e103a0e8cfa260d729d0268c67e3099d0351601700f063138617e048603403444b0bd1618b069074868ec26786db485a0c2fa17ef17683ac5c68309852228c2184097069c2f81a370bb8bbc2fe010d104bf0c3a360c6f0bf83da09e1a84b7811c1fc138c0fbc0b7c082c04dc020bfefbfc7bf9fbf6fbf32bf07bed1bea3be85be52be16bdf6bdd5bd9bbd6dbd42bcffbcc4bc93bc68bc3cbc0dbbd6bbb7bb97bb70bb50bb2ebb07bae8bac9ba9fba6bba3eba17b9e7b9c0b99fb978b94eb92eb910b8edb8ddb8c0b89eb88bb863b830b7f4b7b2b788b75eb73ab6fcb6c1b699b666b62bb601b5cab5abb594b56eb54fb527b4eab4aeb48ab467b442b417b3e3b3beb39ab370b360b33bb313b2e3b2bfb284b251b21db1f7b1bcb19ab178b144b121b0f0b0cbb0abb077b04bb031affeafd2afa5af7daf5aaf33af0caef0aec5ae9aae78ae58ae3aae07adedadbbada1ad7fad53ad2facf9acc4ac9bac73ac36ac0aabe8abc2ab9cab6cab46ab14aaf2aab6aa75aa56aa37aa14a9e2a9bfa996a95ea92ba905a8dfa8cfa8c0a89da872a85fa833a80ca7e3a7c0a795a779a762a743a71ea6f7a6cba6aaa68ea665a64fa624a5fea5d9a5c2a59ca57ba55ea53ea52fa51ea4ffa4e0a4c1a4b9a4a4a47fa45aa42fa409a3e5a3c8a3a3a392a370a346a318a2e9a2baa289a255a235a209a1e8a1aaa180a156a137a10da0e3a0b9a07da054a0269ff29fc79f9c9f5e9f1c9ee79ec09eaa9e8e9e6d9e4b9e289dff9de89dd89db4))) else (if j<9 then (if j<7 then 0xc99990ecf764e1c99990ecc04e1e50999112ff87d13086764400407f981c8097fc3e89856ab22424bf0c0c15a8ca8a7fcbe6884eab222dfe7d02d80487644b300bf17472426ab22b5e3d9e1314c1644db06cf09877332275e3d9e1314c16449ba2eecf3cee6644fef15b80c9256313ffd807009a74644d61c19a6da71a49fd9f991261780b22ab0fce54d8b6ed8d45ff2f70b8e2b1a69f67ff10c2a34644abe081261780b2261f0fd5a616d33225efeab2075908345b0c656579b64ea36c69e7e2f4e34c4d2664555ffe15a3a61a442a32abd7f0d20c92563577371d2bc68004fff782d530d221519561af769d2578d2efff73a4a89e532240000000000f380035f89ed4902bc0f084eac0b22fd8a8004d2f89f1a844aa00fd48c3014ae70bdbb24610415400098286e30078db7fe9e83c20d119a887bd2fd4662cda54b064c84634e10e2951ef0e99013378cd647c87f131714416c4291ac0d586ca71fc82659e14966293c313a8e90ac06a431826562784f2295178444053ca4f0fc88386c92de96e62be8f25022f00cc870837a0dd616b0a984542ca1268e1480a37a155096845421a10507a85342bd079a30a492b2b20d8d2c7c1461bac97d4beeab4abe31ec7763aa630deb18c12994c220ec67631b21d8f49fe32343083f833e187079455f59527fd1928fd474e148623812475240050182e5b289c0dd1accd5661026538562b14c7236913d5321a69064a64373637664105c3301a4294c8045d21b4032a2e88a412863549ed090557a364a018d227d639a9f0ab046a42549dc09ea7a27e15288c6450078d194254c5a42331650f745a82c122125b04b82394438e8c92642b1a0abce298baa54642b214909484642120708e0468232174d0a843421810ae71020c12c113b08d8183546af35a05c82e0175d020c542b20ff06223235a818b0935856c0f46e0ca03e00df68a2a894782a691d55a61941fb06d2974a5995ec470bcb115898ca90b3c54588c9124420290142a355189838c18ad406403ba1c90b608fa36e5a72cd45e0cb2534a3490231ac24f4010e0a1411f852a18294ae0a90fa06db0a5846c2091c92f49d741f33f50a096a1913455824cf46820d858e7461a2f16a229a1868a2422865f191a9a48810b8156515704aab95582010c544088de444c25a15909e68da39841c1e61b8e36a11e08d4900c841342d54d50b084498a5c54478681785210b52d8400229266340814a5956abb09e8d21490a2b020b2c13a614d1aea641e914153b86ccd0c68f343aa0820419e0a52486895cc4662516710b876a4971a20d00a251c9857c000ef076c18423635048395e30ae54187b58fd1ed171a5343fc2c923b96a384dc1782e708307d1fda0852ea3cc80256d824061a09425834b29ec31c0fcc3251b40890670a7219e0ac505c7225b42d21bf else (if j<8 then 0xf3cb6fab1981f849388cc8791b5d7a64363cc8f3a990de7fe049880314cc5ff56ac666ae7f924b333f4fb46cd332203937f90ac6785f34a3a09c54d49bfed633e5fd26b8014653c5eb29ee52e002b51954c1c9bfce633a9fc400a32941eff7fae25a99101fca5eac6657f2f602cfc939c991423fb0b07c33164fee10028ca66a07eb23c1309950ef96463217cfe412e005194e5ca69f93633b9ff821d04ca62fb40ac66f3f904b801465382dfe8f3580532233cb6fab1981f849388cc87dbfbdaa96671a4261108a195be7fe018816f0ca893f8a11bdb1f1441520e8e0ffa5ef34d19322fae076948bc329cc7be11b2908cc6d7c09e1008cc884b7fd813633c30f8f60da6d666454731d364ea36c6a4e47f4c5633b171fd2d98cf2fc7a180a643e5a8043dcdd4ccf0278402332232ccf30ca86536cfcf74a0e81101990cff2199d190d2f27950c0532201ff8ba9ac02991117fda0600a329c4ff7a849c0008632a5a9f878158cf27f980c00a329d0fccd26bd866a3195277e75d2215194e87e66935b630d68ca953950b66bf200ed50000000051f07f8e71d95dab000008bc2e38a125fc80235d5a000000d781c604503afbf8b402bdcf73eb69b799081e1a755b9fc77796cc0af282a5539e06d80d5dfde486dd54000a7f0009bd4905c525202c98c02c52fff0a66a8ca29ccd08de1a5c053a47698600e41ae9d2111c800097f9a9e2752344baa92f58affc2ada64054008780000011fe360df00502b404bc0000fea70ad4902a8053c0000b023b99f827ada00ae65fb1b141b62cada6b9038c698c703aeefac755c580a9024d6cacca5f0c80a907e2ed6e00865bfd6c6e46884400a9000f3f33d2c2fb0a054a999c4e4d6029a0fffd89b4e6a112a8f3f4bdaa44f8d4c5441ff92a647bc6a11002ab4ff6c8dde0490c30155a7e07d909218602a2de9ffb482718c08963ffe138c6252504054932fd1f10b8008604521e47dfec7c8890c301544c1fc59184318112037edb6431811126b607f129380a74bf2fe28302bc0108a903f8a241e380a7ebf4ed4bc828020c055640705d240a6f13a8b80bc31af6800b437900638087fde77f477453edca4188d814d23ed1442c08e34dffd285039c80820aa6cf396e00820a9dcd4ff13bb42082a807c0ef274884288960a7f0144214459ffe92e810d4ceff65d972044000a2af7f72934040816381dfff62f01108513e7f63e2e6946041041055627c5e53060820aa12fff6eccd1980820aa4033dac03202113fb75202d7cf1280b4c607f07282f5f761b131767b9d1875473da95547bbcd331fa64d514703d2002f5f4c9aa44c81147f82536238ba823c0ca6a7fbfe00017c040a9b4a90001d9e5d143586c50057f72881d975380f7f43dfa6d97540107f43d2371cd3a18106b785b9a6ebccceedd50194ecf66ce8 else 0x84214537b67e667ff2444d547f104379f82082a9ec7ca004cd8fce39182143937f96470444d207aa069f13ac404000155a5f9d72952802082a9875fe3c800143bbffcdb048c10a22157ddb60c80014483cdf059ca20005126ec83ff0dfb204000a2c2ff53fe1daa274080002ab03ffc8a4d280054f0c96e2a3d178800145b9fff1320b67c1610000556079e07dffdcb4a00154c1e6d4026c20820aa60fe07599d8182a7dbc0058e7e700550a6002c6bf0054e8eef84e4d428747364899e350a22d483fa210a1c1ff9d1a011e08800145f9fc2fda144d59450410557f3fa82402b8c2d8f2f83e21d9f3e30a242feb5c6367c16100005576edc541b61788001458f212251ffc5f8acf058400015507ca89915ca0f7272cf8800145ac790914ff0eb8995e3f93e21084288a7fc80810c00a22aff8900808a0a9d6fe852c2082082a8a7c1f86810c00a248ffef31c46080002a95e3c0a548f6ffe10102180144cbf9bd64c20005135d571c0267ae9a58e0134374f2a2656edcca89999ff47d8cf09428893fd66f2fa086082a96fd58e01338adca2d9f45e2000517bfdcb1e424857283c5eabc1100028b4ffe702c588009aa8fff583041054f47fa4c0c1041538ea36923542b4fc366667ea0584286e65f6299610a22e5d689fafd7c91f75086082aacfffcb2b1a44d04f97f8284610a215fd782aeb88c2144dbf062fe3984610a249fefbe2bae23085150eefbb56042108515d7ff5b896d18233860820ab30fe239d8390182a81f62e48d17c3c91ba7ea314c0e201816423e0f9b9704210a266ff858c76104153d3fc3002858b93d4f30015301c7c5f93f2cc3049800aac08ff6ba96005100829fdb671285110eb8ec894287db80f0007d5b02282aaa6280df07b3884210a2f1db9bc7a31106c4ebd718ba2cc43b1c0d233318a6cbc426ba5b46326a9b3d5f7aa035b14f1bf1bb877e698cd7fa32924f3029506cb18ba2cc43fdeb4042ce94de7fa5a035b14d47fb1fa2a0c629f5eb8c5d16621d2ddbbf1889d9814553c781e6cbd6dccc9aa00f368268cc62d731052ad4c1edb16ba1153a9d8aa76e01461500340aff565a87d32df2f2ab50ebbf05f2c002a5d8e8c3c5bfd303111cf87e8ac399888c7ff6a25ccc43b3ecab92bc661b130fa1dd7c27988837357f9bd09353112afe2f4561ccc4430fc6600f26189b1c9c4d27f4fc6b0d8983926c09046f4c20d3559389a4fe9f8d61b122ff6572210da6235fd5c8843698726987076fa928da6291f7cfda5a860138d3f96a184d1bb49aa5e61807c34ec3f11edf56a141364f5e70a776be8fbc0ae69f9549f3ea175db47da3fdea1d1f7287dd2d43a2efa7acc0c43938c81fbbd0cb7f805788828ca751ffc3c9833179f8874c85e0cfe3d3db19dd93278a85321d9fbb64ccc86779bfe1e63190eef37fc3cc6321)) else (if j<11 then (if j<10 then 0x1c200041193eff9ea7288887869fe0f063021f1fe4a3438c604407a862433279e1890cd0bfe0810c180040ec83dff5133c3418063d1cf64c9c3f298c5a4344df2b788188a60fca25aa90d137fb938a19a108a8eff62034121a60f9c31148031ffa1e2643236458622ac9b7fdace8888727d2d6744443834fea20ac604451d2f64405293fb8c6042c3fb61690bd248c60464bffb3bbb6d438043022c9f9e82cc886f3fbc0fafa70622a12ff03ffcaa40cb0c30154069e011fb43014e071a857c1d218602a63d00b0cb77f9db28508dc182080ab83ff1751d012229d7a5faf29148022ffa9d232600c108aa0f04af4660686fe01f466067017bf55da082319781385181f0774ba4210ecfff29c8b166f984204589ffe96400c188a7ab9348622967cf44e14717f8aa230c8878bfbf914384200108aac793a0d6ff9b14cf601e8110380ab23b9dbf5651a981420c3015bf3f122f68306018f47f4862290afaf8558e0298004feb70c18063136ffb5dcd111104fa5aee68888899c1139fc8c60429bff5722718c088162fe4644283fcfab16530863022e1fc9231810c77fe9486180a64ff30e4acc0d13f3c09228e8dea590ccb3e30608c48fe85e805867a7e674fd22187a01628caff90c6042b7fc468656fff8466066a3ff12106180a783e68dce186029e0fa328e7ac1c0542dff49820c3014e07fca1345084538dfb30a0d858e02a347fe903a960c231fcc6fe1a13a83c701532f337098c08783ff9db1c3114d6c1ff303b60863022ac8df85d49c0608202a84fd6ec114b4c4542bfff5a0bcf8c6044d573fa9a86180a7cbfdb950b9c130004180ac5b89fadb0808a9151e7ffec7e5c90c3015176b607a9a86180a8cc672b3033e5863605243668475186d089eb4e1741104f5041468f0222ee250b5f09029d2fc701462c6053f9f8a168ae205385c7f5d4eaa2b02a005b9391f00a65734d8a230d83fe200a582519e00c917e3fb1220005114ffd554220005102fff33091000288d5d47e804913e99e80490857fbce8d080014571a7d42001531b67f548014357f917922267028ffff3151818021aa61a7044214333e4f89c6a042144c9f9ab78041054feecfd5ec35020005146f093c2210a1ecafcff6080487366ff6f9144811a265b3ee8e0e20005134d3efea900287f63c3213a042144cb47e547a684000a2b9fcde84000a1c9ffee5dbfdc684000a2f3f87169111345df9427c3258682004aae63f0002210a20062fd3644102058fefd94710850d2ffb5ef887c952005170e4ecfdac7c3f100028be9ff35642da490102c9cb7f96470444d39e153f91133abff02bd528800144cbf8f1e4000a1e3fe7c44fd3089a79e5fc33944000a255ff4925ee342000516d7ffc69b3a079510100005598fa3b5740842882807ff06ccc2fc00f702686c66f4df5f20 else 0x234ba7811073c37f2583408063a5fe0c8fd28ae11e5504055d5fc4a19402130150441fc48d10c81b0405569ff3bf6b4370100e9a8202b0000affff3bc7e8aa500aa3b2dc0bcbb80a797ede6d844767411397c72a02605318fd659a20dc908100c9cb836b1640580540077dcf839980d02a003bee7c1c08b0b80a9d80fd11c42aa09508398c2617d626d60064e8fc4562ac00c6000000016fd8fc5c64c3d0d3a02bd67619def806e118ecfe380c0c8cc2411487ff11ae2805323f2a3e98160811287fc0302310029f6e76858309753d9b19234c900a753ffa734147b4a7d79e0a02ce501122fc147782802206fff87eb7080c702400aa9dff305971c28031edc943999410f9dff1d9e5acf2e73cf84ad26e1022c00031fc2726c00c713ffe0f6814a658bd96a00ac00fcd6b00e4030fee58fe26c8099b6015616a7838b354980a80bea9f2e0912a0540057bbb3f6400d484055058d53e7ca9b0a700af76e7c6400d48405505911fb951d4c47802ff83b83a9cac194581d67be12a40000fdaf75aff58eb8eaaabd563b8538461505793d9fc4a784815000179919fa0e443d91f30108c7d2451a3d91e7c02b80a7fdb0cea00aa0002a7fe805c5f2356e5c4cc388d478c6795821d1d082640039ca6102e2c4f891386e2018d0702cbb2eabd4f53e4f4e4e0e76fd1006569f02693d5eef9cb0955574f200000297eb2ac8b3c34b5a3f23b4e0397237389d4b8312359411f961287b21c1ab0fddbb4ffc631c28621602b1efe176eeda500a7e48ab3d5888110f7f4bb846ddb002a14fffef5803ce4cf01015437dc778118aad4e037743f2bac671080c90787a860d45985644940473def4591e554129f7633e808e0af0c0322cff9ced3035f248c602a8026fe6b1dd90031d77e6fa4d0062f1c8d94f6a940014a35be4c80a803cf0f8149f7c594d00e535dffc6000a7df379015203f458cad200318000f5f458cd5c673e00003dffd21b3a402a8a0597e308b39442bfd49cc9835adff81c7c005c00c94e3c8200573dc4f9d01002805452afaa6f7185050114cfbf97ff0d0410db4519f8348052d014e67e0d470ca1a02a31f6e11685abec7644428053dbfd78a4013404474ff8447806285eeff2377c1014ff7f8d34da51a0002384ab6ff7875d52bc206ac1fd182a03c0319efe27e91a11c780a9c18019f0b62031917d684c6cd1284201938de44102dc957136b65a8014ff6e7c695694810a054fbff4e095802a2808a7beececb20839e02a5df17f250bc087bbfb5ade2682029fdfe31e9602196ffeab380418500a90635f02b686a7eaf93043140446cfe69d4a1628031f5afb34042bbfd65cd998c822177fe12070d10118e5be1bd71a1410463c6701a43357e01cd4248d0df4c62d219e33d06243388f5d44c14817fe29286d11111bd6eb88bc149b5fce3192) else (if j<12 then 0x992146fd0468110429c8e5f12bb8a5360f6e865892b91087626da159a10f9f11aca23f25988312b6b17b1c118aec316c06ed2c4eb8131bd52e37122ee31dfdb223d89cff0b06168d8cbd38bb2207af5038cefee40f52657a59d02724be467a124c17a8f1e08b9a90bf6a5153c0074d486a78016d215cfb3c294866c68a9e274d485a78ada4229f07a8dcf9b528e1c089d0a16aacc274ec04c353e63d4601a6ca28beb998d201ef017a90068fe18a6225f79a894916b65dd488d4cf83f38e0e2527cf0783ce2ee381fa81a1313866751806c52be00995894a37f2002b1297b7f008300d8bd78f6a4711d4d86129f4717f5a112d4a4ece9c84abffc0344384729c1b7c50d48606df143521a1f74e4265912660d4b3694d98352d2dc4e84d0c23ff3280b18658c0be18102c4c39bf51a1a974f6be038a0a9a8f7908c35280c9fcc06c4fb4f851bc04e3aa007eab427a03254c75dffe036803629dedc1c4a4c37a885afd20cc8fa2909e93e9a4274a7a9ca4d6df383342fadec2a1c1c3534c4a41df703444262ee71f1d958945d581b8fb38603719bd52330973e1a70a6236fc03987edd3ac459c90369cc04c49ee6059c73b84c2befa30c1804e50103f4d2989e51d4a3a3fb4d32252f1df920d8859dd1129573c50771d98ec92e160d7ed12af9de969dc61d4ee6cdd47cd9e1c8472e74416c6ea9c06a655bff449a3430a8edcb324359940732e189cceabaf857440bea2dd094dfc2442dc8afec25a10d7f983026222f512cd3682630ad0a43bdea35de0ab9414877f9ea45de0f6f88181311f748a309885b2c6bc1c6098d9ca0ac9ef878f6121643bbda3b3c1f3708a957783358e3f04a5e1fd24a5624ad08c7cae087624877b0252616de1f995682bbc157a709a115e9eb9088bf3de1044d0c531f37231ad008a4d8ee5ce898f38a8e07863d87dbe5b98641d7309345dca261fcbe935299c6f063a4a2d41ff149e7ed3947061fda3000008ffee1de415b0a820684802bc000323fc79001bf80000000e75a0545b3e9792436c400bf80000000c740a8b67f27b92436c40008fe000121fe8ce2cb4b408d7000000000063ffe00539b903d9aff1f377fd950000034e0037d12403b594000001d7ec7ae2f416de4fe56b445f570c9f47bdd97d863b1303e879da55b16748e8b814c5fbffe4e03a86dc80718f2aecabccead279eba6a9abf8fea4f3cb69e9a1dbae8bd6e228c08a8ec8047febbc93cb6a05047feeffa40e5b8912bf0b3ffe13bce86917e7ff026ff9c1cf04f31e55ba1e9fedf8094956e2aef076fc06d239e586daaec08767fff4bd8e6265d8effbbe13bd62631757bbfb8e89e580994aa3391f5d4e5863283b740561bfab2874cb260675424649fccc1d8818c58202a8bff1007096903502ff46dab83141c08064db4ff20310bf7b2448b14baff46 else 0x51f9debbc611e00000c5b2fe306f000002a09ff263800000157f0f9400000213c77cab7fa42844a541c97a140262eefa1187626efa002a62107677f75d530377c39c9c0efa21ef2605cf52bbe1ce4e077d0fe647f322252fbed6b09d7f8140369a99efdf02aa022eaa2107ad6125794c18627afb2c890b953c882ce9ead8ae776f3cb69567f98d01010d2b63f6f865598f956c65b81810dd35355200d0ada5e23df2cfb8633fa5e42394bd677fa1e0652991f1874262e2b061c5fcab32a4c5c560c3c2078ca921e8ae32c28bb7a5841be3894719c37c02727c703840a1972877ed0147391af73f82527af199ca8b62b5ee7f04a437ba10c258f22812c47ba3c0a5a9598344a13be92e64cfcf388cb5e4561f58e2c5cc7b30fd2c124f905006275ff8830652a60bf8f92105584a7e9f47ee0c1c48c71f97d74562c4cbc4f583a97985aeca15effee117aa092a70bf8f9ae5222d4e9bc27a758897e0d770c5a9b17bcfaf1118b631cf4537c189893721858d7719c7b7261fae0c2d399994293a466f619afa466f6206fc10011fa0171847fe1a4d28c171923bef6f8ea2364cb309fa068a90efc8a61152d0ffc572230628df3b27291a28b32d9b87de0e9cc44ba1c0f1c8e71babcc061e256b8aafcc462f77d43df1e8ffb1c02f79cc6cdff7f0efdf8a0001d3ad3d5cb24ef8f75272fe314c83aa3c6c8c6c9b8f1ecd1684adffd976b16c537d18a508bb08cb9ca0c5c6a0eb24296f919619e619cf0a7572987c75043725b70307cde2c4b98839773d2208eb91ef4b8952d4ac7fa172548ef2765a100febbc85246f01c32c4f3d72a36bc1a2c894ad7834591296e3469ce3ccbc60650f2a4190eff78ab700537bd01068f73b23b84c3fbd0107768aa05267f77a67a3329ed7cc237bff2624e0510fefefc8874b587366fba5ac2c1f6e45552d5fc76ae6092eaa01f7f92e721908fdb58487e9165a175ea244985cfc7e9b83867e9ca8823125f56ab119687e4e954b8c008effc831a7a9f47a1f92cb2cc098f0d211610dc24e42434855685c3e468110429a3e344cb2a3cde5))))
def moH11 (j : Nat) : Nat := (if j<1 then 0x2205cad80000000000083a409f8000000105080000000c0d20000000604c80ef02bc0000000c09abc24000000000000000000406a000001180002d1c887488b4000000000000000000000002120bf2692287fc07012f307a000040cc8c0f442085a0000000000040fc000121d00004120000000000000000000000030602eb5000133650a48000000000000000000003a82d400010e5414a04500000000000000000000d268153a41420a000000000001004e028000181040762140c172000261e0000000000000000000000000020a900004dee0528000413a000000000000000000000017a800000000000000000000001213504f60be000000000000c8900000000092000000008a05259000000000000000000000000000000000041f40000846c66b0000000000000000001005f09ac12900000001058000091059054000000089573c4c0000c91c10e00006906088000000000002031000018bc000091f0000000000000000000000000000009d040000000652e0001c22d4790000c1c93d140000000000000012528000c961806581d8000009600000000000000001e00200000012f04780000eba000000000006c3b000003b40000000413800000000000827a000000000009e1600000000000290702cc00000000254000000000000000000000002e452102442079027708d5cabe056e202c24c8090430412b960600000000000000001500000000026400000000000000190180000ce1c2000000000000041ca9bda03400000844000000000000000000004700004176446c0002433000000000000000000000030a20000000000000002018c18a000000064bfc25d12bf83b2e3a00010326690a0e7000020cc00046f3000181740000000000029e8000414e000000012a68000000080e405e0000028200000000000000002a000000000000002c0000000000003600000000000000000000000000000000006ebf0000000206fa10104ed107c0000000125a00000000000000000000004044515800022308000000000002118000811e0001b5e00000000000000040430000000348c00000822000000000000000800d060a0d70000000002f800000000000000480449da0000000000000000003277b67e000000000000000815c00000000000000000000000000000000000000000c00e0003077a035c04e000174e0900000000000000000000000000000000423a00000000000000102b000000009947832000000004141a43207c413609620000000053200ab4ad443600004272000000000000000000000000008dcf83d80006cd827304104051027250040402028921040432255021520171327041300040410121810102007151a001000612019a311129120300154030102020100001303025005001022120000013250030200070 else (if j<2 then 0x2ab800000002037d05d0000000372ea2be92340120000000000000002331000001c4000303d0000000000000000000000000000000636000000000000000c95c0000000000000000000000000000014388000000000000000000000081ac84d0000241b0001b0100000000805e000000066f2000093b908fa02900000000000000000000000000000080ce01c40a884120000000000044454270000307180000001a3cf06700004826000101b2314827d09ed375691e00000000000213c50cc80700078000000000000004045000000006010000e24a0000000284ec00aa41241a80000000000000000000000241c00000000001b8b400000000812000000000000000000000000000000000000000000000000000000000000000289300000000000221c70e100000000000000081fc00004a000001202a3e54144110000000000000000000104680006d2500000000000000000000003009690dc09e90d218900000000000320c80000001043801800000000c49127980000000000000000004530834902c0000000000000000000a61e0000000000000000000000000000000000000000000000000000600e00c8000000000000000050c0000000000000000000000000000000370000000134780000000648c00010498000024a0002067c07c81940000000000000000000040c10751c400012a728340001225400020f7829689ea959800011cc000262e0000000000000004033c1d7bb31019402340c3b22c036000000001bf4000000000000000000000000db103c0006c5785f6000000032ba00000000000400d000081fc000000000000000000000000004ab4000000060b800000490000407600a803e80009a9200000000084591a000000000000000000000000000000000000020e640c4000000000000224000117d0000000000000458668c16d00b0000000000000000000000091e2000000000000000000000000000000000117f40b740fc000000000000000000000000000000029d11ee08cc1f6052001ba034803600000000933019b837384600000000000106a8000caa4c914000201f403c00000004d1f886a0000000463a4dd98383a2de131c85f02980002c86c078842d0328059000182580000000000000000000000521e0000000040c000094b400000000000000106c8000000000007396551000000000000000000000030392917000103500000000da9892e80000000000100ae254e03a0114000247a000000000a800750000115a0003256c0534231cb2f089e08dc1560002097a0dd0000000000000000000000000000000000000000000a240c600010248000022c0003219000000000000000606b000004140004e7c0130002800000004185b154000000000000000000000000013230000000080eb39b4081800 else 0x131b80000000000382f201300018054000000002440002085000000013c3c00000004004000000000500001c38c0000000000000000000000000000000000000000000000000000000024e30878c5e000303b94510111000104210216095190e000000000008260000000060a410c2000120e44b4c9540000000000000000002029400c0000000000000000000000000020c60000000105d000084b6000302f0f11a0b782a808aad1600013c04000409ac137b40901700000000000325ccd480000000000000000001021400000000000051c00000000000000000000000001827c000000000000003023c0bf000000000000000000000000004076d9c000000000000000000000000000000000000000000000000000518000000000000000000001000000000000522a00034758000000000000000000c28c9ba307080000000000004ec3021ce1034c07800000000000147ac86341200088000000000000000000601000018368000000001f20000000411bd9ac12f695660b49e72000100d000000008378050c8dfc18600f4000214c00000000000000000000000039d4ee41e60002002005a00000000000211900000000000000064e4000100a2e310000a0e000000000000dc447856d2a823800000000000000121ad025622b19ca0003454800000018147082000041ea000209d926d0000000000000000001093d4390000010582440002c8a0000000008600000000053c000014d00000000000000000000000616800001980000000692081a0000000029060001101400000000000a1d72086cdd0000000203a0c59010600000006cda00000000000000081b6000000000000000000000000000000000000000000000000102da23a91601a5e099814500000000000000000000000000004ec02300181508000c8bb854000000000259815b68d80001a4624e80592cdb00000000000203e0000820133220ff00f70434016e12702420000000000000e0bacc00000fda95484de06200000000a1cc000000000009080000000000008000000000001e200000000000650400000000000c04a000000000000000000000000008040000048ca1238128000062a0000ccca000108160d1000181700000000000000000000000822e000000060c7813200000000000000000000000000ccce000102b80000000bd1800052b1000000010130000017083a20a9a0cb0000000109400000001005800000bdcdd200000000000000100fc0430d15000029ec4598000000082c40000000000184b400000000000000215b800000000000000627d000110754780000000000003180000820c000000000790001b388000000081128ae9140202190da01800000000000000))
def moD12 (j : Nat) : Nat := (if j<3 then (if j<1 then 0xd308fe9547f4cc3da54ded352ee9a1774d03ba651dd2e8ee8a9774cc39a655cd330de9956f4c3b7a5cdbd2a6de9a96b4d2b5a681ad32ad69946b4aa35a2a5ad14ad68956b4d2b3a6859d330ce995674c133a6059d2a6ce95267498b3a6617d32abe9a85b4d2ada6896d330b69a8574d2aba68d5d330ae995574c9aba60d5d352a69a94f4d2a7a68d3d3429e9a04f4caa7a64d3d2a69e8a94f4d125a64d2d2a6969524b498a5a6a51d3468e9a0474c9a3a60d1d34486993434c121a6a4fd34a7e9953f4c29fa694ed330769823b4c09da548ed3506e9a5374cc1ba64cdd2a66e9a22b4a915a68c6d2a6369a8174d08ba6941d3460e953074d180369706b317c187be4b2df258ef82e374963ba4b2d9258eb9a855b598a9acad4d64aa6b5348da8a06d2d0368a86b3143595a1ac950d69276b433b4a39dacc4cd66256b2f2b59595a4c4ad66246b272349891a49c836a636b2b1b5a9886d4c4e6622195310da2846d440d66201b52fc1977dac9bf061df82e8fe59879acc3d964decb08f41737a0b8bd9551ecaa6f65517b2a0bcd6a5d6952e8da571acc38d655c9b08e0da76dacc36d655b9b28dcd846dad4b43695acb40d359469a54b596a19cb4ace5a2672d0b3966196b30ce595672c8b396099cb02ce58066aa9b375499caa2cd53167254b392a19c94ace4986724ab2368d81b42c0da85c6d2ae368576b30bb5955da4aaed6a166b4ab35a259acc2cd6a156b46ab59855acaaad64d56b52a35a94c6d4a6d65536b269b4a94dac9a4d6a511b528b59346ec122d6a4f1b4a7b5953c6d29cd660ecb00755533aa989d96a0d1b506e5a5346d29b968cdcb306b598372ca9b964cd6b266e585372c19b9600dcaa66dd52372a81b94c0d6b505b5a9286d114d648a6b424b5a521ad40ed54c76b5230da319ac98cd6a451b5028da115acc0ad69436b50135a509ad482368c16b2a0b59305ad480368c06b2605d82000d4e0565ef8b09681a9b22b25602a6b0153481a98c054c406a610352f95977debabcf5d1e7ae6f3d717aca13c02a5d4328d80a9698cc33454d9b2a4cd131642d3ae269970352a00a9500d4a602a530152881a93c0549ec64cdb2a46e15134cd11806a4a2b2e51996296c89406a462330301a9152c98a568c44b4a1a9a8094d28406a4123300959704ccb027654143280a593054c90206a402b2e02194012c980a6480fffffeffcffbffaff7ff6feffbffaff7ff7eeffdffdfedfddfbdf7defddfdbfd7fcffbffbbfb7f9ff5cd605c5605c160591605096050560645306053024530661206512064d20645206112060520601205d1205cd205c12054d2050d20505204c5204c1202612024d2064d106491060d10609106011054910541104c9104c110481106583064430604306602064c20644206042054c2065c1064c10648106081054810 else (if j<2 then 0x6da67140a15a0c13d4a0c91258658290171458aaba398c4c84a124b5a080ff0faa588a427484c6678a6a83c9084512e12fc58141c6d4701ae1a81a3856150868452c751a7a74c4445017d494c364561a2894a90139c2046187b47bc1889ce0184fc0984884a454488854a10674850181a3dc2f852a3ba09c7ba36143e1718da0ec94c88861e2e86d690683c6112dc35c1ec08c1fea5dd29ba027342e545c7c38ddf187e2adc44b867f076e06dbfbf7dbef4dddc5ba1371b6df5db5fb5a36946cfbd977b1ab6206becd75baddf5a4eb14d5c1a96750fe9edd373a5ef49ee8ffd179a1eb410e76ece7d9c5b373e693cc5d977b2c9e562ca2d9207204e3c7c6f98c9314ce235c373853f07ae0a4c07d7f4efb5df38bdd37a7af255debba957316e1ddbfbb7856deeda35afdb53169aed14d9f0b36965f2ca1590cb15d60cabe75746adaf5ab6b3c5649ac3d57b6ad7d57aaa935452a6ad497a8d150529f353a2a69d4bea9485232a3cd462e89ad103a18f41ee8074f8d9e2f3b7674ace5b9bf7362a6934cdd98d730e25f24b97964f2b4a5504a4293af256a490c8d99135217e3fbc7c58edb1cbe363468e8cb9189e2f5457b8a8b12fe22b43bb86950af2107c15e816b01a5ff13fa67ecafc19f5dbe757c52f78decf3d5079f4f22de173bdd7710ec85d5d3a7a7474e7cdcd5b9727274e33dc36382b6fdcdefdbc9b7346dccdaa9b21b5e46b02d475a6d3488687ecf719a632d764f6c7d58c831236112c08d7ec2f845e42bb217362e185b62b4fd676ac91587eb0055e12b56560caae153c2a2e53dea6814a9291251aea1d540fa7b64eca9c1d36126864c3697992cf25564a009279230a40047368d45192a2e1455889ed123220e43ba86c10c4215d42768451067209740cc8068fe71f893ea47c5cf6e1e8a3ca67844edd1d5e3a28734ce331c0437206d94d9c1b1635be6ae0d469a5d34766850cef998e327a6350c56985e2ff45ea8baf171a2dac5a00b1995f02b525548a8b14ca28cc509c9f493ab26b44c3c96a128e24b8484c8dc1186229644048561062202c3f7c7bb8f2b1dea3a0871b0dd41b0834f86710c9b18742f905c20b28152e28b04f709ae12e024b847708cc10d820903ee87b20f121d7439706ee0d701a4832f863f0c0a17042b6054209fa12f023d8445080c0f681ca0354063c0bb415e026f047c07bc0dc0186027a0408063008f007600034d4e1a6970d3097e942bf4c3d9a5cebd351569a5ab4d155a662ad32b56992ab45455a296ad145569a9a74d053a64a9d2a54e8a9a744953a6927d3473e9a19f451cfa6626d3512e9a7974d2cba6865d3312e997974cacba61e5d1512e8a59744c4ba6a24d34726998934c9c9a54e4d3311e9878f4d4c5a68e2d341169988b4c9c5a54e2d127169a2874d0c3a60a1d2630e998834cc3fa64df else 0xf4a6e71400dc0002cec1d5a92c9ab0b6684b2697180583ee92cc4b7146f87d58d06325a8a37c3eac683192d453903e824eb2b4fefd04947fa0ce6245c36df8ba19afc0ba06a38a02aa96bf03da238a02aa80efe3cbea0ada003b00eef66d201d80777b3693bf9757d0570005de55007601ddecda4efb5f8170001cf1d65507e5d80777b3692ec0298ea0da66ffe00180073c75952dd315c99b48cda88f97f7b8d04da9c1ba62b977d9b485ffeca11d1472c211655b74c67066d2336a8de1bd5184a34e9a3360560f8e02d34bf8bc2cd4de2d04e62c98bf63963e4dc13c13b44b44896d3755433716704fe32c6948e9640633a1797147246b2d1a30a2f636c2ea2e1a516b2781781c118254a14e45b14f52752a90546646045c14d16a16ec70629c240eb1182d61c2c271224e44e70de4220bd2382312304bd42d42c42442341842a41b0dfa380dc8a142b41a0c10bfa060c08a92122112060aa0a90a307cab8a66a601321a91bb1a069368267a1291b02011651641632cc2353151561ba2d71512cb2d21b11af42e1938712092991b98f389e2ae46e1031c018818728057168a04a68f12a29306f06da821778fc90704d04707b45f52b578c4d108505c485128b982281f81a81820b81e202a420e2642ce217317217069b23f0c811310602e09c11d2b445512116144d44a44c9518dc8dba0d54163a18e1492cf2ce18a56d1834641b24658631b819c0fb5501bf1992d8a3c4aac234274214200bc419c2d2398574268538aaa0291826713fa5c61160b1ac4c6474aca2812336032d960416719821409d1864011471b414887446a6963271b695545d04c04604bc80485169101160c4514cc21c2a20c175a8a0014a76810c30a70a11622af8658804534d58e4c6849144636d5391854f01b532a8471b72c24254284294ebc7426626026125c2b884460663f8a71aa1bc2e82322da8c71a6a9928ea8e0e90a02b149093986768b44419e04f048296892859105459492c54c50124205a0fa051090c70c52402070670f04a91123506176348bdc250db41fc1a63d4a64a2a43158a341922b32ac13e2942ab10718f168176c28145a0b2d40c66122154c70900830741278a38b6cc44c2c266436d463b6084a46011ab236a3fa9aa031a460927c46c8c585846384b0520560540508fa476cc215bcb5208a0729a8c2142a316140a61a110213a27a8640fd44fc30c7687688589189d18017f19d2b2ac2c222f08c68c8a04607a014834734698a284dc9c17e210c296150a20a415228214a0f7480c9262ec8315c64146f4fa17ca1123d23a6ab0580440c427dcd5c594754848b50fca3215719a1341b3130a1324161360c69a27bc8511049c8844c5a3a0f328317b1ada4123b234a40ad4a358708881554c416d0fe0f68468a0a1460e610133c67c19a264c84671844)) else (if j<5 then (if j<4 then 0xfe5d56710240402280ab95e964480a002a7af85fb7123202110200ab0bf3305032814eb85790802b7cfb9b817afce14ecffe9642648bad04ee25008e8bd5def98132452649d21005719ff889908d4bd7015259b72e100cfa7e4fda0a4e8401500b7bb853ba087db83dfc801252496be3f40092f3f5a9c300009ab6e0f7f2004957f7f395022ab7fe15022a5fe42c004927eea8114dffe150229d3f6391e80e0000aa7bc0707e7001356f2bf9980092844c5ffd5ca490000a2c5bbff93154910000a2f0f8147a9c980005508575c35e4009313f7ae0fa08013507fd0fa6600026ad3e0fa4a6321880000aac0bfaa57c80134e3d3ff1c00e00051217ffee5523901880000aafaf992317d44a01880000ab09f6fba8402e000028bcfe430162e00013603dfb3c9f00b5ff17204c0000a3d8ffcbc822e200682400002ada7f6fff367f6692210540c28002915fe42c004933f32160024a3f75408a67fc4954b001265ffe1502295fe42c004937f3d272a04587eea8114dffe1502295ef5f80b00125e1fff90828e0880000aaaefffa4d30004400005540878be0000dfff00804000028f3cefd184531ffffedc13188b0009b00ef27c0017ff8221180000a380087ff94001180000a335fdb113cb51b070962b58b07dd3d004dce296e77942f928476aa21e8fc9828e94f4a606b8c87f06ff4389103892c5bdfee6003474438a80be90836f3d80a65530f27c0247397c9440ec630df0fa14b1a96a246c09bbb3a8136926aaadfc3ec9f77e1f563418c96a3bdfa0ca08fc19cc4c5cc04d225072b512730132c96ecad42b06d4792cd716a0ce6338e0e01907c940110550047ff689a02aa713fe1c1688e280aaa40df80dfd9f494bfe69b8130300b6548dfdd271302e00039e3acac28d003dea0da5ba61b6b36919b555fa926ca6487045955efff936d114935622198c9a065deec454d08b2a881b23c646643a9436aae525b650860e3000000000033f77c3feb0fe9c7129e367237377c05945dad0677e19a98daffc00503f826f73891ad8202ca4584fe9c80d8130a1062f01bf83f4fd8205fc3566807000013b999e0418b49aaac3c4fab251050802a41fdd801f820583d89c40235efc870a4809b90054811fcbf07347013eb70f40235dff360049e73144dd008c00059bf01b9e053455d5008f57800cff3701a688282608d57e087f8c00260002483c00500afb92c804b8016ffcd8014d1820c797a3a08fa5c401705724031c1ae5fb2bf9290224dff47c40809008817e4f28f8a8040225dfeafc18a8040222b8c83065063fc64c500a237dee25008e03eff922723493b0a93bff210a407000055354e1bc0099e57f30404901e5cb0004ceae2fe48012195ff8b00110000a251ffda44000287bffc2308a2bff4d16001341fba6113ade0e2237649d4f8c02c1f74 else 0xb352678205ca5e1800040b65787ae3f823c66d0000012ff800257e4e9db082dff09e204980065ef78036abc65d02027a2b810ffa81cf11658004930ce0d2b81d2d751304c0000073c16e0449fcc19235fc46440eff800001a9e005381dfe60c008d7f119500010ff8002d7368b4c0ac0cee7c1404c02ebfa104e0000000000001eff0025e2053eaaf1f00b303a90416700000000b7fcbc009609b2a7cde7008180037d1a53757e2b6d48e08b91255400000077f822fd96659cbad61fa2d8025256e87ab2ecfe5323e169e2662e2fcd82fffff360a128c212a5032365ff37ddf40c23385c500000031e0fb50415327e000001d7fb504152000000a793ed410549dee7e4eabf6a082a006b333beb4228e820aa00cf6bf3a746d4a3a082accf018c4a3a9f0065844080100579def6a7423606299a98a02b20fc5f27ca25a60c401546fffc0a169d040601008ce7c3ecffc8c405156c4002011f6f3706007bc5dba8a082b4023c3a746d15bc0201ac8788c70aed10031cbfff705976b20503597fff09c322b2050358ef318aa15c031804efe6645c031812fff0418070c0e41cd18c80488197e57632a500841b0e200ade3f03e886c930054270f9d30082141a9bd756542834009c9ef2d4343fe8fefa565140c8a00c08e97feb826a70c0f8aaa2d8c0abff710e2a9e0ffc1771204a5454b08e1005743c99bef01b9e65144dd008e00003fae119f00df62384015a2166fbc06e7814d156d1201202c0affc51e23402240897fc8273ce4261808d37a2cfe08405006045d7e371837f8aff4e891008070f7ffff01a2c000092083000a015f72590096f7fc7b3fef473c0a72a2222491048ebf83e4834d104c60491046839fc04fd3f7680003660206815fe201296f07b023f60db0663f615008f000d3f80360cd60eeba08f1805782dfccef87d503380001241073100179a40413000197006e3f6e1c9de6e900573df99f244ee0a5400a9003b3ff054a677539008c1bf10cfd07804329c51c4015a000adff6499600ecb9008d022f933629d19a9927200ac4fcfea04cd595fc86506edbfdaf44c248c80da85008015c027ff90dc7e7ed5a8107790ca0484a4c0add939f5d9ec81180f75e3b3762f47fa013011a0d793fe1ca8e3f252045b434e132e4ad40d667f7426b049202a00057f05bf1a3e7437f3cee6823c0028f67e6d90372602a80ffa9b1c001094280aa37fd2d70b1498089ce5c7d38717914281b2bb67c7192605035f3fffe2858810001008b0affffda2233010601b43ff9cd00791701a8ab2fec12605035c9fef40dac91012840284015b375b83f9a905404a14055818743022c00005bf09600602b8bf91ffec9918890300dc0ffffc0420210c21120804703ffeee98445260225bd2d1d14950c1aedff07b01b214d8b1531028804867a265cfb601a09) else (if j<6 then 0xd4fe8450612302240556f8f80cc0ad25dffd20cc6022c88022c08ffffece92fb008587a1c4449d1008c4412c6d7f37f96e8aa6c20c22119c118126c6055f03f059c5544bff3f293f767384a8ad7f570a7e6013e7c09008c77ffe9fc582d350244d5416708c640781290d9fe416d30d1e1a33a1f811e05dfff09b92650e08680408720111632f0702307db2e28fa226a4c048377d7262d3e5fce470d00deac164d8baf250896008cc5bf3634c5a734e9e44c0302429fffb004111f4f38c7dd0060486bfe2077bfce016180cd53e0483950707cc6087233ffe12aadcc250951790147d6304b536402aa4fc8ddf535400a08032ac5fabffe57959c36ba80a046f7ff2d7f1ca5c11f81c8bc93cccb3261fa91a81f21fff3fe0eaf8ca5440f85652e8a328126003bffff2e0879948d3af5296e2288c04a53fcbea19100a0449bfc99730050221dfad7942a3100a045a5ffe1800a029a4a9995a87913330152cd88e5479e09199422c9bc0902e7aa56d833bda543f48a0330150e7ec390ac980a79fef8f0b580ad4b66f1e526082e6a4f0ec302d0415a86f8f0b4909d4baf90379fc031d374448741c0cfd5ff5db74610238610608250a02c4bc75cf41f68daba26303581cabffffdf06dbf687b04cdf10223114581decfff855311fd720218300818057d493f9740cdd7fb4169b80a6d31ffa51049339f5e418920671ff810c4925fe36edb9410135570ff0890809a5bfd289c044d15c3e9402842692ff187f840c404d4db7ffea220321350ffe7021a2499bfff9749a604180004aaa7eedae0121800f9fec2180000a288fd5ffea7144880000aa92fbdffea2b41080000aa84a77f27c9faf81532ac700028fafff4ffb698aab71180009bd18b57ff949180000a2e4fe051c095a083000001560bda0cdf83ca822800051b13d5fe600262b5b1ee0b4847135e7ffb056b1a2d212136f27b71ffe7e18b5a6420ec0009cc5fffff270fe08b226c7801029400052417ca8ba7bd49eed0c10c2155002587bc1f985000051117fb583b648000055211dbfbd70001352be3fff3c0ad9ba2320001468017e4ddfa0c401348ea880000abe9f57fe6af564a609388010a381fd49879c884410517afece3faf5591c4d100c08000148abfc04400028743fc74bd91390400002ab033fd3f90263000014581a7f7be20650ba091cc1000015793ffff4401b92754250a3301ff2bc6424987fdff67d1c61a84840012340000fb5fe1cb9c01860d10025701f0bff5a8186d044801221000000ac4bedf6920c1c4d43ff1bfc0858c08249d6ffc08b200a00a24be5e418120613537fff3ffa5b64206a90200013899e05140ab54d47f601664b1ac25423b557477675026d24d540137e14a80439fd81f6c6926aba2e6a244a0e569e4e6a2cd995a69a289d4771653c9cd37026069b2a3af else 0x16fdef85003564135844c1d8812bc04bfa00034fd2880131ba43836520202ce5ffea27aff660504f3535701c0d4958d03a29199000000000007ffb26fda9a0c0a05eabb0d484e816f084467c000031ffddcffc151c2f3daad37c353c5348b2640097ff55a0003fdd06dca3623518a333e4a51c98409c77f26e2502743a3f3f91544643f37598a044a1d3f85d26e12e90a1b2b1f0be8ca5d124367bfffeda8da642a84012231f7feee0d0a1d0b1de7f60de40a143a16439d1f868a382d3f3e0043fe037151d9129c4b991e061ff16e7ac86020428e90e32bbdffe227d185c71800752c8e15d040466d738a1d0b24000c9a0fc50e858f8ba88bf8ac143a1646dfd88df7600818aa9d7fe0a9d0a011289efd22380833d3dc6fb41e666044a3fe2765ec23080002231342f082e67a3d58117cb211382008abcfbfe2a85f4418d5dfe9b4384173449f17f815a9127eb6a8ad9ea74e89a537e0c69003ffc3b79b83003dead81a6a4f30181275beae12106406319c4c48a8814d4c1687e0b010f67d340e8510445459f4d04b0001115167d340e8510445433fd3f097a2004889871b707168c2302281fc9bbf537ba10c402011a007bfffe4aea078e2af09d922c5320632b10b94c50274be9a151a81a0bf5972819bb95342e503431f03a9fd32b6089186555dfff23560a0690448418a02b72f93559d1ca9211202a)))
def moH12 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x8123524400008aadc7029c4fc382491d570391ba9804835d102d41661dcadefce2f1c23f6308127d00008155828f436b403284fd4290815302d441af02dfc8f2190d493a414009454a9e2ee56f866b130000c221806dcb801da3c0e7400503609f454188c0f4d22bc35b1337831e417b88164325c30e0165c0dc211881f2a1d6d98480a7c2c18837823842982388c66d06be02d3829540e0c0c2ee18eeacc00700005e9702a545aa831b123641f441a2481890eb40d8519211bc935a0000025b0366008f80a1dd1dd16ec2848d9f59859a9f80304025c1a580f185c02ed250c30095c07c08f8003a4053c89701bf812d0000000000006708036a00000ef6198303095223000000004d38029204e14a07081d5defc10380280181005212fa81d941f981019f5bc1ef85200000c079486a5d47022d42030000000002fac0d4000043130000000001455684c0090368c378a67502eadc5c0000cef700008271807a00001f08000059d300000000000d0000dcdd4262c37700000000515b405c011e4136000000000990251a033b81cec0bd503600000000427aa50701c2083c1f430000c25c0000650082dd0000ea8c0000000082c08de0074c81879d03c0ca40170000d1a4e546821dcefb000000000000d35f000000000328ca060000135501ecc44b0000000066c2cab6000000188177c8814107815e912710484074024980630000585400000000814140e9c2f500002b04000002a252300000032d86ca8a2e036cd9e60000820400000000000000001eff000008f7c1f1000000005c35db2791b2000000000000000000001a6e000018d2c2e00000000000000326c32400000000e2dc432743018ec082b700004b7b000099e780240000d777086010b060c12d044030304001041824191020810a0024004141838f008c2060004f0a009c7810e0c48500048a5100808148e8c33044819210005b2180c602007400114001010c0040400005833a6c9cc04006a61a1420274400000e441031a3488b000890102080a70a0008c02004001a1028212142940601104060d3081440c0008506010205100000840106000840600288062400206004820204601000060700002830408886060450500203020e792011404002000000c004400102092010a00391021c0830e38001044838002244803204007000ce013e0000002000420024601163c5860a0000200005000a0401f1c0c0040c1808002000120431101460c1003e088840044082085c08010003800a0038000201060c480090c142041c001002c1c18c0a2c4811008f81001418c0600601080428220040820640182020808500182012048315025c48004040010208500022c00220205020200106000400118713000204100060cf0602440091055a01080c000082c111083c40000002060034ca8 else (if j<2 then 0xf440000c81e00000000000080551345000000004814408c0000000002100000c16d00000aea000000000000c236000000f2000000004af6a6f9c08949110000080d41de02e2081100000000000081d30000593100000000000081f501b4000099d5913f0000000000000000000000000000406e51a592678191c36f0000000080fd05b000000051c027190c03140000024cd16c91b140cfc0d35d26002e9f39c1bc00baca91c86d000006008270403ed313000000005a20104d4594420100000000670100009b289377c21b5b31db7400000000018b410c03454a7b0000000080b841aac16fc620c27b523e5980e68c434b8a79c1fec07600008315e60d95b0c1be01b300008117807f81d4834801690000c5998224d1b800c5192f06ccd245a2c6c5a9409e03310000000045421d19c812000041b74a8f02ac00000000e676010a000040334242ee8c5240009f02c3c50a0000000019e2132101e80000c161d31f0000c14b00000000c92a821f4035c0b4000000001dc1c4e40000493581e60000012101020148197fc2af829482d640c300002a8000000000828c000003214246888942b9c1c9e8ee0000c19dae9b415400000000c265c16a833ec37900005527120e00009abd40ee016800005e0800000256000000009050e1e28344ab7bef8a9cda000003868054000004d20000d31885920171000000008259025f426f0000027d02ce8225c1600000cac1004f41d66ef400000329db02ab32000042f7a1e78112000000008069000000004b7c80758214c2ffc3835d768157000041a1294b59290000927c0000000000000000029ad97c000000000000859e418200004013922e8217000000000000015b00000000625f92f68ace9333c1759a8c0000000000000000614b0958000000000000051d0000904f000000000000000000000000008712f480b5524641ed000000f9cd2b00000000000099d642349b2d81c414fc825ac11a00000000000002ee8a9d80dd0000c24eef1a022f0000000000000000000000008277d273aeb0000000008185019800009c34000001a81170632bd18890c942e4429941c0e2c4de72000093260000000001cd4d2646a94253000088fd0000c0820d8d0000c19900002a59eed0518d0320084102d7819e00001b2ac152c461c19a00009d230110426b0000000000000000410dc2414a730000c21c423b00000000c0910000001c9c33000000004521237e5b2300000274402a000081040000c53b42f4000081ddcacc02f00000000001c79142015a8d870000009640fb12fd001a59e1c0599f14000082290000010b9f7b0d8b82c9c2ca0000e44fd19340cc000015ad0000008a9f5141ee0020054000000000000004cf000000000000000000ac0000a38ad16a81ad9786813982b580e40000c0a200006a9a80150 else 0xe99130900000000a220c12ec179133000004218000000000000597a01c6248580b6c1ab00d0000000000000c2fcc34340d640580156035ca180029e0000c146000000000000d28c065e5d8488879dc7cd890000418a00000000c10600000000000050f40000425795a9c0648384000083124215c2d2c1e98306820ac1f61340d2fbc243c2cfc1ea0000c1946a1100008260962002164223dda4eedeeb198134aae28109420e0000820686cb813a034600009dc440880255000000000000c20c0c610d1e00a6c2fe830d4319000068fc000000004b1640114b7f0000818f41004269dd9d11d2ae9a00000000c0a0c00e80d700009da5022c0000000006bdc28b0000000080574310000042b60000430b0000127a0184c3580000435f013100005d596dc8eedc0000c1b542815368c19b4a7cc57300000000051f4810017c4777670980be826780da00008209d0609f5d8244423e00008247005fc0ef000000004914c3221f524186c69450ef093f000090ce00000000cef30000c52b0000016c0000408500000000008dc02b00005d9e41138333018300001d00000042db2739a9535f0f2af441ae02720ad169b31e75eadb8926a470000040bb48ed000000000002000082fd1d781f70010557808a95ea5351cd45be1a53d1b9c0e300005aa40354828d83379d1a000000000000401f11df0000031a42e1c0eb872d82c7000082eb199c000082be90bd9dcc50635d40c20b091c0000c167c92c8083034dc35780cbc37be730c2a49e7300000d8e0000000000000000c18e0000e28c818d000012104099c32f409a00000000eb7e1f06014fc646803402ef000086c60000000001732eae0000ee00eec05839816bc26e82cc0000a69cc353530482f90000815f8250000041db4219883b000000000000d0f5996f42e7c1acc15c59dc00006ecf833ceebcc13fd2f8434f05a6eeafe9b400000000021100b2000012140000c17f82e5812682059f5ca32490f7834c1a891aa3028a0000000090f300000000000000000000c36481fdc0aad348c1e00ad88365c03f0000000080ab000082a952f90363013b000003320000ab7d0000169c088440260000ddb7cec14093000000000000000000004acbd9cd00000000000000000000094a9982c2ab40190641e4ed45c50293c2d8d26fc159cdad027c0000522200009037ea2e000000080000818080604cecae8b00000a89c2b40000aa81ca708289d1a700000000dcd700009f1a000000000000dd1e11c30000000010b100000000000000000000102c027f0000920f0000c1470000c2a70000de79aedf0b76c80c9ee9422088eb6ee3c88082631f3805c60380006153171f5a4ac30268018c000082ba49478338c06fc2000000821a5a9d80d5511542480000422a41491272817a00000000000050c6000084665)) else (if j<4 then 0x305408e0302002cd1720000c1300000827940920000000001708a742add0000092182c88022412982a885740ef50000000000008356004491cf82e380b9000000000000832cd22a2d3600001a904c3b0000000000002b17c05b43750886823508ea000000000041ca6308965101eae3800f5e810000c91ed97b00009506c00100cd4e0a0000021e0000da9c8f08409c40f00000c06b0000072b168c409d000003520000000000000000000043555a55000080d10000c1dc0000dd959a59417e000093320000000000000000c1eb00000000804000000000919e0000000002a3000000008072000082588122422e41d0000000000000c8e9000000004451000088ee0000000000000000000002aec2839a1f000000000000832ee22ea10c880ec0a34b7815511cd2405a96850124d2ff96c680a4800a51a100bf82aa00009e7600000000c74a000000000000000000bcc0f7534d00000000c2bceeb6c14cc163807d0ab7c12500000ebf400b0000118e81c80000e9560000000091ce498e0000000000004d3d000049ed459f402900000000060f4374431d0000000000000000407e6d2f432bed34ca5b8347ad568239000050f8cac48286000000000c02000002e8000000000000000048f99cee0000000042d100000000410e19d4000041760000c0e200000000536682279735c07122e1c116c128080ae98c000081f3401b9b2000000000814d2a9bd9e4c0f30000000000000000c0a90000000000000000000045ca0000c174d30500008084cacf06441e00c5829cdb41e50000c1bd0000486e82bf91d00f77034a00000000830c8371c94e80e181338231c32a4381406c000082780000811b22b6000081bb41fb40ff00008a77c33fcaca9f59e73c00004ce70839c4d0801de13b425e80f68518930b02a6aa8245c9516d017881d800000000000000009860400341e2c0730080468cd20000e85787de0d40ae419f00000000000048f1028201a441d20000ca8a0000e67dc02d000091d10150984dcef485a84cf8af080000424a00001a004193037e0280c351000002ed00004291c367517f4303d13dc9ad00000000c06a4a93d1f2992bc0ed00000000c285d68600000000199e0000000000000000d1a242b30000c014000000000000811150b5000000000000023c438700000809000050c4000000001e9302c40000000000000000022800005b700000814a433a47080000eae1d3579ce803400000c24d0000812fc1ff00000000c06500000000000081b280c9000000000000c0ec00fa81188012d19c838a0000c266824000fe4a98c0940070cda61da00000816e420dc373c1d7811f000049f1000001e1000042130000638900000000c04eddadc31f9b7300000000d339e1d50000000000004e57d0c7123a0000000000000000880f00000000a else (if j<5 then 0x493b0000c0b3c2bb4287db250000480b6ad2c1f7ed3091570502d1ae0000993b00002d4b00006ef841a90000000000005687db08000000008b08804a000002d500009cd681140230000042020000c26cd04ac2c600000000000001a70000000000000000036182f12a9940360232000084e5c34e00006cf400006b7882a1c70380980000494f00000000000091ac000081c300000000000000004369000001a08512867e00000000000000000000000019d9000000000000c30700000000000000002a83829f812c42ad0000cd0a40ad2850835e41d5836d41e3c317d0f1d2be02e9403140a5090982a0983a0000de376ade000043500000c26a978a81f8c05d9af08a7500004a050000000081cb000ccb19c07741380000491fe9590000c01e992a019500000000c151010fcaa0029650424ae943340000003b80c01199087c433561820000814401da00000000000000000316c1cc82dc42338406811cc2524b7e000081a3c8730927000041434062000000008376922c0000000000000000430fc657c29dc2880000000080db0000c29b00000000000000000000000082760abb404d00008d90000000000000c25d0000c1d10000c37d4330df1900001038df50904e000000000000051602d90000000000009b2b024b098c8119aea300380af4812740a86b10094d000081b100004189c11500000522000040565f780000eb08c1fc119a5320d2f5c817c86cc311c698000000009e0c0000c2b801ca6437902b80ce00004349813c00000000634c00001b29d1ff5f018ad00000417d000040df00000000d3165f4100900000c37f0000c77a533a0000df42020f4c4e8ab981a60000000049b32329c2bd5d89000000008a970000e1ec67450000c1b8d2fe819240e6550540c8c19c8048ed530000413200c60097419700d9e67200000000ee5c2b0a82970a9600001a9e803dc0394362000000000000000011feddfe9354887a030800c1813d9e91000051f100008e8c00002ea5d1964ac50000000000e5c37a1eb38b2c43855c314222c60e00de5322905f436e824f91be1a8ae6c1c690aae411aacd3bc83619df8050000042371708931d01968a8c003c5e92404700009f3c00000000c1c10000e6bb0000c010813e831cc318000000000372c30a801690f600009308022b0000a03941e40000c35a00000000184c0000451b407b5b720000806700009eb215070000004900004d94000000000000c85f004500000000000000002d3f9e8cc23d000000004526837000008d2cdaa1c2f8a6c55af24a7f9f3f80afca7a426d43002ae902f2d1b712fc0929000000660000adbc00002a955a5441fa42de9eb4422600064190c137000003590000c3882d3501c5d9c3886f0000412a6e9c4046c2cd6903c8fec2c20000c04cc1cfc02100000000c else 0x673000001720000000043394a53412b6f1c9f000000000000004551259e42cb0078c2c50000000000004a71000000000000000000000000927000000000013505c8000000000000000000000000000000000000433d00000000000001ba000019dac2d00000123982e6000019dd0000000080f5e904000082fb0b8608764341000000d2c87200b180c7c34200000000c29c00004389405e0000de0381e746c784e20000d0ea804b02f3ca855d77000040810000520404679cd4809b5f090000000041b611ab00000abeca9c425400000000000000001c4d000090ed400400000000037c2533a6008a828264c59a000042da530d923c9e7d5f3a40f8e9b096cac20744e38261c0fc80ea96888e8f585600000000a67300000000c5641b4cca921afd0000c93d868f0000000080422f8800000cfd204c000000000ded0000c158891ac25100000000e679c2f682750000443b4208823ac908492e1b79ca5999ec8142415d1f3b69c5000000000000c14edde0d2280000c89900004d3f011d00001e5900430000c06882b0402f42ec4af745380000450c000042b181b000000000000041dfd049aefec33642450000cb77000042738086c1080037012000000000457540c4d5425364921b828e8e009e82aadcc1f04d8f01b9c0b04023c21285f9808bdaf103230164070c5300427ec1620000887965fe430461d30000637dc0b7d9196b48000085ad82b29981dac693280000888a49180)))
def moD13 (j : Nat) : Nat := (if j<1 then 0x7c02c541810e00dfffff91044c00182181c003bffdbd38104813009a00018020eeeff1c8da185c802299ff8fe7880e00018eec0cbbe66045800007e0761dd41811602fac46c913e38b506c920f7c04f02bc018048b0f87d696b720ccd43fe7c2c7e344002012833839fa595400c68acffbffa4be12000100137001effcad2400423459787ff9e2041175ffc737c40822e00000e4ab69bf10000bc82e3a85d22400f00b0c20071c4805fa49a233207120073c12905ef82c56787c001b824009295d200ee400000000002ff000006ff3cf5ef5b9ffffe000000005e1557d71a0060b5a000000000017f8000037f9e7af7ad80000000000007dbfb7fdbe1bbc06a33021ebfd6904eaa00608606f0001381b580b0b9bf05377af1541e9811002fac46c913e38b506c933e38b11b244117c13d6d02c413647c329f302aa6026c6f8653e60554c04d809fcd41bd935809b3bffe3d200158804d63d7f803859812580007c00be11ad6d02c4138817c33f00fde620136463d2411402691ff9801660494bfc01c2cc092a1641d83906c728e32483a07823e17b0645b8db2cc57c540bf176294ca96d4cc9853025c088ae0a1971514b287f2314608bd1aa9951c1c50220313b24095294526a594127d4f69e83294a2aa18c828641f9356624809412163b4708ac21448c52922211130e117c0540981202003c0600992b2263706286e278418670ea2b4288490f21782723c8570685e4e227299d2c4744668c94d0fa1103906f02d0580ac1382604a0901181c0540840e81b0323887487416c2483b4920b22002b89f0aa14e138f785084604c3614f20cc0927129152280e085509211a0d40c815210220400a41401f03c0680c24347e8e8628c418d19e2c8c20d0116184751e7162168dc41e82e10a4118e320380a38d121212ac296a2a875cc29389013a47b08c11e112144110985123d4698062246d0f706054a125202985223946c8243684a0910be10283c5c81d6a0618528ee440a009a12c5a89c42085509a0c92813027a0e5570d6040500a51860f0540ad07e76f377972c95a38d13f855c09dfd6f977aa3caddcaebc74438c1bd0d9369132c9864bff5d02c9d5c8ab6536a88d3f69cf4c3251d1f28b6430a064fc27aa3b79cc0de26b3338983cb3451e25491408383ce1bf0d1c63e2f31648a144841ff0de05dc27a0e104c81980660009663cb2fe584f2b9f95c7cae1e542f2a0f9646cb036491b2cc496524b27259192c2496064b01257492b9c95c24aa7254392a0c94c64a6124989249c964dcb24e58372c139601caa4e5507299394c1ca40e58152c09954ccb0425520acbf6597b2c9d963eea0e56622b29217090984564dab24e1206ac8a5660ab2655912ac9856480b2c819704ca0364c23243ffffefdfefeffdfbbef7bedfd7f581404c1204403008010 else 0x25fe2067259934b1ccffb7406a1e14b13bfffff9ff85c09f851030b02684d0060b02e8dfffff0befe71b7c41a141902c2e407e05d004fffffa81fe04c2cc7da27100b9c86f85d000ffd93d2a0009c012094a850401740f43ffffc4ffc2e04fe0a2068989a1340182c0be01dff02fa7c01210028249b80018020f2003b043cd2073120f800066015b0d520731a00000001bf819fe2425f35fe08fbbd4c4d5100603828c5e16bfc11cbd72c82c5c1a37fcfc21a1242880301c152df2edc60404de9022d3fffffd833410004000da9fffc7db404904e62800060860750ffff800006401a50028151b6074000aff0cf9c0252ac120814849808079c)
def moH13 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x8ae000001c40000000516800000000000000000000000000d8ea0001041a14ad94ba2f9110b467000184ac0000000d05054a506a80fa000180fc000204c49b7085c00042fcc1fe00030ae80000000000000054eba9e1317f16b00000001833e0a08000012a0000000000000000000000771488e40000000207400000000000000002fc047800070e6000001380000000000182480000000000000000000a5e00011186b3380000000000000000000000000000000000000000307e80000001525c0000000000000000000000000184b400000008150000000009538c4e232000000000000d55126300000000000000000000000000344600000000857d039c2b444c4000000060e4000131bc05680000000028000000008163817000000000000000103d40140001022400061240000000000000001166000000000000000000000000000000000070a800081fc232757300000000000000000002dfe000145e0000000000000006099c0cda2c874b80000001335400000000000000000000000000000095730720000000000000000001b4bf1868000e9f59a520148000401c04040000000000182060108000511c000000000000000810000000000000000000100001a660000000000000000001498c046d26600000006f70000000000000000109c000242d4f40c80400030a00000ca3600000000000985f051c0000000000000000000000000104c80000000000103300000000c1105be8000692a00000000000000082ac0000000408a00000000000000000000000000494e000000000000000000000000000000000000000000000000104f00000000000082d4000000000010600000606c000000020218148000005f000000000000b28400000000000000000000000000000004b00000000a19c00060d2000000000b00000000015f00000000c1be000000000000000000000000000001830800060390000000005a010ac15e000000000006e0e0000000011984da808c04d00000001005400000000000000000000000000000000000004091844c45680000001056c0000000000002c120d914b01900419a3d00008006025f21f4f714d68000005480000000000328880000000000000026310000bcdc00000000000bbb80000409124f8b0a00900000000000027c410000019c0d0550000000012c713a8959000034c745d80000000000000000000000392815b80000000000107a207708da908400040900460000303b00000000bd100000000d1a112a800000002d2880f4000600d34004122460351060000227330202013212740045132070000005072a301113130020210b81043010000000c000016100010064028024520010120056011014402310003150401010300103010012031250001300100100201006000220001001100210 else 0x200030ac0000516a5be3699000000008a3c00000000000000002a000000000002022c2e30000048400060a1000024a007c00009174000000000009d48000000000000000000000000000000000000008990000000000000000000b9744310000c2c2000000000004d48000233766b2000094140840000d9d1896646880f60000000341480005eb000024798000000000030a8e0dd0000000006c80000001807b419600c000083012a9e09b000000000000000ad3000000000000000000000000b0a0000256c00000000000000000060cd00000000000000000000000000208542d000016b80000c8dc000000000d60001102c000217b000082939a00000000084dc00000000000b3fc000000000000000000202f822a29d70b50000000000023498000022c000365e40056ae20d2c0000000000000024330000000003a66b68000000084da22d800002ed004c0000000c296000000000ea000000000000000106c09ac0000000e1e4000000041140000a26000001460000000000060172682000000000000000000300fc07d00000000000217ac8de00200000939407c000000060500001821d03cc11f000184cc000000002a000000000000009382ac00000000000000130d00005864000000e0000000120b805fe92300000001b15c14d00ac000000000004254000000016ec0001b1b800028970000000000051350000000102ee6f8c9e60000000609800000000000493a00012ce40006267000000030aba1281ca80000007800000000000000000000000002495800000000000000000000000000000000000000000000000000000000000685b00000000000000000000000000415381f7225400000000001bab80006b560001017800000000000829c0000000c29200000000000000139b000000000001db85002000042c6000000040a20000000119300000001cd10000245dd2ae000207be03000012b08759800000000000171000000012c340000000c25e840a0988e7b81580515a8c0000594483c800020e0000110fc00061674246000000000bd000000000000000594680a800000000000000000002b6000000000000000000081840000000004800010a78000000184b80000000d26f88b4000000000000000000000048c44baa086e03400000000062000000000001235000000000002697000000000000000000000000000000000040e4000000028bf000139aa00304790221a51055e0000407501fc0002084821c00000000000a8f0a88518500000000000001b000002980000000000000000000897e13000010412048cf420000d1b00006107822e45fa02b800000018298000610f0000000000000000000000218180000000011c06e2d350000000046580000001142eb397671000000000000000aa2925a000000000000000344e) else (if j<3 then 0x41d00000184b66e000000000000000000000000000000829c839e169800042da000201ac0b6000182380000000c61732da469349800000000000007c81ae00000000000ddda00000000000000000020b880000000000000000000000000000000000000000000020c700000000000000092c684600000000c1dc02c900500000000a04400000000000000323c0000000000000000000000000000004c700001ad2c0004152416e80880000000add200020380000c05c00000000000ccca000000000db00000000000000000000000000296c0000000102f800000000001221e0ce000181a811944fe00018129a89a064de30000041d00000000000000000650000000000000008a0e0000000000080d200036390000000000000948000000182e00000000000000020000000000180760ba0000000000000002ac1017c81f843f800000000000000286881f8000000060820000000000000180000000103a800000000001068e0bba1ca05700000000ae2a000000000000000000000022f800000000000211a00000000000000008003a8000000000000000000060d381dea5240000000000000000000000000000020b340372a8e0000000703c000000000000000d93d8183049b2b300000001052800088bc000229c800000013bca0310000614a000123649240001022c00000005d200327abf8000028400000004cfe20ea00030bbe89400000000000667400000002779804180b6000000020f1d28301e0a94095d5277c1df09a80b3000000000000000000083980000000000000000002f0b88ca000201d80000000000376be22ed10c000001980000001806d02a800000000000000294581c70278000000044d8000323180008948000000000000001d2990aa0051c0b00000000000098a9cbcc000000000000003634f6b90000814c0006962000183b220400000000000244deeaf00010059089530f86040000000000000000000031e03841b40000000000002bc000000000002ae00000000000000003ac20c0a08f00010564000600b0000000000000008146000000060eb82d680ad0b60000d5520000000606b000000010aaa0d000000003046000000000000000000000000000000044000000003a5ce493013a13d485ac06700000000000000094ce0000000000000000000000000000000000000000000000001972a746000002e6b1900000000a3da0008000020a000104300000000000160e004b4238048802200000000000374aa26eddf200000000000444e00024b58000000000020618000000005cc494c16e000000024b4f45d00000002649202540a424f0000029f81b050a59708000004f04e2418800000000000000000000000000000295480da00000002960c0b2000228528330000db7c000000042c800000000000827 else 0x544a7a0967a00d00000000000048b4049aa4dc81b266f832a755e4975a6891a603de0f30000000205d0000007800000006b0984ca937c08d8000c23a000172dc12082c485110bc0000d135004146a00009caa0ad712e422f02180000000000000b400000006020000090400000000000000018bf800000000001b8900000000000270c800000000000000000000008064000000000000003037a17f009a000202100000001842c00010e40000c96c0000032c11a000109d250600000000000000000000000b1f42724ae000020848000000083d449700000a5013ec1a6f63a000000000000080000103b40000000c27a0000000000000009029a3b80000000000309a000000000000000000000005ca4000000000000000000016f455284440000000000000033830000000005c80000000000000034268000c94c0001777ad7c000000010960672815c5bac00000009a96000000020c10000a07a443d02e0001a501018895100004a54770000042fa00030780000413800000000000000185c00000000418a0000000413f000000000000000024fa24c07c8000119b23c7274a8a98528000000000000000000067c402880dc00b40000000c85785e4000166f82cb849400000001dc48cb400000000000000104a440c0001c38f200a56d48e2809811e00000000a2e40000000000000000000ee4000085680004f6d000132500000000000000000000000409e000000000000000000000000000000827f003800041c5a33c0000000000000000000000000000000000000000180b000000002ada000000000000000000000040094ae391f800036770001a0c00000000c1ca00020658223000000000000000000105a4000000000012b4c00008f700000000000000041a92d3400005180000000106300004034000000000000000000079400000001838769c00000000000000000000000000209f6cbb000000010ba800009c000000000000d1e0000339300000000253f49e8103c28600014468000000083780000000000000000000000c022000105e0d80000184ec00))
def moD14 (j : Nat) : Nat := 0x1fffff800005f8040e400000002fff97991d63a003ffc0002fca86404fe000b9499fc055108e0003f898a400007ff2f09617fe001905617fe0600540b01a0380c029562117c16858158541384c128481183a0e036110347145d0092a448dc3106e338b01b0c24a1103d8da1a940278942388a400604f8e02c8a43405e148500a826090200781c0601605040481063a0880f03228030610a826096108120f8102b09a5a939919fc01a6ac4114850005916050130481100c020043ff
def moH14 (j : Nat) : Nat := 0xd07800000000010b16ef035b8d00060d400000041c0000000000000000000100a00000000000000000000000000000247b7329af1074e2801b30d892800173a92a812c0b102511f000a24021bab101200006500000000001016000000002201800088e6a840008155ca08d000081c24b80024100000000002054000447800000000000000000000000000000000c3d456800107600000060f4000000000000204200048c2287204000000289800010be8a000000000000000000000000000e38000000000000300c2320000000000000c02800000000000060d20238200000000000000013800000000000480000000000000000000a1c0cb9688000000c19c4741080008018000a3000040200000000020000248000a2900060fc00000001f0000000000000401c000000e990cac65c000811808800000040c80000019054908003750000000000145c00000020c00000000000000536000516e8a80000000098003078000c8d000203a0000000002456000000000063b836000000000000000000000000000001058000000914000000000000000000000000000000000000c5cc274000bb9000000000000000020c5114000000000000000000000000000004830000000000000000000002600000000000005080ce400000069160ca1363b7017000102f039000645346000001480006151a0650000016e1010000001050000000206c0000144076040b30037c07c0022620000000000001bab88000af05a0000002cdc000000000000000012200042a315e000105800208308e0000000000000000406000000002060e80000000004c380000006c860bc24800008d8003534000000103503d10cc0b000000000091a80000000000000000000000000000000000000062e000088d000244800181f00c600880508000114000100510020081c0084222500080020
def moD15 (j : Nat) : Nat := 0x31705c03ff
def moH15 (j : Nat) : Nat := 0x3040022200000000000004200000000000006700107c08000000000000000000020500000000008cc000000000000951970000095f06002310000000000000005c40000000000000d000000000000000145000000000084c00000000000061c0000000000000000000000000000000000127000000000000000001140000000000000000037300000000004dc0000000894000000000000000000000000000000000000000090000000000000110000000000000000000000000000000000000000000000c44000000000024000000000000000edc000000085c0000000000000000000293000000000054000000000000000000d1c000000000318000005dc00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004e000e980000000000000000000000000000000000000003a70000000000000000000000000000000000000000000001c03000000000000024600000000000000000000c0c000000000000000000000000000000000000000000000000017400000000000012100253000000000000000001860000000000000000035100000000000000000000c04000000000000003080000000000000000000000000000000000000000000000000000000000000000009800000000000000000000000000000000000000000000366000000000000000400
def moLevels : Nat → Packing
  | 7 => (1,8,9,65537,0,0,1027,moD7)
  | 8 => (5,7,9,327684,50,6,1032,moD8)
  | 9 => (32,6,9,1835033,85,9,1056,moD9)
  | 10 => (340,5,9,8913075,136,14,1420,moD10)
  | 11 => (907,4,9,6095054,120,16,1816,moD11)
  | 12 => (386,3,9,1769521,86,15,1680,moD12)
  | 13 => (66,2,9,655368,67,13,1288,moD13)
  | 14 => (9,1,9,65537,0,9,1108,moD14)
  | 15 => (1,0,9,65537,0,0,1027,moD15)
  | _ => emptyPacking
def moIndex : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupShort 1 2 0 2 0 0 moH8
  | 9 => lookupShort 1 29 0 7 3 2 moH9
  | 10 => lookupShort 17 359 2 11 5 4 moH10
  | 11 => lookupShort 157 1579 4 15 9 4 moH11
  | 12 => lookupShort 444 2633 7 16 10 4 moH12
  | 13 => lookupShort 199 1993 4 15 9 4 moH13
  | 14 => lookupShort 40 409 5 13 7 4 moH14
  | 15 => lookupShort 12 431 1 10 4 4 moH15
  | _ => fun _ => none
def mo : Forest := ⟨1535,15,fun i => moY[i]?.getD (0,0),moC,moA,moLevels,moIndex⟩
def sgY := moY
def sgC : List ColumnInfo := [(16,0,495,0,13),(64,0,447,0,13),(128,0,383,0,13),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(32,0,479,0,12),(256,0,255,0,12),(17,0,494,0,11),(320,0,191,0,11),(0,16,486,9,10),(0,64,189,258,10),(0,128,347,36,10),(1,16,486,8,9),(2,64,189,256,9),(3,0,508,0,9),(4,128,347,32,9),(8,16,486,1,9),(32,128,347,4,9),(33,0,478,0,9),(256,64,189,2,9),(0,8,227,276,8),(0,32,94,385,8),(9,0,486,0,8),(9,16,486,0,8),(19,0,492,0,8),(28,0,483,0,8),(36,0,347,0,8),(36,128,347,0,8),(49,0,462,0,8),(134,0,377,0,8),(152,0,359,0,8),(258,0,189,0,8),(258,64,189,0,8),(260,0,251,0,8),(352,0,159,0,8),(1,32,94,384,7),(4,8,227,272,7),(7,0,504,0,7),(8,64,181,258,7),(14,0,497,0,7),(16,2,424,69,7),(16,4,353,138,7),(16,8,227,260,7),(16,256,135,104,7),(35,0,476,0,7),(56,0,455,0,7),(64,1,396,50,7),(128,1,332,50,7),(128,32,94,257,7),(256,8,227,20,7),(256,16,230,9,7),(256,32,94,129,7),(268,0,243,0,7),(273,0,238,0,7),(289,0,222,0,7),(296,0,215,0,7)]
def sgA := moA
def sgD6 (j : Nat) : Nat := 0x7f4d341986d552605314c120
def sgD7 (j : Nat) : Nat := 0x801dbb30f4d094f4661b5605314c1206d552605314c120
def sgH7 (j : Nat) : Nat := 0
def sgD8 (j : Nat) : Nat := 0x1000000000000000000000000000000917c1b9b1a9a1999189817870686058504840383028201810080027b7227b715f6f01faef6f6ce5748d4730d4bacd33acd8f6ec09b8b33aca01b89633087b3076330667b6587a452fa4561b65736a41bae317ac23fa813fa80fe85f3c3e7277d0ef25d3d3897efc2df25b74afe45f92bde146be8b7d13f9fa517d9c9e9b94605306a7a6e51814c3a6e515260530697b468f9148153549814c120f055354930483a454d524c1206615354930480c954d524c120661b54c530483b5605314c120e91814c530481b5605314c120661814c53048152605314c120eebb464d5244198edda54c91068d5254520441935495148110
def sgH8 (j : Nat) : Nat := 0x1300008
def sgD9 (j : Nat) : Nat := (if j<1 then 0x7f35fad7db5eed7b75ebd6f757ed5df56fd3f74efcff33facefb3afcdbf1fdc7ef1f7c7bf1dfc77b1ddc6ff1afc5ff16fbfe2ff4bfcafecbfaafdcbf6afd2beeafb6bebaf76bbeaebeb7eadf6b7b6debb6becfdb3bebfcafeabbeadfa9f7a7be9bfa6be97fa5be8ff9ff27fa9fda5fe97ee5ef8ffa3bf8dfe1ff87f61ef86fe17fee1a1e5130ed5a1e5130ec9a1e5130689a1e5130ee1a2e45306e3a064530e979464530ed59264530ea79460530e9b9460530aeb94605306eb94605306cb94605306a79460530e9b92605306d79260530ec59260530e519260530e515260530ed5a3e6120ec5a3e6120699a3e6120edda5e4d20ec5a5e4d20ec1a8e4520ed1a3e4520ec198e4520ed193e4520ee553e45206e553e45206c7a3661206cfa166120e97a066120e87a0661206c7a066120e8da166120e63a564d206c7a564d20e63a464d20e57a464d20663a464d20657a464d20657a164d20ea19864d20ae7a660520aa7a6605206e7a6605206cfa6605206a7a660520663a660520e9b9360520e9793605206d79360520ea79160520e9b91605206cf9160520663916052064f916052054f9160520e99a360520ec19860520ed19360520ec593605206619360520e63a154d20ae7a154d20aa7a154d206dba154d206d8a954d206a4a954d20e63a54c5206e3954c520e61a54c520661a54c52064d954c520e63a44c120663a14c120657a14c12054ba14c120e93934c1206d7934c12054b914c120ecda84c120e61a14c120549a14c120ecd984c120ec9984c120ec5984c120edd954c120ecd954c120549914c120e91814c120e45814c120661814c12054d814c120549814c120ec5534c120661534c1202e5534c120e91524c120e61524c120e4d524c1206e9524c1206a1524c120661524c12054d524c120ee5514c120ee1514c120e91514c1206cd514c120605514c1202e5514c120ed5314c120e91314c1206d5314c120661314c120655314c120605314c120ed5a8e4910ecda8e4910ed5a3e4910ed583e49106a3a564d10e97a464d106a3a464d10663a464d10663a264d10ec5a564d10ec1a564d10e91a264d106d7a164910e96a960d10ed1a960d10aa7a560910e57a360910aa7a3609106a7a360910e979360910ecda960910ed19360910e959360910ae7a754910aa7a7549106e7a7549106cfa7549106a7a754910e9f9354910e9da354910ee99354910ed19354910ec99354910e9d9354910e9d835491064d8254910e63a54c910ed5a94c910ed1a94c910edda54c910e61a54c910661a54c9106d7a14811054ba148110ec5a848110ec5a348110ec99848110ec99348110e4d52481106e552481106e152481106cd52481106a1524811068d5248110661524811064d524811054d52481106cd514811068d514811064d51481105495148110 else (if j<2 then 0x8822c1cc1781581381180f80d80a0080060000438b6421c2b210e4588870ac5ab516223c8b010e45808716c1af6b5e49c6ae77e35693722b09b8558dfa2ab26e2d55572ea6ab935355a9a926e15419f229c9f854e4fcaa63be0d355e9a9847974a4fc5a53be0d2b172e918f4d471794a26bdd50d5e9a86af4d40c5a69f24e34f56f0e757b5138bfb79b79d94d35ed665ab5132d5a59991d94c356a25dab4b2e11ca9609e54ab664e509f89274f98927ad8c8bce8a418f6d1e49c68e68cac69b71a309b8b184eca8b26e44593f16289f83144fc88921e3c40e7061c93870c49c38525e1c257f0210b7810849c98362dcc186f2e089787045bc08241e040b172e002396fec7a67eb4cc3e1df11ee1f4cf6fdb87b7ecc3de0f01e8ef88f26bc87863dcbb86b2dde5764ed2fb17675d33abe661d5fb30e975317308e5b91470dc42396e051c370635cb7b1aa5bd8b72dec5a96f62d4b704f2db42396d8fd816b0965b50432da60f6ed189c66746e33387f2d98bf84cc1fcb652be3b2d8f1d928b6ac733c7628ecc316f54d845b82c02acb5fb3d22f0cb2d785b8aba79c15d16e0ae8c70570f786b70b985a8fcc2c8b705677aa6b13bb657b6cc2be06615aff84aa87c255c1e0aacfed952876ca77d9853dea9a9d1e914a3f30a53dc65248e3295ee61445996a291c650d5dba7e5e613f1b8c9c95c64ed7dba6f1e913733309aafc34c19e5a5a7f152d5f8695bfc949dfe0a4ef6612779929229c84818e123c62e51967828b24b94414e421c7e610a8f6a839198418fcc2047661015f847e8bc73edbe31ed2ed4f797487b49b53dcecc1ef3548f58f6c78c7b63b20e39d04728e4978c704dc83726e11b93f14d89f846a4bc6346bda98b8660c023965ed7b52e08e5968472cb023965613cb2a08e594b1ed8a1af744ed7a5276a5d1384b2c9883864a41c32421e19195f008c87924417cb2121e19095f00857b7040bfb91f20e38f35ee875af503b53a71d81d38eb9e9c75a9743b13b41c12e40e2fee06d7b723473c41908e58c37ec85daf6a2cbfb9155fcc0aaf6605579722a12cb14086589cdf1c4b678e23c153111ae2880d7143c638a1c31c50dc3db862df042cff92149fc50a3fe484a7f14216f82109fc50753e203adf041c67960c97c6064fe28348f2c1467960b97c40553e202e1edc1641960ba7b704dec18218f280c6f9604abc40251e280aaf10056f8403c1a800e0d1807064c0383060009cbaa23e35382f2e948f8d4a45c68c1fe3c48172e140f97040dcb7d4de0a4eee9126e3307a47c63623e31ab2e94cd9f4a64c3b62e00e59200f2c85774e3ba3c700ffc3fe4ff8bfd8ff4bfc2fed3f78fdcbf6afd6bf58fbd3df2f7abde6f6ebdaef5ebcfcf3ebcf6f3d7cf4f3bbcbdefabb7ae6fb9b7e6bf96fe3fb7f4df9b7badedb7aeddf3776dbf36fad else 0xd3a200000000000000008d840000032e84000bba29b128aae86908051d08000418944045d141d0bdd0800039d080000000006a080000bed0400001ff650000003ba133a1ab080000015d08000000000000000000000190990fba2086e8402f82004d840000001ef05e6869c904000000012e48287241000000000069a100cb4259100000061a100000008fd903bd399000000000022d0800d0402ac200000000000080800041a100800000558400000001011a080202000000000001ee04000000000000039c08000031c1004361404020100804f811af610c025ec218056c211d6c6010000000000000000000000000040400000000b22000000000000000000002c88013c298c000000000000000000021c080000019080002d0768200ee07682000015ec400000158d905c080000000000381000000f60402000000000000010080004020100800040200010000f30201ac08000000040200010000cf084358431c56110013610000000000b604027d243bdc04ba14e8961d24000000000086040000732110658c12c252ca0947b8810223a4b48326b612c56200300500200000c151c3c80628c2e49e8723241020e8f91c19343486a0d89311704e018e318a8721360d17d8d8104520500a63e40546e84a2d40a80c8ce0689e448081701786122e0c1c63c1010a2816829f84094144260d20b9a13c0f81e11e100b002603e0f4104c0931931731531331130f309b07b05b03b01affafdafbaf9af62f42f22f02ec2ea2e4adf2db2d86d66d26d06ce6c8ec36bf6bb6b96b76b36b16af6ad6ab6a96a66a46a269ce93a91a8fa8da89a85a8268067e67c67867667467267066e66c66a66866666466265f65c65725324da4ba4824624424223ce39233e31e2fe2de2be26a2161f61d61b619617613a11a0de0a6086066046009fe9fc9f51ee1ec1ea1e81e61e41e05de5db1d91d5dd3dd1dcfdcddcbdc9dc75c55c35bf9bd5bb5b95b75b41b21b01ae1ac1a99a65a45a1d9fd9dd9bd99d97d95d9219018e18c18a18818618418057e57c57757517196f16cd6a96856616155c15995455254ed48d4694494294093e93c93a93893693493293092e92c92a12812612412211e91c91a91891691491291090e90c90a9071050ff0fd0fb0f90f70f50f30f10ef0ed0eb0e74e54e34e14de4dc4da4d70d3cd1cce0cacc8cc6cc1cbfcbdcb70b34b14af4ad4ab4a94a58a38a189f89c099c97c95c93c91c8fc8dc8b889487485082c8087e47c47a077c75c7387186f46bc69c6646446246045e05bc59c5785585344ec4984304103d83b83983783583383002e02))
def sgH9 (j : Nat) : Nat := 0x32e088018ae04c788818990a70b409c57a310154a4180001500083181c006040008340000000109e0780081485c006640800000061580784149800000b9000000429bc102ef300001b0404400182d07212a9ec4a0073000c1
def sgD10 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x1b83b00d91da1ea0e90f4a7485a83a42d29d21660e90f487201b83900da9cb5e90e147487023b63719d89b8dec0dc67626c37b03619d89aa1e90d457666801b33300dc19006d4c81b6a6289a83144cc1888ed8c067626027b42f19d89788ed8b85f645c27b42d17d916806e8a853665487b42915d99480ec8a51f605201b52806d894046c0a003724e01b92600dd12806e89003744619b82316d911a0ed8880766442fb22245d89103ec4891f604413b02201dd0f09ed0782360387ab91b3d548d9e6e46cf3523601b91a3dd38c806e8645b643007b71709d80b80ee8544f682a2fb2153dd38a806e44803742201ba1014d9880b6c840076a1e87b40f17d907a2ec43c07721c07b70e00dd069a6d42e9aa41663b20935d88490edc20d7621053b40735d88392ed818c7640c6bb1066bda0294ed015cf640a63b20583db80b9e4c05cb2603215301a6d9001fe9a1a32a6871d5200ffe7febff1ff6ffaffd3fe5feeff57f9ffcdfdefedff6bfb1fd2fdf7ef7f5ff7bfbd7bfbdfbefbf5ff7fbbfbdfbefd77dfbeddefef776ffb7ddbdebff3ff9fdcfddff6ff77f7bfadf7efbb77fbafdbfe7ff3fd9fdcf7e6ff35f97fc7fdffaffb7fcbfddfeafef7f6bf7dfbaf7f7bebbfddfadfd5ffaff57f6bf75f7af7d6feaff4ff9ffcffa7fb3bf9bfc7fda1e51306a3914c1a5e453068b914c3a564530e89914c3a064530e51914c19864530649914c39460530e49814c2a9605306a5814c19260530549814c1a6e612068f98481a8e4d206979348198e4d206a391481a3e45206639148193e452054f91483a366120e8598483a06612068598483a864d20e9593483a464d20e85934839864d20e55934819864d2065593481986452064d91483a960520e9981483a360520e4d814839160520aa581481a96052068d81481986052064d814815360520e8553482a954d206a553481a154d202a553483a54c520e5531482a94c5206a531481a54c52065531480a94c520e9130483a14c120e6130483954c120e4d30483914c1206a130481a54c12068530481984c12065530481914c12060530481534c12054930481514c1204c530481a8e4d106a392441a3e491060f92443a864d10e9593443a464d10e8993443a064d106a193441a564d10689934419864d10ea192443a364910e8592441a86491068d92441986491064d92443a960d10e8983442a960d106a583443a960910e9582443a360910e55824439360910aa582441a96091069582441a36091065582441936091054d82443a954910e9d52443a354910e4d52442a9549106a552441a35491064d52441835491060952443a54c910e5532442a94c9106a532441a54c91065532441854c910e852044393481106a120441a54811068d20441984811064d20441854811060d204415348110549204415148110 else (if j<2 then 0x9542aac0a15266106932a8293b53f49d99fa4ed4f8776a7a91a53d0ada9e056c8f127507639b83b0adc1da46c8ec73647615b23b48d41da4660ed4f5074dba53a53d29d24ea0e5274a72a7a4390adc1c856d4e5233072b7a83879d29c2de94e0776a6e3bb53549d29aac60cc47766603bb82f1dda978eed4b877665c3bb82d1dda969c6c0b15b4456f9822b49d2950e6d4a9276a523bb52939d814a4e94a42b6a5055b4280ad9941b6c4a0e3605092b927495493a46e49c73724e15b32748d493a4e549925724c92a92648dc930e6e4982b6a4c91a92648ca930e6cc95274a4839b5241cda918e6cc8c776a4417b52249d9910eecc882f664467b22237d8911cec08877724247b72133d9100eecc7de7603e73b01f49dd0f05ee878776a3cdbb41e2bda0f24e947921743c14ba1e0b5d0ea46a47429743a15b31c4adc8da56cc6d2b523615b81a49d40cb1e9c6473703239b3181dd98b85ecc5ce7602e3bb91633d90b25e9c5927742a17ba151ddc0ab6ed054af682aebb21533d90aa4ea0558f4e2a97a715485d0a85ee8512f4e2839b91493da89c2e9c4d5f4626eb931374c989c954c4d27302415b81249d4088e6e044736a2093b50f1dda879bec43d27721c3bb90e0bdc0725edc388f6e1cafb20e33d90724e603923301c90b90e1ddc06bcec034e7601a93a80d48d406a46a432ab0a1755830baaa985bc61428e76a1273b30939dc041cecc20e7700e73b50739da831cecc19e7700a73b80579da829ced415e30a0a73b30439da819cee008e37005298502a4c181546e406a3700351b301a8d400d468c06a33003519301a8c180d56e802ab660155a300aac9805560c004f712027b59013d948216a2410b452003b58f01d94780ee23807651c03b88d01dac6a1e522daf291411b88a43d444a1e96250f530c9ba686435d43216ea190b530c83a68500dd428c6c6104f690633b18301dabf80ec5fd034cfe03b57e01d8bf00ee1f4f76efa1fb77d01d8be80ecdec0770f403b57a43da3d09ed1e84f68f001ba7700d9baaae89d17f30e811b17411db39a1e61c10f2ae085987042cab8086d9b8ef50d827b46908d83420ae59d0552ce81b96740d4b3806e599074cca01ba650cdc32a2ea591974cc8b9b86418d9b22e661903370c601b36318d8b182ed9886762c413b0621fd830006e574136cba01b85c14d9ae0aecd6c0372b011b05800dd2b8a6cd5c0370ac01b55614d9ab0c6c5586762aa03b95400daa935e6145ab30a2a9525066db27926d93e5f489a59b54d6ecc2696ecd2cc7649663b24a31d924a8e9125bf66905bb34831d9242fe6120876e8e5bb34725db22af66114b762892fa4449bd221b9e610e7f268637b9421a5ca116ed5065f488259b541a0c0a080ed50007648083b63f01da9f80eccfc07707c03b53e00dd1e806d4f0036478 else 0x45344a5d949f291651b0a2b1444284e500c9f293c827484e349b4134d263a4bd096612b32514497491e121823de47508dd919e22fa452089210f52180427083d104820383f9c7e18f8e1ed43d0c78e8ef41d743a3c7358e421c2e38006f18dc01b5436446bf8d6b1a9e34846840ce4198432406338c4d1866308460b0c0417ec2f905e70bbc175c2df85b00b37162c2bc856f8aaa151029985170a0113a826cc4bd09631298246447d08d5117a224843f0858106c20083ee07a20eea1d1038b86f00d6c1a1033306470c4217bc2dd859b0aba14e828404d4097a12a8244045e0880109820083c907260d981a9033306080b9c15b028904ca092011a020c03cc06e40cd017a02ae04e407f80d9016401dc01b00006ddc4836ed641b7652093b58f49d947a4eca3927711a93b58d0adc46056ca31233118b7a58a6dd2c48eed620776b0e93a58787d343366ea19b3650cd9a98669d342a4e9614736b0a39b2841dd9419cec20c2f75046fb1824fd34136e5209b72902d3b3804fd9c024ed5fc776afe17b57f49d8bfa4695fc2f6afc3bb87d0bdc3eb1eddf52f6efa93b17d48d43ea4661f4776af8ebb27c49d9bd8eecdec2f66f6b7b07b76d8bd8eee1e82f70f493b57a1ddabd05ed5e9b768f4a7b47a48d43d24695e92330f43bb37979d83c8eee1e0776af0dbb47848d43c24695e07774ee17ba771ddcbb8eee1dc7374ee15ba771cdcbba46a1dd8730ec15b5760ad8bb2dec1d52746ea91b3751cd9ba856cdd56f4ae8b7a17438d8ba0eecdcd2746e615b5720ad8b924e61c5c726e215b8710ad8b8a4661c54f50e0a7a5706dcc3836e55c26262e0a7a46f0adc37856d5bd2330de91956fa298b78e6d5b92750da3aba6d1cdc368eed5b07762d8e1316c49d4358eecda87770d23bb5690ad9b4276e59d3b66ce9da9677acc33856d599a74cca93a5651cdab2c4e9991db66c86db36476c9b23b54d907366c63bb3620bd9b11bec588e760c43bb9614fd330bfec5820760c017ba5f2bda2f9bec57d3f4cbec1985f4fd32f24aa5792730ba92b95d1d5caea4aa5752372ba39b95d0adc2ea76d9749b6cba91a95d49d4ae176cd707362b83bb15b39d82d8eee5687172b44db65948d4aca4e61602b70b093a8571cdc2b8e6d558776aaa6fb15549dcaa0eee5502f70a8b3b15437d8aa24e61512330a890b9540bdd2991edd4dc326a73b98519dcaa8ad661416b2aa0f1b54f38daa79c6e139e3309d3ba44c38dc261c6d531e3309949534ca8a9261ced52ce7629673b84a39d8a53ce6128e7709273b54979cc24d454924e76a90f3b14839d8a41cee11ce7628ef39847a4a9a3545491a2f6c8a73b5459dd222d5e451603308b495345a8a922d2ee512976289499844a45ca254e610ea3748751a843a8cc219cee10a774884f39842a4d9a1546c909e3308529)) else (if j<5 then (if j<4 then 0x180f0a2c30902fd0f45d1ec5d102cb1b8471b83f002a09429e201605426f0bc19be1375e6ddcdab9b2f360e6b64d5c9a8134ba6854cf499a932d2646cc669883308a600cbe497892eb65ca4b7696b12cce5844aea958f2a925404a6c94a729125194a1c9409279e4e849be935d26464b3494d925123fa47448c39163223a435c859908520c2409c8028fe51f523dcc7908ed91d1a38dc6f78dd91b5a360469e8d01192a31fc62b8c4718362f345ba8b2f160e2b8c5518a5b145627b44de896d124e241c47488c1112e21b442388230fc21e6c3bc87570e2e1bc436886930ce218a42ff85d50b1a14fc28784e1094e1204231843707ea0ef41bb8337061e0b64156828904ba087c0f681bf033e057c0a280e7015e01d40298008ffa5fe6bfb17f3efe09fb6bf4f7e7afc9df8abee97d8efa95f3ebe607c90f891ef9bdd57b80f6c5ed33d947b0af5b5eaf3d2d7a38f429e7b3ce2799ef2dde45bc777898f079e07bbf977ceef0ddda3b9e7712ede9db5bb507662ec35d7f3ad67562ea6dd3d3a657484e8cdd0b3a0e73f4e765cdeb99972f4e539c9d391d7224e3e1c6ab8bd7140e1f1c30b847704edffdbef37c66f4ade31bb537546e7edcd1b8eb70e6df4db81b6736bf6d60da55b3eb6626c94d8ddb0735e86b84d691ac435736ab8d4e1a8cb4fc69ced349a58349e6910d1c1a2f3447686ad081a0233f267c4cf399dd33aa6714cd819a733346648cc5597c32e46594cad994cb28464d4c94191fb2236412c7e18f331d46388c6958c5316f62a8c4fd897b127623ec42187ab0de6192c279846307660c8c13d81d302e604cc0297f42fd65f72be9d7cdaf935eeebd417982f195e04bb9d76aaebc5d4aba3d73c2e665ca0b8e97142e1c5c0eb7c96f02dc85b70b67d6c7ad7f5ad6b5656a02d2a5a2ab3e16742cd65988b281638ac5f5892b0b560f2c0c57e8af495db2b9a56fcadb15aaab3d564eac215762ac8555aaa355392a535470a85d4fda9d5538aa6954c6a95d52aaa51549ea92d5222a42547ba8e55196a2d54532895510ca1c542fa84d5076a095406a7fd4fda9f453d7a7a14f169ded3b5a7584e829c5d387a7074dfe9bdd36d26c24d6a9a79348a6754ca49919318261c4c1897ad2eda5cc4b7a96b92cfa58a4aea9549299250a49d49311254a48548fa9169222a42c480a8ff51e3a38b46ae8cd918822dc455e89ed127221f43e487010d6a18d42be84b507fa0c9413681b501d20083fbc7eecfcc1f713e6e7c2cf6c1e9e3ce878e8f029ddb3b62763ceb71d4b3a4273dce5f9c8f38bc70e0e091bf137786e30dae1b2a35f86af8d539a9435066950d1499f43388668ccb89949325e6438c7098c0312061c8c2c98383052604cbf797de2f7a5e5cbb297412e485c1cb7216c82d2c59dcb2a162a2c205804af595c62b4655e0aa895332a0 else 0xf080a33d861287e7080a1d01cec687398a8108e790487d820425df6d9a0526ffe329861438e6390023af79c9157bce48a79e19c09e2cdc09c7f1c4094804a3ec3984d6ce7080a63a70a600673d91099d01c54ac67e50cd029de167008fcff04ab02191fc04ac42a8f7848a9fb59a1c02684fdacd0e01347646c7bd4848b3988745f1f99033e63ef9897d3548b8f8e2850ab5ec5a2c7acf9913c720c9950e62217e94045989b8f3227fa435271344c57cab412175e2214123ab5cc976193582a56ff898680338afe9091a1f0e24a163f00e128cdbb53117a33cc8bcf0c45acf93c13c7ff00901001a4cf78840a43e5b5308933a7fd82000801a4ef33080a5fe7bc409dffb81844012afcef33080a83fdbc480800d267bc420531ff8424040069bfa18d0299f0781808f3d4f94023af4bc4501201ff202022800882fef91000cfb1f22808f3e9e2100499ebec220092373a89dfa8107bdbe2c91f32a63de16a25d6464ae499e700c93c6bcf060246f89510ef33080a5fe7bc409dffb81844012b9fd3b4010a97fa222ff20891e312028f18a9228f18a1e4828f18a9221fa79e21004a5fd5211738f89400cebf3108461f8fd004699c861ff26280200692fd068196bbe1a0655ffe7e9484804a3ff703c081547fe2000019ee5c42052bffcf58c00804a2c5c4c6ec8953fb43208313417f320279ce650424478612e7fec541066439436fca1a8199fc7acc0a6f3c601010069cf9c04019b32c3fbde741069760d9eb004353e79d084021e1ecf142010d77f0b940a61fb0d5502a0089dffb8184401297fc8245d782810941f30d0336ffdc0c220094de78c020200d2beaa648dde11a435f32c0351e78730271fc78105201287f958c202012ce381287d05bfcc6409f32e301006763c03a8c758844bf2072814fbfb641110804448fe3c082900968fe260000865f805a71149080f751ea80218733268aeddf688b008777fa2a0004347f90c832c7c495927310d1f4c2e8216df4114285a7dc8ca004337fba2642ffc0264581af268d31f2122f7ffc25221804d35e5ef01337bfb59c285b416f6c29178512ded4fc2b3580006b0cf5e8d4c001a619580332625c07184835101a53509e3823a41449116098047305118382790580e0085211a062217e358690a4020a5031aa701da0f872a68a2109a9011a8aa9a8408c0210b4048385e9725cc1a185445d8716e8716a1332a440794bf13c3234431050e2401312a6100e431860820913308c34508611d4222c8190844810c4919616186063e280c583063c7f1740b0a47a014151c35c62840109c200853000522a98d084008d0fa2143108c512d85a3c375105cb01815181a6200c0ad261160f23c4c02b41c12c108303e164531822b11c40d9c070bc670c0b0b91831d450d34606f0805dc10b407862c771c32899c5) else (if j<6 then 0xfa91672622c7f1cc6cc01fb095c3faa5ccd45af6e654fd4632b15bf32e7e558f1eedae8483668b5c904c0607b616da1d78820f3d18f7c42d343a686bac232053f31a3d04830a7e63ee8c55f0608eb662cbc3cb9941e4853a85a2e5f990bfa39911170452ad8c4fc56aa912fa02d1a427b68d4af05b8c4307ddf3a10f4239f810dbf998db8628e0cc7de313be609380619339629942d68829708299428fae4f6497f8d56b2173c62d771a0c6508b91127da1939460ade5183e518226d27b23b0e0819b6838fe318eba47de54cc86d5ec1fcf073662cf18a450abb07c327b8cb839448f07282ae0d5e50567420001871a8ab21261c6a257941000558d85a55ed099ec82cd9895e504af28294100a2f70a3053f44210bc62a2642d1c6cc52820145ee146077ee512153af2f1928a1d1470663476e106dc3137da18e6e8512f1a873742897b429f810d78d43cd98a5055e504af2824d58b16430ace85bf0cc7d743d7434e505c1b137da18f2c6a29764103f01a0c3c8b83622f1880ab9d1a92d6f50cda643e6cc507cd10527a51ab812f188a21d8f1bb06884170688377c828377c8283cd98b7bd21c19d2201d544b743228e8f64a8d3af480d945f1841a9df6342332ec83f7d28d09ee0b20f5c42cd0947c2146ad0d0e0c29991275e5e32549ae106722fe3b4338066e08066e0f3db84180370c45e314b343064f3416e42ae91ee4257941664c49ab1178c5af34166c36159d0d9d0f9d0351f31790d0871113cd05d743d7431e18a3833181f70600d4a000000008f67483b754839a0c6a9639a0c9e0a51a5ea645a4d41ad158e9d60b6d0b5d176d09ab8386870d0e1a1c343761a222bc127ab534659239a28407ca99558504cfe465560a306e144ec9c194bd27db28027ab5346553e21d04bd8d3c5205ab300761ea1e64600d3ee0f6d2348801121ea818ac600d39f32b0650eb58c019bbdbf9101001a447eb3820093dedf5080800d33e388198049d33d44620095a78e231004957827eca0021dbf3167f198321be6a748010d6eebbf840043abeaf250010da04b67a45e14407ae6ed7e4cfccddf2e80342be6e2928008727a36422f0a1cffdd7c1029ed69d40ccefee5021375f9a0423b7ffe0d400800d27fee5b020554ff010cc00a1d3fffa080040069df2aa0401253fff80a0040069cfffd1c06403473e0834010c7f7f6b2814967384053669c2029df217008f9961c48033db934e0010cafecd240e0011123fc6a270093bfe08c80804aadbff001965f5000085e03e014227fec9219189a43c774e1401a03c774e1401a2bfa9a04c0069afea713001a03ff8fe99a3c0269b5364a98588f2085e0d0ffb899c02ed0ee14317837b3f3189a40bcbfe81899ee2e42053cfc19018e143cf1ad200241a3984d6fa8028417e0a14054363e6102129e2d3cc4021c0 else 0x949660f1d2d07058d94722852e105ad10511858e45091e4ca0ed72342facf665dfb90d8fce1a8f9dc2f6135b33c5ec28bc0dabd85c384023d246e280c3e6c913c273c9820edc93b211ba431929f20f8f680a3e3da028f0f91601496f6f984ca193fa04646be312548352fee291afc53c693da60bbf68c7b908f42323828939d98e3da0cc839f10f39629c428ba045185fe48408a50fa131ebd2082217583c00e88527a209eed7109499b3145e6106a407e4a09083e216dfc43ce589bc4b2c95d239142b72812129f8341f3bbe4c1a161c22a1a15baced0666ab5216a0d4a6fc590d08c068dca227a2089464e684ed3a59915f077581c0687a42b7a8600bee219a46fddb8557265829086348ddbf09decc587a1132cc0c2178762e32f0d6614bf88684af366327f33a868507f15a109068564881e20b6d1444dd82ac2c59db17b93aa213afc0c95208d084685ee3f61091858a0d0a40ce261d2f07691184e916c686b63434fbc9a16520be9b990b58f0c7eb5308193d1074f20a62151b9442a714b8483986a3a3d330d482f3a87099e8c4c919e0f5e4824f98b04f8253cee9475f1c636a274562474e9b9908702268f20a0d90d6d7d906dcf94649e214bb42892159fb8c1abea041abea041a7cc5062c0a31d421978740c91e314d27443e215baaec02e4307f1042cbefa708426bf9ae80c2c11b728f06db080ab9d1a901ec5f179890d779c051af190f4d0a029f90ac9111e6515b8100016ff772435798a7c429668296682ed6c4171888017e0c01d0d0c9054ff90114e1692799bc4486b24509c31efc8426ae70d49b909bde635c6219922b2440fd3a0daee67518bd1e02421d221793e00e8583ea102524a9e868d39a684d68c169f620ea4870306621a300f7682eb7d4232bbab241e3f96874256398465040deedae86af462d390251b018fe398c5fc82742672a31c5c83a8daa9a5)))
def sgH10 (j : Nat) : Nat := (if j<1 then 0x600400590104000000020cc9812343000020280001d27e9106109800b8393416a03cd13112051228512014381ea0648000822e041f03d80000000805c000204a406b038f74380000000000204d963e0204a342092e0020001821a4170f0f000082c800000000001205c0000000c8a40000000005b0173227a15090769e2e22f7070a08f807e846647460d38057a39f03e0000d1c3819504e6089013e81730696c7d91ea82d80000000401641d20246123000082a70482e9851cb1915065f650c1c4000008200d9409f00dc0006070c20d39ec00060c60092915c00020f00837026500608e3918181d000000ca0000038306dcd13402101fc07c451900ee02a000020d5418b23600004f154141a1ef440e49d41a303ce047251b886b00562344ec5c0bd811801dc120d0f5845461f20e94149842802fe0c1c19ea0c304a00da80d3943f0794c7601e904700002097ea25045342f36400045822a4650018000080cc0000000017a00da234a8380000a2492106024516d0027093603ac02c00d340ea0b3d53a000244c88208223806e07fa419412d18000006040415e000000040524106845808f001e1ce80371475a897914022340130eb2d07400a408ec02000008341000800000cf3a5d076000e80f00002705801a4155819000028f642260487051c0c0c10382b10378066c21d08250354013412a02ea0800000c221030f03ae0fdc1d58a2d086e10b91cc036106ee0edd058000003880c410e541dc00008a80171229800040fcc0da000306160cd80d603961518000c16301b347480000000000004d002c817e0001762601d0001a2520490000c0dc0001021a88c11f0023363de08bc0738ab1685c0795d49206001c40f5c83d81fa006a8df013a00c0087800081e2001800000009a29235c46b0000000180bca51d655017932da20d202508b2810a78940ee417d812f03000004033a0bc01f60b04252000000020e800a9a02a06a282241fc0407073a027824510a000060ef00a2000000000000001021620b28a2c612000000001120001840c092604ec23f0a4fa69c0fa0001b85400028e0008b8414000000310628220055c88f4055824c0006128000020e605760b580e40000000611880b031d707b44740001049c00000000000000300e404d106e20ad07d8056c08e801100880870000026102600d60000ba6802ac02e40880288005000044f80000000206340a183e400020ce1e140001019005d41d7b487056a81e0000008e05a00000001a2a800fc0f77e0500440c241c00003f212657001706000310e568005e001608002201040e0c01019c0c0016660202330210030b390407232414150c080200040b10010000040015150b02051022032b022d06010d0c020703040802040101100000070100090b013e001e08010609000804210c0003 else 0x601488ad02780000000e8c8039b02bc06182112a7c23d0000c0a7109d06f00df0177031d0532510d1d8023646c80000001222604880008234bc940006000400ea07000000004042a29e007c07605530a2b053807d000100f4a56282a00d1835c47220c892010049052800000631a4f039a8c8810180b520880b78219846e02d608440c481)
def sgD11 (j : Nat) : Nat := (if j<1 then 0x41fa57e25f697d31f227be9ed37a99e837989e427861de176b9d877561d3f7499d017379ccc725dc737161c237029bd56eb1b806cfdb166bc5ab66a49a6468f9a1667999b6664196164f992964158d562b187961198145fb57c45e5d7645ced7075b916aa59cd641587d5f156e559c55c5546546d4ee52e948c519543350553ee4f153894da13454c7d2fc4b252a049d525148cd20d47851b0462d165450112943e50dc428d07140fd0043f4cfa93e00f433c50ed53a90e803938e2237bcdca3674d7234d0cfe333cc9a31e4c48304cbd52ed0b812d4cb1c2bf4ada2ad0a8e29a0a2e28009d0268497724f4904234c8a421fc86420e48041fc87c71e547721d2072d1be86c81a3c6641900619181c5c9167c57c156c53d144c4e412cc48a118443f10b43ff0f703b30e2035a0cc03030b5c2b40a30271096023d08881fd0710197059013004000e503300a501f805800b4000d74b4d3533d3253d2a53d2a70d746fd742fd750ed74aed742ed2a6dd352cd346cd326cd2a6cd742bd552bd352bd342bd152bd352ad34aad32aad7506d74a6d7446d3065d7524d7444d3524d7523d74a3d7463d3523d34a3d3463d32a3d3263d2a63d3522d3462d3262d3062d3521d34a1d32a1d30a147514474b447454cf41473314732b4732549f29377253755337353373472434727351143511734b1434b17331173510435107347043470733107327072a704746f7742f4742fcf40f7342f4750e474ae9f48e4742e7730e772ae7330e732ae7330d7326d4752c8f4cc4746c7726cc722c7552c7352c4352c7b30c4742b7552b7352b474aa772aa7552a7352a434aacb40acf309cf2a9cf229cb509cb4a9cb429cb309cb2a9cb229cb029caa29730677750647506774a6474a69f4867744647446cf40673506734a67344673306735057346573305732a573265755247352447523474a347463772a377263755237352343523732a37326347522874e2474627726275522735224352273262b3042474a1772a17552173521434a1732a1cb500cb4a0cb460cb300cb2a0cb260cb0a0cb060caa605b43613515134b5134553f4145f2945f293534d2234d2134721343213511134b11343113510134701742f3f40f4f30f2f48e274cc6722c1552c1552b1152b1552a1152a974893f4296f309a72696b309a2a69aaa49a262913508134a81344813507134a71346717506174a65f4862f486174466f4063f40617505174656742537425175241352417523135231f4e213521bf4206f2606b260aaa40baa20034d20f486fffffeffdffcffbffaff6feffeefbff7feffdffdfedfddefdbfcffbffbfebfdbefbbfb7f9ff9ef9bfe5130e45306453060530e6120e4d20e45206612064d20645206052054d204c5204c120e4d10e491064d106491060d1060910549104c91048110 else (if j<2 then 0xadcfef24800957cb0060a943012bf03b208f9fae44c000d12abac750486ea1fd82480d1bfe3deb0c41277ebcf094004abfec380053b88fc60047dc57e2c0024b61e3658e206927cf7e00148f6447d1400264c74780474f4f4c7050001ab7f1ebf38400252ffb8884800953c478023774e224000d07f997b9a40805cb107845dfdc4000092bd7703001257aee0600248f260652c12b789d98194a12efe5e18f542bb97e594852b97ea70a04a56fb1208d59e58500aeacf2c28059dfe5989c44800d76799a0288fe424052747e9281551fd1102a2fe550c5480d23fdb648049bfe7dc640527cdc640527ef6a045f039ca0537ff8dbc00544ffded100c2c5f88e0023cfac580090bf11c0047cc28c79f8e84c000d170ea0289affd7a0524025a79cadb8a00d25ffafb0328166ffae97200b804cdfae95028025dfad36b20577fe971e0291ffef810850002617ce96100068d99f15ca1403009e6f6b6091d02f1d2fb5a4602f1fe19989a07a59e25c9246effda6d8025edfbfe011b6f83fb000929c5b840019c6cf9aec8413804f1fafa978a6012d67abd08c0254afebd2214012c29c600cb3e39e3d80049b3f5afdd42817561fff97db0ea05c7e47a8288bfeb842b2094bffc652482427b61e012220692f4d30c87cc7aa0a69c91d402ba7247500ae9c91d402b0fd13224e8801a96cf07c4804ad435e4f1804a423f38c900953bf7d5402407edd008b4400d45e61cd2212006a4ff3d700103407e7ae0020683fe8f0014befe0073ffbd940055be7efe408004a5801eff3db300155f3fcdc7c00577f62e80a47e3f9000477f7c00fa3fefe0b2012a57ffce52a049cfe5b1051100350ffae8000489f7c400474a7e4000ccb0038f03f5ffd40000973cf81540245fb3b00287fdf30049ffbc01170cf2cb0159e7f9666802b5d7ab3a020253ff36f7802f7167810092b3d48023ac00fbdec2f040254e063004798e4d840249fecf32a02a9ebcea060126fd40f6e02b9ff43d640241fff72550151f13f20288f5ea200677fdc00efde0077fbc00eff7801f3d7cc00cc3f03ff40a4804b4fa75f30033dffff0c2e002b0dbfe08666269def8b6a0004b7fbc00efde0077fc8bbe0187be74d00a69f0f340296fec58480ceabf9f2c8049c0410391c51a012f073004a0c422dc0c561945150860303132431e10d08c636208400a40c3052c24b060131e0e4d1124d4108858361a1004c1a381224d0e9c1a22234c242e1c160a0b9170a5a60a105cc4232605807433008fc32e1846a2d0ab0c1f08117128d0fa1c611e321286289c5143145f84c1d1c522ae3b1e8ac6c47038c26e0f0a55694de50d935e4b5926a4859176438904e3ee8f423ab8dee3568cf631b8b962bf8a8228289a223f8886202879e1c786c2194859e14b84c210d83a20bd8286084819603e8071ffb7f else 0x1b95bc517575f122a57ea9648cf5c6d6ae0343b4abe8649093c41d10d72493fd6d0828e9f54028664f0c5123337f86791966b8c24590bd46123c5ff698eb624c7d5cbd194b21ec65974f23297f89c4c0bc8d25c492c5b31573e4659e24f1147d3c44587feb4623c7e4264c994721954a98a29bf902422f7b43a4d6b646f861a816b38fd89a21683c648f2d606cb6cd1604850f8faa2d8cf94e92c9ad2d684c3d5768a58ca14ed99ba772065cc6b9832f7d92b54d67af3f20a76cd5d328c9d162f6cbad2d684afb87b4ed987d08f40120e03f98815177e1a7e40a8f0bf901454bf440a4819f50a27a8975004906f9fa442400d33ea2e870b0128508fd6023a82847eb804a77f003bbf801f7af00008fbf800011d28072f1f901100034deff940143fee0078fe92b0000034bf7801d73fbf9100009479fb82802b3feb9da802bcff5e095102000361f73a8e80aefed1c0054bfff9354a00012e0fe40011cffbf253882abffd8a80a6fefa4140ab7f5e230581267fabc140012ae6fba802))
def sgH11 (j : Nat) : Nat := (if j<3 then (if j<1 then 0x81c80000819800000001a4e28542000000000000122d816098f600db80b600008357832ea4bdb88a0000000000000000000085320000000000000000000000000000000000000000000000000000000000018400824f817a04ac9b7283778258038c01298351a0720000000000000000000000000001043104b1807c0000000083c6000001ba0001bbfc0484000000000001da720000000000000000000000000000000000000001102e00000000000104f200000000000000000000da4a000000008202000000000000000100c4000000000000000000000000000002f8000000000000010600011294a405c2740000000181700000000000005a7400000000039e847a83d20000000000000000000000000000000000000000000000000000000122220000000000000000812b814bbb8f951e000000000000052684b6808f822f04c8009c021e83e9a323006c00000000000021080001d4ab597bd2e5218a0001550fda6380f60000051b83b200000001a42e000192a000000000848a0000000000013b8200009b6e80ba000081ec908a8152000000010404000000000000000084ec851ea3d6051c00000000000000000000000000000000000081958396000024e0000000000000000000000000000180e20001830c0000000182ea00000001819b804600000001a13f82780000a1440000a2260000000104360000000001b12a0a00000000808180bc0000a3d200000000000080ec02dc00000000b23c000180f2219c000181660001049205080000000000000001013e000000010117848200008413845e0000000002418086a1e90353a3a20000000000000000000000000001245e000001f503c200000001005200000001090539ee0000000000000000000080f00000000000000000000000018190000002a8000000000000000080d800000001806a000000000000000082b40000013a000000000000000000000001843200000000000181a2000000000000a3b99b86000001cc0001845102220000010b80ce831613e600000001a44200000001d83204e40000000080d40000000023a52146031a84bc80ea0001daa6035f845a01fa0000000120fe0000000000000000000000010496b14184a8834a00000000050120fa0000901c044e809e04d8000083c88156000000005a3e0000804e900047180202200000022000020140100c210024018421000220a82800040008011100000c200004110c000002108c4231840014040068020021400204100100c6008d2218020000c0100c10800118c0108806000c008803004030042000c65414002000038c6000808000220086108402008e01006300540008200006003020094c1184040802009880000022000200041020201800000040080601002000800081400040000c0030c04 else (if j<2 then 0x1025a00000096929c00000001043a542e000000008439816a0000000000000000391a000181040001849fc06b0480829ba4c80000000054920001802c000124e800000000000198f80000047e0000000000000001b0bc000083280000000183580000000000000000c3e4000198000000000083f8000183020000000000000000000180cb109db0f00000901a844380cc0000000000000001037c03ac0000a4520001530700840000018600003a04bc100000000000000000848c000000018012000000000000000000000000000082040001839400000000000000000000000000000000000100360000000000000000000183de00000000000000000001045802ee8090829e0000000000000001a124000000000001a04000010349a493a39320b1da300000825c0000000000000000000000000000000000000000000000000000000000000000000158460000000000000000825e000000000000000183e7391d02680001012c00015a9801b2000000000000000000009b7400000000000000000000000000012498820c0000850c0001003180ee0000042c000000000511035d04f80000394a0000021400000000000000000001821a00019018000000e01215811e0001dae60000000000000000009a000104060000000101e8007600000000801e000004d4831d82ec0000000191c00000000080c111b800000001a39a000010460000000183180000a4a405138028832600000000a4ce000091f200000000000000000000000000000014000110cc0000000108fe000000000001a38a000099ec00000093243600002026000000000001bc0d054103f600000230000000001092000181ee803400000000000000000000000000000000000182a4000000011130000084860001803a0000028800000000826400018a6880c785280000000000000000018a0000000000b40000000180fc0000000000005aee018902120000000000000001394c000000000000000101c3045400000000536a000000000000000101d600000000000004a40000000101e60000000000000000000081dc0000000000018b7b51ee0001817e00de0000000000000000000000019be60000000000011a6821f60000244a0000000000000000202a000000000000000000000000000182f603bb03139204000000000242000000000000006f5858250a000082c8000102600506000000000001831e82bebc12043400000000000000000000238200000000051400008237033e00000000000083b400010ba003ea82930184000000000000000081f20000000000000000d113828e04b983b0ba0600000001a3beda8504da0000000000000000000000004bffa126000000018178000000000000837000000000000184038546000193740000836000000 else 0x3b868064000000000000000000000000000000000000b12e00000001139000000000a39d02d00000000003bc0000000084080000000000000000000000000000000000010424da5e0000000084fc0000000002b800000000d2e6000000000000000000000000a09a0000a4380001aa2b00aa000000000000217e12a6001a00000000800c80e62159052000000000000182fe000082169372000002de33e40000000084d000000000037e000104280000000000018210a15e0001d51f5431019d92ba000003c581c4013c000030f4000000012448000000019063002f0124838800010491004000010392000121fa000100ae0000839011ee000003f03b060000000000000000000000000000000000000000000084e183a20001dae2807e04c700a40000000000005206000112840000000000000000000000000000000000000000000004f6a37800000000054501d80000000181d20000000000000000000000000001243e000081ea0000000083da000002cc00000000a470da860001a3965a4400000000000002240000829800000347108c000000000001dc920000000000010270045680b15a580000000000000000000000000000aa2483a4936ebd18850e00000001016804fa00000000000080b800000000000124e6000002ce00000000000081e40000052a00014046000000000000000102c4000000000001923d52280001303b24620001a00a0001038a0000000002f4032d52de33e983780001900930b8000000000001046a00000284000180d0000000000000b51200000000a0f00000000000000000000000010bb00000000000000001b50c0000bc1c034e000000019bdd1306000082f321eb091903640000000000000001842e000000000000000000018020936b82bb0476000000000000000000000000000000000000000182500000249a0001053b005000ac00015a480000993000000343019780c304a703d40001004521f40001053d890c000092dd9333a15084160000049800009a34000000000001032000000000000000000000000000000000000000000000000000000000000000000000000003840000000001b400000b860000000000000000000191e6000000000000000000000000000000000001246782c2000180a790071234000003ae0001236e0000000083d000000000014c00000000000081a400000000d844000000000000000000008522000000000000000104ae000185179b7000e4000023c20000000184ee0001bc0b03be0000815a00000000029000010267249f012600000000000080c800000000817358300000182e0001036e83fc00000000000000000000246c00000143024502cb017524c7024c0276008a0000000081a8000000000103d17a001c00000344033b882e0000000000000)) else (if j<4 then 0x2e000000000000000015a41984600000001019e0001027c00000000000000000000844b83e00001bbfe044804a2000000000000000000000000000182540000000084440000010f0338000104eb01b8000084cc000024a00000000000000001a3ef84740001842302a18060809523c80000000000008296110784f0804382e0000000000001a456826b8063850a000182080000000024be2b86000000012028000180e98138000115208206b24c8306000000000001028200000000000103f20000000000000000000000000000000000000000821d81f600000000000000000000a10a84a00000042704d7802a0000c3f200000000000000000000000091c200000000000000000000000000000000000000000000823a0000b8be0001a49d00a2000000000000000000000000000181140000000000000000041c000000000000834c844600010330000000000000841482d59264150e0000012000000000000000000000000000015a9c01500000000000000000000182720001803351b824cb351a00000000000000008228000000018538000091e83d2200000000000080671254826f03dc0000049c0001b142000003ec00000000000000000000011203b8000000000001927000000001a10f82b002d2222c000000001170000184ab109a04fe000000010419005402a3022a0000000000005ac0000000000000043e0001a3bc0000000000000000846c0000000000000000000000000000000003620001a3d400008154daf4c0bd04b40000000000000000000192400000000022ce00000144000800000000852c004a92bc0001934490420000000000010162000003340000000103e200000001a3a00000000000000000000a0000000000000000304600000000000090f800000000048800000000852e0000000000000462242a2440000003f4000084e20000031402a782c6000000100000000104ba0000830e00000000000102e804dc0000000000012176000000000000a3900000000101400000000000000001bd0c00000001018200000000221e004c828a0000000101acc3de000000000001907ea4e4000000000000931a04c4000101be0001033d81e3202280a9d2ee24640000036904720001516c0000000082d6218e00000000000030358201985c000101bc81de000180a000000000824800001a72000112178006032b00240000000102b303cc00000000000102e4a36d820a04b20000839d015c00000000000102c0000000000000000000000001826caa09d2ac0000029400005ac20287840e128c81011091040b0218939202fd212881d4000ea0080001811d4a0b84ce818f927400000001928a0000000000000000a42330b6000183540000000000000000000000000001123a00009056045c0000000000000000000000000 else (if j<5 then 0xbb83522512a000181650461510700d60000000000000000000000000000000000000000000000000000000000000000b1b600000000000000000000000000008baf044000000000037403400001023891ea85315a67250600000000000000000000837a0000000000000001a13c823e237e05180000000000000000000004e6bbe2013401e104c0a0f600000001243a20060000853600004a0400000000000503faa38830fe00000001931c0332000101ab21f80000000185020304000000000001950a0000000101fc000024ab827e00000000000010b203b600000000000000010253a21c0000000103e5da8800003c3c00000000000000000000000000000000000184c20000b12880b20001835a00000001005e000023c40000000000000000000000011b6c000104be000000000000830a0000000000000000000000000000b230000008940000000000000000905200000001814800000000000000005ae000000000000183980000000000000000000091bb0108003c00005ae4000000000000000000000000200e4aa2000000000000000001db82343d16000000000000000000000000000123c612960000127301cb02f000001b6882dbdaf20324d452000000000000000000000000000000000000217c0000a16a0310000000008058000000018411bc0808bb23fe00000000000042720000022c00000000000000000000b8f000000000000182fab5100001044c00000001b234000000000000923200003be000000000813703a05514bc0f214f239902d800000000000000000001830800012a0203d800000000900f048e00008070000000000001815e000000000000000000000000027580be00018382000112a40000000000000001803900d283fe000000000000000000000000000000000000000000000220000000000001807a000000000000000083cf80220000038e00000000000080fe000000000000a06b83ee000000000000000000000479840c000004703bdc00000000a43200008002a45c0000016c00000000000000000001849a000000000000000000000000000000000000000000002420000080dc0000000000000000000003cb25080001012e000001d00000049400000000000000000001000000000000000000000000931502abd3932a2c036c0000000000018534000003d600000000000000000000000182b680780000000182260336000000000000da42000000005aac00000000000000013aa40000000000000000000000000000d88139b4000000000000210c00002103544c047d80180000000000000000000004520000000000005a6420240000000103a800000000000000000000000000005883916ed203837200000192480881c1042a000084e8000081c600000001824a00000000838600000000d else 0x81ce00000000000101ff827b012200008132000001818075b0ee000000000000000002bdd080018c008d00f423ba00000000000181f18098000000000000daf0041e000000000001820e00013903836a000000000000000082e20000000102570146000000000466a1aa000000000000000000000001017c0000000000000000828c508b32733d15138600000000000000000000039a000000018468853f8056000002e600000000b9e4000000018465011a000182805caa8b798158000081f800010072000000000000004800011236030184de000000000000000000000001104e0000000003aa00010017b9b10504000000000000000000000001023c000000000000b0c40000000000000001a4eb046e83a68176841a00f9202d4a5dc0eea4a2805a000104cac1420000000000008118000000000000029c000081100000000000000068000180fa238c05240000000101a0000000000000000000000000000000000001826200018088000002338366000000000000000000002495810c0000014e00000000000000000000803f83c000000001108e00000000000112b8185b84d3816f032304218082000002ad81a6000101b60000000000000000000184f4000002ae000100260000210600000001da4602460000000000000000239e81300000843c000000000380000015140000000000000000805c000001ae0000b)))
def sgD12 (j : Nat) : Nat := 0x5ffec1a00577e5b4ae00b0f300e7f9300141fce00014bffd6c4053bede60063f5c4028ffe6c4059fef30840547ffd0800155ffb2280153bdc402aff268300567fc132802b0fb8b910163fde9f98030bfd380143b7e00effb62025ffe6004bb0012b6a0216f3c0249c021ee6010bd300539fc002d9fc402af1d380149912cc1714149a910e2e2d000b85021510b0a30d01c28f04478c2241e1a1a3e062422287e2934463e36160f65c3ee5a8659845c963d493d4a114416f1372c82cea2254859d86b17e5191e3b0b81f8460046468c0d3986726ce458cc31936322c6058a9b131632646488c1918222a444c85ca47918f309e4d3c8a5985a609e4c3c905930b2434801ca5fffff7efbff7bd3048110
def sgH12 (j : Nat) : Nat := (if j<1 then 0xa1493e00040ce000415ab59e14c004c0af073800000076ac06fe12200041ba00061ae253c59c0000c9f826a9bd05ba4ac000000000000003d1a8d0000401d829e8f20006186bc400008424900000000087409bb019803ac43c120858000184ecef1816a12a818800000001548304c9c000025c17408f432880018858000000013c85c806a82c017904bc11aa01810e857e01407085250a545a000060ff933e6ae00060c4000000002080014288000000000000000d081d80000000000027e1a224b800000000018380000000288200000000000000ca0e1cc037e45918400260000001b428000000606f801000084140d400000018622146000204e064000085a00000002f6600020c301341c000049025598000000000080d000000061b60000000159b1aa4422184bf0407d120807181700000004e815a80955825292380da4a103cd5a1248007282fe0ac000617a808650601d2c4e00000008560c94804000000000000000001041ed08814884600046a6101cda8000408e00020878179794958e11e0100000000601a000000b02926a200001348150ec7066c80f031a16603f000083d058d000c94c0002c98005e89085480004e260da00066ee00000012a1c03c0006f1382f0001325e58584fa116000000000060b812d000002456c00000001864ed7b12f80d60004d7d0a0000000048f0b26800184708f6803a056000000000061d200000018520000000000000021020000000218e48a0006fcc000000182a778f86a215684064aa000000000000005ae0001d10a94801141620004198d3b00018128000b94d796bed800006c808aa970099d74000000065640006276065c8425e449618118001257881e892a02a06521c5053c0f8a964b2480200ee025e0b5050618dd2e017e0204031814649d81a0000c2ce19d05b414585da57a01e42125b0b5bc925402585c40aa5a7a01e0216f14869c11082202fba510000000000083af59406281c73f4741484b608c8388000034c0e80120a6100b886f94680b30377615000412900a4840000405883c34c10728d0498f8001563e0f7923448580880c9125c4b624a433c8365484b43e00c181615000000008a88000843693106d0133104c093075080d863a261a24e9cb85d617dbec74b4810a1b891d0c8084501120007523042f2ae04de1642d08038000603e80c8f06a84e0ba01ff4f08da615c04921a413b800108fd4b286c484f03924ed00b20e7302006003341c801b64f1be800000d08001001b2115e12daa374027404e013104661bda1780005a500000880d240428b02c5780101d6810205087003898814054952abc00e6c0880424003803a08907007c18102188949a080030a08085060288200080268a04a440000e010200307081c40d160c007062038a06297081260e9012142800610891 else 0x23f8126a6a00648276e82067c018392c56800021805df0001052c1aa0004ec801e800000061ac0284183b09669400040a324c96978686efc23bafb5daca0ed83e8b3d31de1420328d0c0006e761288000000290c85ac7060000eec0000582000448602dcc4b5a880000000000b)
def sgD13 (j : Nat) : Nat := 0x1d0025900410012602841e0e1c5891e342822254804c120443ff
def sgH13 (j : Nat) : Nat := 0x13ae07e26ca224c0000042410606e07dcc000000001c68540000090200000000c2e001030000000000000000130d6300090c000000000000000000000088c000000083f40000000000127e00caa0700000089a002370009ba000000000000000000000100e08c3c0848f4000000000020800000000000000c19ad500c0b000000000000011480009a00107400000000003448000000000000000185000000000000000000005bc000008348ac2280000084c002050008640b00800125c0061bc05038a780041200205000000c0c000000000000000000000397000d961100c44362122d0052001005
def sgD14 (j : Nat) : Nat := 0x49038c288184081ff
def sgH14 (j : Nat) : Nat := 0xc1009de4c0000284000045004a5c00c9005500000000000000000000000000000000000000000000008d0000000000d40000008c00000000009200
def sgLevels : Nat → Packing
  | 6 => (1,8,6,65537,0,0,1024,sgD6)
  | 7 => (2,7,6,131074,17,4,1024,sgD7)
  | 8 => (25,6,6,1179667,85,8,1025,sgD8)
  | 9 => (298,5,6,7602355,120,12,1116,sgD9)
  | 10 => (676,4,6,5636241,120,15,1241,sgD10)
  | 11 => (235,3,6,1769495,85,14,1142,sgD11)
  | 12 => (30,2,6,327683,50,10,1067,sgD12)
  | 13 => (3,1,6,65537,0,6,1037,sgD13)
  | 14 => (1,0,6,65537,0,0,1033,sgD14)
  | _ => emptyPacking
def sgIndex : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupShort 1 2 0 2 0 0 sgH7
  | 8 => lookupShort 1 11 0 4 1 1 sgH8
  | 9 => lookupShort 10 59 6 11 5 4 sgH9
  | 10 => lookupShort 112 557 8 15 9 4 sgH10
  | 11 => lookupShort 273 2731 5 16 10 4 sgH11
  | 12 => lookupShort 109 593 7 14 8 4 sgH12
  | 13 => lookupShort 16 163 4 11 5 4 sgH13
  | 14 => lookupShort 3 59 0 8 2 4 sgH14
  | _ => fun _ => none
def sg : Forest := ⟨511,14,fun i => sgY[i]?.getD (0,0),sgC,sgA,sgLevels,sgIndex⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem monoGeometry : graphValid mo (boundsBefore pri) = true := by
  simp only [graphValid, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem signedGeometry : graphValid sg (boundsBefore known383) = true := by
  simp only [graphValid, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,listPieces_all (d:=6) ?_⟩,listPieces_all (d:=3) ?_⟩
  all_goals simp only [listPieces]
  all_goals repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows7_0 : block mo 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand7 : block mo 7 0 1=true := moRows7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows8_0 : block mo 8 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows8_2 : block mo 8 2 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand8 : block mo 8 0 5=true := (@block_merge mo 8 0 2 3 moRows8_0 moRows8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows9_0 : block mo 9 0 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows9_11 : block mo 9 11 21=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand9 : block mo 9 0 32=true := (@block_merge mo 9 0 11 21 moRows9_0 moRows9_11)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows10_0 : block mo 10 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows10_5 : block mo 10 5 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows10_101 : block mo 10 101 67=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows10_168 : block mo 10 168 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows10_264 : block mo 10 264 76=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand10 : block mo 10 0 340=true := (@block_merge mo 10 0 101 239 (@block_merge mo 10 0 5 96 moRows10_0 moRows10_5) (@block_merge mo 10 101 67 172 moRows10_101 (@block_merge mo 10 168 96 76 moRows10_168 moRows10_264)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_0 : block mo 11 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_7 : block mo 11 7 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_103 : block mo 11 103 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_112 : block mo 11 112 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_208 : block mo 11 208 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_304 : block mo 11 304 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_400 : block mo 11 400 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_496 : block mo 11 496 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_592 : block mo 11 592 19=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_611 : block mo 11 611 96=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_707 : block mo 11 707 96=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_803 : block mo 11 803 96=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows11_899 : block mo 11 899 8=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand11 : block mo 11 0 907=true := (@block_merge mo 11 0 400 507 (@block_merge mo 11 0 112 288 (@block_merge mo 11 0 7 105 moRows11_0 (@block_merge mo 11 7 96 9 moRows11_7 moRows11_103)) (@block_merge mo 11 112 96 192 moRows11_112 (@block_merge mo 11 208 96 96 moRows11_208 moRows11_304))) (@block_merge mo 11 400 211 296 (@block_merge mo 11 400 96 115 moRows11_400 (@block_merge mo 11 496 96 19 moRows11_496 moRows11_592)) (@block_merge mo 11 611 192 104 (@block_merge mo 11 611 96 96 moRows11_611 moRows11_707) (@block_merge mo 11 803 96 8 moRows11_803 moRows11_899))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows12_0 : block mo 12 0 62=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows12_62 : block mo 12 62 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows12_158 : block mo 12 158 75=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows12_233 : block mo 12 233 96=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows12_329 : block mo 12 329 57=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand12 : block mo 12 0 386=true := (@block_merge mo 12 0 158 228 (@block_merge mo 12 0 62 96 moRows12_0 moRows12_62) (@block_merge mo 12 158 75 153 moRows12_158 (@block_merge mo 12 233 96 57 moRows12_233 moRows12_329)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows13_0 : block mo 13 0 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows13_5 : block mo 13 5 18=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows13_23 : block mo 13 23 43=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand13 : block mo 13 0 66=true := (@block_merge mo 13 0 5 61 moRows13_0 (@block_merge mo 13 5 18 43 moRows13_5 moRows13_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows14_0 : block mo 14 0 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand14 : block mo 14 0 9=true := moRows14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem moRows15_0 : block mo 15 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem moBand15 : block mo 15 0 1=true := moRows15_0
set_option maxHeartbeats 0 in
theorem moTables : checkedTables mo 15 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo 0 0 0 = true)
  · exact (rfl : block mo 1 0 0 = true)
  · exact (rfl : block mo 2 0 0 = true)
  · exact (rfl : block mo 3 0 0 = true)
  · exact (rfl : block mo 4 0 0 = true)
  · exact (rfl : block mo 5 0 0 = true)
  · exact (rfl : block mo 6 0 0 = true)
  · exact moBand7
  · exact moBand8
  · exact moBand9
  · exact moBand10
  · exact moBand11
  · exact moBand12
  · exact moBand13
  · exact moBand14
  · exact moBand15
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows6_0 : block sg 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand6 : block sg 6 0 1=true := sgRows6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows7_0 : block sg 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand7 : block sg 7 0 2=true := sgRows7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows8_0 : block sg 8 0 25=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand8 : block sg 8 0 25=true := sgRows8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows9_0 : block sg 9 0 21=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows9_21 : block sg 9 21 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows9_117 : block sg 9 117 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows9_213 : block sg 9 213 85=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand9 : block sg 9 0 298=true := (@block_merge sg 9 0 117 181 (@block_merge sg 9 0 21 96 sgRows9_0 sgRows9_21) (@block_merge sg 9 117 96 85 sgRows9_117 sgRows9_213))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_0 : block sg 10 0 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_3 : block sg 10 3 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_99 : block sg 10 99 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_195 : block sg 10 195 47=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_242 : block sg 10 242 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_338 : block sg 10 338 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_434 : block sg 10 434 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_530 : block sg 10 530 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows10_626 : block sg 10 626 50=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand10 : block sg 10 0 676=true := (@block_merge sg 10 0 242 434 (@block_merge sg 10 0 99 143 (@block_merge sg 10 0 3 96 sgRows10_0 sgRows10_3) (@block_merge sg 10 99 96 47 sgRows10_99 sgRows10_195)) (@block_merge sg 10 242 192 242 (@block_merge sg 10 242 96 96 sgRows10_242 sgRows10_338) (@block_merge sg 10 434 96 146 sgRows10_434 (@block_merge sg 10 530 96 50 sgRows10_530 sgRows10_626))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows11_0 : block sg 11 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows11_2 : block sg 11 2 63=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows11_65 : block sg 11 65 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows11_161 : block sg 11 161 27=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows11_188 : block sg 11 188 47=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand11 : block sg 11 0 235=true := (@block_merge sg 11 0 65 170 (@block_merge sg 11 0 2 63 sgRows11_0 sgRows11_2) (@block_merge sg 11 65 96 74 sgRows11_65 (@block_merge sg 11 161 27 47 sgRows11_161 sgRows11_188)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows12_0 : block sg 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows12_1 : block sg 12 1 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows12_13 : block sg 12 13 17=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand12 : block sg 12 0 30=true := (@block_merge sg 12 0 1 29 sgRows12_0 (@block_merge sg 12 1 12 17 sgRows12_1 sgRows12_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows13_0 : block sg 13 0 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand13 : block sg 13 0 3=true := sgRows13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem sgRows14_0 : block sg 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem sgBand14 : block sg 14 0 1=true := sgRows14_0
set_option maxHeartbeats 0 in
theorem sgTables : checkedTables sg 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block sg 0 0 0 = true)
  · exact (rfl : block sg 1 0 0 = true)
  · exact (rfl : block sg 2 0 0 = true)
  · exact (rfl : block sg 3 0 0 = true)
  · exact (rfl : block sg 4 0 0 = true)
  · exact (rfl : block sg 5 0 0 = true)
  · exact sgBand6
  · exact sgBand7
  · exact sgBand8
  · exact sgBand9
  · exact sgBand10
  · exact sgBand11
  · exact sgBand12
  · exact sgBand13
  · exact sgBand14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem monoRoot : Impossible false graph 15 inputs.toFinset := by
  rw [show graph = targetOf mo by decide +kernel]
  exact root_index (g:=mo) (top:=15) (i:=0) (before_sound pri vpri) monoGeometry moTables (by decide) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem signedRoot : Impossible true graph 14 inputs.toFinset := by
  rw [show graph = targetOf sg by decide +kernel]
  exact root_index (g:=sg) (top:=14) (i:=0) (before_sound known383 valid383) signedGeometry sgTables (by decide) (by decide +kernel)
end PEqualNP.Outside.L_meta_670

theorem PEqualNP.Outside.L_meta_670 : ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) 15 :=
  PEqualNP.Outside.L_meta_670.directSplit PEqualNP.Outside.L_meta_670.monoRoot PEqualNP.Outside.L_meta_670.signedRoot
