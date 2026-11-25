import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_10494.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_10494
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
def graph : Sig := 0xfffffffffffffffffffffffffffffffffffffffffffffffffefefefefafafafafffefffefffefffeffeeffeeffeeffeefefefcfcfafaf0f0eeeeccccaaaa0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8) || (x 7 && x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 0 &&& x 8) ||| (x 2 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 5) ||| (x 2 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 0 &&& x 8) ||| (x 2 &&& x 8) ||| (x 6 &&& x 8) ||| (x 7 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 152) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 152) :
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

structure KWRooms (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (T : Sig) : KWRooms {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,hp,hn⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T := by
  let z := bin d a b
  let sel := fun p n : Row => if d=0 then (if bit n a then b else a)
    else (if bit p a then a else b)
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (hp : bit p z=true) (hn : bit n z=false) :
      bit p (sel p n) = true ∧ bit n (sel p n) = false := by
    have b0 (r : Row) : bit r (bin 0 a b) = (bit r a && bit r b) := by simp [bin,bit]
    have b1 (r : Row) : bit r (bin 1 a b) = (bit r a || bit r b) := by simp [bin,bit]
    rcases d01 with e | e <;> cases pA : bit p a <;> cases nA : bit n a <;>
      simp_all [sel,z]
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    obtain ⟨v,hv⟩ := H.total p n hp hn
    rcases Finset.mem_insert.mp (H.valid hv).1 with eq | mem
    · have vz : v=z := eq
      refine ⟨sel p n,Or.inr ⟨rfl,?_⟩⟩
      rw [←vz]
      exact hv
    · exact ⟨v,Or.inl ⟨mem,hv⟩⟩
  · intro v p n h
    rcases h with ⟨mem,hv⟩ | ⟨e,hv⟩
    · exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem mem),(H.valid hv).2⟩
    · subst v
      have inS : sel p n ∈ insert a (insert b U) := by
        rcases pick p n with eq | eq <;> simp [eq]
      exact ⟨inS,separates p n (H.valid hv).2.1 (H.valid hv).2.2⟩
  · intro v w p n h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact H.unique hv hw
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hv hw]
      exact vU
    · apply False.elim
      apply hz
      change z∈U
      rw [←H.unique hw hv]
      exact wU
    · exact ve.trans we.symm
  · intro v p n p' n' h1 h2
    rcases h1 with ⟨vU,hv⟩ | ⟨ve,hv⟩ <;> rcases h2 with ⟨wU,hw⟩ | ⟨we,hw⟩
    · exact Or.inl ⟨vU,H.rect hv hw⟩
    · exact False.elim (outside p' n (we ▸ vU))
    · exact False.elim (outside p n' (ve ▸ wU))
    · refine Or.inr ⟨?_,H.rect hv hw⟩
      by_cases h : d=0
      · simpa only [sel,h,ite_true] using we
      · simpa only [sel,h,ite_false] using ve

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {T k S} (run : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf T⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,hab,hfresh,tail⟩ := run
    have fresh : bin d a b∉U := fun h => hfresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have li := kwWidth tail
    rw [Finset.card_insert_of_notMem fresh] at li
    have le1 := Finset.card_insert_le (a:=a) (insert b U)
    have le2 := Finset.card_insert_le (a:=b) U
    have ha : a∉U := by
      intro h
      rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem h : a∈insert b U)] at tight
      omega
    have hb : b∉U := by
      intro h
      rw [Finset.insert_eq_of_mem h] at tight le1
      omega
    have eq : (insert (bin d a b) U).card=k+1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    obtain ⟨H⟩ := ih tail eq
    have d01 : d=0 ∨ d=1 := by rcases hd with h | ⟨h,_⟩ <;> simp_all <;> omega
    exact ⟨kwFork d01 ha hb fresh H⟩

def onlyWire (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, bit p w=true → bit n w=false → w=v

theorem kwOwn {S T v p n} (H : KWRooms S T) (one : onlyWire S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2.1 (H.valid hw).2.2
  exact eq ▸ hw

theorem kwCross {S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : Impossible false T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwWireB (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !bit p w || bit n w || w==v)
theorem kwWireB_sound {ws T v p n} (h : kwWireB ws T v p n=true) :
    onlyWire ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hp hn
  simpa only [hp,hn,Bool.not_true,Bool.false_or,beq_iff_eq] using
    h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB ws T a p (kwProbe neg (field 4)) && kwWireB ws T b p (kwProbe neg (field 5)) &&
    kwWireB ws T a (kwProbe pos (field 6)) n && kwWireB ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {pos neg T ws k v} (h : kwWord pos neg T ws k v=true) : Impossible false T k ws.toFinset := by
  simp only [kwWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact kwCross h.1.1.1.1.1 h.1.1.1.1.2 (kwWireB_sound h.1.1.1.2)
    (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2)

def CutRow (g : Forest) (k start n : Nat) : Prop :=
  ∀ j, start≤j → j<start+n → nodeVerified g k j=true ∨ Impossible g.mode (targetOf g) k (stateSet g k j).toFinset
theorem mixedEmpty (g : Forest) (k a : Nat) : CutRow g k a 0 := by
  intro j lo hi
  omega
theorem checkedRow {g k a n} (h : block g k a n=true) : CutRow g k a n :=
  fun j lo hi => Or.inl (block_at h j lo hi)
theorem joinRow {g k a x y} (first : CutRow g k a x) (last : CutRow g k (a+x) y) :
    CutRow g k a (x+y) := by
  intro j lo hi
  by_cases e : j<a+x
  · exact first j lo e
  · exact last j (by omega) (by omega)
def kwTest (pos neg : Nat) (g : Forest) (k a n : Nat) (data : Nat → Nat) :=
  (List.range n).all (fun j => kwWord pos neg (targetOf g) (stateSet g k (a+j)) k (packedAt data (32*j) 32))
theorem mixedCut {pos neg g k a n data} (mode : g.mode=false) (h : kwTest pos neg g k a n data=true) :
    CutRow g k a n := by
  intro j lo hi
  right
  rw [mode]
  have hh := List.all_eq_true.mp h (j-a) (List.mem_range.mpr (by omega))
  have sum : a+(j-a)=j := by omega
  change kwWord pos neg _ (stateSet g k (a+(j-a))) k _=true at hh
  rw [sum] at hh
  exact kwWord_sound hh

def mixedTables (g : Forest) (top : Nat) := ∀ k ≤ top, CutRow g k 0 (g.levels k).1
theorem mixedForest (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior=true) (rows : mixedTables g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) checked
    · exact done
  | succ k ih =>
    intro hk i hi
    rcases rows _ hk i (by omega) (by omega) with checked | done
    · exact nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
        (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
        (fun _ => by simpa using ih (by omega)) checked
    · exact done
theorem mixedRoot {g top prior k i ws} (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior=true) (blocks : mixedTables g top) (le : k≤top)
    (idx : indexedRoot g k i ws=true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact mixedForest g top prior lower geom blocks _ le i idx.1
def neighbor10495 (i : Fin 9) : Nat := [4, 5, 6, 7, 0, 1, 2, 0, 0].getD i.val 0
def absentRow10495 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor10495 i)
def presentRow10495 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor10495 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow10495 i) graph ≠ bit (presentRow10495 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow10495 i) (inputs.getD j.val zero) =
      bit (presentRow10495 i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 13) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 12 else 13) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 13 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 12 else 13) := by
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
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow10495 i) (presentRow10495 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 13 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 12 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 13 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def g324Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x92409240924092409240924092409240924092),(0x0,0x0),(0xf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124)]
def g324C : List ColumnInfo := []
def g324A : List (List Nat) := [[],[134],[98],[98,130],[130,98],[130]]
def g324D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g324L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g324D3)
  | _ => emptyPacking
def g324I (_ _ : Nat) : Option (Nat × Nat) := none
def g324 : Forest := ⟨324,3,fun i => g324Y[i]?.getD (0,0),g324C,g324A,g324L,g324I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g324P3_0 : block g324 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g324B3 : block g324 3 0 1=true := g324P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g324T : checkedTables g324 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g324 0 0 0 = true)
  · exact (rfl : block g324 1 0 0 = true)
  · exact (rfl : block g324 2 0 0 = true)
  · exact g324B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g324G : graphValid g324 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low324 : Lower true (varsX 324) (graphGoal 324) 4 := lower_forest (g:=g324) (i:=0) (hints:=8623490560) (before_sound [] baseKnown) g324G g324T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K324 := extendKnown [] 4 [(324,[]),(385,[16,32,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V324 : Known true K324 := extend_ok (m:=324) baseKnown low324 (by decide +kernel)
def g147Y : Array (Bits × Bits) := #[(0xe6de3fff03fff1ffe6de3fff03fff1ffe6de3f,0x648490a285024020648490a28502402064849),(0x19e9c0fffc07fe3f19e9c0fffc07fe3f19e9c0,0x50e8db2c3161408450e8db2c3161408450e8db),(0x0,0x0),(0x0,0x0),(0xece607fffff8003fece607fffff8003fece607,0x8a7b6b04185892808a7b6b04185892808a7b6),(0x0,0x0),(0x0,0x0),(0x1b3df8ffffffffc01b3df8ffffffffc01b3df8,0x891524c082060030891524c082060030891524),(0x0,0x0)]
def g147C : List ColumnInfo := []
def g147A : List (List Nat) := [[],[112,65]]
def g147D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g147L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g147D3)
  | _ => emptyPacking
def g147I (_ _ : Nat) : Option (Nat × Nat) := none
def g147 : Forest := ⟨147,3,fun i => g147Y[i]?.getD (0,0),g147C,g147A,g147L,g147I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147P3_0 : block g147 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g147B3 : block g147 3 0 1=true := g147P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147T : checkedTables g147 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g147 0 0 0 = true)
  · exact (rfl : block g147 1 0 0 = true)
  · exact (rfl : block g147 2 0 0 = true)
  · exact g147B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147G : graphValid g147 (boundsBefore K324) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 4 := lower_forest (g:=g147) (i:=0) (hints:=116) (before_sound K324 V324) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K324 4 [(147,[]),(153,[49,33]),(163,[16,84]),(170,[16,48,32,84]),(277,[33,135]),(337,[128,65,33,50,99,83,112]),(390,[128,32,66,84,101]),(450,[128,32,50,100,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V147 : Known true K147 := extend_ok (m:=147) V324 low147 (by decide +kernel)
def g325Y : Array (Bits × Bits) := #[(0xe6e00e3f80fc7e3fcdc01c7f01f8fc7f9b8038,0x56e1b6d52a292480adc36daa545249015b86db),(0x0,0x0),(0xfdb871ffff007fc7fb70e3fffe00ff8ff6e1c7,0x858892460c3208110b11248c18641022162249),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xfbb781ffffff8007f76f03ffffff000feede07,0x235249830403122046a49306080624408d492),(0x0,0x0),(0x64ffe3ffffffff80c9ffc7ffffffff0193ff8,0x24920408040040004924081008008000924)]
def g325C : List ColumnInfo := [(1,0,324,0,4)]
def g325A : List (List Nat) := [[],[98]]
def g325D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g325L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g325D4)
  | _ => emptyPacking
def g325I (_ _ : Nat) : Option (Nat × Nat) := none
def g325 : Forest := ⟨325,4,fun i => g325Y[i]?.getD (0,0),g325C,g325A,g325L,g325I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g325P4_0 : block g325 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g325B4 : block g325 4 0 1=true := g325P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g325T : checkedTables g325 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g325 0 0 0 = true)
  · exact (rfl : block g325 1 0 0 = true)
  · exact (rfl : block g325 2 0 0 = true)
  · exact (rfl : block g325 3 0 0 = true)
  · exact g325B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g325G : graphValid g325 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low325 : Lower true (varsX 325) (graphGoal 325) 5 := lower_forest (g:=g325) (i:=0) (hints:=33555976) (before_sound K147 V147) g325G g325T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K325 := extendKnown K147 5 [(325,[]),(389,[32,118]),(449,[96,32,50,67,84,117]),(452,[112,16,49,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V325 : Known true K325 := extend_ok (m:=325) V147 low325 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[(0xf8003ffe00fff803fffffffffffffb5d61e03f,0x501a80941a029058280540940a414940616249),(0xffffc00000fffffc01ffe001ffe008a3d3c1c0,0x61530ad8ac2b22914c2986d84c8668a351c6db),(0x0,0x0),(0xffffffffff00000001fffffe000004e42dde00,0x819c0ce13033c4e2704e04e06f0b84e429c6db),(0x1fffffffffff22feda007,0x5e02f01c0bc070381701701700c022f8c8db6),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffe00000000000dfa9e5ff8,0x600300000c000000180180180100018861924),(0x0,0x0)]
def g155C : List ColumnInfo := [(2,0,153,0,4)]
def g155A : List (List Nat) := [[],[49]]
def g155D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g155L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g155D4)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,4,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P4_0 : block g155 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B4 : block g155 4 0 1=true := g155P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact g155B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K325) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 5 := lower_forest (g:=g155) (i:=0) (hints:=28788) (before_sound K325 V325) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K325 5 [(155,[]),(171,[16,84]),(426,[16,48,32,130,84,66,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V325 low155 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[(0x3fffffc07ffff800fffffc07fffff27a560f0f,0x822810810004504a014008102201300a525555),(0xc003ffff80ffffff001fffffff001dadf9f0f0,0xb005000201600c058050000404102c993333),(0x0,0x0),(0x0,0x0),(0xfffc000000ffffffffe00007fffe67e88e000f,0x24c2a61a34a98510a6156165485047e08caaaa),(0xfffffffffffff800002697f400f0,0x3703382c58ce0660c81982467098269364cccc),(0x0,0x0),(0xffffffffff0000000000000000019d530dff00,0x3803c03060f00780f01e038780e08d51048888),(0x0,0x0)]
def g179C : List ColumnInfo := []
def g179A : List (List Nat) := [[],[16,84]]
def g179D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g179L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g179D4)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,4,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P4_0 : block g179 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B4 : block g179 4 0 1=true := g179P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact g179B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 5 := lower_forest (g:=g179) (i:=0) (hints:=1048660) (before_sound K155 V155) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K155 5 [(179,[]),(422,[128,32,66,100]),(482,[16,128,32,50,84,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V155 low179 (by decide +kernel)
def g341Y : Array (Bits × Bits) := #[(0xffc01ffffe1fffc01ffff87fffe4d2a4007c1f,0x228944508440228940a01108826012a45294a5),(0x0,0x0),(0xffffe007ffe1ffffe00fffffc03359f20f83e0,0xb01816028040b0182c0a00108205932318c63),(0x0,0x0),(0xfffffff80001fffffff0007ffccfd11c00001f,0x4c12098530894c22130ac252008fc119ad6b5a),(0x0,0x0),(0x1ffffffffff80004d2fe9f003e0,0x701c0e01c110700c0403001c104506c8c6318c),(0x0,0x0),(0xfffffffffffe000000000000033aa61bfffc00,0x8020100600018030180c0460211aa001084210)]
def g341C : List ColumnInfo := [(0,16,324,1,5),(16,0,325,0,5),(1,16,324,0,4),(4,0,337,0,4),(64,0,277,0,4)]
def g341A : List (List Nat) := [[],[98]]
def g341D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d41
def g341D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20120260d140ff41fd41fd31
def g341H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x70
def g341D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18d09f
def g341H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6ada614ae
def g341L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g341D4)
  | 5 => (3,1,3,0,0,5,0,g341D5)
  | 6 => (1,0,3,0,0,0,0,g341D6)
  | _ => emptyPacking
def g341I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g341H5
  | 6 => lookupWord 1 5 0 7 2 1 g341H6
  | _ => fun _ => none
def g341 : Forest := ⟨341,6,fun i => g341Y[i]?.getD (0,0),g341C,g341A,g341L,g341I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P4_0 : block g341 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B4 : block g341 4 0 1=true := g341P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P5_0 : block g341 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B5 : block g341 5 0 3=true := g341P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341P6_0 : block g341 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g341B6 : block g341 6 0 1=true := g341P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341T : checkedTables g341 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g341 0 0 0 = true)
  · exact (rfl : block g341 1 0 0 = true)
  · exact (rfl : block g341 2 0 0 = true)
  · exact (rfl : block g341 3 0 0 = true)
  · exact g341B4
  · exact g341B5
  · exact g341B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g341G : graphValid g341 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low341 : Lower true (varsX 341) (graphGoal 341) 7 := lower_forest (g:=g341) (i:=0) (hints:=33555972) (before_sound K179 V179) g341G g341T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K341 := extendKnown K179 7 [(341,[]),(419,[16,32,84,134,118]),(454,[112,16,65,84]),(460,[112,16,49,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V341 : Known true K341 := extend_ok (m:=341) V179 low341 (by decide +kernel)
def g358Y : Array (Bits × Bits) := #[(0x0,0x0),(0xff003ffffc3ffc00fffff0fffc7a695700003f,0x8a9288a10892294a4290224880380957555555),(0xffffc00fffffffff003fffffc289acf903ffc0,0x2c0302c05000b00c0b0140010a002c990c30c3),(0x0,0x0),(0x0,0x0),(0xfffffff0003fffffffc000fffd77e88a00003f,0x3024130a6124c2108c2584920147e088aaaaaa),(0x3fffffffffff00012697f4fc0fc0,0xc0381c03820700601006001c1122836030c30c),(0x0,0x0),(0xffffffffffc0000000000000039d530dfff000,0xc0200c00380380e03808e0209d5004c30c30)]
def g358C : List ColumnInfo := [(0,2,324,32,5)]
def g358A : List (List Nat) := [[],[134],[98],[98,130],[130,98],[130],[81],[81,134],[81,98],[81,98,130],[81,130,98],[81,130]]
def g358D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g358L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g358D5)
  | _ => emptyPacking
def g358I (_ _ : Nat) : Option (Nat × Nat) := none
def g358 : Forest := ⟨358,5,fun i => g358Y[i]?.getD (0,0),g358C,g358A,g358L,g358I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358P5_0 : block g358 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g358B5 : block g358 5 0 1=true := g358P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358T : checkedTables g358 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g358 0 0 0 = true)
  · exact (rfl : block g358 1 0 0 = true)
  · exact (rfl : block g358 2 0 0 = true)
  · exact (rfl : block g358 3 0 0 = true)
  · exact (rfl : block g358 4 0 0 = true)
  · exact g358B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g358G : graphValid g358 (boundsBefore K341) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low358 : Lower true (varsX 358) (graphGoal 358) 6 := lower_forest (g:=g358) (i:=0) (hints:=8624539216) (before_sound K341 V341) g358G g358T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K358 := extendKnown K341 6 [(358,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V358 : Known true K358 := extend_ok (m:=358) V341 low358 (by decide +kernel)
def g391Y : Array (Bits × Bits) := #[(0x7ff003ff80fffffff003ffffe03ff4b19901c7,0x2a1a8251a148a02a1a84a0a458a44b1811249),(0x7ffffc0000ffc07ffffc00ffffc068db260038,0x44c132362c191344c9326c8c891360d3265b6d),(0x7fffffffff00007fffffff0000000ff00e8e00,0x1705c0b8305e1c1701c0702f0e1c0db00eb6db),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x800000000000007fffffffffffff99af6d703f,0x180600c040602018020080300000190c082492),(0xffffffffffffff800000000000006754f2ffc0,0x60080300008000600c0300c010202240704924)]
def g391C : List ColumnInfo := [(2,0,389,0,5)]
def g391A : List (List Nat) := [[],[33,135]]
def g391D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g391L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g391D5)
  | _ => emptyPacking
def g391I (_ _ : Nat) : Option (Nat × Nat) := none
def g391 : Forest := ⟨391,5,fun i => g391Y[i]?.getD (0,0),g391C,g391A,g391L,g391I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g391P5_0 : block g391 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g391B5 : block g391 5 0 1=true := g391P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g391T : checkedTables g391 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g391 0 0 0 = true)
  · exact (rfl : block g391 1 0 0 = true)
  · exact (rfl : block g391 2 0 0 = true)
  · exact (rfl : block g391 3 0 0 = true)
  · exact (rfl : block g391 4 0 0 = true)
  · exact g391B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g391G : graphValid g391 (boundsBefore K358) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low391 : Lower true (varsX 391) (graphGoal 391) 6 := lower_forest (g:=g391) (i:=0) (hints:=2167) (before_sound K358 V358) g391G g391T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K391 := extendKnown K358 6 [(391,[]),(403,[128,66,50]),(405,[112,33,65,49,128]),(465,[112,65,98,49,50,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V391 : Known true K391 := extend_ok (m:=391) V358 low391 (by decide +kernel)
def g453Y : Array (Bits × Bits) := #[(0xffc00ff87fc3fff00ffffffe257e300007fe0,0x20a82a051048802a2a0a12004a546306318c63),(0x0,0x0),(0xfffff0007ffc3ffff00ff1ffd9276c00f801f,0x42308c262110088c0c4c0444811226ca5294a5),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffff80003ffffff001ffce8f541f0001f,0x84c13048026111303010588900e8d114a5294a),(0xf0000000000003ffffffffe0005f98fe0003e0,0x701c070438221c04060600e100b98d8c6318c),(0xfffffffffffffc000000000003280bbffffc00,0x8020080040002008080801000000021084210)]
def g453C : List ColumnInfo := [(1,0,452,0,5),(4,0,449,0,5),(64,0,389,0,5),(128,0,325,0,5),(68,0,385,0,4),(129,0,324,0,4)]
def g453A : List (List Nat) := [[],[98],[32,118],[32,112,96],[96,32,114],[96,114],[112],[112,98]]
def g453D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x31826f62547409bd89544426d6215110
def g453D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8118204c10001882188201161080d176bcc8d018160c02faa3a077d4d40bfa8a81fb40502fea8885f95110beaa2217c54443f2808857d4d40
def g453H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6000000000000000000000000000000000000000000000000000527100000000000000d90000000008
def g453D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2150c8543540a0380ff40fd40fd10
def g453H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x24500000c855341f81003889180000389c67c280083000170008400000c5000001d100000c08
def g453D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1605f
def g453H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18800006a0000133000080000000053064000000000000000000fa000d000e4e4a880000000000000000000000
def g453L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g453D4)
  | 5 => (10,2,3,0,0,7,0,g453D5)
  | 6 => (3,1,3,0,0,6,0,g453D6)
  | 7 => (1,0,3,0,0,0,0,g453D7)
  | _ => emptyPacking
def g453I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 43 0 8 2 2 g453H5
  | 6 => lookupWord 4 29 3 10 4 2 g453H6
  | 7 => lookupWord 3 47 0 9 2 3 g453H7
  | _ => fun _ => none
def g453 : Forest := ⟨453,7,fun i => g453Y[i]?.getD (0,0),g453C,g453A,g453L,g453I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g453P4_0 : block g453 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g453B4 : block g453 4 0 3=true := g453P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g453P5_0 : block g453 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g453P5_1 : block g453 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g453B5 : block g453 5 0 10=true := (@block_merge g453 5 0 1 9 g453P5_0 g453P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g453P6_0 : block g453 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g453B6 : block g453 6 0 3=true := g453P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g453P7_0 : block g453 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g453B7 : block g453 7 0 1=true := g453P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g453T : checkedTables g453 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g453 0 0 0 = true)
  · exact (rfl : block g453 1 0 0 = true)
  · exact (rfl : block g453 2 0 0 = true)
  · exact (rfl : block g453 3 0 0 = true)
  · exact g453B4
  · exact g453B5
  · exact g453B6
  · exact g453B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g453G : graphValid g453 (boundsBefore K391) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low453 : Lower true (varsX 453) (graphGoal 453) 8 := lower_forest (g:=g453) (i:=0) (hints:=33555975) (before_sound K391 V391) g453G g453T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K453 := extendKnown K391 8 [(453,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V453 : Known true K453 := extend_ok (m:=453) V391 low453 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[(0x3ffffffffffffffffffcd8034dfabc9c007c1f,0x80a0a80a1280a14810a4d003043a28985294a5),(0xfffffc00003ffffc0001a55e33360f780f83e0,0x53000db0009900331a11e21200c58318c63),(0x0,0x0),(0x3fffffffffc00000000233e3a455ec53f00000,0x2c9c02c9c02cde025c231c3a454ac52f7bdef),(0x3ffffffffffffffffffac58e65c5f6a400001f,0x2b0e02b0e02b0e014602058c61c5d625ad6b5a),(0xc000000000000000000245795afe62520003e0,0x33f0033f0033f002780244615ade6203ce739c),(0x0,0x0),(0x73aa5b8895b2bfffc00,0x3c0003c0003c000380000a2018815321084210),(0x0,0x0)]
def g187C : List ColumnInfo := [(8,0,179,0,5),(16,0,171,0,5),(32,0,155,0,5),(1,16,170,0,4),(2,32,153,0,4)]
def g187A : List (List Nat) := [[],[16,84]]
def g187D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ef52
def g187D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x222317f
def g187H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g187L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g187D5)
  | 6 => (1,0,3,0,0,0,0,g187D6)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g187H6
  | _ => fun _ => none
def g187 : Forest := ⟨187,6,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 1=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 1=true := g187P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact g187B5
  · exact g187B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K453) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 7 := lower_forest (g:=g187) (i:=0) (hints:=1077332) (before_sound K453 V453) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K453 7 [(187,[]),(430,[128,32,66,100]),(490,[16,128,32,84,100,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V453 low187 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[(0xfffffffffffffffffff99d1e43ae9d6903f03f,0x282a00a1280285202149801c032a9c01145145),(0xffff000003fffff000076a94e958a6b3fc0000,0xb14c02cdb00b264046672a946148a4333cf3cf),(0xfffffffffc000000000067e53733d476000fc0,0x2702809c0a037820b8067241212d4764d34d3),(0x0,0x0),(0xfffffffffffffffffff58b1674957bf000003f,0xc380b30e02cc38048c040b02749563f0ebaeba),(0x0,0x0),(0x48afbb7e9c20e000fc0,0xfc00c3f0030fc008f00488dba5e90208b2cb2c),(0xe754a985f269dfff000,0xfc0003f0000f000055429815028cc30c30),(0x0,0x0)]
def g215C : List ColumnInfo := [(0,4,147,64,5)]
def g215A : List (List Nat) := [[],[98],[112,65],[112,65,98]]
def g215D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g215L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g215D5)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,5,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : block g215 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B5 : block g215 5 0 1=true := g215P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact g215B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 6 := lower_forest (g:=g215) (i:=0) (hints:=33556084) (before_sound K187 V187) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K187 6 [(215,[]),(231,[16,84]),(238,[16,48,84]),(311,[33,101,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V187 low215 (by decide +kernel)
def g359Y : Array (Bits × Bits) := #[(0x3ffff80000ffffe000b1e1c037cba24003f000,0x854950ab6a154a4256b0e14037cb824f3cf3cf),(0x3fffffffffffffffff3e9d68b211be8000003f,0x118262304c460c84243e0d6092013e15555555),(0xffffffffff00000000066a54cff58b00fc0fc0,0x13800270006f00b802624085358b030c30c3),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffffff58b1cca9bed48000003f,0x261c04c380987008c040b08c29bec0aaaaaaaa),(0xc0000000000000000048af2b5ecc4a7f000fc0,0x7e000fc001f800f00088d095ac8404c30c30c),(0x0,0x0),(0xe754b7112b657ffff000,0x3800070000e00010004510b600002430c30c30)]
def g359C : List ColumnInfo := [(0,2,325,32,6)]
def g359A : List (List Nat) := [[],[98],[81],[81,98]]
def g359D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g359L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g359D6)
  | _ => emptyPacking
def g359I (_ _ : Nat) : Option (Nat × Nat) := none
def g359 : Forest := ⟨359,6,fun i => g359Y[i]?.getD (0,0),g359C,g359A,g359L,g359I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g359P6_0 : block g359 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g359B6 : block g359 6 0 1=true := g359P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g359T : checkedTables g359 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g359 0 0 0 = true)
  · exact (rfl : block g359 1 0 0 = true)
  · exact (rfl : block g359 2 0 0 = true)
  · exact (rfl : block g359 3 0 0 = true)
  · exact (rfl : block g359 4 0 0 = true)
  · exact (rfl : block g359 5 0 0 = true)
  · exact g359B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g359G : graphValid g359 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low359 : Lower true (varsX 359) (graphGoal 359) 7 := lower_forest (g:=g359) (i:=0) (hints:=34604632) (before_sound K215 V215) g359G g359T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K359 := extendKnown K215 7 [(359,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V359 : Known true K359 := extend_ok (m:=359) V215 low359 (by decide +kernel)
def g407Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffe29798e321cb00f0ff,0x14000a8004a00148014e0948880008a111111),(0xffffc0000ffffc0007d409d2ed1b2000f00,0xa6a0532836ca09910666d409d2e5182bbbbbb),(0xfffffffff000000001cf88f852b660f0000,0x3380a9c02a700ade02b814d88c852b66777777),(0x0,0x0),(0xfffffffffffffffff216395b13d3d00000f,0x5c0cce033380cce024c0016315313d35eeeeee),(0x0,0x0),(0x0,0x0),(0xfff00000000000000000115e685ddcf0f00ff0,0x6000f0003c000f000700100a40418c70444444),(0xcea977125e06fff000,0x800f0003c000f00038000a2133125000888888)]
def g407C : List ColumnInfo := [(2,0,405,0,6),(4,0,403,0,6),(16,0,391,0,6),(0,4,147,256,5),(1,0,390,0,4),(1,16,390,0,4),(128,2,277,0,4),(256,4,147,0,4)]
def g407A : List (List Nat) := [[],[33,135],[112,33,65,128],[112,65],[128,66],[128,65,33,112]]
def g407D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4d576d0630
def g407D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x930c0b759230f5d0630bdd9510f9d4910
def g407H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4
def g407D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1908328d3081d4ab0942c07f503bc61f510
def g407H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10a000100039d8c8300206
def g407D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3ea881bf
def g407H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x348223818401065075001d1750031000748035960
def g407L : Nat → Packing
  | 4 => (1,3,3,0,0,0,0,g407D4)
  | 5 => (4,2,3,0,0,5,0,g407D5)
  | 6 => (3,1,3,0,0,6,0,g407D6)
  | 7 => (1,0,3,0,0,0,0,g407D7)
  | _ => emptyPacking
def g407I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g407H5
  | 6 => lookupWord 2 11 1 9 2 3 g407H6
  | 7 => lookupWord 3 17 3 9 2 3 g407H7
  | _ => fun _ => none
def g407 : Forest := ⟨407,7,fun i => g407Y[i]?.getD (0,0),g407C,g407A,g407L,g407I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407P4_0 : block g407 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g407B4 : block g407 4 0 1=true := g407P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407P5_0 : block g407 5 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g407B5 : block g407 5 0 4=true := g407P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407P6_0 : block g407 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407P6_2 : block g407 6 2 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g407B6 : block g407 6 0 3=true := (@block_merge g407 6 0 2 1 g407P6_0 g407P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407P7_0 : block g407 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g407B7 : block g407 7 0 1=true := g407P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407T : checkedTables g407 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g407 0 0 0 = true)
  · exact (rfl : block g407 1 0 0 = true)
  · exact (rfl : block g407 2 0 0 = true)
  · exact (rfl : block g407 3 0 0 = true)
  · exact g407B4
  · exact g407B5
  · exact g407B6
  · exact g407B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g407G : graphValid g407 (boundsBefore K359) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low407 : Lower true (varsX 407) (graphGoal 407) 8 := lower_forest (g:=g407) (i:=0) (hints:=2164) (before_sound K359 V359) g407G g407T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K407 := extendKnown K359 8 [(407,[]),(413,[33,49,135]),(467,[128,66,50,99,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V407 : Known true K407 := extend_ok (m:=407) V359 low407 (by decide +kernel)
def g423Y : Array (Bits × Bits) := #[(0xfffffff00007fffc0038f5f618c070800f83e0,0x128012a01b50094815b825f208406086318c63),(0x1fffffffffffffffdf0a222ba86fc0007c1f,0x4c804c402620190091b02222380239294a529),(0x1ffffffff8000000073433e14bd881f00000,0x6702a7015380ade0ae053433214bd88e739ce7),(0x0,0x0),(0x0,0x0),(0x1fffffffffffffffc858f56c4e4f4000001f,0xb81338099c04ce01300058d54c4e4c6d6b5ad6),(0x0,0x0),(0xffe00000000000000004578a17773c3e007fe0,0xc003c001e000f001c004500814231c08421084),(0x33aa5dc49781bfff8000,0x1c000e0007000200028a04c09401318c6318)]
def g423C : List ColumnInfo := [(4,0,419,0,7)]
def g423A : List (List Nat) := [[]]
def g423D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g423L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g423D7)
  | _ => emptyPacking
def g423I (_ _ : Nat) : Option (Nat × Nat) := none
def g423 : Forest := ⟨423,7,fun i => g423Y[i]?.getD (0,0),g423C,g423A,g423L,g423I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423P7_0 : block g423 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g423B7 : block g423 7 0 1=true := g423P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423T : checkedTables g423 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g423 0 0 0 = true)
  · exact (rfl : block g423 1 0 0 = true)
  · exact (rfl : block g423 2 0 0 = true)
  · exact (rfl : block g423 3 0 0 = true)
  · exact (rfl : block g423 4 0 0 = true)
  · exact (rfl : block g423 5 0 0 = true)
  · exact (rfl : block g423 6 0 0 = true)
  · exact g423B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g423G : graphValid g423 (boundsBefore K407) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low423 : Lower true (varsX 423) (graphGoal 423) 8 := lower_forest (g:=g423) (i:=0) (hints:=1050711) (before_sound K407 V407) g423G g423T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K423 := extendKnown K407 8 [(423,[]),(435,[128,66,50]),(483,[98,50,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V423 : Known true K423 := extend_ok (m:=423) V407 low423 (by decide +kernel)
def g427Y : Array (Bits × Bits) := #[(0xffffff80001ffff8003be9a29980e981f003e0,0x280095006d40129015ba21a20900e906318c63),(0x1ffffffffffffffffdd20676ab96640007c1f,0x4c50261409850321091d20632291221294a529),(0x0,0x0),(0x1ffffffffe0000000053e23e14bd9000f8000,0x716138584e161bc22e052e23e14bc937bdef7b),(0x0,0x0),(0x1ffffffffffffffffca58e56c4e4fc000001f,0x8185c06170185c04300258844c4e4ded6b5ad6),(0x0,0x0),(0xfe000000000000000004579a17773c3e0fffe0,0x60001800060004000501014201408421084),(0x33aa5dc49781bff00000,0x1f8007e001f800780018a4dc09700b18c6318)]
def g427C : List ColumnInfo := [(8,0,419,0,7)]
def g427A : List (List Nat) := [[],[128]]
def g427D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g427L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g427D7)
  | _ => emptyPacking
def g427I (_ _ : Nat) : Option (Nat × Nat) := none
def g427 : Forest := ⟨427,7,fun i => g427Y[i]?.getD (0,0),g427C,g427A,g427L,g427I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g427P7_0 : block g427 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g427B7 : block g427 7 0 1=true := g427P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g427T : checkedTables g427 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g427 0 0 0 = true)
  · exact (rfl : block g427 1 0 0 = true)
  · exact (rfl : block g427 2 0 0 = true)
  · exact (rfl : block g427 3 0 0 = true)
  · exact (rfl : block g427 4 0 0 = true)
  · exact (rfl : block g427 5 0 0 = true)
  · exact (rfl : block g427 6 0 0 = true)
  · exact g427B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g427G : graphValid g427 (boundsBefore K423) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low427 : Lower true (varsX 427) (graphGoal 427) 8 := lower_forest (g:=g427) (i:=0) (hints:=1077335) (before_sound K423 V423) g427G g427T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K427 := extendKnown K423 8 [(427,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V427 : Known true K427 := extend_ok (m:=427) V423 low427 (by decide +kernel)
def g455Y : Array (Bits × Bits) := #[(0x3fffffe0003fff800ced935024f10000f83e0,0x589402540da81250b44cd930024d10c6318c63),(0xfc00fffffffc0000003084f67fcc1000007c00,0x9126849909321b61581084f67b4c14e739ce73),(0xffffffffffffff794512935ac801f0001f,0xe03810e021c04380607840129252c14a5294a5),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0xffffffffffffff428bea0b89e83e00001f,0x1c027004e009c0181028ba009892a94a5294a),(0xffff0000000000000122fa117cb687c0007fe0,0x38007000e0020122220104928318c6318c),(0x9d26ecc07137ffff8000,0x200c001800300040081044c40200421084210)]
def g455C : List ColumnInfo := [(2,0,453,0,8)]
def g455A : List (List Nat) := [[],[98]]
def g455D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g455L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g455D8)
  | _ => emptyPacking
def g455I (_ _ : Nat) : Option (Nat × Nat) := none
def g455 : Forest := ⟨455,8,fun i => g455Y[i]?.getD (0,0),g455C,g455A,g455L,g455I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455P8_0 : block g455 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g455B8 : block g455 8 0 1=true := g455P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455T : checkedTables g455 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g455 0 0 0 = true)
  · exact (rfl : block g455 1 0 0 = true)
  · exact (rfl : block g455 2 0 0 = true)
  · exact (rfl : block g455 3 0 0 = true)
  · exact (rfl : block g455 4 0 0 = true)
  · exact (rfl : block g455 5 0 0 = true)
  · exact (rfl : block g455 6 0 0 = true)
  · exact (rfl : block g455 7 0 0 = true)
  · exact g455B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g455G : graphValid g455 (boundsBefore K427) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low455 : Lower true (varsX 455) (graphGoal 455) 9 := lower_forest (g:=g455) (i:=0) (hints:=33556087) (before_sound K427 V427) g455G g455T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K455 := extendKnown K427 9 [(455,[]),(469,[112,65,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V455 : Known true K455 := extend_ok (m:=455) V427 low455 (by decide +kernel)
def g462Y : Array (Bits × Bits) := #[(0x0,0x0),(0xfffffff00007fffc002b43b65aa4d1000003e0,0x929412aa1b55094915ab03b64a84d12739ce73),(0x1fffffffffffffffdfa022abe9c6400f801f,0x4c084c042602190090d8022a3a1060a5294a5),(0x1ffffffff8000000273c33e50c7800007c00,0x2718270c13860de22e233833e50c702739ce73),(0x0,0x0),(0x0,0x0),(0x1fffffffffffffffe858f5684a4fc1f0001f,0x380138009c004e0030205884484a48d4a5294a),(0xffe00000000000000024578a17773c3e007fe0,0x1c000e00070004004440810630c18c6318c),(0x13aa5dc49781bfff8000,0xc01e000f000780038012225104148121084210)]
def g462C : List ColumnInfo := [(2,0,460,0,7)]
def g462A : List (List Nat) := [[],[98],[49],[49,98]]
def g462D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g462L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g462D7)
  | _ => emptyPacking
def g462I (_ _ : Nat) : Option (Nat × Nat) := none
def g462 : Forest := ⟨462,7,fun i => g462Y[i]?.getD (0,0),g462C,g462A,g462L,g462I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g462P7_0 : block g462 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g462B7 : block g462 7 0 1=true := g462P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g462T : checkedTables g462 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g462 0 0 0 = true)
  · exact (rfl : block g462 1 0 0 = true)
  · exact (rfl : block g462 2 0 0 = true)
  · exact (rfl : block g462 3 0 0 = true)
  · exact (rfl : block g462 4 0 0 = true)
  · exact (rfl : block g462 5 0 0 = true)
  · exact (rfl : block g462 6 0 0 = true)
  · exact g462B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g462G : graphValid g462 (boundsBefore K455) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low462 : Lower true (varsX 462) (graphGoal 462) 8 := lower_forest (g:=g462) (i:=0) (hints:=8891954800) (before_sound K455 V455) g462G g462T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K462 := extendKnown K455 8 [(462,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V462 : Known true K462 := extend_ok (m:=462) V455 low462 (by decide +kernel)
def g486Y : Array (Bits × Bits) := #[(0x0,0x0),(0xffffffff003ffffff31d6ba6603cd00003f03f,0x400a40020090088002006b20203cc4d34d34d3),(0xffffffffffc00ee0088bfe370000fc0fc0,0x52c0514120141046260088be4070145145145),(0x0,0x0),(0x0,0x0),(0xffff0000003ffffffbcec0e788c2900000003f,0x963096582725920949ce80c788c21b2cb2cb2c),(0xffffffffffc000000816794c9b93603f000fc0,0x1840186044061c11881661041b90228a28a28a),(0x915a69155cf0fc003f000,0x1f801f807807e01e091580915583030c30c30c),(0x4ea977125e06ffffc0000,0xe000e000803800200488166000604c30c30c30)]
def g486C : List ColumnInfo := [(32,0,454,0,7)]
def g486A : List (List Nat) := [[],[98]]
def g486D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g486L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g486D7)
  | _ => emptyPacking
def g486I (_ _ : Nat) : Option (Nat × Nat) := none
def g486 : Forest := ⟨486,7,fun i => g486Y[i]?.getD (0,0),g486C,g486A,g486L,g486I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486P7_0 : block g486 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g486B7 : block g486 7 0 1=true := g486P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486T : checkedTables g486 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g486 0 0 0 = true)
  · exact (rfl : block g486 1 0 0 = true)
  · exact (rfl : block g486 2 0 0 = true)
  · exact (rfl : block g486 3 0 0 = true)
  · exact (rfl : block g486 4 0 0 = true)
  · exact (rfl : block g486 5 0 0 = true)
  · exact (rfl : block g486 6 0 0 = true)
  · exact g486B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486G : graphValid g486 (boundsBefore K462) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low486 : Lower true (varsX 486) (graphGoal 486) 8 := lower_forest (g:=g486) (i:=0) (hints:=8892974672) (before_sound K462 V462) g486G g486T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K486 := extendKnown K462 8 [(486,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V486 : Known true K486 := extend_ok (m:=486) V462 low486 (by decide +kernel)
def g375Y : Array (Bits × Bits) := #[(0x3841b54f817e9582a58e5c00000ffc00003ff,0x2041a503805e9502a58e14154551545515455),(0xf01bb69681d50b94eb2e82f0000000000ffc00,0xb013969681d40984ea2c80a4cd334cd334cd33),(0xbe52c8410b2fcc83f6d1829003ff003ff00000,0x345248410803cc8066c182903c0f03c0f03c0f),(0x0,0x0),(0x61cfc026a5a2c12f438d4d90000000000003ff,0x61cbc02685a2002f41850c9eabaaeabaaeabaa),(0x4c9970885ccbae3949575370000000000ffc00,0x4c8860085c0ba6390153535b32ccb32ccb32cc),(0x6a6496ea9e8415f6a433190ffc00003ff00000,0x4a0492a29684115280321103c0f03c0f03c0f0),(0x0,0x0),(0x952a4f3b5578326d10e4b80fffffffc0000000,0x812805084178022d1004080c0300c0300c0300)]
def g375C : List ColumnInfo := [(0,2,341,32,8)]
def g375A : List (List Nat) := [[],[98],[81],[81,98]]
def g375D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g375L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g375D8)
  | _ => emptyPacking
def g375I (_ _ : Nat) : Option (Nat × Nat) := none
def g375 : Forest := ⟨375,8,fun i => g375Y[i]?.getD (0,0),g375C,g375A,g375L,g375I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375P8_0 : block g375 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g375B8 : block g375 8 0 1=true := g375P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375T : checkedTables g375 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g375 0 0 0 = true)
  · exact (rfl : block g375 1 0 0 = true)
  · exact (rfl : block g375 2 0 0 = true)
  · exact (rfl : block g375 3 0 0 = true)
  · exact (rfl : block g375 4 0 0 = true)
  · exact (rfl : block g375 5 0 0 = true)
  · exact (rfl : block g375 6 0 0 = true)
  · exact (rfl : block g375 7 0 0 = true)
  · exact g375B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g375G : graphValid g375 (boundsBefore K486) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low375 : Lower true (varsX 375) (graphGoal 375) 9 := lower_forest (g:=g375) (i:=0) (hints:=34604628) (before_sound K486 V486) g375G g375T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K375 := extendKnown K486 9 [(375,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V375 : Known true K375 := extend_ok (m:=375) V486 low375 (by decide +kernel)
def g415Y : Array (Bits × Bits) := #[(0xffffffffb2aeae81f3640f57403562300f00ff,0x800015541008808172640b4740214011111111),(0xc00000000b8114b86dc546df076993e0000f00,0x150566660a8114b86dc546df036982ebbbbbbb),(0x7c49c85ec85d9dca6f389820f00000,0x29b8783c49c858c05c9d426f389027777777),(0x1cf9c783f8c854e18a882ed000f000,0x260e3f801ce98783f8c054e18a082edbbbbbbb),(0xffffffff2163af4c8d3b65558ae49ab000000f,0x384fc00021632f4c8d1b64108ac49aaeeeeeee),(0x0,0x0),(0x0,0x0),(0x11565928769efa2097da15cf00fff0,0x700000011648000018a00004921104444444),(0xcea924f70cd3e0baf803e80fff0000,0x3f800000c2a024260c8340b890002808888888)]
def g415C : List ColumnInfo := [(2,0,413,0,8)]
def g415A : List (List Nat) := [[],[49],[128,66],[128,49,66]]
def g415D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g415L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g415D8)
  | _ => emptyPacking
def g415I (_ _ : Nat) : Option (Nat × Nat) := none
def g415 : Forest := ⟨415,8,fun i => g415Y[i]?.getD (0,0),g415C,g415A,g415L,g415I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g415P8_0 : block g415 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g415B8 : block g415 8 0 1=true := g415P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g415T : checkedTables g415 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g415 0 0 0 = true)
  · exact (rfl : block g415 1 0 0 = true)
  · exact (rfl : block g415 2 0 0 = true)
  · exact (rfl : block g415 3 0 0 = true)
  · exact (rfl : block g415 4 0 0 = true)
  · exact (rfl : block g415 5 0 0 = true)
  · exact (rfl : block g415 6 0 0 = true)
  · exact (rfl : block g415 7 0 0 = true)
  · exact g415B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g415G : graphValid g415 (boundsBefore K375) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low415 : Lower true (varsX 415) (graphGoal 415) 9 := lower_forest (g:=g415) (i:=0) (hints:=30836) (before_sound K375 V375) g415G g415T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K415 := extendKnown K375 9 [(415,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V415 : Known true K415 := extend_ok (m:=415) V375 low415 (by decide +kernel)
def g431Y : Array (Bits × Bits) := #[(0x49571644b9a2072bad38b15001f003e0,0x2aaab08151640b9a20723a910a150c6318c63),(0xffffff95c0c96a70b303f782968db800007c1f,0x80133205404868303301f78094842a5294a529),(0x3e34640d64668ee57b9d48103e000000,0x14dc3c1e34640c64660ea17b9c4811ce739ce7),(0xe6ce3c1fc253a608d451768000f8000,0x71fc00e64c3c1fc213a608d05176ef7bdef7b),(0x0,0x0),(0xffffff90b1d7a6469ca2aacd734d580000001f,0x27e00010b19786468ca2084d634955ad6b5ad6),(0x0,0x0),(0x8ab2c943b4f7d1043ec0ae7c00fffe0,0x380000008a2014024400004268088108421084),(0x6754927b8669f05d7c01f407fff00000,0xc00000614080230009f05c04011406318c6318)]
def g431C : List ColumnInfo := [(4,0,427,0,8)]
def g431A : List (List Nat) := [[]]
def g431D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g431L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g431D8)
  | _ => emptyPacking
def g431I (_ _ : Nat) : Option (Nat × Nat) := none
def g431 : Forest := ⟨431,8,fun i => g431Y[i]?.getD (0,0),g431C,g431A,g431L,g431I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g431P8_0 : block g431 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g431B8 : block g431 8 0 1=true := g431P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g431T : checkedTables g431 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g431 0 0 0 = true)
  · exact (rfl : block g431 1 0 0 = true)
  · exact (rfl : block g431 2 0 0 = true)
  · exact (rfl : block g431 3 0 0 = true)
  · exact (rfl : block g431 4 0 0 = true)
  · exact (rfl : block g431 5 0 0 = true)
  · exact (rfl : block g431 6 0 0 = true)
  · exact (rfl : block g431 7 0 0 = true)
  · exact g431B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g431G : graphValid g431 (boundsBefore K415) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low431 : Lower true (varsX 431) (graphGoal 431) 9 := lower_forest (g:=g431) (i:=0) (hints:=1079383) (before_sound K415 V415) g431G g431T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K431 := extendKnown K415 9 [(431,[]),(443,[128,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V431 : Known true K431 := extend_ok (m:=431) V415 low431 (by decide +kernel)
def g439Y : Array (Bits × Bits) := #[(0xffffdca100220cdb43f3493b7cb8003f03f03f,0x8504000002048801f3492868905145145145),(0x367ebfc07440051dc8cc89cc0000fc0fc0,0x19966a2c0054400419c80c890d34d34d34d3),(0x2f523215e92017d2967c3a380fc0000000,0x552e2d523210292017d2967c3838f3cf3cf3cf),(0x0,0x0),(0xffffeb6b872890ee72c922df1248000000003f,0x66302b6b87289066720822d7124baebaebaeba),(0x20192dd32196dbb462e436e40000000fc0,0x87c0201101d32196dba422e036e2cb2cb2cb2c),(0x0,0x0),(0x2454d24a1f27bc0825b29533f000fff000,0xf8002014d24809271800049214208208208208),(0x13aa493dc334f82ebe00ea03ffff000000,0x12a80925c210e00c200082030c30c30c30)]
def g439C : List ColumnInfo := [(4,0,435,0,8)]
def g439A : List (List Nat) := [[],[128,66]]
def g439D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g439L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g439D8)
  | _ => emptyPacking
def g439I (_ _ : Nat) : Option (Nat × Nat) := none
def g439 : Forest := ⟨439,8,fun i => g439Y[i]?.getD (0,0),g439C,g439A,g439L,g439I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439P8_0 : block g439 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g439B8 : block g439 8 0 1=true := g439P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439T : checkedTables g439 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g439 0 0 0 = true)
  · exact (rfl : block g439 1 0 0 = true)
  · exact (rfl : block g439 2 0 0 = true)
  · exact (rfl : block g439 3 0 0 = true)
  · exact (rfl : block g439 4 0 0 = true)
  · exact (rfl : block g439 5 0 0 = true)
  · exact (rfl : block g439 6 0 0 = true)
  · exact (rfl : block g439 7 0 0 = true)
  · exact g439B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g439G : graphValid g439 (boundsBefore K431) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low439 : Lower true (varsX 439) (graphGoal 439) 9 := lower_forest (g:=g439) (i:=0) (hints:=1050708) (before_sound K431 V431) g439G g439T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K439 := extendKnown K431 9 [(439,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V439 : Known true K439 := extend_ok (m:=439) V431 low439 (by decide +kernel)
def g471Y : Array (Bits × Bits) := #[(0xff7484102137a474d145c3be000007f01fc07f,0x1410801021158074d14000ac0a142850a14285),(0x9193ddfa9b014e409932da0000000fe00000,0x66118195fa9b014e409132da9f3e7cf9f3e7cf),(0x3bc8cab6a04bfc1c1424270003f800003f80,0xb831c8c83420493c1c042007264c993264c993),(0x0,0x0),(0xffaf2f187e4ed4994a15d0120000000000007f,0xc0af2f085e4a54890a15d012f5ebd7af5ebd7a),(0x0,0x0),(0x8265b71d8414c43b981db901fc0000003f80,0x822437098404c0231815b858b162c58b162c),(0x935249417865032e6e954cfe00000fffc000,0x825248006064002e2c850060c183060c1830),(0x4ca9248a495a2ba7a32a80fffffff0000000,0x4c01008208120300830a0081020408102040)]
def g471C : List ColumnInfo := [(2,0,469,0,9),(16,0,455,0,9),(0,2,341,128,8),(0,16,454,1,8),(4,0,467,0,8),(64,0,407,0,8),(1,0,454,0,7),(1,16,454,0,7),(128,0,341,0,7),(128,2,341,0,7),(0,4,147,320,6),(0,64,147,260,6),(2,16,452,1,6),(6,0,465,0,6),(68,0,403,0,6),(256,0,215,0,6),(1,2,324,128,5),(3,0,452,0,5),(3,16,452,0,5),(4,2,337,128,5),(4,16,450,1,5),(4,64,147,256,5),(17,2,324,128,5),(64,4,147,256,5),(128,16,324,1,5),(130,16,324,1,5),(256,4,147,64,5),(256,64,147,4,5),(5,16,450,0,4),(129,2,324,0,4),(131,16,324,0,4),(260,64,147,0,4),(320,4,147,0,4),(324,0,147,0,4)]
def g471A : List (List Nat) := [[],[98],[112,65],[112,65,98]]
def g471D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3d8930c0c4d217945c971582954a564587d8a30a6369f82211628c21d5a961f62d4630c6561f9458b518c2ca5a41d962d4520
def g471D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x68fe084000000058b61d82181e0e0e1000000c78012920a93a0052482001e002000000000001a202008808000200a8408008588158a081620200000000000183f82160fc278218000000880e0c64040802070f057801e0fe2f821d755a55d545454e4f1394b129499234590e404f93d8f33ace8394e237cdc364d634ccb320c02f4ba2c8aa29c9a2488f21c842047e1ec781d4721bc621404d128471103c0bc27090120015749560570d8abe720b8ae1b156b643721d162af8c86c5b82c35b79458b705872e90bb92e2b065d215725c560adbca2e4b8ac1770955c7605832f70bc02eca8567e51825da309cfca305b2c6195f9561d658c38bf2abb2cb18557e557659630aaecbecab2c61c5d76d95658c23bb2fc12cb18477e5587d8a30ceac8b0fb14611dd985d7628c32bb0abaec51867561d81d8a30ccebb708b146199d75e11628c371f04422c51857365f6258a308eecbd0ca14613cf92619428c3d1ac8b12851857565f6258630bcbca2c4b0c619d5985db518c33ab0cbb6a31857565f62d4630ceac3ec5a8c619d58758b518c2f2f28b16a31867561d42d4630cbbc8b0a3b2411f5989db51482b6f28bb6a29047d66076d4520abaca8eda8a415b5941db514839c8ecb16a29053ea607658120a7cca8ecb02417709560560482de32da8ac09066dddb8458910dd3c1108b12213e79261942443d4ac8b128488555255815da308eacc2eda8c618d5865db518c295b283b2c49051e6547658120
def g471H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6800000320000000000000000045002c00001e09000000000
def g471D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x838441a04343314207c1c20e06820941f09c1120f040b080e1e8802e08813a250e822314122d102a2d102008a08045a2044404880846884301104502880914160d0292c71383c0a2a3c4e0f00341f07810a0709c10d6243e0f003587138bc4e09230e292782870c37c1e006913071b810664860c833243e021a9218600dc0a4881800f029227010d490c31c0431244e2d1380861381860a8149430686a405c1e006b0e270781c507e1c505f078184c383c645e1f800a078b07e2f041e27070f890f8bc4240404e8ee64e43e22e1cdf2dbfd95d62d53d44d2cd14cfccdbcb1ca2c81c69c48c27c0fbe5bc4b9ab82b4fb2eb0daf5ad4ab3a92a83a62a41a32a23a029d89b798d97e96694592d9159069008f18eb8d38c48b588b8858768678588378288197f87e97da7b078675c7326ff6f96ea6d26ba69967863c62d60c5f45dc5c459a58257354951f5104f84e04da4cb4c54ad49e48f45c45644743840e3e43c339937834e31b2fa2be29d27c25b2312071e61bc19217a1591411170e40a807504b02a000bf7805c7629ff855c362df5815c362df5715c362bed80d89629fd85dc1629fd809d942bf580d8961df762dc161df562dc161df542dc161efb8059560bfb80595609fd85dc960bbf845c960bbf8458960df7725c560df5725c560bf985d8160ef965d8160ff171d8160dfb805d9509fd87d8950bf980d8950bbf8458950f7b8558150f796558150ddf855da30ddd855da30ddf825da30ddd825da30ddd87d9630ddd76d9630bdd82d9630ddd8759630ddd7659630f5f6559630bdf8259630ddd87d8a30ddd76d8a30bdd85d8a30ddd75d8a30bdd84d8a30edf64d8a30fd581d8a30ddd7658a30bdf8558a30ddd7558a30bdf8458a30f9f8458a30f9c8458a30edf6458a30edd6458a30fcf6258a30bde8650a30bdd8650a30ddd7650a30ddd7550a30fcd6250a30fd76258630fd56258630fd54258630fd762d4630fd562d4630fd542d46309fd859d9209ff855d9209fd851d9209fd86dd5209ff855d120bef8558920def7558920bf586d4520df776d4520df676d4520df576d4520df476d4520df774d4520df574d4520fe562d4520dfb7558120ef96558120ff18158120ff35158120ff35150120df687d8910df776d8910bf584d8910ef764d8910df77658910bf78458910fb78458910fb48458910ef76458910ef56458910fe76258910bf68650910bf58650910df77650910fe56250910dd5735c762daf721d1629ef825d942ead6458942bb784589619bf845cb60b74855c560bf38058560e7965581509df855da30dd5815da309dd87d9630cdd76d96309dd8759630cdd7659630d5d75596309dd87d8a30b9f8458a30dd57658630dd576d46309bf845d92097d851d9209bd841d920cec7658920cf87658120bb784589109d587d4630 else 0xc270400c710060200f004a3f04001d0e82c00c001808020013080301004002834860220880d6230d8246158a0b10107a1c2c0a1c2010002e0f030e1e0b0380c3880d058ac360860f83841d07b0c383f0424187782100c0401000887210203c0e0313871113070b83c007a260e280f80c90c31c06486c260041462b10301f0292186381490c8a0f0031490c07c0a4864904060d1007c00c2944a1500401908801d1285400c08c5048b440a8983200745a2044220054504022820116881110122034401908802014406880914126b11061b1416202c44190836282c40406020080040180803c0100587e0f00401808020013080301004002814507078109068109060240868541a04343215088340820662)
def g471H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc19c3a095dd08ea8880ab053cbf7268af4ce013c8cc6d47c00066000109a8540000030c34400020a48874cb892424000ee1468000003959809cb78d8e1c000000000002877878000003044c355d4003c0c002c4a0c7a8400000211a8e7860058000430003c16e15c728b00034e2c280000038baa7800202da7704fa2655c06601ecd6ebcc2143fe18000000001c05c010d00011280020a097a49ccdc001c8145cb35304904150428e0ad00104c01b
def g471D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa8442c1c047183f0701261c50fc1c0498714770701261c51d0fc1c049871b0701261c442c18744c01a187c7029170113061c81c0f4482428141804087287d160a060069121c8448281800e871a1c7512050601002a261c945448180891f0a8721120600382a261c783814140491c1a1c70160d0a050210545c945c1c0171b17070116103c5c784000fc149171c08231613046f011c8c1c0171b1016130700287c684c1c00a1f14161307005c5460504c1c01715181307003c5c508c1c0471f14201a100c0b0700383c9c1c00a21130700386840d464344c1891b1d17046a247c544c14e891a1414106f07006a1d24849870f0c1707002a1c7c6c1001b49871a184a046d261c6860b0a0504c1c08749206c77070069261c7c1c0498710200b045f021c687c5c4c11249871a16106f050069261c81bc1c0071a142c2814100402261c3c91d0b0a0504c1c08987246c1f046a247864544c0864915151301261854248c544c08619211701121854844c0864e147c0f0304687060b088402c1c5c0870f24201613045f021c6880bc5020805c184c0870f283c2c0f170701247080b0100c549871a1d1707021c5c6c608c145c0871a191707005e1c6861787491a12047f15261c686c5c1844887146c5707001e1068707c1c045171f184b1705121e246c1454487891513061e253851a0b17c9c784c1c0231106006c6a251c74700c5c409161b2717130018549c5c406191503171219245c5c44886130717102448586342620d503c8033f81f54f647873b21d14e3c6fb36e1af4d2c67f3341924c4c6132fc1784b8c5ab2ca15f4aac54329814449f44e326012c492c47b23010f483c40b1f60f4475c3971b80d2465c3171800b9459c2b714e09d44a422710207943941af0ca06042cc14f09804541f40e306602a411406f02c01040540170003feb86c5ff5d760ffeeab07fd75583ffb2ac1ff59560ffee4b07fd72583ffb12c1ff58960ffa84b07ff62543feb12a1ff50950ffaca907fd54482feba6c5bfd9362feae3b15fd70d8affba2c5efdd162f78e8b16ff6458b7eb22c5fbd8962bfee0b15fe7650afebb285fb58942feec4b0ff562587faa12c37f5d760dfecbb05fd72d83fab8ec1fd58760bfeeab06ff655837eb2ac17fdc960feae2b07f561583fdb02c17f9d950bfaeca87f960543efb2c61f759630fbec5187dd628c3eea14617fdd920bfcec905fd76482fe3b2417fdd520bfaea905ff74482feba241fb58920fdaa4907f561483fba8a41fe58120ff280907f762443fab1221fd50910b7ee8b17d563586fbb82c3775da30bbaeb187d5618c3eba8c617ddd910
def g471H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x205dc340000002ea800000042b400067052105656bac2062b402c001f34661892359600000033754c312300028f8000000b2228c4ca51090000002c1881784df2b0000000d67f34400000097699e4c0371d321d16e2f4036ba508afc1d011c90e6b78bc730b340001834000012b91560f802a97b1e85eb0464770000001c3ca70cc880008a1000000000000080f0000837c04837a1e1c6ea08b8f8558cb4a7200001b8eb552687070a8c9a000000000286bb4862380026e40000007960a48b27b3100bde896749300001c960000002130061869000000000160320970a000043f93e80038b3a1962488b0d80473c2e213f026000f6158b54a6040000497c00000000020c80000001327d35e6c0000b5e0500a874b51c21ee847a6b0bc799c01ba4ed0e800086636fc95804384200672819a96411380000976482ad500019f8f680000001407030c292a38000000d3300000019af62200041d54a334e0000002f6cf1e0a8101c63663d97b06ad531a1fa52800302c40522ae09829854900000010ee000b053000cae03a00018ed4d84392620000094c764123857e2ce271a9819a2d286300075cf17f16700000008dba094389995f66c7c46c800000081c15444b601e880860640189c8b00bd1e0010232a8081242c41e0a1c28202142192e0008a0a0001a1028089046c08c080c007
def g471D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x305263c536120c0242c98e5c241807c8086a4c7830070e08dc4832629a801c905064c5890038e003c1131621e1ce458324240401c8011e2c48224693162400c2c18b1038917d1aab9cb9eec0411485200ffd8bfd62ff50bff60ff583fd50ff483f561f78c3f510
def g471H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa38000000000000000000030b80000000000000000000000d88000000011d00000034200007169108000227e0c800000000011d2034000000000000000000000000010560000000cbfc0a00000019040011430000001c08000d12000000000000000000000000000ce8a5d21d0004a900006c200000000000000000002e2c0000000003c72000000000000000000010ec84200000009140000000002420000000000000244ac0c0000000000caab5b5ccec9800000000000000002220003b7e00000000010140000000002450000000000000000000060d400090d262800341c00000000000000000000000000a090000000000000aa488dca380000000000001e3850f0002c68000000000387e000545000000000028d8001c660006130000000000900000000000090900000000000000000000000000000000071a000000082a0000000000000e3200079280000000007b040008460000002c0da2a0000000160a9300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000f2000000016c60000000000000b11281c000000a8880000000000000003a5a0000000000000000e620002c5e000000106c000000e1e8000001848000406000000000000000000000000000000000000000000182e30d6514512000fc680000000000000000000c03000710c00000000000000018afa9de82cd360000006d12c53e0f0000000000000000000052fa130000000000000300b07c0016160000820000814885708c000000000000000000092480000000000000002c9600041000000000000004c240000000002844000000000000000000000020b2060000b268000000000000000092ce47f8f7c6400000000000000000000000000d8e000000000000000000000000000000000000000000000000000174d00024fc000000000000000000000000000000000000000000000000000224c0000003c5c00168c00000f00018020000000000000000000000000000000000010aed188003d34000000000000000000008d800000011f687000000060220000108508000120a008
def g471D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x48e28808037f
def g471H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18200000000220000000000000000000040000000000000090c00000000000000000000000018700059b9609003a128c00000000008400000b1400000000000000000000000000000000000000000000046280006cc0040566002880000034c00d6180
def g471L : Nat → Packing
  | 5 => (6,5,6,0,0,5,0,g471D5)
  | 6 => (59,4,6,0,0,10,0,g471D6)
  | 7 => (127,3,6,0,0,12,0,g471D7)
  | 8 => (78,2,6,0,0,13,0,g471D8)
  | 9 => (10,1,6,0,0,9,0,g471D9)
  | 10 => (1,0,6,0,0,0,0,g471D10)
  | _ => emptyPacking
def g471I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 31 0 7 3 0 g471H6
  | 7 => lookupWord 19 107 6 12 6 2 g471H7
  | 8 => lookupWord 51 277 7 13 7 2 g471H8
  | 9 => lookupWord 32 479 3 13 7 2 g471H9
  | 10 => lookupWord 5 79 2 10 4 2 g471H10
  | _ => fun _ => none
def g471 : Forest := ⟨471,10,fun i => g471Y[i]?.getD (0,0),g471C,g471A,g471L,g471I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P5_0 : block g471 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B5 : block g471 5 0 6=true := g471P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P6_0 : block g471 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P6_5 : block g471 6 5 54=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B6 : block g471 6 0 59=true := (@block_merge g471 6 0 5 54 g471P6_0 g471P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_0 : block g471 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_1 : block g471 7 1 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_27 : block g471 7 27 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_123 : block g471 7 123 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B7 : block g471 7 0 127=true := (@block_merge g471 7 0 27 100 (@block_merge g471 7 0 1 26 g471P7_0 g471P7_1) (@block_merge g471 7 27 96 4 g471P7_27 g471P7_123))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_0 : block g471 8 0 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_8 : block g471 8 8 54=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_62 : block g471 8 62 16=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B8 : block g471 8 0 78=true := (@block_merge g471 8 0 8 70 g471P8_0 (@block_merge g471 8 8 54 16 g471P8_8 g471P8_62))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P9_0 : block g471 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P9_3 : block g471 9 3 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B9 : block g471 9 0 10=true := (@block_merge g471 9 0 3 7 g471P9_0 g471P9_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P10_0 : block g471 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B10 : block g471 10 0 1=true := g471P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471T : checkedTables g471 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g471 0 0 0 = true)
  · exact (rfl : block g471 1 0 0 = true)
  · exact (rfl : block g471 2 0 0 = true)
  · exact (rfl : block g471 3 0 0 = true)
  · exact (rfl : block g471 4 0 0 = true)
  · exact g471B5
  · exact g471B6
  · exact g471B7
  · exact g471B8
  · exact g471B9
  · exact g471B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471G : graphValid g471 (boundsBefore K439) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low471 : Lower true (varsX 471) (graphGoal 471) 11 := lower_forest (g:=g471) (i:=0) (hints:=33556084) (before_sound K439 V439) g471G g471T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K471 := extendKnown K439 11 [(477,[49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V471 : Known true K471 := extend_ok (m:=471) V439 low471 (by decide +kernel)
def g487Y : Array (Bits × Bits) := #[(0x2ad01878891c236e516ead000000ff00ff0000,0xa5018188900236e116ea90f0f0f0f0f0f0f0f),(0xdc5fec904b44aa4826ab5000000000ff0000ff,0x854c8904a44aa480688504545454545454545),(0x19e0755b5023fb1614928a0000ff000000ff00,0x18e0745b10218b161412001313131313131313),(0x0,0x0),(0x0,0x0),(0xd7871c3f07684d9940678300000000000000ff,0x5783142f05284591406783babababababababa),(0x4132cb8ec28262f3e2348d00ff00000000ff00,0x41120984c2826061e2248d2c2c2c2c2c2c2c2c),(0x49a924e0bcb28551784474ff000000ffff0000,0x41a9246030b204116000043030303030303030),(0x2654920534ad14a58f8813ffffffff00000000,0x24048200040c1080088012c0c0c0c0c0c0c0c0)]
def g487C : List ColumnInfo := [(0,32,453,2,9),(32,0,455,0,9),(1,0,486,0,8),(2,0,453,0,8),(2,32,453,0,8),(4,0,483,0,8),(64,0,423,0,8),(0,2,325,160,7),(68,0,419,0,7),(128,0,359,0,7),(0,4,163,320,6),(0,64,163,260,6),(1,2,324,160,6),(129,0,358,0,6),(256,0,231,0,6),(5,0,482,0,5),(64,4,163,256,5),(256,4,163,64,5),(256,64,163,4,5),(260,64,163,0,4)]
def g487A : List (List Nat) := [[],[98]]
def g487D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2ca9a41d962d4120
def g487D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c6040f00200000341000000f0f80200000000002cc0f87c10a0fc90ae107e1f07983a6d1e833b9acbe53238ec5e23027e3b5cee16db318cc05d2d1389648229087e3c1c8c642108038f720c3ecb32d6ee5182dc165addca2e5b82cb1fb985c870596b7728b90e0b2e5ee438759465cbdc3f00b28cbd6b90595721972f730b2ae032c7ee418799762addc82cbba2c53eb906176258ba7720b2ae9a953e6407659552cbdc3f00b2ea137995e0162d432f72ec2ec1a871ee5d65d83509ddca305b06a197b85e01765432f720c28ec9053ea607658120a7cca8ecb02411fa98dd5604823f3313b6a09055e65676d41208fccc0eda8241579951db50482b73283b6a09073a1d962d4120eb5baac5a82414ad941d96254a95b283b2c49051e6547658120
def g487H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5
def g487D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x458580311620b181c6042810008100003141c50428147e00b14100441110598142043410e04390820004381890208081c20708100441110439240830e0d09081090508100081c2c1c00c28182043418204341003410d042508200081090400902083834203801c2e1e00c00504081a60508381110f08141000810f0598084c311e1e00c48378f8044512e00de3111787804834412e00de311179b1787804e40d0b87802e1e0082f178780385e6e1e00e122387802838511e1c2e4138780343e1e0490f8780343e1e008484790344e1e00b87983b930850bc2e1c50ee41a23930828385e1e0e60e139b87803ca458e08da8d48c68b88aa89487e87086285c84683882a8248168088027fc7ee7e87da7c47a679878a78476e75073a72c71e71070a6fc6f66f06ea6dc6ce6c06aa69c69668867a66c65e65064262c61e6105fa5ec5de5d05ca5bc5ae59057a56c55e55054a53c51e5105024f44e64d84d24c44b64a049a48c47e47846244c44643841a4144063f83e23d43be3b03aa39c38e3703523242f62d02a227c26625023a20c1e61b81921741561381220fc0e60b808205402e000b7d80d95659fd80dc965bbf845c965bfb805c965dfb85dc165dfb82dc165df982dc165f7b85dc165dfb75dc165f7b65dc165dfb72dc165df972dc165bfa871c165f7b651c165dfb721c165df9721c165d7f8759465f7b80594659ff805d762dfb805d762df8805d762bfb805d7629fd87997629ff8759762bfb80597629ff855c3629fd80dd562bfb8059562dbe65dd162dbd65dd162bed85d8962bed80d89629fd85dc162f7b80597529fd859d9529fd809d9529ff805d9529fd801d952f7b8059552f788059552cff7659552cfc7659552bfb8059552bef80589529fd86dc152d7d65dc152ded62dc152dfb805d760efb8059760e7f7559560efb8059560d7f7559560e7f6559560bfb80595609fd85dc960bbf845c960bbf84589609ff87549609fc8754960e7d6554960bf985d8160ef965d8160dfb805db50d7f8759750f7b80597509fd87d8b50b7d85d8b50bbf8458b50bfb8058b50df987d8350df976d8350f7985d8350f7965d8350bf982d8350d7f855d950dfb805d950f7b80595509fd87d8950b7d85d8950bf980d8950bbf8458950f7b8558150f7965581509fd859d9209ff855d9209fd851d9209fd86dd520bfb8059520bef8558920def7558920dfb7558120ef96558120bf986d4120dfa76d4120df876d4120f7965d4120fe962d41209bf845cb65c7d87d966597f8759465d6d655c865d79655c0659fb805d762d3d655d3529bf845d9529fb805d9529bd841d9529f9801d952cec76589529bf845cb60cf976d8350b7985d8350e7965d83509fb805d950e7965581509bf845d92097d851d9209bd841d920cec7658920cf87658120d7b75d4120 else 0x3810002204341650599942492209241490400f660980149040660434100002040c504140820501000f141e0040c6c508)
def g487H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7123072502d000000003058008340020b00001c67cc428964245c0058f000a4f10398922002ce00030b041c0000b0c001cd800000e7405000000c1c0000023c810ccd8d0000000060c00045480c823a27e650
def g487D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c3428587009112910898a4c8928a384a20c683150a0142098a88509150a01c2454438315151071a2a1404498d1a2a2224c5458700a131468a8850638684386843b00d0c682386843414a442263c526849461e9470699291262252210a4b06042123264b0604226287149610d11325844c50b087910c361c82898a18292239068c18292239068c486e42220dc829408484e422202c39140a1458acd9720d1b0e6ca8a4e41b365c834416283051b9070e486e42220dc8a0888270821d9240d84709459240c28161c84c50d170e4144c6c380508104e1459098b2320d1c248c83438b9098d10161919088a0b0c8c83852784148c84460e24161c92070f9240d22209c920889844e410445223724810305244720d187641a19223906881a161c82898c2c5060a3720c488e41a2641a109c22b2281496192472021858a0c16109c83881628305139210e488e484245c391411101649218b141828dc838716283051b906244720d10911c834491872111e289c30a4641c30f130b0c8c82870e270c2919070e38529c32320f1e40dc8444c39044222288c8446880b0a9c92088c3c16490a45244740dc82a2c32746415292203720a488e8c02460c488e8c8345c244590c51720e405c51b905e34e12dfedd5dbadadd8bd69d47d2cd11ce1cb8c88c6dc59c45c2ac1dc09bfcbe8bb8b9db7bb67b37b00adeab5a9aa71a41a119ef9cd9ab9829529229008c98a78858558257fc7cc7aa78175f7447226f96d06a06696476255fc5da5aa58f56d53d50d4eb4d74ae47e4404093e03be3a336c33c31a2f82cf29f2682311fa1d81af18d15d13410b0e20b9089060029000ffae1b2fff65597ffb92cbff5c965ffee0b2ffd70597ff3aec5ff5d762ffccbb17fd65d8bfeb86c5ff99562ffacab17fd6554bffb82a5ff5d760ffacbb07ff75583febaac1ffd9560ffacab07ff72583feb92c1ffd8960ffac4b07fd52583ffb16a1ff58b50ffec4a87fd62543feb2a417f5cb65bfae1b2dfd76997bfb2ccb7f5ca65efecab2dff72596ffb82cbfedc165ff0e0b2dfe76197beb28cb7f5c865bfaebb15fd70d8affbaac5efdd162fdec4b15ff7058aff3b6a57f5db52efacba95ff7654aff3b2a57f5d952bf8eca977e6554bbeb2aa5fb58952bfee0a95fd75d837fb2ec1bf59760bfae5b05ff755837fb2ac1bf59560bfee4b07fb60582ff3b6a17f5db50efacba85fd72d43fdb06a17f9d950bfaeca877d65543fcb02a17fdd920bfcec905fd76482fe3b2417fdd520bfaea907ed62483f6a9241fe58120ff6a09067f65996fdb82cb7b5c865beae232df970196dfba2c56f5d352
def g487H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3fcc000003da24ca7495cc0fd497dd0002cf40a400000374488b960003d74000d7d4dbc071bd739029c1794d01ac13ba6dbb53c001438000000003e84000000000001e70c91925d225dae6d9541afda95c9c85d0c0031721c0000003c70fba4ab168f800d65280025965480022500025400035b40000000000025dc001cd207e50a0dc003d1dfa946800000000292f5445a69780c153898e84b0e0000000c5a8254ac0011890a1d870b8001c0c88c0000f2558000003d3000000259c00377400380800383c001830003518002c200000000b000216c0035814613c84ed41e8b69061980025d40032f6c53a6444655d8e891400000000002c000002d34881cc4003de0c9c000001455865c4c0020e6d64003d104340006bc1b0000cf91c5003e7400305e878000000003c43153d9010186df5dcbdc764988cebb400034040b10000052030552c86d324114000518400a04e1c10423c1
def g487D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10a48d06c830344868814341b20a90c2840a34486930927452103424a68c52103824486890a26c840b0a46a340520f09b40520a0d014848a15121a21f08489b2103f83859eb14e210ea63258e44e18003ff65ff997fd65ff197ff62ff58bff52ff54bff60ff583ff50ff543fd20
def g487H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf4a0000008bc0000009d300075b4a803300000055fa02000000000c3de21117b580000000000000000000000004090000000000000000004dc00054d135a1e00000000000000000000000000000000000000000000000000000000000000000000000000e0000000000000000000004457c6d54000000000000000000000000000000000000000000000c4f1c1000000000000000000c2423063c0000000422470008060000009ca5d4000000dc523e94c52770b000000000000000000000d56e3100000000000000000000048fd1a000b0ff3f000288ac78c20000000001c0ebad0c0000000000000000000000000000000000000000000000000000001190006d6000e0a5a9b40edd000000000000000820000000000000000000000000000000000018000000000000000000000000000b4e00000000000051d91200000000000000081f000000000000000000000c23000000000957149000e1600000000000000000000000000000030132e02500010700000000000000000000000000000000000000000028be48c43000000000a8e00000000000000d0000002d734b000000000000000a00000000000000000000000000000000000000a960000000000000000008847c80000000005c3000000000000c2c00000085223ad59000000000000f1b00000021100000012dc9f000000b2a00000000000000000000000300000000025d000000000c26000000000a14fa5000000000000000000000f2b000513000000000000f1c000000000000000000000000000000000a4122880500023700000000000000093255a00000000000000045500022f00013b00000000094400000000025c838000000000000000000000000000204000000251000000bc97d20002500005ab99b000b08c10415229000ab40009871c4000936000000000000946000000000822000000000ba6253000d3400000000000000000000083900000095e000000000000000000000000000000000228020019003100819058600
def g487D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1120827f
def g487H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa00000000258000000000000000000000000000000000002dc0000000000064000000000000000000000000000000000000000000000004080000000000000000000000000000000000000000000000000000000161000000000000000000000000000000000000000000000002300000000000000000000000000012c00000000000003280000000000000000000000b1800000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000002f0000000000000000000000000000000000000680000000000000000000000000000021800006380000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001c5380000000000000000004240115000000000000000000
def g487L : Nat → Packing
  | 5 => (1,5,5,0,0,0,0,g487D5)
  | 6 => (34,4,5,0,0,9,0,g487D6)
  | 7 => (121,3,5,0,0,12,0,g487D7)
  | 8 => (96,2,5,0,0,12,0,g487D8)
  | 9 => (13,1,5,0,0,9,0,g487D9)
  | 10 => (1,0,5,0,0,0,0,g487D10)
  | _ => emptyPacking
def g487I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g487H6
  | 7 => lookupWord 8 59 4 11 6 1 g487H7
  | 8 => lookupWord 35 211 6 12 7 1 g487H8
  | 9 => lookupWord 32 487 3 12 7 1 g487H9
  | 10 => lookupWord 4 293 0 9 4 1 g487H10
  | _ => fun _ => none
def g487 : Forest := ⟨487,10,fun i => g487Y[i]?.getD (0,0),g487C,g487A,g487L,g487I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P5_0 : block g487 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B5 : block g487 5 0 1=true := g487P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P6_0 : block g487 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P6_3 : block g487 6 3 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B6 : block g487 6 0 34=true := (@block_merge g487 6 0 3 31 g487P6_0 g487P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_0 : block g487 7 0 24=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_24 : block g487 7 24 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_120 : block g487 7 120 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B7 : block g487 7 0 121=true := (@block_merge g487 7 0 24 97 g487P7_0 (@block_merge g487 7 24 96 1 g487P7_24 g487P7_120))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_0 : block g487 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_7 : block g487 8 7 58=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_65 : block g487 8 65 31=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B8 : block g487 8 0 96=true := (@block_merge g487 8 0 7 89 g487P8_0 (@block_merge g487 8 7 58 31 g487P8_7 g487P8_65))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P9_0 : block g487 9 0 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B9 : block g487 9 0 13=true := g487P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P10_0 : block g487 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B10 : block g487 10 0 1=true := g487P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487T : checkedTables g487 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g487 0 0 0 = true)
  · exact (rfl : block g487 1 0 0 = true)
  · exact (rfl : block g487 2 0 0 = true)
  · exact (rfl : block g487 3 0 0 = true)
  · exact (rfl : block g487 4 0 0 = true)
  · exact g487B5
  · exact g487B6
  · exact g487B7
  · exact g487B8
  · exact g487B9
  · exact g487B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487G : graphValid g487 (boundsBefore K471) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low487 : Lower true (varsX 487) (graphGoal 487) 11 := lower_forest (g:=g487) (i:=0) (hints:=34604631) (before_sound K471 V471) g487G g487T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K487 := extendKnown K471 11 [(487,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V487 : Known true K487 := extend_ok (m:=487) V471 low487 (by decide +kernel)
def g494Y : Array (Bits × Bits) := #[(0x0,0x0),(0xf38bc04fd63ac0f45462c36200000000ff00ff,0x4102804fd22a80745442026045454545454545),(0xd510db13c54094cf61b06730000ff0000ff00,0x61510d901450090cd603044313131313131313),(0x3b6bcc01b8d91fea0171a0e000000ff000000,0x8392b8401b8d91fea0131a0acfcfcfcfcfcfcf),(0x0,0x0),(0xfaf8f18824f726b840b7d492000000000000ff,0xaf8718024d5268800b5d492bababababababa),(0x8265b74c8a094e518b91db900ff000000ff00,0x8265224882084e008b819382c2c2c2c2c2c2c),(0x93524928749ef02096cb54cff0000ffff0000,0x825049004404e00082ca50430303030303030),(0x4ca924f70cd3e0baf802a80ffffff00000000,0x488804b608d300321000280c0c0c0c0c0c0c0)]
def g494C : List ColumnInfo := [(8,0,486,0,8),(32,0,462,0,8),(0,8,358,128,7),(2,32,460,0,7),(4,0,490,0,7),(64,0,430,0,7),(0,4,170,320,6),(0,64,170,260,6),(128,0,358,0,6),(128,8,358,0,6),(256,0,238,0,6),(4,64,170,256,5),(68,0,426,0,5),(256,4,170,64,5),(256,64,170,4,5),(260,64,170,0,4)]
def g494A : List (List Nat) := [[],[98]]
def g494D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x309ed87d4b61daf74d4961
def g494D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20029020a5902901cc808dc70cc4c139e303c02febaec3fbd4b61fdea4b0fef52506f6bb6a56fdd161
def g494H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x374
def g494D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x73148054d24148e836691d028aea484d44949181a6f1c0bacd2d189184d8d1a80735331ab444c485b895e86310f83400ffd97fd65ffd87fd61ff547fd41fb58bef52
def g494H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb3004b00008435000061000000a2000040ac00
def g494D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x32a80637f
def g494H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9540848100001d6200975600002b0c0073c
def g494L : Nat → Packing
  | 6 => (2,3,4,0,0,3,0,g494D6)
  | 7 => (6,2,4,0,0,7,0,g494D7)
  | 8 => (8,1,4,0,0,9,0,g494D8)
  | 9 => (1,0,4,0,0,0,0,g494D9)
  | _ => emptyPacking
def g494I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 5 1 0 g494H7
  | 8 => lookupWord 2 23 0 8 3 1 g494H8
  | 9 => lookupWord 2 17 2 8 3 1 g494H9
  | _ => fun _ => none
def g494 : Forest := ⟨494,9,fun i => g494Y[i]?.getD (0,0),g494C,g494A,g494L,g494I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P6_0 : block g494 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B6 : block g494 6 0 2=true := g494P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P7_0 : block g494 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P7_2 : block g494 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B7 : block g494 7 0 6=true := (@block_merge g494 7 0 2 4 g494P7_0 g494P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P8_0 : block g494 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P8_2 : block g494 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B8 : block g494 8 0 8=true := (@block_merge g494 8 0 2 6 g494P8_0 g494P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494P9_0 : block g494 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g494B9 : block g494 9 0 1=true := g494P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494T : checkedTables g494 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g494 0 0 0 = true)
  · exact (rfl : block g494 1 0 0 = true)
  · exact (rfl : block g494 2 0 0 = true)
  · exact (rfl : block g494 3 0 0 = true)
  · exact (rfl : block g494 4 0 0 = true)
  · exact (rfl : block g494 5 0 0 = true)
  · exact g494B6
  · exact g494B7
  · exact g494B8
  · exact g494B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g494G : graphValid g494 (boundsBefore K487) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low494 : Lower true (varsX 494) (graphGoal 494) 10 := lower_forest (g:=g494) (i:=0) (hints:=8893003344) (before_sound K487 V487) g494G g494T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K494 := extendKnown K487 10 [(494,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V494 : Known true K494 := extend_ok (m:=494) V487 low494 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0xe00f8d0f76078603669878300000ffc00003ff,0xc00a840d360182034098382154551545515455),(0x6aa8b6ed23ba60c588a28ea003ff00000ffc00,0x62a8b68d23a200c500a088a0cc330cc330cc33),(0x8b9e80fd98e3fc70d5ae21600000003ff00000,0x8a0480fd18a2fc40958e21643d0f43d0f43d0f),(0x147fe0d47550914a455ba8cffc000000000000,0x7fe0c47550914a441aa8c3fcff3fcff3fcff),(0x3f45a653583e9454a765d390000000000003ff,0x3f452252483e1454a765c39eabaaeabaaeabaa),(0xc276ae2967830529b033df0000000000ffc00,0xc074862945830129b03355f33ccf33ccf33cc),(0xf1ba0808aa4919b6723da7d00000003ff00000,0x71ba0800a24901b66231869bc2f0bc2f0bc2f0),(0x5f405916a5806baf11d5c61fffffffc0000000,0x1d000912800068201145461c0300c0300c0300),(0x0,0x0)]
def g255C : List ColumnInfo := [(0,4,187,64,8)]
def g255A : List (List Nat) := [[],[98],[16,84],[16,98,84]]
def g255D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def g255L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g255D8)
  | _ => emptyPacking
def g255I (_ _ : Nat) : Option (Nat × Nat) := none
def g255 : Forest := ⟨255,8,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 1=true := g255P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g255 0 0 0 = true)
  · exact (rfl : block g255 1 0 0 = true)
  · exact (rfl : block g255 2 0 0 = true)
  · exact (rfl : block g255 3 0 0 = true)
  · exact (rfl : block g255 4 0 0 = true)
  · exact (rfl : block g255 5 0 0 = true)
  · exact (rfl : block g255 6 0 0 = true)
  · exact (rfl : block g255 7 0 0 = true)
  · exact g255B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K494) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (varsX 255) (graphGoal 255) 9 := lower_forest (g:=g255) (i:=0) (hints:=34633300) (before_sound K494 V494) g255G g255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K255 := extendKnown K494 9 [(255,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V255 : Known true K255 := extend_ok (m:=255) V494 low255 (by decide +kernel)
def g447Y : Array (Bits × Bits) := #[(0x404e52b118f0a34a60ecd9cc0003f8001fc07f,0x4652b008608240608489800a142850a14285),(0x9600462cfb0e82d50117007a0000000fe03f80,0x8400060c5008825101060068468d1a3468d1a3),(0x3df0929ffde88a821d24c68201fc0000000000,0x11e09293fde88a820c24c6823e7cf9f3e7cf9f),(0xa0a7b3670848f9a033d0acf3000007f0000000,0xa087b3670848a1a033d0acf2dfbf7efdfbf7ef),(0x987b8049b6589bf7c97a70d80000000000007f,0x98398049b61819b7897a7058f5ebd7af5ebd7a),(0x29968a1ef0e78b650d69a9600000000003f80,0x29968a1af0678a650d09a96b972e5cb972e5c),(0x0,0x0),(0xd1a52f5286835c238a097a25fe0007ffffc000,0x5120000086825c020809520520408102040810),(0x2f1099cc0421242dbd828758fffff800000000,0x2e10094c0001202d91020058c183060c183060)]
def g447C : List ColumnInfo := [(0,32,413,2,9),(4,0,443,0,9),(8,0,439,0,9),(16,0,431,0,9),(32,0,415,0,9),(0,4,187,256,8),(0,16,430,1,8),(2,32,413,0,8),(12,0,435,0,8),(24,0,423,0,8),(0,8,311,128,7),(1,0,430,0,7),(1,16,430,0,7),(256,0,187,0,7),(256,4,187,0,7),(0,2,277,160,6),(4,16,426,1,6),(8,4,179,256,6),(8,16,422,1,6),(128,0,311,0,6),(128,8,311,0,6),(1,4,170,256,5),(5,16,426,0,5),(9,16,422,0,5),(17,4,170,256,5),(260,16,170,1,5),(261,16,170,0,4)]
def g447A : List (List Nat) := [[],[128,66]]
def g447D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc28c65bb44cc6c720438dba66363dca40
def g447D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5602000078410000000000000000000000319e30b19e3e1060793c7e0e609e4f0633c6248e3b0e84409f8ed73b85b6d567b2586bd5bac556a54fa65267b2d1505400a7329d9260363af2e818260363af268363e0162c7325f8360960a6b29d9261a408e76a3935da408e7e9d98d8e40ce368998d8e408e76a587d8e40c6765d87d8e40ce366192d8e408eb6a586dca40cab65986dca40ae36a363dca40ce366363dca40ae36a36358a40c73e8997219308f36a686dc9308f36a486dc930a7369c86dc930af168486dc930ab6aa48658130ab669c8658130b7229d9258130bb269b7258130a3369c8658930a3669c8658130
def g447H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xea
def g447D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c60f083c60d182d810156040402602071f1660798101260216cd8a28270820080200001702001c9c3c0180009020000700250080dd99c7c220002102271810a0b842d19c7842464104008825311c9ced99c325f270f3885bc9c42bce2f1f0f3e6098bc7c21f98262e673d7098919c7ce262701b96c9ab681956498b621795b9675514d529435013d4e9334c12d4791b461114390b421013e8f7390e1378d7330c12b8a3280991f86b1503d098130017cf9060b639efcbb01b1ef364980d8f79b04c06c77cd90d8d62de7b1f00b14f7663635c2fb321b1ae13dd97e0d60af64bb04b06f3e0d82582fd720b12c1cf9765c1609dfcbb0d206e7e4d8690375b24c34813bd989da40d5ec34ed204ef6617690337b0ebb481abd865da40bcfc9aed206e766363902f3b2fb1c81b9d87d8e40dcec36c7207e364b6390375b0db9481f8f63dca40dd6c32c5207e3d8d629027bb2f432613dd9721930be6cb6e4986f3a1b724c37990db9261bdb8758130f6cbb2c0987f2649604c3f96e4b0261bce98d8d20de7c36c6907a35936358a73b31b1c813ad98dca408eecb90c984f5644864c35990cb1261ad88658130
def g447H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x306007a20000000000a40000020a40bd1d30d300103003969554bc5c00153da9240000000110007348726259c3c00c14482b712a018e7910511
def g447D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4b93063c2b07150e0ce982860a0c1012830a0c14182c230a0c14182023268a5031a9a28b109e3058660a5c9c5870660d8f1169824384070149830d8a30a0819222428170c191215c223425ca2e171e75c4c4c84f1e1ceb06268e0e4c53966720463cf3898b93101583b3981f1e1cf30a0abb262179cc8d93161ce2c5c88b0e7962e4c59e5ad17262439e5ae18564278f0aecf308999d714131e1cf3098b8c161cf3098d92163cf3168d9e62e28263858466728364c7887672c364c68a6679c36759383bd16fec7d5fa5f452794c99331de23c257eaf4dd53886b0c6978aba5229851c20f3cc6d8bc15625a3f4668ab0f612c0d800fdd80d8ff7d8d70bfd87d82ffe1d60bfd87583bf9d960efd76583f7e0d60fdf63583fb60960fed62583fe5c160fbe76903ef5da40fdd764c3f360b63bdd80d8feb59162fcf6358afbe0162bdf83582ef61e40bbd86903e7d8e40faf72903eb58a40bdf874c2f761d30bde864c2f721930fcf724c3f358930fd9604c2fbe1920fcf63483ab59162
def g447H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1b6c0980095600343ec923960197b1100152d840000000020bd20000000007280004a5509220000000008c760a580068eb5c00000000000003ce800c9c0013480072a89800503320c2e1680000000000000000000000000000038100000000000000000000d2d0173029c000000016498c800000000000000000000000033f626068000000000000000000396000000000ea8000000000000040c000005cf0000000000000181552114634000005a30000000000000000000000d080000000000042955000b3cb6487800000c6c1b05300088
def g447D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x52404c8ce8a76893451238a19cc50916450d8e18a7309902bac4e3867214901b228e738892e8a19cb197902ba35213272648e2327386ba4e1f8c6481985400ffae1ffd83feb07df63fdac5ef903ee987ed20
def g447H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10200060b000424001225a200108c150000002da0673123c00396001851f1f9e8ac0010980000000300d873af7140000d7ab4856670383a000a989c3b128c006413bd00a4fc0cd09e810df97c8fc024939ab1563b4280083395288000c75410bc0a10340
def g447D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x47306209c7ff
def g447H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x739900e68b80c5fee200377498009a2d210d0
def g447L : Nat → Packing
  | 5 => (2,5,5,0,0,3,0,g447D5)
  | 6 => (27,4,5,0,0,9,0,g447D6)
  | 7 => (49,3,5,0,0,10,0,g447D7)
  | 8 => (36,2,5,0,0,11,0,g447D8)
  | 9 => (8,1,5,0,0,9,0,g447D9)
  | 10 => (1,0,5,0,0,0,0,g447D10)
  | _ => emptyPacking
def g447I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 5 1 0 g447H6
  | 7 => lookupWord 7 43 4 10 5 1 g447H7
  | 8 => lookupWord 14 149 3 11 6 1 g447H8
  | 9 => lookupWord 12 67 5 11 6 1 g447H9
  | 10 => lookupWord 3 17 4 8 3 1 g447H10
  | _ => fun _ => none
def g447 : Forest := ⟨447,10,fun i => g447Y[i]?.getD (0,0),g447C,g447A,g447L,g447I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P5_0 : block g447 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g447B5 : block g447 5 0 2=true := g447P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P6_0 : block g447 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P6_2 : block g447 6 2 25=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g447B6 : block g447 6 0 27=true := (@block_merge g447 6 0 2 25 g447P6_0 g447P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P7_0 : block g447 7 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P7_7 : block g447 7 7 42=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g447B7 : block g447 7 0 49=true := (@block_merge g447 7 0 7 42 g447P7_0 g447P7_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P8_0 : block g447 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P8_1 : block g447 8 1 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P8_21 : block g447 8 21 15=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g447B8 : block g447 8 0 36=true := (@block_merge g447 8 0 1 35 g447P8_0 (@block_merge g447 8 1 20 15 g447P8_1 g447P8_21))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P9_0 : block g447 9 0 5=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P9_5 : block g447 9 5 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g447B9 : block g447 9 0 8=true := (@block_merge g447 9 0 5 3 g447P9_0 g447P9_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447P10_0 : block g447 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g447B10 : block g447 10 0 1=true := g447P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447T : checkedTables g447 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g447 0 0 0 = true)
  · exact (rfl : block g447 1 0 0 = true)
  · exact (rfl : block g447 2 0 0 = true)
  · exact (rfl : block g447 3 0 0 = true)
  · exact (rfl : block g447 4 0 0 = true)
  · exact g447B5
  · exact g447B6
  · exact g447B7
  · exact g447B8
  · exact g447B9
  · exact g447B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g447G : graphValid g447 (boundsBefore K255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low447 : Lower true (varsX 447) (graphGoal 447) 11 := lower_forest (g:=g447) (i:=0) (hints:=1079380) (before_sound K255 V255) g447G g447T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K447 := extendKnown K255 11 [(447,[]),(507,[128,66,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V447 : Known true K447 := extend_ok (m:=447) V255 low447 (by decide +kernel)
def g479Y : Array (Bits × Bits) := #[(0x290f21ed7294a371495a35000003f8001fc07f,0x210b20e960908251080231050a142850a14285),(0x53000e276ee392c8ca2c08800000000fe00000,0x11000e256ea392c8ca2808cf9f3e7cf9f3e7cf),(0xe629f0d1feb8968003a1040001fc0000003f80,0xe6095041fa90960001010413264c993264c993),(0x11230281c112d996d2cbc180000007f0000000,0x11230281c012d996d2cb41cf9f3e7cf9f3e7cf),(0x929c0a06961cbfea5ce824000000000000007f,0x92940a06960c3daa54e8047af5ebd7af5ebd7a),(0x0,0x0),(0x8094f3baac6818aaaa8aeb80fe000000003f80,0x84a3ba046808a22a8aebac58b162c58b162c),(0x5ac29d42414b64271506ce7f000007ffffc000,0x4a809102014824200104863060c183060c1830),(0x25f10a2d00814c18e47113fffffff800000000,0x70080400014008c470004081020408102040)]
def g479C : List ColumnInfo := [(2,0,477,0,11)]
def g479A : List (List Nat) := [[],[98],[49],[49,98]]
def g479D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def g479L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g479D11)
  | _ => emptyPacking
def g479I (_ _ : Nat) : Option (Nat × Nat) := none
def g479 : Forest := ⟨479,11,fun i => g479Y[i]?.getD (0,0),g479C,g479A,g479L,g479I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P11_0 : block g479 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B11 : block g479 11 0 1=true := g479P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479T : checkedTables g479 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g479 0 0 0 = true)
  · exact (rfl : block g479 1 0 0 = true)
  · exact (rfl : block g479 2 0 0 = true)
  · exact (rfl : block g479 3 0 0 = true)
  · exact (rfl : block g479 4 0 0 = true)
  · exact (rfl : block g479 5 0 0 = true)
  · exact (rfl : block g479 6 0 0 = true)
  · exact (rfl : block g479 7 0 0 = true)
  · exact (rfl : block g479 8 0 0 = true)
  · exact (rfl : block g479 9 0 0 = true)
  · exact (rfl : block g479 10 0 0 = true)
  · exact g479B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479G : graphValid g479 (boundsBefore K447) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low479 : Lower true (varsX 479) (graphGoal 479) 12 := lower_forest (g:=g479) (i:=0) (hints:=33584756) (before_sound K447 V447) g479G g479T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K479 := extendKnown K447 12 [(479,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V479 : Known true K479 := extend_ok (m:=479) V447 low479 (by decide +kernel)
def g495Y : Array (Bits × Bits) := #[(0xcf1d53009122c3919796000000ff0000ff0000,0x8d1d43001122c39117860f0f0f0f0f0f0f0f0f),(0x11e0238209ef20772b2a0000000000ff0000ff,0x1c0028201ce00572322454545454545454545),(0x19476c29337c8a1467920000ff00000000ff00,0x19466801116408104392131313131313131313),(0x829c89705294d91c0e4200000000ff00000000,0x829c89705294c9140e42cfcfcfcfcfcfcfcfcf),(0x0,0x0),(0xb6642f215035eb419bcd0000000000000000ff,0xb6242d215031eb0098cdbababababababababa),(0x24a38fbdb54ac36e144900ff0000000000ff00,0x24a1873ca40ac36e14492c2c2c2c2c2c2c2c2c),(0xf4104453ec8015aa00feff000000ffffff0000,0x70000401ac0014280018303030303030303030),(0x2b8c908606126c10f001ffffffff0000000000,0x200108202102000a000c0c0c0c0c0c0c0c0c0)]
def g495C : List ColumnInfo := [(8,0,487,0,11)]
def g495A : List (List Nat) := [[],[98]]
def g495D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def g495L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g495D11)
  | _ => emptyPacking
def g495I (_ _ : Nat) : Option (Nat × Nat) := none
def g495 : Forest := ⟨495,11,fun i => g495Y[i]?.getD (0,0),g495C,g495A,g495L,g495I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g495P11_0 : block g495 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g495B11 : block g495 11 0 1=true := g495P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g495T : checkedTables g495 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g495 0 0 0 = true)
  · exact (rfl : block g495 1 0 0 = true)
  · exact (rfl : block g495 2 0 0 = true)
  · exact (rfl : block g495 3 0 0 = true)
  · exact (rfl : block g495 4 0 0 = true)
  · exact (rfl : block g495 5 0 0 = true)
  · exact (rfl : block g495 6 0 0 = true)
  · exact (rfl : block g495 7 0 0 = true)
  · exact (rfl : block g495 8 0 0 = true)
  · exact (rfl : block g495 9 0 0 = true)
  · exact (rfl : block g495 10 0 0 = true)
  · exact g495B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g495G : graphValid g495 (boundsBefore K479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low495 : Lower true (varsX 495) (graphGoal 495) 12 := lower_forest (g:=g495) (i:=0) (hints:=34633303) (before_sound K479 V479) g495G g495T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K495 := extendKnown K479 12 [(495,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V495 : Known true K495 := extend_ok (m:=495) V479 low495 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0xa71b08d61313dec40000000ffc00ffc00003ff,0x830b008401124e842d0b42d0b42d0b42d0b42d),(0x8326fb6924dc2c380000000003ff00000ffc00,0x8222fa6824dc0c391b46d1b46d1b46d1b46d1b),(0x7c6a06f8e964ce2800003ff00000003ff00000,0x3c2a06d8c804cc204711c4711c4711c4711c47),(0x0,0x0),(0xf6b416f6e60904b000000000000000000003ff,0x74b41672e6090033d2f4bd2f4bd2f4bd2f4bd2),(0x59d8579c4f02f84000000000000000000ffc00,0x59d805944b02f042e4b92e4b92e4b92e4b92e4),(0x5bc4b1053b21429800ffc0000000003ff00000,0x4344b10533210288b82e0b82e0b82e0b82e0b8),(0x142585019abd8143ff00000003ffffc0000000,0x140405019a218140c0300c0300c0300c0300c0),(0x8a6c20c4ca1137fffffffffc000000000000,0x80482004c8101300c0300c0300c0300c0300)]
def g503C : List ColumnInfo := [(16,0,487,0,11)]
def g503A : List (List Nat) := [[],[98]]
def g503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def g503L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g503D11)
  | _ => emptyPacking
def g503I (_ _ : Nat) : Option (Nat × Nat) := none
def g503 : Forest := ⟨503,11,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : block g503 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B11 : block g503 11 0 1=true := g503P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503T : checkedTables g503 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0 = true)
  · exact (rfl : block g503 1 0 0 = true)
  · exact (rfl : block g503 2 0 0 = true)
  · exact (rfl : block g503 3 0 0 = true)
  · exact (rfl : block g503 4 0 0 = true)
  · exact (rfl : block g503 5 0 0 = true)
  · exact (rfl : block g503 6 0 0 = true)
  · exact (rfl : block g503 7 0 0 = true)
  · exact (rfl : block g503 8 0 0 = true)
  · exact (rfl : block g503 9 0 0 = true)
  · exact (rfl : block g503 10 0 0 = true)
  · exact g503B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : graphValid g503 (boundsBefore K495) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low503 : Lower true (varsX 503) (graphGoal 503) 12 := lower_forest (g:=g503) (i:=0) (hints:=34604628) (before_sound K495 V495) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K503 := extendKnown K495 12 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V503 : Known true K503 := extend_ok (m:=503) V495 low503 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0x4129a40a000000000fff000000fff000000fff,0x4029840a055055055055055055055055055055),(0x92152a21000000000000000fff000000fff000,0x90152a21433433433433433433433433433433),(0x340d3da000000fff000000000000fff000000,0x300d39210f10f10f10f10f10f10f10f10f10f),(0x6dff017a000000000000fff000000000000000,0x6d7f017acffcffcffcffcffcffcffcffcffcff),(0xb1c83680000000000000000000000000000fff,0xb1c03280faafaafaafaafaafaafaafaafaafaa),(0xe6ab9533000000000000000000000000fff000,0x66aa9512bccbccbccbccbccbccbccbccbccbcc),(0x6c3b0dec000fff000000000000000fff000000,0x6c2b0c6c2f02f02f02f02f02f02f02f02f02f0),(0x7a861896fff000000000fffffffff000000000,0x2801084300300300300300300300300300300),(0x474d205ffffffffffff000000000000000000,0x540001c00c00c00c00c00c00c00c00c00c00)]
def g511C : List ColumnInfo := [(0,32,477,2,12)]
def g511A : List (List Nat) := [[],[98]]
def g511D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3ff
def g511L : Nat → Packing
  | 12 => (1,0,1,0,0,0,0,g511D12)
  | _ => emptyPacking
def g511I (_ _ : Nat) : Option (Nat × Nat) := none
def g511 : Forest := ⟨511,12,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_0 : block g511 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B12 : block g511 12 0 1=true := g511P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511T : checkedTables g511 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g511 0 0 0 = true)
  · exact (rfl : block g511 1 0 0 = true)
  · exact (rfl : block g511 2 0 0 = true)
  · exact (rfl : block g511 3 0 0 = true)
  · exact (rfl : block g511 4 0 0 = true)
  · exact (rfl : block g511 5 0 0 = true)
  · exact (rfl : block g511 6 0 0 = true)
  · exact (rfl : block g511 7 0 0 = true)
  · exact (rfl : block g511 8 0 0 = true)
  · exact (rfl : block g511 9 0 0 = true)
  · exact (rfl : block g511 10 0 0 = true)
  · exact (rfl : block g511 11 0 0 = true)
  · exact g511B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : graphValid g511 (boundsBefore K503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 12 inputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=12) (i:=0) (before_sound K503 V503) g511G g511T (by decide) (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0x4129a40a000000000fff000000fff000000fff,0x4029840a055055055055055055055055055055),(0x92152a21000000000000000fff000000fff000,0x90152a21433433433433433433433433433433),(0x340d3da000000fff000000000000fff000000,0x300d39210f10f10f10f10f10f10f10f10f10f),(0x6dff017a000000000000fff000000000000000,0x6d7f017acffcffcffcffcffcffcffcffcffcff),(0xb1c83680000000000000000000000000000fff,0xb1c03280faafaafaafaafaafaafaafaafaafaa),(0xe6ab9533000000000000000000000000fff000,0x66aa9512bccbccbccbccbccbccbccbccbccbcc),(0x6c3b0dec000fff000000000000000fff000000,0x6c2b0c6c2f02f02f02f02f02f02f02f02f02f0),(0x7a861896fff000000000fffffffff000000000,0x2801084300300300300300300300300300300),(0x474d205ffffffffffff000000000000000000,0x540001c00c00c00c00c00c00c00c00c00c00)]
def mo511C : List ColumnInfo := [(0,32,477,2,12),(8,0,503,0,12),(16,0,495,0,12),(32,0,479,0,12),(0,16,494,1,11),(2,32,477,0,11),(4,0,507,0,11),(64,0,447,0,11),(0,8,375,128,10),(1,0,494,0,10),(1,16,494,0,10),(0,2,341,160,9),(0,4,187,320,9),(0,64,187,260,9),(8,2,341,160,9),(68,0,443,0,9),(128,0,375,0,9),(128,8,375,0,9),(256,0,255,0,9),(4,64,187,256,8),(9,0,486,0,8),(9,16,486,0,8),(64,4,187,256,8),(256,4,187,64,8),(256,64,187,4,8),(5,16,490,0,7),(260,64,187,0,7),(320,4,187,0,7),(324,0,187,0,7),(137,16,358,0,6),(145,8,358,0,6)]
def mo511A : List (List Nat) := [[],[98]]
def mo511D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe8717f1be53a45bcb6b0aaa49e98928c86807a746e68625c56504a443e3800bb98c0691a261d83bb98c06d18760d82c7b8ca6c0985d172d5b9c76c0985d172bb98c06d18760d6297d5c12dd9364980d9d8cb61da360170a7d8c968da260170e9d98768da260170e2dcc66c9a825d30c3ddb66c9a825d30b2ddc825ca660930b6d5c125ca660930b3d5c125d8660930c3ddca6e09758930d3cdc26e09758930c3ddb86a09758930c7d5a86c49758930b3cdc825d8258930b7c5c125d8258930f2cc976198258930fac986609625c1309fd1c12dda360120b998c06d18760d72
def mo511D9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xb8269f291c7f1f88619acb8c30e3f8bcb9acb8dc6f1f8a24d11735e1e3794d39718a5c6f1e4754294b8de3d26445cd71bcb1788f886d0c5f8de5750bc6f1f8861cfcb8c30e378bcbcfcb8de1c67970d6a17cfe6f10ac60e5e50fc7e36632e2bf178c61ca27cfe6c5797c450193097f3f983be2f2e2880c05ec21df1797143b99cf10f2f285d369ca1e5e50ba625e9fc650e50c32d378f9591174de3f10cb2229434de5e56bc52869897e0e56bc6f14b395e5930b9a15f1f8de31878b2e471f8c30f17972e379fcdc134e47ca3663cc5025e5dcbaa1f31e6cbf943a2caa4a74a44a149e49b49849549248f48c48948648348047d47a47747447146e46b46846546245f45c45945645345044d44a44744444143e43b43843543242f42c42942642342041d41a41741441140e40b4084054023ff3fc3f93f63f33f03ed3ea3e73c93a6b8435d33f321307ae9ad02b6a98a7f261243229a071db9bd99697415a9411231098f00d68b889f07805a03c0198005fb8b06519261fdced2344c3b077ee2c1a461d829fbb6053b06c17b9db461d8360b3fcdbb404c2e59f76cda026172bf7160d230eb967ddb02a5835cbceed830ec1ae57ee2c1a461d629fbb6053b06b17b9db461d8358b5ee5d30ec9b015f76cc9764980afeb624bb24c057dcb764d926039eec3b26c93019f76cca95c980f3bb0ec9ae4c079ddb261d835c2bee5cb06c12e1e7761d83609709dfb6c542e4b857dcb960d625c3ceec3b06b12e1ebb6198258970f3f364c3b00b87dd98768d805c3eecc3b06c02e1e7e61da260170dfb346d1300b84ff8ba649805c3cfcc3b24c02e1e7e61d8260170f3f30eb9300b879f987589805c33eed93504ba619f72a5a261d30afbb704bb049876dc97299824c39ee4bb0cc1261d772e5875c930afbb704bac49867dda825d624c3be64bb04b1261f766c9875c130bfb170d12e0986fd9a8689704c3eecc3b44b8261bf6699a25c130bfb374c12e0987dd987609704c3f6c5b304b8261ef6619825c130ff9344c12e0985fd9ba589704c2fecdc2c4b8261f7661d625c130ff9304b12e09873dcb961d83482fecd994ec02417fc6c4a760120bfb16ed1b00906fd9a768d80483decc3b46c02415ee2c19464987cfb370d012ec1e7d9b26809760efcc58348c3b073f56c4a760d829fb36053b06c167d9b3680985caedc58348c3ae55af6d8985d172af73604c2e8b947ddb02a5835cbcceda30ec1ae53f56c4a760d629fb36053b06b17aad865d18258a7ead894ec9b013f56c4a760d80afb172d1b00b879d98768d805c3cecc3b06c02e18f76c9a825d30a7bb704bb049857d5b125d824c276edb150b92613f66c0a85c930a7bb704bac49857d5b125d624c3d66c3304b12613f56c4a760d209fb36053b06905b98b06918760ebcad892ec23075e66c09761183 else 0x19ad3e5fc3e5348ce773361afe2f287476d39dcd10f1795ae3e632f91f3f9)
def mo511H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x45000c24e4000005c15200181000000000045800b4c00f8787114cd18000f1800212884a0511cb0af3e36c5d40a4000338c2003cb6df8ca0eaf0009500000000000617211c
def mo511D10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xb5b5ac2d556a4b4f5a62d2568cb435a02cf5674b3759a2c655ecad35582a554f4a5f52028654049db4e0269530c9674a624c5234903472231515489343c21850848274041fa4f947a33c21d74e6c7133781b34d4c67b3301904c2c5ef2e816e4b3c5832b21524a6451727c13749844a724611c48ac43b21210147cc3c31d20e346dc3471900c045cc2cb15c0a7450427312c08f443c1fb0ee070434417b0ae051425410306c030413c087036013406401b0003fbd9464987dff6499061ffbda261d74ff76818760ffbda461d82fef61d7460bdfda061d72fef691875cbfbda461d62fef61d7458bbfda261d80ff765d93603fdd8764d80ff765d83603fdd8760d80dff65d926037fc9764980eff61d92603fdd9364980eff61d82603fdd9360980bff2a572603bfd875c980ff764d72603bfd8758980ff764d626037fda266170f7f689875c2ffca864970dff661925c3dfd8764970dff659925c2ffda960970dff661825c3dfd8760970fbf299825c3bfd8660970ff760d825c3fed9260970bff6a1725c2ffca85c970dff661725c3dfd875c970f7f5d9725c3fed825c970bff6a5625c2ffda858970dff661625c2ffda758970f7f61d625c3fdd8358970ffb609625c3ff9a760170ffe61d805c3ff9a260170ffe649805c3ff98260170ffe5c9805c3ff96260170ff7689874c3fdd8760930ff761d624c37fca961d20ffe69d80483ff8a760120def6519261fbdda261d83ef76818760ff9da461d83fe761d8460febc965d182eef6197460afdca760d82ef761d8360bf9d7460d829ff680985cbdbda461d72def661745cb7bc985d172f6f61d745cbdbd765d172feb5d1825cb7bd985d162def65d7458afdca760d62ef761d8358bf9d7460d62feb5d18258afdda325d80bfb68897602ff5a125d80bf768c87602feda221d80bfd68487602fdca764d80df765d93603bdd8764d80bf729d83603bdd8760d80df764d926027fca95c980e7f61d726037dd9860d70f7761d835c37f8a960170efe61d805c3df98760170ff668d805c3fd98360170df72a5874c37dd9860930df725d824c3edca660930ef7619824c37dca95c930bf76a1724c2fdca85c930f7761d724c3ddd765c930ff3609724c2fdda858930df7661624c2fdda758930df725d624c3fcd8258930ff66a1704c3fd9a25c130ff6609704c3fd9625c1309ff69c984837dca960d20bf729d83483bdd8760d20efe61d80483fd9a360120bee2819461ef9da321d84beb68887612fb5a121d84bee680876127dda025d83ee76918760f79c9761183ee761d8460e6fda6261729fe680985ca7dca960d72e7761d835cbaed86609629fb688985c27dca960d70e7761d835c39f987601709f76a0974c3dd9875c13097f69c984826fda6261209f56849760e7d9a025d838f76a0974c27d5a125d30 else 0x4d53cbf0f2b50cd234cfc5cb83222e40c0bb3b37172e0b511312f23cfcd82d5ca4280c608bf2d50d63c3cb54ceae329f0ab72e3550d8fc443cb34612e3e4e30c63f150f28b98938fcad4633428c88046371708c72b51335c38dcb2ed4348a3f0f2d52b0c9c9b8dcb5522a43a988f0e372d52b8e238dcb54aca6353f1cb3528cb8c20afc3cb542e370f2d52b8b8dc443cb9e612e3e371f150988be78f8dc6d4639f2e370f2b563cb8bcfcd95cbc46236572f10d988bcfcdc794cbc4623e50c0bf2f1188d948c5831cbc4623e5718c0bb2f1188fcfcdc42b95ca603ac2bb3b36550f2f118922bcfcdc463cb943e3e34c4bf110f2e518138f8dc542302e63cb944cd08e510d3f172cb901a100f4dc395ca2e40d08f15370f2e50b91209a988e8dc543cb9448c0bf3f371508e88f2e51514302fcbc4a230c0bf170f2c5288e3a302fcfcc23c5c3cb1450ecc4bf3f34572f128923a302fcbc514a23f3f308f2e50b4fc7c46ea27435320d3f2e5280daba3c595cace6e3e51371729b198d4c6d95ca6e28a13f2e5489b0c1c5b4d95cb2264399f2e553089b8dc7954c226c66333f1f11b489b8c2861c595ca6e35371f157a89b8c294d95caa26e357a0d372e5280d95c5cb4e6e2b3b34560f2f1488f22cecd15cb83c438eb37133e0c572c890cdc583cb14df223e3708c72e50a9a8f8c2f95ca623cd6563e310f172984b938f8d843543cb94622e48d716370f2c50b8f3515cb8dc52e368f3f37094f28c2f95ca6221673896572988c57cfc62f946230bf28e862bcfc5cdca3a373f360c8b5728d31cc832f55caa03f38c73608ba8f2d511d58c1bc5c225ca3e8e371708c728dd535cfc4222fca3f563508d7388f10bf293d40dc5c29bcb18389708b72e50a21ce03cdca3a30c0b88e573d0f3728f123a302e23c5cfcdc315ca573f30872e50a3bc583cfcc2315ca463708c72e50b8c241bc3cb9437573f30805f1328fcfcc21c43bca373f30872e50bcfcc2016cb9435fa2fc57dcbeb5f42f957c4bdf5ee2f657acbd35e82f35794bc75e22f0577cbbb5dc2ed5764baf5d62ea574cba35d02e75734b975ca2e4571cb8b5c42e15704b7f5be2de56ecb735b82db56d4b675b22d856bc)
def mo511H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa1ae493c1000a375cce51000a4fb0802e82b083641a3f05353060318c927747b5538b2564b150030ffb5259617c3a8c31bb3d10a77d934aec7fdb34388a30550bd2d81d9def6000014245c8354a5000000433106e12a0e716fbd73e3b2314731a5bc2009e81b40c957834000948762d0952a9a36323a0f23828b5ea2233b484fb4acd4a2000818000ee2d1163cc4d000d5aaa40007100008460df74c63934b000dbc23d000c26a25c1c2af000000361dc469900072cec0000fbf024000a02ae1119a9c55da0ab38a040008a1901844f4ed0775800000025f0d44500000b821f69b5d24365296ce000040000295e2190d00081eb545d3013d150cf000de0b2f052fae645001b39040e039f0701013f080302000418341b0a002e09031003010000011b1300010801
def mo511D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xce6b527c58729720c17cf9b161caa88531d262c394b9a2121ad59e361c5948972831623a93e2c394d12a6324c5872cf2e4182ec73e6c58656524c17cf9b16594c486247167cc60be1cb28ac460be594c46639cd2795871652e4d14f88be1cb28d111d3a62388d619594b9545362c32b2af2e4274d8a561ca787305f3e6c587291944e2959f0e53c3474c753e2186b0e594517271d3914d8b0e5945262f8b0cacabc732423a78d08d61cb28b9664807851b0caca58d15473e6c2ab28da8b62ca44b8d9f362305c8e554467cc60be1cb287305e565622e1cf988e59432483ab398cc5f111ca56a198b0e53436a0d8b096ca4c78e5f0e55468698c63c6c36b2aa235472ec716534387d45f161ca5871da82118d8b0e5304eace6a362c394b911b0e22d94d0c6b3e1caa8b8d9f0db22ab28d24d67c5948971c8ea4f8b096ca5c821aa3e2c394b8faa3e2c394b8d1b0cfcaa8b8cc6361559678daa331c53f2971f562c31f29719891c59f361cb288c59f33195946c59f318625f2ca2288d198b3e6c32b29238898c3965171ce982f8b3e6c39651260b91cf0a566ca789305c8e7c59b08a3b94a2b9f311cb286598aaa74d45d4aca495ceec8caca3554d8a8cacabc7201c117c32b296207088d872ca303822d865652e310049f0caca5c7846b3b19594b8e9f096cb28b8d84be594585c59cd46c22b2972230ac25b29a1b398cc5f165223ea199cc62ca44717ab1e73198be24a44ace63317c59488fab381cd8b2901f567839b111ca3e73198bd155947cf988aaca2e7cc4656517381cd9651018ee2cf0730aca4488f746c22e5126870c28e0bd0207ea3e91ebef2176aba5dcc0e1b6f5b67daa6d1c664b1f589ac1d5efaea16feb4f581ab4d538a6c51727dd38097b49ea4351ba8ad43b20e10027d13d09dc4e7470a3661a70cbc6192f11674ab050c26e125c8ce4301f90eec71635418e8bb458828612b087c3d019c0b284b81ee0c004b81b807c000ffec930fffd9061fffb0ec17ff61d72ffebb2e5ffd8758bffb2ec07ff25d80ffec3b01ffc87603ffb24c07ff60980ffeb9301ffd62603ffb30b87ff61d70ffec92e1ffd825c3ffae4b87ff58970ffec3a41ffd76483f7b28c3dff64887bfec810ffbd87613f790ec27ef61d74feec3b07efc9660b7fb0cc17ef61182fdeba305fdd8360affb30b95ff26172efec3ae5dfd765cbf7b08b97ef5d172feec1ae5fed825caffb30b15ff65d62fdec22c5fbd7458bfbb06b17fb60962dfec3b01fdd93603fbb06c05ff66170bfe4c2e1dfd875c3fbb06b87fe60170feec3a61fdd824c3fbae4987f758930bfecc2417fc98482ffb2e905ff65920feec1a41fed82483fdae4907fe60120ffcb02417dd9321efdb2443dfd64487bfcc810f7dc9760f7bb0ec1fe761183fceba3077dd984c2fb92e987f65c130
def mo511H11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xa0000b480000000006400000000000000354c000000f339a260d200000000000000000000000000000000190400000010500022be820a3581cb9280000000000000000000000000000000000000000000001dfc00044800000030b20000000000d2685a00000000000000000000000c960000000000000000000000000000000000000000000000000000000000000147433d21403217619bf00000000000000000000000738800000000000018400000000000000001f51000000000000021d000000000000000000000004cd800352400051580000000001aa38300000000000000001c43d0fe65b4de4350000001b38000000000000000000000000000000000003067039000000000000000015a00000006c6000000071d000000108909700000000000000000000000000000019000169ab30800000091caa2526000107b00000000000000000000000000000000000165e000000000074900000014b8000633422a90ea030000000000000f140001664000000000000023400000024b6000e4810080000000000000000000000000000141600000000016860000000000806000602c000000902000000000000069c0000000d8d0001c8c00030e800161722700048a400000000000006bc017000000000000040e2084000000136800085c00000000000000000000001a2e0000000000000000000000000000000000038ba000000000000000000051e40000002c8dd580000009238000000000000000000000000000000000000000000cf0000000000000000071bd900000000000422c000000000000000000000039fda76000d21000343460f0000000000000000000000178df250078000484000694400000000000000000000000000c7000000041940000000bc80000000000000000001e5400069f8000000000000100e00000038f000000000000000000000000000000000c317a2247e000c398cc40000000000000000000000426e87cb8e0000da98f8c360000000001c7d000151c0000000000000000777c13000000149c00000000000000000000000000eb280001220000002824a36c6872771d400148c51280000000240000000000000000000000000000000000000000007d626ede1500024f6e1a0000000000001780000000000122d00000002ae000000000000000000000000000000000000000000000093c82600000010b14240000000002464000000000000000000000000012050001930000c116cc8000000000000000000000000000010960000000000000000a228003d3e5676c4906c000000000000000000000000000000000000003cd5f2d0001a3800000000000000000000000000001b6d000000000000000000000000000000003c460005428000000000a0800325900284000828b0020042002000c9049600 else 0x160000000000000000000000c7600000020bc000000e2b00000018304cff850001d22f4f000047a0000004e3c000000000000000000061100000000000000000541219c1500000000000000000000000000000143000000000000000000000000001c8d795cd80001585000000000000000000000000000000000000000cb200000000000000000c9a00000000012f63830000000000000000000173c00000000000ee000000ca0c00000000000000000000000001c9200000000000000007d020c4000000000000373400000000000000630000001f04000fc3000081128100041b800005300000018ede82000000201a00002a8000000000000000000158a000000000045f92949800000000005c9000000000022540d8e8f000000000000000000000000000000000000458090800201c0000000000000000000000000000034c8000000657000000053)
def mo511D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1112a9e68a19489c46265e29512111c6aa732285a94a1c6aa285b9475c6aa28653c74629e684a9479e299d84a9476511c68a16ca9499e684a9454679a12a51aa9e64629465629e644a947871e66917451114390a82105a0c000ffd87ffc87ffd82ffd72ffd62ffd80ffd70ffd20fbd84fbd74fdd83fdd30
def mo511H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3b8000000007a1600000000021fe0b71b70a00000031ec010000003210000000000000000000004ad64a000000000f3cb0900000000093822caae6bf925000000735000000a2e029dcdc1248c0006bec28000d4d90663e917000000e0e00000004e00024f000000000000000b95000941000000f08000b42000a3f0007390000000006c5945000000000000000000000a1a0002190009332c400000000000024400000080f3ab000031540ba70000000007bdecfb3b000549000ecc000000000000000000000526000d3a000000000f15000000000000d48000502000000000523000000e1d00000000012200008ff000001470000000000000000000000000003bb0000003c300072bcb0000000f274378af000000c3000092a82f24c000000000b3d00033262430d00000000044b000000000000000000893a10000000491b13000000b050000000000000004a0000000000000000000804000b36000403000000e46743734a2000000000092d00000000041471c0000000009ba089da98117189a8000000000000000000000c0c000b96000000070901001500251400010130020
def mo511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa3984128dff
def mo511H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10a00335e6ce000000001cb00000004a0000000000000000290000000000000000000000000000000000c4410600000a4000000000000000030802e800002000000000000000000000000000034600000000000000000000
def mo511L : Nat → Packing
  | 8 => (24,5,5,0,0,8,0,mo511D8)
  | 9 => (99,4,5,0,0,12,0,mo511D9)
  | 10 => (161,3,5,0,0,13,0,mo511D10)
  | 11 => (80,2,5,0,0,13,0,mo511D11)
  | 12 => (12,1,5,0,0,10,0,mo511D12)
  | 13 => (1,0,5,0,0,0,0,mo511D13)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 8 53 4 10 5 1 mo511H9
  | 10 => lookupWord 36 173 8 12 7 1 mo511H10
  | 11 => lookupWord 56 829 3 13 8 1 mo511H11
  | 12 => lookupWord 27 271 4 12 7 1 mo511H12
  | 13 => lookupWord 3 79 0 9 4 1 mo511H13
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,13,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_0 : CutRow mo511 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_1 : CutRow mo511 8 1 23 := mixedCut (pos:=929968589449777517289292817) (neg:=198103173862210345137568832830479) (data:=fun _ => 0x8789a23191a9b44051a924505149246091a9b4408786a2418789a2418786a2418786a24191a9b45191a9b46191a9b451199ab484199ab4858789a25291a9b4518789a2528789a24191a9b451199ab48491a9b44151492430726b0853) rfl (by decide +kernel)
theorem mo511B8 : CutRow mo511 8 0 24 := (@joinRow mo511 8 0 1 23 mo511P8_0 mo511P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : CutRow mo511 9 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_3 : CutRow mo511 9 3 30 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_33 : CutRow mo511 9 33 66 := mixedCut (pos:=929968589449777517289292817) (neg:=198103173862210345137568832830479) (data:=fun _ => 0x8789a2418789a24291a9b45051a9246191a9b4515149246051a92461929b886451a924619109248191a9b45051a9246191a9b4518789a2528786a2528786a2518786a2528786a25251a92461911924918789a2524069136091492491514924614069136091492491514924518789a2518789a2418789a2418786a2518786a241514924609149249091492490910924909149249091a9b4618789a25291a9b46191a9b45191a9b46191a9b47191a9b4618789a25291a9b4518789a241514924505149245051492490514924508789a24151492490514924405149245051492440514924508789a241514924905149244091a9b46151a92450159a2495726b086451a9245091a9b450) rfl (by decide +kernel)
theorem mo511B9 : CutRow mo511 9 0 99 := (@joinRow mo511 9 0 3 96 mo511P9_0 (@joinRow mo511 9 3 30 66 mo511P9_3 mo511P9_33))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : CutRow mo511 10 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_4 : CutRow mo511 10 4 22 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_26 : CutRow mo511 10 26 70 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_96 : CutRow mo511 10 96 65 := mixedCut (pos:=929968589449777517289292817) (neg:=198103173862210345137568832830479) (data:=fun _ => 0x8789a2528789a2628789a2528789a25291a9b46191a9b46151092491929b887591a9b46191a9b4618789a2628789a2528789a2528789a2528789a2528786a2628786a2628786a2628786a25291a9b47151a9246151a92471726b08a65119246191a9b47151a924618789a2628789a2625149247151492471514924a1514924718789a2629669a370514924a1514924615149247151492461514924618789a2625149247151092471510924a1510924a151092461514924718789a2629669a37051492471514924a151492461514924618789a2518789a2518786a251514924605149246051092460514924608789a25291a9b46191a9b46191a9b47151a9246051a92460) rfl (by decide +kernel)
theorem mo511B10 : CutRow mo511 10 0 161 := (@joinRow mo511 10 0 26 135 (@joinRow mo511 10 0 4 22 mo511P10_0 mo511P10_4) (@joinRow mo511 10 26 70 65 mo511P10_26 mo511P10_96))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : CutRow mo511 11 0 11 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_11 : CutRow mo511 11 11 47 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_58 : CutRow mo511 11 58 22 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B11 : CutRow mo511 11 0 80 := (@joinRow mo511 11 0 11 69 mo511P11_0 (@joinRow mo511 11 11 47 22 mo511P11_11 mo511P11_58))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : CutRow mo511 12 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_4 : CutRow mo511 12 4 8 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : CutRow mo511 12 0 12 := (@joinRow mo511 12 0 4 8 mo511P12_0 mo511P12_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : CutRow mo511 13 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : CutRow mo511 13 0 1 := mo511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511T : mixedTables mo511 13 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo511 0 0)
  · exact (mixedEmpty mo511 1 0)
  · exact (mixedEmpty mo511 2 0)
  · exact (mixedEmpty mo511 3 0)
  · exact (mixedEmpty mo511 4 0)
  · exact (mixedEmpty mo511 5 0)
  · exact (mixedEmpty mo511 6 0)
  · exact (mixedEmpty mo511 7 0)
  · exact mo511B8
  · exact mo511B9
  · exact mo511B10
  · exact mo511B11
  · exact mo511B12
  · exact mo511B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511G : graphValid mo511 (boundsBefore K503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 13 inputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact mixedRoot (g:=mo511) (top:=13) (i:=0) (before_sound K503 (known_down V503)) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_10494

open PEqualNP.Outside.L_meta_10494 in
theorem PEqualNP.Outside.L_meta_10494 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 5) || (x 2 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 6 && x 8) || (x 7 && x 8)) t → 14 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo511R g511R ⟨C,hf,by omega,heq⟩
