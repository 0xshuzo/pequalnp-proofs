import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_11008.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_11008
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
def graph : Sig := 0xfffffffffffffffffffffffffffffffcffffffffffffffffffffffeeffffffccfffffffffffffffafffffffffffff0f0fffefffefffafffaeeeeeeee00000000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)
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
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 6 &&& x 8)
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


abbrev Bits := BitVec 62
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 62 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 62 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 62 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 62 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 62) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 62) (j : Fin 9) :
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
  (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 0 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 1 &&& x 8) ||| (x 3 &&& x 8) ||| (x 4 &&& x 8) ||| (x 6 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 62) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 62) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 62 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 62) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 62 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 62) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 62) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 62) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^63*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^63 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<63 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<63 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<63 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 62) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (63*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^63)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 63*(i+1)-63=63*i := by omega
      have ge : ¬63*(i+1)<63 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 62 = (a==BitVec.allOnes 62) := by
  by_cases h : a=BitVec.allOnes 62
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^62-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^62 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (63*i) =
      (f xs[i]==BitVec.allOnes 62) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^63*u+x+(2^63*v+1)=2^63*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^63 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬63*(i+1)+62<63 := by omega
      have di : 63*(i+1)+62-63=63*i+62 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 63) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (63*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 63) (i:=i) (by simpa using hi) _ ok.2
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 62 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 62
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

def kwDir (u p n : Bool) : Prop := p≠n ∧ (u=false → p=true)
structure KWRooms (u : Bool) (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ kwDir u (bit p v) (bit n v)
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def kwLeaf (u : Bool) (T : Sig) : KWRooms u {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,by simp [kwDir,hp,hn]⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwBoolGate (d : Nat) (x y : Bool) : Bool :=
  if d=0 then x && y else if d=1 then x || y else if d=2 then x && !y else !x && y
def kwTurn (d : Nat) (a : Bool) :=
  (if d=3 then !a else a) == decide (d=1)
def kwTurnGate (d : Nat) (p n value : Bool) :=
  if value=decide (d=1) then kwTurn d p else kwTurn d n
theorem kwGateTable : ∀ (u : Bool) (d : Fin 4) (pa pb na nb : Bool),
    allowed u d.val → kwDir u (kwBoolGate d.val pa pb) (kwBoolGate d.val na nb) →
      kwDir u (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then pa else pb)
        (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then na else nb) := by
  unfold kwDir allowed
  decide +kernel

def kwFork {u : Bool} {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms u (insert (bin d a b) U) T) : KWRooms u (insert a (insert b U)) T := by
  let z := bin d a b
  let branch := fun r : Row => if kwTurn d (bit r a) then a else b
  let sel := fun p n : Row => if bit p z=decide (d=1) then branch p else branch n
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel,branch]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (h : kwDir u (bit p z) (bit n z)) :
      kwDir u (bit p (sel p n)) (bit n (sel p n)) := by
    have lt : d<4 := by rcases hd with h | ⟨_,h⟩ <;> omega
    have gate (r : Row) : bit r z = kwBoolGate d (bit r a) (bit r b) := by
      dsimp only [z,kwBoolGate,bin]; split_ifs <;> simp [bit,r.isLt]
    have ok := kwGateTable u ⟨d,lt⟩ (bit p a) (bit p b) (bit n a) (bit n b) hd
      (by simpa only [←gate] using h)
    change kwDir u (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _)
      (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _) at ok
    rw [←gate] at ok
    by_cases side : bit p z=decide (d=1)
    · cases ha : kwTurn d (bit p a) <;> simpa only [sel,side,ite_true,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_false] using ok
    · cases ha : kwTurn d (bit n a) <;> simpa only [sel,side,ite_false,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_true] using ok
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
      exact ⟨inS,separates p n (H.valid hv).2⟩
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
      have e : bit p z = bit p' z := by
        have v1 := (H.valid (H.rect hv hw)).2.1
        have v2 := (H.valid hw).2.1
        cases ep : bit p z <;> cases ep' : bit p' z <;> cases en : bit n z <;> simp_all
      by_cases h : bit p z=decide (d=1)
      · simpa only [sel,h,ite_true] using ve
      · have h' : bit p' z≠decide (d=1) := e ▸ h
        simpa only [sel,h,h',ite_false] using we

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem kwTight {u T k S} (run : Live u T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms u S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨kwLeaf u T⟩
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
    exact ⟨kwFork hd ha hb fresh H⟩

def onlyWire (u : Bool) (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, kwDir u (bit p w) (bit n w) → w=v

theorem kwOwn {u S T v p n} (H : KWRooms u S T) (one : onlyWire u S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2
  exact eq ▸ hw

theorem kwCross {u S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : onlyWire u S T a p na) (B : onlyWire u S T b p nb)
    (C : onlyWire u S T a pa n) (D : onlyWire u S T b pb n) : Impossible u T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := kwTight run tight
  exact different (H.unique (H.rect (kwOwn H A) (kwOwn H C)) (H.rect (kwOwn H B) (kwOwn H D)))
def kwEnabled (u p n : Bool) : Bool := if u then p != n else p && !n
theorem kwEnabled_iff (u p n : Bool) : kwEnabled u p n=true ↔ kwDir u p n := by
  cases u <;> cases p <;> cases n <;> unfold kwEnabled kwDir <;> decide
def kwWireB (u : Bool) (ws : List Sig) (T v : Sig) (p n : Row) : Bool :=
  bit p T && !bit n T && ws.all (fun w => !(kwEnabled u (bit p w) (bit n w)) || w==v)
theorem kwWireB_sound {u ws T v p n} (h : kwWireB u ws T v p n=true) :
    onlyWire u ws.toFinset T v p n := by
  simp only [kwWireB,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw hz
  have cut := (kwEnabled_iff _ _ _).mpr hz
  simpa only [cut,Bool.not_true,Bool.false_or,beq_iff_eq] using h.2 w (List.mem_toFinset.mp hw)

def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
def kwWord (u : Bool) (pos neg : Nat) (T : Sig) (ws : List Sig) (k value : Nat) : Bool :=
  let field := fun i => (value >>> (4*i)) &&& 15
  let a := ws.getD (field 0) zero
  let b := ws.getD (field 1) zero
  let p := kwProbe pos (field 2)
  let n := kwProbe neg (field 3)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    kwWireB u ws T a p (kwProbe neg (field 4)) && kwWireB u ws T b p (kwProbe neg (field 5)) &&
    kwWireB u ws T a (kwProbe pos (field 6)) n && kwWireB u ws T b (kwProbe pos (field 7)) n
theorem kwWord_sound {u pos neg T ws k v} (h : kwWord u pos neg T ws k v=true) : Impossible u T k ws.toFinset := by
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


namespace SingleRead
def kwDir (u p n : Bool) : Prop := p≠n ∧ (u=false → p=true)
structure PolarRooms (u : Bool) (S : Finset Sig) (T : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false → ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ kwDir u (bit p v) (bit n v)
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

def polarLeaf (u : Bool) (T : Sig) : PolarRooms u {T} T where
  owns v p n := v=T ∧ bit p T=true ∧ bit n T=false
  total p n hp hn := ⟨T,rfl,hp,hn⟩
  valid := by rintro v p n ⟨rfl,hp,hn⟩; exact ⟨by simp,by simp [kwDir,hp,hn]⟩
  unique := by rintro v w p n ⟨rfl,_,_⟩ ⟨eq,_,_⟩; exact eq.symm
  rect := by rintro v p n p' n' ⟨e,hp,_⟩ ⟨_,_,hn⟩; exact ⟨e,hp,hn⟩

def kwBoolGate (d : Nat) (x y : Bool) : Bool :=
  if d=0 then x && y else if d=1 then x || y else if d=2 then x && !y else !x && y
def kwTurn (d : Nat) (a : Bool) :=
  (if d=3 then !a else a) == decide (d=1)
def kwTurnGate (d : Nat) (p n value : Bool) :=
  if value=decide (d=1) then kwTurn d p else kwTurn d n
theorem kwGateTable : ∀ (u : Bool) (d : Fin 4) (pa pb na nb : Bool),
    allowed u d.val → kwDir u (kwBoolGate d.val pa pb) (kwBoolGate d.val na nb) →
      kwDir u (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then pa else pb)
        (if kwTurnGate d.val pa na (kwBoolGate d.val pa pb) then na else nb) := by
  unfold kwDir allowed
  decide +kernel

def polarFork {u : Bool} {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : PolarRooms u (insert (bin d a b) U) T) : PolarRooms u (insert a (insert b U)) T := by
  let z := bin d a b
  let branch := fun r : Row => if kwTurn d (bit r a) then a else b
  let sel := fun p n : Row => if bit p z=decide (d=1) then branch p else branch n
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel,branch]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (h : kwDir u (bit p z) (bit n z)) :
      kwDir u (bit p (sel p n)) (bit n (sel p n)) := by
    have lt : d<4 := by rcases hd with h | ⟨_,h⟩ <;> omega
    have gate (r : Row) : bit r z = kwBoolGate d (bit r a) (bit r b) := by
      dsimp only [z,kwBoolGate,bin]; split_ifs <;> simp [bit,r.isLt]
    have ok := kwGateTable u ⟨d,lt⟩ (bit p a) (bit p b) (bit n a) (bit n b) hd
      (by simpa only [←gate] using h)
    change kwDir u (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _)
      (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _) at ok
    rw [←gate] at ok
    by_cases side : bit p z=decide (d=1)
    · cases ha : kwTurn d (bit p a) <;> simpa only [sel,side,ite_true,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_false] using ok
    · cases ha : kwTurn d (bit n a) <;> simpa only [sel,side,ite_false,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_true] using ok
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
      exact ⟨inS,separates p n (H.valid hv).2⟩
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
      have e : bit p z = bit p' z := by
        have v1 := (H.valid (H.rect hv hw)).2.1
        have v2 := (H.valid hw).2.1
        cases ep : bit p z <;> cases ep' : bit p' z <;> cases en : bit n z <;> simp_all
      by_cases h : bit p z=decide (d=1)
      · simpa only [sel,h,ite_true] using ve
      · have h' : bit p' z≠decide (d=1) := e ▸ h
        simpa only [sel,h,h',ite_false] using we

theorem kwWidth {u T k S} (h : Live u T k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf tail ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a:=a) (insert b U)
    have h2 := Finset.card_insert_le (a:=b) U
    omega

theorem polarTight {u T k S} (run : Live u T k S) (tight : S.card=k+1) :
    Nonempty (PolarRooms u S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := run
    exact ⟨polarLeaf u T⟩
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
    exact ⟨polarFork hd ha hb fresh H⟩

def polarOnly (u : Bool) (S : Finset Sig) (T v : Sig) (p n : Row) :=
  bit p T=true ∧ bit n T=false ∧ ∀ w∈S, kwDir u (bit p w) (bit n w) → w=v

theorem polarOwn {u S T v p n} (H : PolarRooms u S T) (one : polarOnly u S T v p n) : H.owns v p n := by
  obtain ⟨w,hw⟩ := H.total p n one.1 one.2.1
  have eq := one.2.2 w (H.valid hw).1 (H.valid hw).2
  exact eq ▸ hw

theorem polarCross {u S T k a b p n pa pb na nb} (size : k+1=S.card) (different : a≠b)
    (A : polarOnly u S T a p na) (B : polarOnly u S T b p nb)
    (C : polarOnly u S T a pa n) (D : polarOnly u S T b pb n) : Impossible u T k S := by
  intro j hj run
  have lb := kwWidth run
  have tight : S.card=j+1 := by omega
  obtain ⟨H⟩ := polarTight run tight
  exact different (H.unique (H.rect (polarOwn H A) (polarOwn H C)) (H.rect (polarOwn H B) (polarOwn H D)))
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

theorem polarDirFalse (a b : Bool) : kwDir false a b ↔ a=true ∧ b=false := by
  cases a <;> cases b <;> simp [kwDir]
def polarOfMono {S T} (H : KWRooms S T) : PolarRooms false S T where
  owns := H.owns
  total := H.total
  valid := fun h => ⟨(H.valid h).1,(polarDirFalse _ _).mpr (H.valid h).2⟩
  unique := H.unique
  rect := H.rect
def monoOfPolar {S T} (H : PolarRooms false S T) : KWRooms S T where
  owns := H.owns
  total := H.total
  valid := fun h => ⟨(H.valid h).1,(polarDirFalse _ _).mp (H.valid h).2⟩
  unique := H.unique
  rect := H.rect
def kwFork {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : KWRooms (insert (bin d a b) U) T) : KWRooms (insert a (insert b U)) T :=
  monoOfPolar (polarFork (u:=false) (Or.inl (by omega)) ha hb hz (polarOfMono H))
theorem kwTight {T k S} (r : Live false T k S) (tight : S.card=k+1) :
    Nonempty (KWRooms S T) := by
  obtain ⟨h⟩ := polarTight r tight
  exact ⟨monoOfPolar h⟩
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
structure FreeRooms (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    (bit p H=true ∧ bit n H=false) ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ bit p v=true ∧ bit n v=false
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

structure SingleFactor (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : KWRooms inner pivot
  outside : FreeRooms outer T pivot

def freeFrom {S T} (D : KWRooms S T) (h : Sig) : FreeRooms S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect

def freeHide {S T h} (D : FreeRooms S T h) : FreeRooms (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩

def factorOfTree {S T} (D : KWRooms S T) : SingleFactor S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl ⟨hp,hn⟩
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }

def freeFork {h : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (d01 : d=0 ∨ d=1)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreeRooms (insert (bin d a b) U) T h) : FreeRooms (insert a (insert b U)) T h := by
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
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
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

theorem supportSide {A B U : Finset Sig} {a b z : Sig}
    (e : A∪B=insert z U) (disj : Disjoint A B) (za : z∈A)
    (freshA : a∉insert z U) (freshB : b∉insert z U) (freshZ : z∉U) :
    (insert a (insert b (A.erase z))) ∪ B=insert a (insert b U) ∧
    Disjoint (insert a (insert b (A.erase z))) B ∧ a∉A.erase z ∧ b∉A.erase z := by
  have hb : z∉B := fun h => Finset.disjoint_left.mp disj za h
  have allmem (w : Sig) : w∈A∨w∈B ↔ w=z∨w∈U := by
    rw [←Finset.mem_union,←Finset.mem_insert,e]
  have aout : a∉A ∧ a∉B := by
    have h : a∉A∪B := by rw [e]; exact freshA
    simpa using h
  have bout : b∉A ∧ b∉B := by
    have h : b∉A∪B := by rw [e]; exact freshB
    simpa using h
  refine ⟨?_,?_,fun h => aout.1 (Finset.mem_of_mem_erase h),fun h => bout.1 (Finset.mem_of_mem_erase h)⟩
  · ext w
    have m := allmem w
    by_cases eq : w=z
    · subst w; simp [freshZ,hb]
    · simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at *
      tauto
  · apply Finset.disjoint_left.mpr
    intro w hw hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact aout.2 hwB
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact bout.2 hwB
    exact Finset.disjoint_left.mp disj (Finset.mem_of_mem_erase hw) hwB

def factorExpand {U T a b d} (hd : d=0 ∨ d=1)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : SingleFactor (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : KWRooms (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,kwFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreeRooms (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freeFork hd ha hb (by simp [z]) old⟩

def factorKeep {U T a b d} (hd : d=0 ∨ d=1) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : KWRooms (insert (bin d a b) U) T) :
    SingleFactor (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : FreeRooms (insert z (U.erase a)) T a := set0 ▸ freeHide (freeFrom H a)
  have H1 := freeFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreeRooms (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,kwLeaf a,freeHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp

theorem oneShare {T k S} (r : Live false T k S) (budget : k≤S.card) :
    Nonempty (SingleFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨factorOfTree (kwLeaf T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    have hd01 : d=0 ∨ d=1 := by rcases hd with q | ⟨q,_⟩ <;> simp_all <;> omega
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨factorKeep hd01 ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := kwTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin d b a=z := by
          rcases hd01 with eq | eq <;> subst d <;> simp [z,bin,BitVec.and_comm,BitVec.or_comm]
        have H' : KWRooms (insert (bin d b a) U) T := by simpa only [comm] using H
        have fr : bin d b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := factorKeep hd01 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨factorExpand hd01 fa fb zU F⟩
theorem factorForced {S : Finset Sig} {T : Sig} (F : SingleFactor S T) (p n : Row)
    (hp : bit p T=true) (hn : bit n T=false)
    (none : ∀ v∈F.outer, bit p v=true → bit n v=false → False) :
    bit p F.pivot=true ∧ bit n F.pivot=false := by
  rcases F.outside.total p n hp hn with h | ⟨v,hv⟩
  · exact h
  · exact False.elim (none v (F.outside.valid hv).1 (F.outside.valid hv).2.1 (F.outside.valid hv).2.2)

theorem factorOuterOwn {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a p n} (ao : a∈F.outer)
    (one : onlyWire S T a p n) : F.outside.owns a p n := by
  rcases F.outside.total p n one.1 one.2.1 with hpivot | ⟨w,hw⟩
  · obtain ⟨w,hw⟩ := F.inside.total p n hpivot.1 hpivot.2
    obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
    have eq := one.2.2 w ws wp wn
    rw [eq] at wi
    exact False.elim (Finset.disjoint_left.mp F.apart wi ao)
  · obtain ⟨wo,wp,wn⟩ := F.outside.valid hw
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := one.2.2 w ws wp wn
    exact eq ▸ hw

theorem outerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (aout : a∈F.outer) (bout : b∈F.outer)
    (different : a≠b) (A : onlyWire S T a p na) (B : onlyWire S T b p nb)
    (C : onlyWire S T a pa n) (D : onlyWire S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (factorOuterOwn F aout A) (factorOuterOwn F aout C))
    (F.outside.rect (factorOuterOwn F bout B) (factorOuterOwn F bout D)))

theorem innerCannotCross {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (A : onlyWire F.inner F.pivot a p na) (B : onlyWire F.inner F.pivot b p nb)
    (C : onlyWire F.inner F.pivot a pa n) (D : onlyWire F.inner F.pivot b pb n) : False :=
  different (F.inside.unique (F.inside.rect (kwOwn F.inside A) (kwOwn F.inside C))
    (F.inside.rect (kwOwn F.inside B) (kwOwn F.inside D)))

theorem innerSource {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {v p n}
    (hv : v∈F.inner) (only : onlyWire S T v p n) : onlyWire F.inner F.pivot v p n := by
  have h : bit p F.pivot=true ∧ bit n F.pivot=false := by
    apply factorForced F p n only.1 only.2.1
    intro w wo hp hn
    have ws : w∈S := F.cover ▸ Finset.mem_union_right _ wo
    have eq := only.2.2 w ws hp hn
    exact Finset.disjoint_left.mp F.apart hv (eq ▸ wo)
  refine ⟨h.1,h.2,?_⟩
  intro w wi hp hn
  exact only.2.2 w (F.cover ▸ Finset.mem_union_left _ wi) hp hn

theorem hornRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b c p n pa na}
    (ar : onlyWire S T a p na) (br : onlyWire S T b pa n) (cr : onlyWire S T c p n)
    (ia : a∈F.inner) (ib : b∈F.inner) : c∈F.inner := by
  have ah := innerSource F ia ar
  have bh := innerSource F ib br
  obtain ⟨w,hw⟩ := F.inside.total p n ah.1 bh.2.1
  obtain ⟨wi,wp,wn⟩ := F.inside.valid hw
  have ws : w∈S := F.cover ▸ Finset.mem_union_left _ wi
  exact (cr.2.2 w ws wp wn) ▸ wi

theorem parityRule {S : Finset Sig} {T : Sig} (F : SingleFactor S T) {a b p n pa pb na nb}
    (hs : a∈S) (ht : b∈S) (ne : a≠b)
    (h1 : onlyWire S T a p na) (h2 : onlyWire S T b p nb)
    (h3 : onlyWire S T a pa n) (h4 : onlyWire S T b pb n) :
    ((a∈F.inner ∧ b∈F.inner) ∨ (a∉F.inner ∧ b∉F.inner)) → False := by
  rintro (⟨ia,ib⟩ | ⟨oa,ob⟩)
  · exact innerCannotCross F ne (innerSource F ia h1) (innerSource F ib h2)
      (innerSource F ia h3) (innerSource F ib h4)
  · rw [←F.cover,Finset.mem_union] at hs ht
    exact outerCannotCross F (hs.resolve_left oa) (ht.resolve_left ob) ne h1 h2 h3 h4

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
theorem panelAnd {a b : Bool} (h : (a && b)=true) : a=true ∧ b=true := by
  simpa only [Bool.and_eq_true] using h
def polarCell (ws : List Sig) (T v : Sig) (p n : Row) :=
  bit p T && !bit n T && ws.all (fun w => (bit p w==bit n w) || w==v)
theorem polarCell_sound {ws T v p n} (h : polarCell ws T v p n=true) :
    polarOnly true ws.toFinset T v p n := by
  simp only [polarCell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw sep
  have e : (bit p w==bit n w)=false := beq_eq_false_iff_ne.mpr sep.1
  simpa only [e,Bool.false_or,beq_iff_eq] using h.2 w (List.mem_toFinset.mp hw)
structure FreePolar (S : Finset Sig) (T H : Sig) where
  owns : Sig → Row → Row → Prop
  total : ∀ p n, bit p T=true → bit n T=false →
    bit p H≠bit n H ∨ ∃ v, owns v p n
  valid : ∀ {v p n}, owns v p n → v∈S ∧ kwDir true (bit p v) (bit n v)
  unique : ∀ {v w p n}, owns v p n → owns w p n → v=w
  rect : ∀ {v p n p' n'}, owns v p n' → owns v p' n → owns v p n

structure PolarFactor (S : Finset Sig) (T : Sig) where
  inner : Finset Sig
  outer : Finset Sig
  pivot : Sig
  cover : inner ∪ outer = S
  apart : Disjoint inner outer
  inside : PolarRooms true inner pivot
  outside : FreePolar outer T pivot

def polarFreeFrom {S T} (D : PolarRooms true S T) (h : Sig) : FreePolar S T h where
  owns := D.owns
  total p n hp hn := Or.inr (D.total p n hp hn)
  valid := D.valid
  unique := D.unique
  rect := D.rect

def polarHide {S T h} (D : FreePolar S T h) : FreePolar (S.erase h) T h where
  owns v p n := v≠h ∧ D.owns v p n
  total := by
    intro p n hp hn
    rcases D.total p n hp hn with yes | ⟨v,hv⟩
    · exact Or.inl yes
    · by_cases eq : v=h
      · exact Or.inl (eq ▸ (D.valid hv).2.1)
      · exact Or.inr ⟨v,eq,hv⟩
  valid := by
    rintro v p n ⟨ne,hv⟩
    exact ⟨Finset.mem_erase.mpr ⟨ne,(D.valid hv).1⟩,(D.valid hv).2⟩
  unique := fun h1 h2 => D.unique h1.2 h2.2
  rect := fun a b => ⟨a.1,D.rect a.2 b.2⟩

def polarFactorOfTree {S T} (D : PolarRooms true S T) : PolarFactor S T where
  inner := S
  outer := ∅
  pivot := T
  cover := by simp
  apart := by simp
  inside := D
  outside := {
    owns := fun _ _ _ => False
    total := fun p n hp hn => Or.inl (by simp [hp,hn])
    valid := fun h => h.elim
    unique := fun h _ => h.elim
    rect := fun h _ => h.elim }

def freePolarFork {pivot : Sig} {U : Finset Sig} {T a b : Sig} {d : Nat} (hd : allowed true d)
    (ha : a∉U) (hb : b∉U) (hz : bin d a b∉U)
    (H : FreePolar (insert (bin d a b) U) T pivot) : FreePolar (insert a (insert b U)) T pivot := by
  let z := bin d a b
  let branch := fun r : Row => if kwTurn d (bit r a) then a else b
  let sel := fun p n : Row => if bit p z=decide (d=1) then branch p else branch n
  have pick (p n) : sel p n=a ∨ sel p n=b := by
    dsimp only [sel,branch]; split <;> split <;> simp
  have outside (p n) : sel p n ∉ U := by
    rcases pick p n with eq | eq
    · simpa only [eq] using ha
    · simpa only [eq] using hb
  have separates (p n) (h : kwDir true (bit p z) (bit n z)) :
      kwDir true (bit p (sel p n)) (bit n (sel p n)) := by
    have lt : d<4 := by rcases hd with h | ⟨_,h⟩ <;> omega
    have gate (r : Row) : bit r z = kwBoolGate d (bit r a) (bit r b) := by
      dsimp only [z,kwBoolGate,bin]; split_ifs <;> simp [bit,r.isLt]
    have ok := kwGateTable true ⟨d,lt⟩ (bit p a) (bit p b) (bit n a) (bit n b) hd
      (by simpa only [←gate] using h)
    change kwDir true (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _)
      (if kwTurnGate d (bit p a) (bit n a) (kwBoolGate d (bit p a) (bit p b)) then _ else _) at ok
    rw [←gate] at ok
    by_cases side : bit p z=decide (d=1)
    · cases ha : kwTurn d (bit p a) <;> simpa only [sel,side,ite_true,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_false] using ok
    · cases ha : kwTurn d (bit n a) <;> simpa only [sel,side,ite_false,branch,kwTurnGate,ha,
        Bool.false_eq_true,ite_true] using ok
  refine { owns := fun v p n => (v∈U ∧ H.owns v p n) ∨ (v=sel p n ∧ H.owns z p n)
           total := ?_
           valid := ?_
           unique := ?_
           rect := ?_ }
  · intro p n hp hn
    rcases H.total p n hp hn with closed | ⟨v,hv⟩
    · exact Or.inl closed
    right
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
      exact ⟨inS,separates p n (H.valid hv).2⟩
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
      have e : bit p z = bit p' z := by
        have v1 := (H.valid (H.rect hv hw)).2.1
        have v2 := (H.valid hw).2.1
        cases ep : bit p z <;> cases ep' : bit p' z <;> cases en : bit n z <;> simp_all
      by_cases h : bit p z=decide (d=1)
      · simpa only [sel,h,ite_true] using ve
      · have h' : bit p' z≠decide (d=1) := e ▸ h
        simpa only [sel,h,h',ite_false] using we

def polarExpand {U T a b d} (hd : allowed true d)
    (freshA : a∉insert (bin d a b) U) (freshB : b∉insert (bin d a b) U)
    (freshZ : bin d a b∉U) (F : PolarFactor (insert (bin d a b) U) T) :
    PolarFactor (insert a (insert b U)) T := by
  classical
  let z := bin d a b
  by_cases inn : z∈F.inner
  · obtain ⟨eq,apart,ha,hb⟩ := supportSide F.cover F.apart inn freshA freshB freshZ
    have old : PolarRooms true (insert z (F.inner.erase z)) F.pivot := by
      rw [Finset.insert_erase inn]; exact F.inside
    exact ⟨_,F.outer,F.pivot,eq,apart,polarFork hd ha hb (by simp [z]) old,F.outside⟩
  · have out : z∈F.outer := by
      have m : z∈F.inner∪F.outer := by rw [F.cover]; exact Finset.mem_insert_self _ _
      exact (Finset.mem_union.mp m).resolve_left inn
    obtain ⟨eq,apart,ha,hb⟩ := supportSide ((Finset.union_comm _ _).trans F.cover) F.apart.symm out freshA freshB freshZ
    have old : FreePolar (insert z (F.outer.erase z)) T F.pivot := by
      rw [Finset.insert_erase out]; exact F.outside
    exact ⟨F.inner,_,F.pivot,(Finset.union_comm _ _).trans eq,apart.symm,F.inside,
      freePolarFork hd ha hb (by simp [z]) old⟩

def polarKeep {U T a b d} (hd : allowed true d) (ab : a≠b) (hb : b∉U)
    (fresh : bin d a b∉insert a (insert b U)) (H : PolarRooms true (insert (bin d a b) U) T) :
    PolarFactor (insert a (insert b U)) T := by
  let z := bin d a b
  have za : z≠a := by
    intro eq
    apply fresh
    exact Finset.mem_insert.mpr (Or.inl eq)
  have zU : z∉U := fun h => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
  have set0 : (insert z U).erase a = insert z (U.erase a) := by
    ext v
    simp only [Finset.mem_erase,Finset.mem_insert]
    by_cases eq : v=z
    · subst v; simp [za]
    · tauto
  have H0 : FreePolar (insert z (U.erase a)) T a := set0 ▸ polarHide (polarFreeFrom H a)
  have H1 := freePolarFork hd (show a∉U.erase a by simp)
    (fun m => hb (Finset.mem_of_mem_erase m)) (fun m => zU (Finset.mem_of_mem_erase m)) H0
  have eq : insert a (insert b (U.erase a))=insert a (insert b U) := by
    ext v
    simp only [Finset.mem_insert,Finset.mem_erase]
    tauto
  have H1' : FreePolar (insert a (insert b U)) T a := eq ▸ H1
  refine ⟨{a},(insert a (insert b U)).erase a,a,?_,?_,polarLeaf true a,polarHide H1'⟩
  · ext v; simp only [Finset.mem_union,Finset.mem_singleton,Finset.mem_erase,Finset.mem_insert]; tauto
  · simp

theorem polarOneShare {T k S} (r : Live true T k S) (budget : k≤S.card) :
    Nonempty (PolarFactor S T) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,_⟩ := r
    exact ⟨polarFactorOfTree (polarLeaf true T)⟩
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,_,_,ab,fresh,tail⟩ := r
    let z := bin d a b
    have zU : z∉U := fun m => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem m))
    have size := kwWidth tail
    have zcard : (insert z U).card=U.card+1 := Finset.card_insert_of_notMem zU
    change (insert z U).card ≤ k+1 at size
    by_cases ain : a∈U
    · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ain : a∈insert b U)] at budget
      by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin'] at budget; omega
      · rw [Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨H⟩ := polarTight tail (by change (insert z U).card=k+1; omega)
        exact ⟨polarKeep hd ab bin' fresh H⟩
    · by_cases bin' : b∈U
      · rw [Finset.insert_eq_of_mem bin',Finset.card_insert_of_notMem ain] at budget
        obtain ⟨H⟩ := polarTight tail (by change (insert z U).card=k+1; omega)
        have comm : bin (flipOp d) b a=z := (bin_flip hd a b).symm
        have H' : PolarRooms true (insert (bin (flipOp d) b a) U) T := by simpa only [comm] using H
        have fr : bin (flipOp d) b a∉insert b (insert a U) := by simpa only [comm,Finset.insert_comm] using fresh
        have F := polarKeep (flip_flip hd).1 ab.symm ain fr H'
        exact ⟨by simpa only [Finset.insert_comm] using F⟩
      · have an : a∉insert b U := by simp [ain,ab]
        rw [Finset.card_insert_of_notMem an,Finset.card_insert_of_notMem bin'] at budget
        obtain ⟨F⟩ := ih tail (by change k≤(insert z U).card; omega)
        have neA : a≠z := fun e => fresh (Finset.mem_insert.mpr (Or.inl e.symm))
        have neB : b≠z := fun e => fresh (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl e.symm)))
        have fa : a∉insert z U := fun h => (Finset.mem_insert.mp h).elim neA ain
        have fb : b∉insert z U := fun h => (Finset.mem_insert.mp h).elim neB bin'
        exact ⟨polarExpand hd fa fb zU F⟩
theorem polarDepends {S T} (H : PolarRooms true S T) {p n : Row}
    (agree : ∀ w∈S,bit p w=bit n w) : bit p T=bit n T := by
  cases hp : bit p T <;> cases hn : bit n T
  · rfl
  · obtain ⟨w,hw⟩ := H.total n p hn hp
    exact False.elim ((H.valid hw).2.1 (agree w (H.valid hw).1).symm)
  · obtain ⟨w,hw⟩ := H.total p n hp hn
    exact False.elim ((H.valid hw).2.1 (agree w (H.valid hw).1))
  · rfl

theorem polarForces {S T} (F : PolarFactor S T) {p n : Row}
    (hp : bit p T=true) (hn : bit n T=false)
    (agree : ∀ w∈F.outer,bit p w=bit n w) : bit p F.pivot≠bit n F.pivot := by
  rcases F.outside.total p n hp hn with e | ⟨w,hw⟩
  · exact e
  · exact False.elim ((F.outside.valid hw).2.1 (agree w (F.outside.valid hw).1))
theorem polarPair {S T} (F : PolarFactor S T) {w p n} (only : polarOnly true S T w p n) :
    bit p F.pivot≠bit n F.pivot ↔ w∈F.inner := by
  constructor
  · intro different
    by_contra missing
    apply different
    apply polarDepends F.inside
    intro v vin
    by_contra sep
    have eq := only.2.2 v (F.cover ▸ Finset.mem_union_left _ vin) ⟨sep,by simp⟩
    exact missing (eq ▸ vin)
  · intro wi
    apply polarForces F only.1 only.2.1
    intro v vo
    by_contra sep
    have eq := only.2.2 v (F.cover ▸ Finset.mem_union_right _ vo) ⟨sep,by simp⟩
    exact Finset.disjoint_left.mp F.apart wi (eq ▸ vo)

theorem roomPhase {S T} (H : PolarRooms true S T) (v : Sig) :
    ∃ phase : Bool, ∀ {p n}, H.owns v p n → bit p v=phase ∧ bit n v=!phase := by
  by_cases used : ∃ p n, H.owns v p n
  · obtain ⟨p0,n0,start⟩ := used
    refine ⟨bit p0 v,?_⟩
    intro p n here
    have d1 := (H.valid here).2.1
    have d2 := (H.valid (H.rect start here)).2.1
    cases z : bit p0 v <;> cases q : bit p v <;> cases r : bit n v <;> simp_all
  · exact ⟨false,fun h => False.elim (used ⟨_,_,h⟩)⟩

theorem freePolarPhase {S T pivot} (H : FreePolar S T pivot) (v : Sig) :
    ∃ phase : Bool, ∀ {p n}, H.owns v p n → bit p v=phase ∧ bit n v=!phase := by
  by_cases used : ∃ p n, H.owns v p n
  · obtain ⟨p0,n0,start⟩ := used
    refine ⟨bit p0 v,?_⟩
    intro p n here
    have d1 := (H.valid here).2.1
    have d2 := (H.valid (H.rect start here)).2.1
    cases z : bit p0 v <;> cases q : bit p v <;> cases r : bit n v <;> simp_all
  · exact ⟨false,fun h => False.elim (used ⟨_,_,h⟩)⟩

theorem polarOuterOwn {S T} (F : PolarFactor S T) {w p n} (wo : w∈F.outer)
    (one : polarOnly true S T w p n) : F.outside.owns w p n := by
  rcases F.outside.total p n one.1 one.2.1 with d | ⟨v,hv⟩
  · exact False.elim (Finset.disjoint_left.mp F.apart ((polarPair F one).mp d) wo)
  · have vs : v∈S := F.cover ▸ Finset.mem_union_right _ (F.outside.valid hv).1
    exact (one.2.2 v vs (F.outside.valid hv).2) ▸ hv

theorem polarInnerPhase {S T} (F : PolarFactor S T) {w : Sig} (wi : w∈F.inner) :
    ∃ phase : Bool, ∀ {p n}, polarOnly true S T w p n → (bit p F.pivot == phase)=bit p w := by
  obtain ⟨phase,dir⟩ := roomPhase F.inside w
  refine ⟨phase,?_⟩
  intro p n one
  have d := (polarPair F one).mpr wi
  have found {r s} (hp : bit r F.pivot=true) (hn : bit s F.pivot=false)
      (only : ∀ u∈F.inner, bit r u≠bit s u → u=w) : F.inside.owns w r s := by
    apply polarOwn F.inside
    exact ⟨hp,hn,fun u hu diff => only u hu diff.1⟩
  have whole {v} (h : v∈F.inner) : v∈S := F.cover ▸ Finset.mem_union_left _ h
  cases hp : bit p F.pivot
  · have hn : bit n F.pivot=true := by cases q : bit n F.pivot <;> simp_all
    have owns := found hn hp (fun v vin diff => one.2.2 v (whole vin) ⟨Ne.symm diff,by simp⟩)
    have eq := (dir owns).2
    cases phase <;> simpa using eq.symm
  · have hn : bit n F.pivot=false := by cases q : bit n F.pivot <;> simp_all
    have owns := found hp hn (fun v vin diff => one.2.2 v (whole vin) ⟨diff,by simp⟩)
    have eq := (dir owns).1
    cases phase <;> simpa using eq.symm

theorem polarInnerOwn {S T} (F : PolarFactor S T) {w p n}
    (wi : w∈F.inner) (one : polarOnly true S T w p n) :
    if bit p F.pivot then F.inside.owns w p n else F.inside.owns w n p := by
  have d := (polarPair F one).mpr wi
  have whole {v} (h : v∈F.inner) : v∈S := F.cover ▸ Finset.mem_union_left _ h
  cases hp : bit p F.pivot
  · have hn : bit n F.pivot=true := by cases h : bit n F.pivot <;> simp_all
    apply polarOwn F.inside
    exact ⟨hn,hp,fun v hv dir => one.2.2 v (whole hv) ⟨Ne.symm dir.1,by simp⟩⟩
  · have hn : bit n F.pivot=false := by cases h : bit n F.pivot <;> simp_all
    apply polarOwn F.inside
    exact ⟨hp,hn,fun v hv dir => one.2.2 v (whole hv) dir⟩
theorem beqPhaseInject {p q r : Bool} (h : (p==r)=(q==r)) : p=q := by
  cases p <;> cases q <;> cases r <;> simp_all

theorem polarOutsideCross {S T} (F : PolarFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (ao : a∈F.outer) (bo : b∈F.outer)
    (c1 : polarOnly true S T a p na) (c2 : polarOnly true S T b p nb)
    (c3 : polarOnly true S T a pa n) (c4 : polarOnly true S T b pb n) : False :=
  different (F.outside.unique (F.outside.rect (polarOuterOwn F ao c1) (polarOuterOwn F ao c3))
    (F.outside.rect (polarOuterOwn F bo c2) (polarOuterOwn F bo c4)))

theorem polarInsideCross {S T} (F : PolarFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (ai : a∈F.inner) (bi : b∈F.inner)
    (c1 : polarOnly true S T a p na) (c2 : polarOnly true S T b p nb)
    (c3 : polarOnly true S T a pa n) (c4 : polarOnly true S T b pb n)
    (matchA : bit p a=bit pa a) (matchB : bit p b=bit pb b) : False := by
  obtain ⟨sa,qa⟩ := polarInnerPhase F ai
  obtain ⟨sb,qb⟩ := polarInnerPhase F bi
  have sameA := beqPhaseInject ((qa c1).trans (matchA.trans (qa c3).symm))
  have sameB := beqPhaseInject ((qb c2).trans (matchB.trans (qb c4).symm))
  have h1 := polarInnerOwn F ai c1
  have h2 := polarInnerOwn F bi c2
  have h3 := polarInnerOwn F ai c3
  have h4 := polarInnerOwn F bi c4
  rw [←sameA] at h3
  rw [←sameB] at h4
  cases h : bit p F.pivot
  · simp only [h,Bool.false_eq_true,ite_false] at h1 h2 h3 h4
    exact different (F.inside.unique (F.inside.rect h3 h1) (F.inside.rect h4 h2))
  · simp only [h,ite_true] at h1 h2 h3 h4
    exact different (F.inside.unique (F.inside.rect h1 h3) (F.inside.rect h2 h4))

theorem polarBinate {S T} (F : PolarFactor S T) {w p p' n n'} (ws : w∈S)
    (h : polarOnly true S T w p n) (j : polarOnly true S T w p' n')
    (different : bit p w≠bit p' w) : w∈F.inner := by
  by_contra no
  rw [←F.cover,Finset.mem_union] at ws
  have out := ws.resolve_left no
  obtain ⟨phase,dir⟩ := freePolarPhase F.outside w
  exact different ((dir (polarOuterOwn F out h)).1.trans (dir (polarOuterOwn F out j)).1.symm)

theorem polarOpposite {S T} (F : PolarFactor S T) {a b p n pa pb na nb}
    (different : a≠b) (hs : a∈S) (ht : b∈S)
    (c1 : polarOnly true S T a p na) (c2 : polarOnly true S T b p nb)
    (c3 : polarOnly true S T a pa n) (c4 : polarOnly true S T b pb n)
    (matchA : bit p a=bit pa a) (matchB : bit p b=bit pb b) :
    (a∈F.inner) ↔ (b∉F.inner) := by
  constructor
  · intro aIn bIn
    exact polarInsideCross F different aIn bIn c1 c2 c3 c4 matchA matchB
  · intro bOut
    by_contra aOut
    rw [←F.cover,Finset.mem_union] at hs ht
    exact polarOutsideCross F different (hs.resolve_left aOut) (ht.resolve_left bOut) c1 c2 c3 c4

theorem polarOddThree (A B C : Prop) (ab : A ↔ ¬B) (bc : B ↔ ¬C) (ca : C ↔ ¬A) : False := by
  by_cases a : A
  · have c : ¬C := fun c => ca.mp c a
    exact ab.mp a (bc.mpr c)
  · have c := ca.mpr a
    have b : ¬B := fun b => bc.mp b c
    exact a (ab.mpr b)
theorem polarOddFive (A B C D E : Prop) (ab : A ↔ ¬B) (bc : B ↔ ¬C) (cd : C ↔ ¬D)
    (de : D ↔ ¬E) (ea : E ↔ ¬A) : False := by
  by_cases a : A
  · have e : ¬E := fun e => ea.mp e a
    have d := de.mpr e
    have c : ¬C := fun c => cd.mp c d
    exact ab.mp a (bc.mpr c)
  · have e := ea.mpr a
    have d : ¬D := fun d => de.mp d e
    have c := cd.mpr d
    have b : ¬B := fun b => bc.mp b c
    exact a (ab.mpr b)

def oddLink (ws : List Sig) (T a b : Sig) (rows : Nat) :=
  let r := kwProbe rows
  (decide (a∈ws ∧ b∈ws ∧ a≠b) && ((bit (r 0) a==bit (r 1) a) && (bit (r 0) b==bit (r 2) b))) &&
    ((polarCell ws T a (r 0) (r 4) && polarCell ws T b (r 0) (r 5)) &&
     (polarCell ws T a (r 1) (r 3) && polarCell ws T b (r 2) (r 3)))
theorem oddLink_sound {ws T a b rows} (F : PolarFactor (List.toFinset ws) T)
    (h : oddLink ws T a b rows=true) : a∈F.inner ↔ b∉F.inner := by
  obtain ⟨mem,one⟩ := panelAnd h
  obtain ⟨ma,ph⟩ := panelAnd mem
  obtain ⟨am,bm,diff⟩ := of_decide_eq_true ma
  obtain ⟨left,right⟩ := panelAnd one
  exact polarOpposite F diff (List.mem_toFinset.mpr am) (List.mem_toFinset.mpr bm)
    (polarCell_sound (panelAnd left).1) (polarCell_sound (panelAnd left).2)
    (polarCell_sound (panelAnd right).1) (polarCell_sound (panelAnd right).2)
    (beq_iff_eq.mp (panelAnd ph).1) (beq_iff_eq.mp (panelAnd ph).2)
def oddCheck (ws : List Sig) (T : Sig) (k n : Nat) (labels rows : Nat→Nat) :=
  decide (k≤ws.toFinset.card) && (n==3 || n==5) &&
    (List.range n).all (fun i => oddLink ws T (ws.getD (labels i) zero)
      (ws.getD (labels ((i+1)%n)) zero) (rows i))
theorem oddCheck_sound {ws T k n labels rows} (ok : oddCheck ws T k n labels rows=true) :
    Impossible true T k ws.toFinset := by
  obtain ⟨budget,links⟩ := panelAnd ok
  intro j hj live
  obtain ⟨F⟩ := polarOneShare live (hj.trans (of_decide_eq_true (panelAnd budget).1))
  have edge (i : Nat) (bound : i<n) := oddLink_sound F
    (List.all_eq_true.mp links i (List.mem_range.mpr bound))
  have ar : n=3 ∨ n=5 := by
    simpa only [Bool.or_eq_true,beq_iff_eq] using (panelAnd budget).2
  rcases ar with rfl | rfl
  · exact polarOddThree _ _ _ (edge 0 (by decide)) (edge 1 (by decide)) (edge 2 (by decide))
  · exact polarOddFive _ _ _ _ _ (edge 0 (by decide)) (edge 1 (by decide))
      (edge 2 (by decide)) (edge 3 (by decide)) (edge 4 (by decide))
def monoLink (ws : List Sig) (T a b : Sig) (rows : Nat) :=
  let r := kwProbe rows
  (decide (a∈ws ∧ b∈ws ∧ a≠b) && ((bit (r 0) a==bit (r 1) a) && (bit (r 0) b==bit (r 2) b))) &&
    ((kwWireB ws T a (r 0) (r 4) && kwWireB ws T b (r 0) (r 5)) &&
     (kwWireB ws T a (r 1) (r 3) && kwWireB ws T b (r 2) (r 3)))
theorem monoLink_sound {ws T a b rows} (F : SingleFactor (List.toFinset ws) T)
    (h : monoLink ws T a b rows=true) : a∈F.inner ↔ b∉F.inner := by
  obtain ⟨mem,one⟩ := panelAnd h
  obtain ⟨am,bm,diff⟩ := of_decide_eq_true (panelAnd mem).1
  obtain ⟨left,right⟩ := panelAnd one
  have bad := parityRule F (List.mem_toFinset.mpr am) (List.mem_toFinset.mpr bm) diff
    (kwWireB_sound (panelAnd left).1) (kwWireB_sound (panelAnd left).2)
    (kwWireB_sound (panelAnd right).1) (kwWireB_sound (panelAnd right).2)
  tauto
def monoCheck (ws : List Sig) (T : Sig) (k n : Nat) (labels rows : Nat→Nat) :=
  decide (k≤ws.toFinset.card) && (n==3 || n==5) &&
    (List.range n).all (fun i => monoLink ws T (ws.getD (labels i) zero)
      (ws.getD (labels ((i+1)%n)) zero) (rows i))
theorem monoCheck_sound {ws T k n labels rows} (ok : monoCheck ws T k n labels rows=true) :
    Impossible false T k ws.toFinset := by
  obtain ⟨budget,links⟩ := panelAnd ok
  intro j hj live
  obtain ⟨F⟩ := oneShare live (hj.trans (of_decide_eq_true (panelAnd budget).1))
  have edge (i : Nat) (bound : i<n) := monoLink_sound F
    (List.all_eq_true.mp links i (List.mem_range.mpr bound))
  have ar : n=3 ∨ n=5 := by
    simpa only [Bool.or_eq_true,beq_iff_eq] using (panelAnd budget).2
  rcases ar with rfl | rfl
  · exact polarOddThree _ _ _ (edge 0 (by decide)) (edge 1 (by decide)) (edge 2 (by decide))
  · exact polarOddFive _ _ _ _ _ (edge 0 (by decide)) (edge 1 (by decide))
      (edge 2 (by decide)) (edge 3 (by decide)) (edge 4 (by decide))
def cycleTest (u : Bool) (ws : List Sig) (T : Sig) (k code : Nat) : Bool :=
  let n := if code.testBit 20 then 5 else 3
  let labels := fun i => (code >>> (4*i)) &&& 15
  let rows := fun i => (code >>> (21+54*i)) &&& 18014398509481983
  if u then oddCheck ws T k n labels rows else monoCheck ws T k n labels rows
theorem cycleTest_sound {u ws T k code} (h : cycleTest u ws T k code=true) :
    Impossible u T k ws.toFinset := by
  cases u
  · exact monoCheck_sound h
  · exact oddCheck_sound h
abbrev HornGroups := BitVec 16
abbrev HornSlot := Fin 4
def hornActive (s : BitVec 4) (w : HornGroups) := w.getLsbD s.toNat=true
def hornMask (i : HornSlot) : HornGroups :=
  BitVec.ofNat 16 (((2^16-1)/(2^(2^i.val)+1)) <<< (2^i.val))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem hornMask_at : ∀ (s : BitVec 4) (i : HornSlot), hornActive s (hornMask i) ↔ s.getLsbD i.val=true := by
  have table : ∀ (j : Fin 16) (i : Fin 4), (hornMask i).getLsbD j.val=j.val.testBit i.val := by
    decide +kernel
  intro s i
  have row := table ⟨s.toNat,s.isLt⟩ i
  change (hornMask i).getLsbD s.toNat=s.toNat.testBit i.val at row
  rw [BitVec.testBit_toNat] at row
  unfold hornActive
  rw [row]

def hornAssignment (A : Finset Sig) (wire : HornSlot→Sig) : BitVec 4 :=
  (BitVec.ofBoolListLE (List.ofFn (fun i : HornSlot => decide (wire i∈A)))).cast List.length_ofFn

theorem hornAssignment_at (A : Finset Sig) (wire : HornSlot→Sig) (i : HornSlot) :
    hornActive (hornAssignment A wire) (hornMask i) ↔ wire i∈A := by
  rw [hornMask_at]
  simp only [hornAssignment,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]

theorem hornNever (s : BitVec 4) : ¬hornActive s 0 := by simp [hornActive]
theorem hornAlways (s : BitVec 4) : hornActive s (BitVec.allOnes 16) := by
  have bound : s.toNat<16 := s.isLt
  unfold hornActive
  rw [BitVec.getLsbD_allOnes]
  simp [bound]
theorem hornAnd (s : BitVec 4) (a b : HornGroups) : hornActive s (a &&& b) ↔ hornActive s a ∧ hornActive s b := by
  simp only [hornActive,BitVec.getLsbD_and,Bool.and_eq_true]
theorem hornOr (s : BitVec 4) (a b : HornGroups) : hornActive s (a ||| b) ↔ hornActive s a ∨ hornActive s b := by
  simp only [hornActive,BitVec.getLsbD_or,Bool.or_eq_true]
theorem hornNot (s : BitVec 4) (a : HornGroups) : hornActive s (~~~a) ↔ ¬hornActive s a := by
  have bound : s.toNat<16 := s.isLt
  simp [hornActive,BitVec.getLsbD_not,bound]

def hornCase (ws : List Sig) (T : Sig) (wire : HornSlot→Sig) (a b c : HornSlot)
    (p n na nb pa pb : Row) (parity : Bool) : HornGroups :=
  let A := wire a
  let B := wire b
  if parity then
    if decide (A∈ws) && decide (B∈ws) && decide (A≠B) &&
       kwWireB ws T A p na && kwWireB ws T B p nb &&
       kwWireB ws T A pa n && kwWireB ws T B pb n then
      (hornMask a &&& hornMask b) ||| (~~~(hornMask a) &&& ~~~(hornMask b)) else 0
  else if kwWireB ws T A p na && kwWireB ws T B pa n && kwWireB ws T (wire c) p n then
    (hornMask a &&& hornMask b) &&& ~~~(hornMask c) else 0

theorem hornCase_sound {ws T wire a b c p n na nb pa pb parity}
    (F : SingleFactor (List.toFinset ws) T) :
    ¬hornActive (hornAssignment F.inner wire) (hornCase ws T wire a b c p n na nb pa pb parity) := by
  intro active
  cases parity
  · simp only [hornCase,Bool.false_eq_true,ite_false] at active
    split at active
    next h =>
      simp only [Bool.and_eq_true] at h
      simp only [hornAnd,hornNot,hornAssignment_at] at active
      exact active.2 (hornRule F (kwWireB_sound h.1.1) (kwWireB_sound h.1.2) (kwWireB_sound h.2) active.1.1 active.1.2)
    next => exact hornNever _ active
  · simp only [hornCase,ite_true] at active
    split at active
    next h =>
      simp only [Bool.and_eq_true,decide_eq_true_eq] at h
      simp only [hornOr,hornAnd,hornNot,hornAssignment_at] at active
      exact parityRule F (List.mem_toFinset.mpr h.1.1.1.1.1.1)
        (List.mem_toFinset.mpr h.1.1.1.1.1.2) h.1.1.1.1.2
        (kwWireB_sound h.1.1.1.2) (kwWireB_sound h.1.1.2) (kwWireB_sound h.1.2) (kwWireB_sound h.2) active
    next => exact hornNever _ active

def hornWire (ws : List Sig) (core : Nat) (i : HornSlot) := ws.getD ((core >>> (4*i.val)) &&& 15) zero
def hornWord (_pos _neg : Nat) (ws : List Sig) (T : Sig) (core r : Nat) :=
  let slot := fun i => Fin.ofNat 4 ((r >>> (2*i)) &&& 3)
  let row := kwProbe (r >>> 7)
  hornCase ws T (hornWire ws core) (slot 0) (slot 1) (slot 2)
    (row 0) (row 1) (row 2) (row 3) (row 4) (row 5) (r.testBit 6)
def hornCollect (pos neg : Nat) (ws : List Sig) (T : Sig) (core : Nat) : Nat → Nat → HornGroups
  | 0,_ => 0
  | n+1,data => hornWord pos neg ws T core (data &&& 2305843009213693951) |||
      hornCollect pos neg ws T core n (data >>> 61)
theorem hornCollect_sound {pos neg ws T core} (F : SingleFactor (List.toFinset ws) T) (n data : Nat) :
    ¬hornActive (hornAssignment F.inner (hornWire ws core)) (hornCollect pos neg ws T core n data) := by
  induction n generalizing data with
  | zero => exact hornNever _
  | succ n ih =>
    intro h
    rcases (hornOr _ _ _).mp h with cur | rest
    · exact hornCase_sound F cur
    · exact ih _ rest

theorem hornReplay {pos neg ws T core cap count data} (budget : cap≤(List.toFinset ws).card)
    (rejected : hornCollect pos neg ws T core count data=BitVec.allOnes 16) :
    Impossible false T cap ws.toFinset := by
  intro k hk live
  obtain ⟨F⟩ := oneShare live (hk.trans budget)
  have contra := hornCollect_sound (pos:=pos) (neg:=neg) (core:=core) F count data
  rw [rejected] at contra
  exact contra (hornAlways _)
def hornTest (u : Bool) (ws : List Sig) (T : Sig) (k code : Nat) :=
  if u then false else decide (k≤ws.toFinset.card) &&
    (hornCollect 0 0 ws T code ((code >>> 16) &&& 7) (code >>> 19)==BitVec.allOnes 16)
theorem hornTest_sound {u ws T k code} (h : hornTest u ws T k code=true) :
    Impossible u T k ws.toFinset := by
  cases u
  · obtain ⟨hb,hr⟩ := panelAnd h
    exact hornReplay (pos:=0) (neg:=0) (core:=code) (count:=(code >>> 16) &&& 7) (data:=code >>> 19)
      (of_decide_eq_true hb) (beq_iff_eq.mp hr)
  · simp [hornTest] at h
end SingleRead
def cycleCodes : Array Nat := #[0x4001040245021040800221048a00208100a04209000210,0x4041240245021240808221048a00248100a04209000321,0x40416422550a12428082a144aa002c8500a04209400432,0x4141a40245021a40828221048a00348100a04209000432,0x4141e422550a1a428282a144aa003c8500a04209400543,0x60110c06470310c0c022310c8e02218100a04219000420,0x60512c06470312c0c0a2712c9e02258181e0e259000531,0x60512c06470312c0c0832184ce02258104a24319000642,0x60512c06470312c0c0a2310c8e02258181e0e259000642,0x303032492d118324606038184226060a60323830b24c0c170b25d041648c0503064b41530,0x601142c175b3042c30223908c326024860323830924c00391c2ed0308c180d0608c561320,0x49058c26570a58c2c022310c8e02298504a24319400642,0x60114c064703106092032184cb02298504a24319400642,0x60114c26570b10c2c022310c8e02298500a04219400642,0x60114c06470310c2c022b14cae02298500a04219400642,0x60114c06470310c2c022310c8e02298500a04219400642,0x3cc18160e0c8c60616030584233081e8a473288c00763,0x309172492d918724306038184326060a60323830b24c08391c2ed041648c0503064b52640,0x60516c06470312c292032184ca00b0c104a2430d000642,0x60516c064703126092032184cb00b0c104a2430d000753,0x60516c26560b12609222310c8b022d8504a24319400753,0x60516c26560b126092032184cb00b0c10422430d000643,0x490586034582586092032184cb022d8500a04219400753,0x60516c06470312c2922231048a00b0c10422430d000753,0x30b032492d918324306038184326060a60323830b24c08391c2ed041648c0703064b52640,0x60516c06470312c292032184ca00b0c104a2430d000642,0x49058c26540a5860c0a2210c8a022d8580e06219400753,0x60516c26560b12609222310c8b022d8504a24319400753,0x309172492d91860f61221908c236060a60223830b24c08391c2ad060648c0703064347530,0x60516c06470312c292032184ca003d8504a24309400753,0x60516c0647031260920b2586cb00b0c124b24b0d000753,0x60516c06470312c292032184ca00b0c104a2430d000753,0x4905860345825860920b2586cb00b0c104a2430d000753,0x60516c064703126092032184cb00b0c104a2430d000753,0x60516c064703126092032184cb00b0c104a2430d000753,0x49058c064702586092032184cb00b0c104a2430d000753,0x30b032492d118324616038184226060a60323830b24c08391c2ed041648c0503064b52640,0x30b032492d918324306038184326060a60323830b24c08391c2ed041648c0703064b52640,0x30b032492d918324306038184326060a60323830a2c458391c2e5403c58c0503045b52640,0x30b032492d918324306038184326060a60323830b24c0c170b25d041648c0703064b52640,0x30b032492d918324306038184326060a60323830b24c0c170b25d041648c0703064b52640,0x6051670394c3063c9222210989a308a5048a211a43c45949a47254148e181d0e0ce567530,0x60516c06450312c2c0a2210c8a022d8500a04219400642,0x60516502c4431270922231048b022d8504224319400642,0x60516502c44312709222310c8b022d8504224319400642,0x60516502c44312709222310c8b022d8504224319400642,0x22d850422431958145940b110c49c24888c4322c000864,0x6051670394d306709222310989a308a5249a281a47061149a47270148e18050608e573641,0x605167039443063c9222310989a308a5048a611a47061149a47270148e18050608e562530,0x309163c1e9e1861f29221908c2b6060a522b34b0a7061149a4727041648c0703064b47530,0x605167039443063c9222310989a308a5048a611a47061149a47270148e18050608e562531,0x309163c1e9e1863c38221908c3a6060a502a3430a7061149a4727041648c0703064b47530,0x4920ac060b824ac238148e4d2704170270781d30a701e22118c83a22d8524b24958785740,0x605167039443063c9222310989a308a5048a611a47061149a47270148e18050608e563841,0x605167039443063c9222310989a308a5249a281a47061149a47270148e18050608e562530,0x309172492d91863c38229948e3a22c3e502a3411e7061149a4727041648c0703064b47530,0x309172492d91863c38221908c3a22c3e502a3411e7061149a4727041648c0703064b47530,0x605167039443063c9222310989a308a5249a281a47061149a47270148e18050608e568531,0x1c0a580c1280e4c238148e4d2701498524d24d1a5241e22131889a22f0270881cb0785361,0x605167039443063c9222310989a308a5249a281a47061149a47270148e18050608e563541,0x6060a502a3430a3c45949a4725441648c23130e4ac245c924a64618f0e08864230e942730,0x6051670394c3063c9222310989a308a5048a611a43c45949a47254148e18190e0ce551420,0x6051670394c3063c9222310989a308a5048a611a43c45949a47254148e18190e0ce558420,0x1c0a581c1c84e48b1e148e4d2541498504c2451a5241e22131889a22f0270981cb0784250,0x6051670394c3063c9222310989a308a5048a611a43c45949a47254148e18190e0ce552830,0x6051670394c3063c9222310989a308a5048a611a43c45949a47254148e18190e0ce562530,0x4920ac26198a4a8b1e148e4d2544170250681530a701e22118c83a22d8524324958778240,0x4920ac26198a4a8b1e148e4d2544170250681530a701e22118c83a22d8524324958775240,0x309163c1ecd1863c38223908c3a6060a502a3430a3c45949a4725441648c23130e4b62540,0x309172492991863c38221908c3a6060a502a3430a3c45949a4725441648c23130e4b52640,0x6051670394c3063c9230b04d29a308a5048a611a43c45949a47254148e18190e0ce562530,0x309172492991863c38221908c3a6060a502a3430a3c45949a4725441648c23130e4b41530,0x22d8524b24b195241e140b110961c2481888162c000764,0x1c0788846320e88b61490c92561c920ac060b824ac238148e4d2704170250681530b86340,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce552430,0x6051670394c3063c9222310989a308a5048a611a524c0949a472d0148e180d0608e582530,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce552430,0x6051670394c3063c9222310989a308a5048a611a524c0949a472d0148e180d0608e582530,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce557430,0x1c0a581c1c84e4c238148e4d2701498504c2451a5241e22131889a22f0270981cb0774350,0x6051670394c3063c9222310989a308a5048a611a524c0949a472d0148e180d0608e583570,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce553840,0x6051670394c3063c9222310989a308a5048a611a524c0949a472d0148e180d0608e583740,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b82470,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b72860,0x1c0788846320e88b61490c92561c920ac060b824ac238148e4d2704170250681530b67340,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce552430,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce552430,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce558430,0x1c0a581c1c84e4c238148e4d2701498504c2451a5241e22131889a22f0270981cb0784350,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce553840,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b61430,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b61430,0x4920ac060b824ac238148e4d2704170250681530a701e22118c83a22d8524324958784160,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b61840,0x4920ac060b824ac238148e4d2704170250681530a701e22118c83a22d8524324958784260,0x1c0a581c1c84e48b1e148e4d2541498504c2451a5241e22131889a22f0270981cb0774250,0x6051670394c3063c9222310989a308a5048a611a43c45949a47254148e18190e0ce552730,0x4920ac26198a4a8b1e148e4d2544170250681530a701e22118c83a22d8524324958767240,0x4920ac26198a4a8b1e148e4d2544170250681530a701e22118c83a22d8524324958767240,0x60516c06470312c2c0a2310c8e022d8580e06219400653,0x309172492911863c3860381843a22c3e502a3411e3c45949a4725441648c0503064b52640,0x60516c06470312c2c0a2310c8e022d8500a04219400753,0x6058470395c3043c9222210989a308a5048a211a43c45949a47254148e180d0608e578641,0x49078c06450258c2c0a2210c8a022d8500a04219400753,0x60516c06470312c2c0a2310c8e022d8500a04219400653,0x49078502c5425870c08623058a022d8500a04219400853,0x60516c06470312c2c0a2310c8e022d8500a04219400753,0x60516c06470312c2c0a2310c8e022d8500a04219400753,0x60516c06470312c2c0a2310c8e022d8580e06219400753,0x49078c06450258c2c0a2210c8a022d8500a04219400753,0x49078c06470258c2c08623058e00f0e100a0420f000753,0x60516c06470312c2c0a2310c8e022d8580e06219400963,0x49078502c4425870c0a2210c8a022d8580e06219400863,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x6051670394c3063c9222210989a308a5048a211a43c45949a4325407c7981d0e0c7d73640,0x60516c06450312c2c0a2210c8a022d8500a04219400752,0x6060a502a3430a3c45949a4325441648c0503064ac245c924b6461c90e08864230c964951,0x60516522d44b12709222310c8b022d8504224319400753,0x60516c06470312c2c0a2310c8e022d8580e06219400863,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x60516c26560b12c2c0a2b14cae022d8580e06219400763,0x49078502c342583c45949a4728422f02c0f03231200973,0x1c0792496590f124380f0f93cb022f0250881631200863,0x49078502c4425870920f2787cb00f0e10422430f000753,0x49078703c5c25870920f2787cb00f0e124b24b0f000642,0x49078703c5c25870920f2787cb00f0e124b24b0f000953,0x60516502c4431270922231048b00f0e10422430f000753,0x60516502c44312709222310c8b022d858160e259400753,0x49078502c4425870920f2787cb00f0e124b24b0f000753,0x60516502c44312709222310c8b022d8504224319400753,0x60516522d44b12709222310c8b022d8504224319400753,0x3091780c4701958161229958ae022f02c0e03231200763,0x6051670394c3063c9222310989a308a5249a691a524c0949a472d0148e180d0608e573640,0x6058470394c3043c9230b04d29a308a5048a611a524c0949a472d0148e180d0608e573640,0x309172492991863c38221908c3a60648502a3430924c0949a472d060648c0703064351640,0x30b032492d91823c3860583853a6060a502a3430b24c0949a472d041648c0703064b58640,0x309172492991863c38221908c3a60648502a3430924c0949a472d060648c0703064352640,0x30b032492991823c3860583853a6060a502a3430b24c0949a472d041648c0703064b52640,0x49078c06470258c2c08f2787ce00f0e180e0620f000763,0x1c0792496590f124380f0f93cb022f0250a81631200962,0x49078502c5425870920f2787cb00f0e100a0420f000752,0x60516c06470312c2922231048a00f0e10422430f000863,0x309172492d91863c38221908c3a60648502a343087061149a4727022c78c0703045359640,0x30b032492d91823c3860583853a6060a502a3430a7061149a4727041648c0703064b58640,0x605167039443063c9222310989a308a5048a611a47061149a47270148e18050608e573641,0x605167039443063c9222310989a308a5048a611a47061149a47270148e18050608e573641,0x605167039443063c9222310989a308a5249a281a47061149a47270148e18050608e573641,0x605167039443063c9222310989a22c3f048a611363c458793c3e54148e18050608e573641,0x60516c06470312c2c0a2310c8e022d8580e06219400863,0x6051670394c3063c9222310989a308a5048a611a43c45949a47254148e18190e0ce562530,0x4920ac26198a4a8b1e148e4d2544170250681530a701e22118c83a22d8524324958795240,0x309172492991863c38221908c3a6060a502a3430a3c45949a4725441648c23130e4b52640,0x309172492991863c38221908c3a6060a502a3430a3c45949a4725441648c23130e4b52640,0x309163c1e9f1863c38221908c3a6060a502a3430a3c45949a4725441648c23130e4b82540,0x30b032492d918324386038184326060a502a3430b24c0949a4725441648c0543064b52640,0x22d8500a0421958145b0191c0c4b0b0288c43238000875,0x309163c1e9f1863c38221908c3a6060a502a3430a3c45949a4725441648c23130e4b52640,0x309172492991863c38221908c3a6060a502a3430a3c45949a4725441648c23130e4b52640,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce563540,0x6051670394c3063c9222310989a308a5048a611a524c0949a472d0148e180d0608e593640,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce573640,0x6060a502a3430b24c0949a472d041648c23130e4ac245c924a64618f0e08864230e964851,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b92540,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce573641,0x309172492991863c38221908c3a6060a502a3430a3c45949a4725441648c23130e4b52640,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b92580,0x1c0a581c1c84e4c238148e4d2701498504c2451a5241e22131889a22f0270b81cb0786471,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce573640,0x49078884c622688bc09c26072c19c0a581c1c84e4c238148e4d2701498504c2451a579463,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce573641,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce563540,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b71540,0x309172492991863c38221908c3a6060a502a3430a7061149a4727041648c0703064b72540,0x4920ac060b824ac238148e4d2704170250681530a701e22118c83a22d8524324958795270,0x6051670394c3063c9222310989a308e1249a691a124c0c170b25d0308e180d0608c573640,0x309172492991863c38221908c3a60648703a3c30924c08793c3ed060648c0703064352640,0x60516c06450312c2c0a2310c8a022d8500a04219400752,0x22d8500a0421958145b019140c4b0b0288c43228000975,0x60516c06470312c2c0a2310c8e022d8580e06219400863,0x4143ec0647021ac2c0a221048e007ca500a0420b400863,0x6051670394c3063c9222f169b9a308a5048a611a524c0c170b25d007c7980d06087d73640,0x4920ac26198a4a8b1e148e4d2544170250681530a701e22118c83a22d8524324958785240,0x60516c26560b12709222b14cab022d8504224319400752,0x60516c26560b12709222b14cab022d8504224319400752,0x22d850422431958145b099582c49c2488ac532ac000975,0x60516502c44312709222310c8b022d8504224319400753,0x60516c06470312c2c0a2310c8e022d8580e06219400763,0x60516c06470312c2c0a2310c8e022d8580e06219400863,0x309172492911861f2960381842b22c3e502a3411e3c45949a4325441648c0503064b62750,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x30b032492d918324386038184326060a502a3430b24c0949a432d041648c0503064b62750,0x6058470395c3043c9222210989a308a5048a211a43c45949a4325407c7980d06087d84751,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x49078c06450258c2c0a2210c8a022d8500a04219400863,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x309172492d9187243860381843222c3e502a3411e3c45949a4325441648c0503064b62750,0x309172492d918724386038184326060a703a3c30b24c0c170b25d041648c0503064b62750,0x49078703c5c25870920f2787cb00f0e124b24b0f000753,0x3091780c4701958161229958ae022f02c0e03231200873,0x60516c0647031270920f2787cb00f0e124b24b0f000863,0x60516c06470312c2c0a2310c8e022d8580e06219400863,0x49078c06470258c2c08f2787ce00f0e100a0420f000863,0x4143ec0645021ac2920f2387ca00f0e124b24b0f000863,0x60516c0647031270920f2787cb00f0e124b24b0f000863,0x1c0792496590f124380f0f93cb00f24870b81e25800a73,0x49078c0647025870920f2787cb00f0e124b24b0f000863,0x49078703c5c25870920f2787cb022d8504224319400863,0x49078703c5c25870920f2787cb00f0e124b24b0f000753,0x49078703c5c25870920f2787cb00f0e124b24b0f000753,0x49078703c5c25870920f2787cb00f0e124b24b0f000753,0x49078703c5c25870920f2787cb00f0e124b24b0f000753,0x3091780c4701958161229958ae022f02c0e03231200873,0x1c0792496590f124380f0f93cb00f248c0e03225800973,0x309172492991863c38221908c3a60648502a3430924c0949a472d060648c0703064362750,0x30b032492991823c3860583853a6060a502a3430b24c0949a472d041648c0703064b62750,0x30b032492d9183243860381843260648502a3430924c0949a472d060648c0703064362750,0x30b032492d918324386038184326060a502a3430b24c0949a472d041648c0703064b62750,0x60516c06470312c2922231048a00f0e10422430f000863,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x49078c0647025870920f2787cb00f0e100a0420f000863,0x309172492d91863c38221908c3a60648502a343087061149a4727022c78c0703045362750,0x49078c06470258c2c08f2787ce00f0e180e0620f000863,0x309172492d91863c3860381843a60648502a3430924c0949a472d060648c0703064362750,0x60516c06470312c2c0a2310c8e022d8580e06219400863,0x60516c06470312c2920f2387ca00f0e124b24b0f000863,0x30b032492d91823c3860583853a6060a502a3430a7061149a4727041648c0703044b62750,0x49078c06470258c2c08f2787ce00f0e100a0420f000863,0x49078c06470258c2c08f2787ce00f0e100a0420f000863,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce584751,0x6058470395c304709230380d098308a5048a611a47061149a47270148e18190e0ce584751,0x30b032492d918324386038184326060a502a3430b24c0949a472d041648c0703064b62750,0x6051670394c3063c9222310989a308a5048a611a47061149a47270148e18190e0ce584751,0x6058470395c304709230380d098308a5048a611a47061149a47270148e18190e0ce584751,0x60516c26560b12709222b14cab022d8504224319400863,0x60516c06450312c2c0a2310c8a022d8500a04219400863,0x60516c06470312c2c0a2310c8e022d8580e06219400863,0x30b032492d9183243860381843260648502a2430924c09492432d060648c0703064362750,0x4143ec0647021ac2c0a221048e007ca500a0420b400863,0x30b032492d918324386038184326060a502a3430b24c0949a472d041648c0703064b62750,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x60516c06470312c2c0a231048a00f0e180a0620b000863,0x4143ec0645021ac2c0a221048a007ca500a0420b400863,0x60516c06470312c2c0a231048a007ca500a0420b400863,0x60516c06470312c2c0a2310c8e022d8580e06219400863,0x60516c26560b12709222b14cab022d8504224319400863,0x60516c26560b12709222b14cab022d8504224319400863,0x4143ec0647021ac2c0a221048e007ca500a0420b400863,0x60516c06470312c2c0a2310c8e022d8500a04219400863,0x30b032492d918324386038184326060a502a3430b24c0949a472d041648c0703064b62750,0x309072492d918624306078385326060a60323830b20c04170b25d041648c27130e4b42630,0x309072492d9187806020d8783e020f0260b018b06602160707a13141648c27130e4b46130,0x4920ac261b8a4b80904164b85d04170260701930a42036070bc12320d8524b24958764230,0x60506603158306609020f06c3b020d8524b2495872482b0986e292908c181d0e0cc553620,0x309072492d9187203001c8f07b001e0a60b018a0e24034160f251341648c27130e4b45130,0x309072492d9187203020d8783b020f0260b018b06602160707a13141648c27130e4b45130,0x60506603158306609020f06c3b020d8524b2495872482b0986e292908c181d0e0cc553620,0x309072492d9187806020d8783e020f0260b018b06602140607213141648c27130e4b46130,0x309072492d918624306078385326060a60323830b20c04170b25d041648c27130e4b42630,0x60506603158306609020f06c3b020d8524b2495872482b0986e292908c181d0e0cc553620,0x309072492d9187806020d8783e020f0260b018b06602160707a13141648c27130e4b35120,0x60506603158306609020f06c3b020d8524b2495872482b0986e292908c181d0e0cc553620,0x309072492d918624306038184326020860323830920c04170b25d041648c27130e4b42530,0x309072492d9187806020d8783e020f0260b018b06602160707a13141648c27130e4b46130,0x309072492d9187203020d8783b020f0260b018b06602160707a13141648c27130e4b46130,0x309072492d9187806020d8783e001e0a60b018a0e60214160f253141648c27130e4b46130,0x309072492d9187806020d8783e001e0a60b018a0e60214160f253141648c27130e4b46130,0x309072492d9187806020d8783e020f0260b018b0660214160f253141648c27130e4b46130,0x6050670395c306349220f06939a308a5058ae15a420404170b2550148e181d0e0ce556420,0x30906341a9d187806020d8783e020f0270b81cb06702960707a13941648523914e4b46130,0x30906341a9d186343860783853a6060a522b34b0b20c04170b25d041648523914e4b31420,0x309072492dd187806020d8783e020f0270b81cb06340b60707a11b41648c27930e4b46130,0x309072492d9187806020d8783e020f0270b81cb06702960707a13941648c27130e4b46130,0x6060a522b34b0a5261493493469490688349e0e68408020f06c3a0058a581e0e14ad72541,0x6060a522b34b0a52614170b156949068c26970a68609020f06c3b00d0e08361a1ce941530,0x6050670395c306349230b84d29a308a5249a691a460604170b2570148e181d0e0ce551420,0x6050670395c306349230b84d29a308a5249a691a520c0949a472d0148e181d060ce562530,0x6060a703a3c30a526149349346949068c26970a68609020f06c3b00d0e181e0e14e941530,0x6060a703a3c30a526149349346949068c26970e68c0c08d26874e08d0e181e0e14e952641,0x6060a522b34b0a526149349346949068c26970a68609020f06c3b00d0e181e0e14e941530,0x6060a522b34b0a52614170b156949068c26970a68609020f06c3b00d0e181e0e14e941530,0x6050670395c306349230b84d29a308a52098681a460604170b2570148e181d0e0ce551420,0x6050670395c306349230b84d29a308a5249a691a520c04170b25d0148e181d0e0ce562530,0x6050670395c306349230b84d29a308a5249a691a520c04170b25d0148e181d0e0ce562530,0x309072492d9187806020d8783e020f0270b81cb06702960707a13941648c27130e4b46130,0x6050670395c306349230b84d29a308a5249a691a460604170b2570148e181d0e0ce562530,0x308a5249a691a52482149a472d20c10124c24d12000743,0x6050670395c306349230b84d29a308a5249a691a520c04170b25d0148e181d0e0ce551420,0x309072492d9186343860783853a6060a522b34b0b20c04170b25d041648c27130e4b41530,0x6050670395c306349230b84d29a308a5058ae15a460604170b2570148e10592c1ce551420,0x4920ac261b8a4ac2414164b457104ca524b2494a600730,0x6050670395c306349230b84d29a308a5249a691a460604170b2570148e10592c1ce551420,0x309072492d9187002020d8783a020f0270b81cb0670294160f253941648c27130e4b35720,0x309072492d9187806020d8783e020f02349a0db0670294160f253941648c27130e4b46130,0x60506341b4d306349220f06939a308a5249a691a460604170b2570148e10592c1ce551420,0x49202c261b1a4a701a6074be13a20d8524b24958600630,0x309072492d9187806020d8783e001e0a349a0da0e70294160f253941648c27130e4b45130,0x309072492d91878020050a914e001e0a70f81ca0e70294160f253941648c27130e4b45130,0x309072492d9187806020d8783e020f02349a0db06702960707a13941648c27130e4b46130,0x1c0a581c1e84e50592148e45392b09072492d9187203020d8783b020f0270b81cb0776350,0x60506341b4d306c0c020f06c3e020d84343a0d5872482948a67292948e181d0e0ce554630,0x309072492d9187203020d8783b020f0270b81cb0670294160f253941648c27130e4b75160,0x60506341b4d306349220f06939a308a5058ae15a460604170b2570148e10592c1ce552430,0x30906341a9d186343820d86873a6060a703a3c30a60604170b257041648c27130e4b61430,0x6050670395c306349230b84d29a308a5249a691a520c04170b25d0148e181d0e0ce562530,0x308072492e918720c04178b65d0044e0c27130ce200540,0x6050670395c306349220f06939a308a5058ae15a460604170b2570148e181d0e0ce562530,0x30906341a9d1870020050a914a001e0a70b81ca0e702960707a13941648523914e4b46130,0x30906341a9d1870020050a914a001e0a70b81ca0e702960707a13941648523914e4b46130,0x30906341a9d187806020d8783e020f0270b81cb06702960707a13941648523914e4b46130,0x30906341a9d187806020d8783e020f0270b81cb06702960707a13941648523914e4b46130,0x6050670395c306349230b84d29a308a5249a691a520c04170b25d00586981d0e0c6d68531,0x309072492d9187806020d8783e020f0270b81cb06340b60707a11b41648c27130e4b57140,0x30906341a9d187806020d8783e020f0270b81cb06702960707a13941648523914e4b57140,0x6060a522b34b0a526149349346949068c26970a68408020f06c3a0058a581e0e14ad52641,0x309072492d91870020050a914a001e0a349a0da0e340b60707a11b41648c27130e4b57140,0x6050670395c306609005e2e57b004ca524b2494a72482b0986e292948e10592c1ce564730,0x6050670395c306349230b84d29a308a5249a691a46060149a47270148e181d0e0ce562530,0x6050670395c306349230b84d29a308a5249a691a46060149a47270148e10592c1ce562530,0x6050670395c306609020f06c3b020d8524b2495872482948a67292948e10592c1ce564730,0x6060a703a3c30a6060149a4727005468c27130c6ac241c924b64618d0e181e0e14e953741,0x4140e70395c20e609005e2e57b020d8524b2495872482b0986e292948e181d0e0ce564730,0x6050670395c306609020f06c3b004ca524b2494a72482948a67292948e181d0e0ce564730,0x6050670395c306349230b84d29a308a5249a691a46060149a47270148e181d0e0ce562530,0x6050670395c306349230b84d29a308a5249a691a46060149a47270148e181d0e0ce562530,0x6050670395c306349230b84d29a308a5249a691a520c0149a472d0148e181d0e0ce573641,0x1482d81c2e84ad80904164b85d04170270781d30a00642,0x1482d81c2e84ad80904164b85d04170270781d30a00642,0x4142ac26978a2ac09005e2e97f004d0724f24d12600543,0x308a5249a691a5204005d2f37d005248c27134a6800643,0x309072492d9187806020d8783e020f0270b81cb06702960707a13941648c27130e4b57140,0x6060a703a3c30a526149349346949068c26970a6860900d26874b00d0e08361a1ce963752,0x308a5249a691a46060149a472700c10124c24d12000743,0x6050670395c306349230b84d29a308a5249a691a520c0149a472d0148e181d0e0ce563841,0x6050670395c306349230b84d29a308a5249a691a520c0149a472d0148e181d0e0ce562530,0x6050670395c306349230b84d29a308a5249a691a520c0149a472d0148e181d0e0ce563541,0x6050670395c306349230b84d29a308a5249a691a520c0149a472d0148e181d0e0ce573641,0x309072492d9186343860783853a6060a703a3c30b20c04170b25d041648c27130e4b52640,0x49068c26970a68c08000e06c3e00498524b24d1a400653,0x148272492d90a70020050a914a020f0270b81cb0670294160f253941648c27130e4b46130,0x30906341a9d186343820d86873a6060a703a3c30a60604170b257041648c27130e4b47530,0x6050670395c306349230b84d29a308a5249a691a460604170b2570148e10592c1ce562531,0x309072492d91870020050a914a001e0a70b81ca0e70294160f253941648c27130e4b46130,0x309072492d9186343860783853a20c0e703a3c10e6060149a4727041648c27130e4b47530,0x309072492d9187806020d8783e020f0270b81cb0670294160f253941648c27130e4b46130,0x309072492d9187806020d8783e020f0270b81cb0670294160f253941648c27130e4b46130,0x309072492d9186343820d86873a20c0e703a3c10e60604170b257041648c27130e4b47530,0x6060a703a3c30a60404170b4570050e181e0e14e800542,0x30906341add186162920d86872b6060a703a3c30b20c04170b25d041648c27130e4b52640,0x20c0e703a3c10e526149349346949068c26970a68c0c020f06c3e0058a581e0e14ad53642,0x309072492d9187806020d8783e020f02349a0db0670294160f253941648c27130e4b57140,0x309072492d9187203005caf17b001e0a70b81ca0e702960707a13941648c27130e4b57140,0x309072492d9187806020d8783e020f02349a0db06702960707a13941648c27130e4b57140,0x4920a52299ca4a52384164b07396050670395c306609020f06c3b020d8524b24958781640,0x60506341b4d306349220f06939a308a5058ae15a460604170b2570148e10592c1ce563541,0x60506341b4d306349220f06939a308a5058ae15a520c04170b25d0148e10592c1ce583641,0x60506341b4d306349220f06939a308a5058ae15a460604170b2570148e10592c1ce573641,0x60506341b4d306349220f06939a308a5249a691a520c04170b25d0148e181d0e0ce573641,0x30906341a9d186343820d86873a6060a703a3c30a60604170b257041648c27130e4b72540,0x30906341a9d186343820d86873a6060a703a3c30a60604170b257041648c27130e4b72540,0x60506341b4d306349220f06939a308a5058ae15a460604170b2570148e10592c1ce563541,0x148272492d90a78060050a914e001e0a70b81ca0e340b60707a11b05468c27130c6b57140,0x148272492d90a7806005caf17e001e0a70b81ca0e702960707a13941648c27130e4b57140,0x6050670395c306349230b84d29a308a5249a691a520c0149a472d0148e181d0e0ce573641,0x60506341b4d306349220f06939a308a5249a691a520c0149a472d0148e181d0e0ce573641,0x6050670395c30640900d26854a01486181d0e0c6400641,0x308072492e918720c04178b65d0044e0c27130ce200540,0x148272492d90a6162960783852b6060a703a3c30b20c04170b25d041648c27130e4b52640,0x6050670395c306349220f06939a308a5058ae15a46060149a47270148e181d0e0ce573641,0x6050670395c306349230b84d29a308a5058ae15a46060149a47270148e181d0e0ce562530]
def hornCodes : Array Nat := #[0x380002c3011070004c00610188891c06416308c08498ca470b1848a224843098c0c203282ed5431,0x1a0008b1408448012200380444270d02945b085041906221a2ce04210c4488c4e0c208a82ed6540,0x17001842c2431001a0000f300983000d000078b04c380047004900e26594586a2d8505245d92c1c1f248289a463210,0x128001e2413120010c01240389968020e00924144a90006c0041458251c6c16e05842c20cc92c1c1f248289ace3210,0xb20001f24810b00188002c3012090025800610b090b4002a003085048432c1703f022c814cb24b058c292122ce5321,0x310030260208700084000f100889002800082c9042380107004920a21494092e05852420cc92c1c1f248288ace4310,0x41c0124828852000c80082890423a4b07614920a22b26221c16484210c8320960ac212106654310,0x128001e2413120010c01240389968020e00924144a9000680041458251d258383e49051359340b702c216106664310,0x1500184282431001a0000f300883000c8000789044380046004900c2259258383e49051148a2c3516c282922ee4320,0x42400c28090520028400c0908823a844a45e048508ba6412e05842420c822c3516c282922cd6420,0x108001e2011120011801240308968020e0092414429000640041448211d258383e490511593209702c212106664310,0x108001e2011120011801240308968020e0092414429000640041448211d258383e490511593209702c212106664310,0x590018192084700206009240442924303614920222b26221e06484210c8b24960ac292106654310,0x40c0124808852000c800c0890423a4303614920222b26221e06484210c8320960ac212106654310,0x19000c23008830010c009201844b10a25926040aa0dd2181b0a490111487019248c230212ed5310,0x19001813008430010a009201442b10a25926040aa0dc6221e06484210c87019248c230212ed5310,0x40c0124808852000c800c0890423a4303614920222b26221e06484210c8320960ac212106654310,0x40c0124808852000c800c08904238c82582b084841992181b0a490111593110f032421086455410,0x40c0124808852000c800c0890423a4303614920222b22221e06484210c83209702c212106654310,0x40c01248088520008800c089042388825c0b084841992181b0a490111591110f032421086455410,0x40c0124808852000c800c08904238c825c0b084841982181b0a490111593110f032421086455410,0x3400184601106001280124210892000d000610a044380043004900622592181b0a49011148a0c2516c280922ee4320,0x4240124808852000d000c08a04238c443c0c908421906814e05842820cc20c2516c280922ed4320,0x40c0124808852000d000c08a0423a4303614920222b26221e06484210c8340a702c214106654310,0x208001f01811b0040c00c2809052000c400c098082180107003080e41592c1703f022c815d3209702c212106466410,0x40c0124808852000d000c08a04238d029c0b085041992181b0a490111593110f032421086455410,0xc10024980421200608012441210f0004c00c089108840106006040c845ae03249302604259940a985811440a666510,0x2200058402412002a000c2141216802580061490889000e000490c0441ce0324930260424c324b058c292122ce5421,0x408002c21120f0005400610a09086044a45e048508bb64960b185242459940a985811440a656421,0xc10024980421200608012441210f0004c00c089108840106006040c845ae03249302604259940a985811440a666521,0xc10024980421300608012441210d8004c00c089108c40106006040c8472e0324930260425d940a985811440a468621,0x408002c21120f0005400610a09086044a45e048508bb64960b185242459840a985811440a656421,0x618024883112c002180124410892000c80061180441800640030848221cc142c918481225dd0e0d8524c088a464310,0x2140124408852000c800c089042398285923090244bae261e0648c210c83209702c212106654310,0x60c0124c08852000c800c0890423b4383614930222b2e261e0648c210c83209702c212106654310,0x60c0124c08852000c800c0890423b4383614930222b2e261e0648c210c83209702c212106654310,0x310011642241b0030c0124418896000d000611804418004a004908422492181b0a49011148e0e2516c2c0922ee4320,0x310030242208b00424012480885200182009220442b0006800604c0210c6221e06484210c860e2516c2c0922ee4320,0x40c01248088520025000c08a0423a4303614920222b3281530b0228815d3110f032421086456310,0x40c01248088520025000c08a0423a4303614920222b3281530b0228815d3110f032421086456310,0x40c012480885a0025000c08a0422cc443c0c90842199281530b0228815990c0d85248088aed8610,0x310011642241b0030c0124418896000d000611804418004a004908422492181b0a49011148e0e2516c2c0922ee4320,0x3400184601106001280124210892000c8006109044380043004900622592181b0a49011148a0c2516c280922ee4320,0x438024883112400190008b300883000c800458904438004300490062258c142c918481225d90c0d17248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x108001e2011120011801240308968020e0092414429000640041448211d258383e490511593209702c212106664310,0x40c0124808852000c800c0890423a4303614920222b26221e06484210c83209702c212106654310,0x2140124408852000c800c089042388285923090244ba6221e06484210c83209702c212106654310,0x108001e2011120011801240308968020e0092414429000640041448211c6412e05842420cc92c1c1f248288ace5410,0x310030260208700084000f100889002c00082c8042380107004920a21496090e05852020cc92c1c1f248288ace5410,0x40c0124808852000c800c08904238c82582b084841992181b0a490111593110f032421086455410,0x59001819208470020600924044292c92582b0a4841992181b0a490111593110f032421086455410,0x40c0124808852000c800c08904238c82582b084841992181b0a490111593110f032421086455410,0x40c01248088520008800c089042388825c0b084841992181b0a490111591110f032421086455410,0xb00001f20810b00188002c3012090025800610b090b4002a0030850484360940b185202459960b81f811640a667531,0x90801850120a40038001813010470030a009241442700064006044821126412e05842420c8c2c96498182a82ee6540,0x40c0124808852000c800c08904238c825c0b084841982181b0a490111593110f032421086455410,0x108001e201112001180124030896802060092404429000640060448211c6412e05842420cc90c0c1f248088ace5410,0x58001819008470020600924044292c121c0b0a4041992181b0a490111593110f032421086455410,0x40c0124808852000d000c08a04238d029c0b085041992181b0a490111593110f032421086455410,0x40c0124808852000c800c08904238c825c0b084841992181b0a490111593110f032421086455410,0xc10024980421200608012441210f0004c00c089108840106006040c845ae03249302604259940a985811440a667621,0xc200185808107006080124c021090038000923010878002600604488442e03249302604259b018985813040a667621,0xc10024980421200608012441210f0004c00c089108840106006040c845ae03249302604259840a985811440a667621,0x60c0124c08852000c800c08904238c825c0b08484199a1c1b0a498111597130f032461086455410,0x60c0124c08852002c000c0c80423ac121c0b0a404199a1c1b0a498111597130f032461086455410,0x61400c2c09052001c000c0980823ac121c0b0a404190e0324930260425de0e1648c2c0912cd6520,0x21400c2409052001c000c0980823983859230b0244b24412e05842420c870192498130212ed6520,0xe00024980501b0048400c28090520030a009241442700064006044821126412e05842420c8c2c96498182a82ee6540,0x40c01248088520025000c08a0423a502a616045102bb2181b0a490111593110f032421086457410,0x40c0124808852002c000c0980423a4303614920222b26221e06484210c8b018985813040aed7410,0x40c01248088520025000c08a0423a502a616045102bb2181b0a490111593110f032421086457410,0x58001819008470020600924044292c121c0b0a4041992181b0a490111593110f032421086455410,0x40c0124808852000c800c08904238c825c0b084841992181b0a490111593110f032421086455410,0x3400084601106001280120210892000d000210a0443800430048006225941848a0c101245d90c0c85208088a463210,0x40c0120808852000d000808a04238c44380c808421906814c04c02820cc90c0c85208088acd3210,0x40c0120808852000d000808a0423a4303214820222b26221c06404210c8340a6026014106654310,0x58001019008470020600904044292c121809824041986221c06404210c890c0c85208088acd4310,0x2140124408852000c800c08904238c825c0b084841984142c918481225d3110f032421086455410,0x4240124808852000c800c08904238830945b0a0248ba6221e06484210c83209702c212106654310,0x6800116c024060026000c2441212001a000459409038008c00308184859858a9c30305485d20c2516c280922464310,0x45000c2821112001a00092140883b0b15386060a90bac142c9184812248681d2498138212654310,0x43000c2821112001a000921408838830945b0a0248b2c142c9184812248681d2498138212654310,0x43000c2821112001a000921408838830945b0a0248b2c142c9184812248681d2498138212654310,0x43000c28211120020400921088838830945b0a0248b3303c22f0270845d60a1648c240912455410,0x43000c2821112001a000921408839a07492604e084984184a2d8501245960a1648c240912455410,0x980018520110600248012441089200108006109044380086004900c22592181b0a49011148c2c54e18182a42ee4210,0x3400184601106001280124210892000c8006109044380043004900622584184a2d8501245d90c0d85248088a463210,0x408008b21120f0005400610a09084830945b0a0248b3281530b0228814c981e1178138422ed5310,0x3400184601106001280124210892000c8006109044380043004900622584184a2d8501245d90c0d85248088a464310,0x3400184601106001280124210892000c8006109044380043004900622584184a2d8501245d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a463210,0x310024860221200408012421110f0004c006109088840106003080c445ac142c9184812259940a985811440a665310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x310024860221200408012421110f0004c006109088840106003080c445ac142c9184812259940a985811440a665310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce5410,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce6410,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x43000c2821112001a000921408839a07492604e084984184a2d8501245960a1648c240912455410,0x3400184601106001280124210892000c8006109044380043004900622584184a2d8501245d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x43000c2821112001a000921408838830945b0a0248b2c142c9184812248681d2498138212654310,0x408008b21120f0005400610a09084830945b0a0248b3281530b0228814c981e1178138422ed5310,0x310024860221200408012421110f0004c006109088840106003080c445ac142c9184812259940a985811440a665310,0x43000c28211120020400921088838830945b0a0248b3303c22f0270845d60a1648c240912455410,0x3400184601106001280124210892000c8006109044380043004900622584184a2d8501245d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x310024860221200408012421110f0004c006109088840106003080c445ac142c9184812259940a985811440a665310,0x81801850120a40018801813010430020400c090882380103003080641586412e05842420c8940a985811440aee5310,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce5410,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106465410,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce5410,0x60c0124c08852000c800c08904238c825c0b08484198a1c1b0a498111597130f032461086455410,0x2200078402412002a000c2141216802580061490889000d000490a0441ce0324930260424c324b078c292122ce5421,0x2c0030250483100340003c601203001a0001e140903800a800308504859858a9c30305485db24b078c292122465432,0x2200078402431002a000c214120d802580061490887000d000490a04412e0324930260424896191843c92122ee9542,0x2200078402412002a000c2141216802580061490889000d000490a0441c64960f18524245970192498130212669532,0x2200078402412002a000c2141216802580061490889000d000490a0441cf03a4930270424c224b078c292122ce5432,0x1280181214092002040045908906e607845e04e108b3281530b02288148e0e2516c2c0922ed7620,0x26000c244121a002840045908902f84d2386058510b3303c22f0270844860e2516c2c0922657632,0xc1000e0c2701e0018800c2303810801a40092148446001280030850221b281530b0228814c691c8e0c229382ce6541,0x40c01248088520021000c08a0423a102a616045102ba2181b0a490111593110f032421086457410,0x1280181214092002040045908906e102a61604510291103c22f0270845960e2516c2c0922ed7621,0x40c0124808852000c800c08904238c443c0c908421906412e05842420cc90c0d85248088acd6510,0x2140124408852000c800c08904238c825c0b084841984142c918481225d3110f032421086455410,0x40c0124808852000c800c08904238c825c0b084841982181b0a490111593110f032421086455410,0x408003c21120f0005400610a09086102a61604510299103c22f0270845db24b078c292122cd6421,0x408003c21120f0005400610a09086102a61604510299103c22f0270845db24b078c292122cd6421,0x108003e2011120011801240308968020e0092414429000640041448211c6412e05842420cc92c1c3f248288ace5410,0x43000c2821112001a000921408839a07492604e084984184a2d8501245960a1648c240912455410,0x3400184601106001280124210892000c8006109044380043004900622584184a2d8501245d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce6410,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x43000c2821112001a000921408839a07492604e084984184a2d8501245960a1648c240912455410,0x3400184601106001280124210892000c8006109044380043004900622584184a2d8501245d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a464310,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce6410,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466410,0x40c0124808852000c800c08904238c825c0b084841992181b0a490111593110f032421086455410,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466510,0x81801850120a40018801813010430020400c090882380103003080641586412e05842420c8940a985811440aee7510,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x40c0124808852000c800c08904238c825c0b084841992181b0a490111593110f032421086455410,0x43000c2821112001c000921808839c06492604c08498649622d8524245960a1648c240912455410,0x6500248c211240030c0124418896000d00061180441800640030848221c649622d8524245dd0e0d8524c088a464310,0x618024883112c002180124410892000c80061180441800640030848221cc142c918481225dd0e0d8524c088a464310,0x618024883112c002180124410892000c80061180441800640030848221cc142c918481225dd0e0d8524c088a464310,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce6410,0x618024883112c002180124410892000c80061180441800640030848221cc142c918481225dd0e0d8524c088a465410,0x618024883112c002180124410892000c80061180441800640030848221cc142c918481225dd0e0d8524c088a465410,0x618024883112c002180124410892000c80061180441800640030848221cc142c918481225dd060d8524c088a465410,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466410,0x60c0124c08852000c800c08904238c825c0b08484199a1c1b0a498111597130f032461086455410,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466510,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce6410,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce6410,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x618024883112c002180124410892000c80061180441800640030848221cc142c918481225dd0e0d8524c088a465410,0x438024883112400190008b300883000c800458904438004300490062258c142c918481225d90c0d17248088a465410,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466410,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466410,0x81801850120a40018801813010430020400c090882380103003080641586412e05842420c8940a985811440aee7510,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466510,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466510,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466510,0x310024860221200408012421110f0004c006109088840106003080c445b281530b0228814c60a1648c240912ce6410,0x81801850120a40018801813010430020400c09088238010300308064159281530b0228815d3209702c212106466410,0x110030242208b00424012480885200182009220442b0006800604c0210dc1c4a2d8581245d1110f032421086466530,0x500018190084700206009240442904443c0c908421914090e05852020cc90c0d85248088acd6510,0x40c01248088520008800c089042384443c0c908421904412e05842420cc90c0d85248088acd6510,0x60c0124c08852000c800c08904239c4c3c0c918421906412e05842420cc50e0d8524c088acd6510,0x2200078402412002a000c2141216802580061490889000d000490a0441c64960f18524245970192498130212666532,0x2200078402412002a000c2141216802580061490889000d000490a0441c44960f18524245970192498130212666532,0x1280181214092002040045908906e502a61604510291303c22f0270845960e2516c2c0922ed8731,0xe0000e0c0501e0018800c2302810802c00061180443400d200490a42230d2391c184525059b018985813040a667651,0x40c01248088520021000c08a04238c443c0c90842191081530b0228815d10c0d85248088acd8510,0x40c01248088520025000c08a04238c443c0c90842191281530b0228815d90c0d85248088acd8510,0x1280181214092002040045908906e102a61604510291103c22f0270845960e2516c2c0922ed8731,0xe0000e0c0701e0018800c2303810801a40092148446001280030850221ad2391c184527059940a985811440a667651,0x408003c21120f0005400610a09084c92c1e30a4848b3281530b0228814c981e1178138422ed8631,0x40c0124808852000c800c08904238c443c0c908421906412e05842420cc10c0d85248088acd6510,0x22000784024120023000c21612168025800614908890009000490a0441d60940f185202459481d2498138212667632,0xc10024980421200408012441210f0004c00c089108840106006040c845b081530b0228814c70192498130212ce8721,0x408003c21120f0005400610a09086c92c1e30a4848b3081530b0228814c881e1178138422ed7521,0xc10024980421200608012441210f0004c00c089108840106006040c845ae03249302604259840a985811440a667621,0x3200184601106001180124210892000c800610904438004300490062258c142c918481225d90c0d85248088a465410,0x40c0124808852000c800c08904238c825c0b084841992181b0a490111593110f032421086455410,0x81801850120a40018801813010430020400c090882380103003080641586412e05842420c8940a985811440aee7510,0x40c0124808852000c800c08904238c443c0c908421906412e05842420cc90c0d85248088acd6510,0x618024883112c002180124410892000c80061180441800640030848221cc142c918481225dd0e0d8524c088a465410,0x60c0124c08852000c800c08904238c825c0b08484199a1c1b0a498111597130f032461086455410,0x81801850120a40018801813010430020400c090882380103003080641586412e05842420c8940a985811440aee7510,0x60c0124c08852000c800c08904239c4c3c0c918421906412e05842420ccd0e0d8524c088acd6510,0x60c0124c088520008800c08904239c4c3c0c918421904412e05842420ccd0e0d8524c088acd6510,0x60c0124c08852000c800c08904239c4c3c0c918421906412e05842420ccd0e0d8524c088acd6510,0x81801850120a40018801813010430020400c090882380103003080641586412e05842420c8940a985811440aee8610,0x81801850120a40018801813010430020400c090882380103003080641586412e05842420c8940a985811440aee7510,0x81801850120a40018801813010430020400c090882380103003080641586412e05842420c8940a985811440aee7510,0x90801852081130040c00c2809052000c400c0980821801020060484411d6090e05852020c8b018985813040aee8610,0x580018190084700206009240442904443c0c908421916090e05852020cc10c0d85248088acd6510,0xe0002498050060062001244428070025000c08a140b000640060448a0490d26b03020da05d42896498102a82465432,0x38001243011070004a00600148891c06492604c08499c0c2c918181224842896498102a82ed5431,0xc40024888500e00304012440a8030025000c08a140b000640060448a0488512c930205504884925818104d02ee6543,0x38001053011070004a00600148891828582b01024490e0324930260424c42896498102a82ed4320,0x380002c3011070005a00600348891c06492604c08498c8468b18089224842896498102a82ed4321,0x38001243011070004a00600148891c06492604c08499c0c2c918181224842896498102a82ed5431,0x47001848a242100508000e2111870009400071088c180106003080c4659422522b0042845d652381cc24511a465310,0x380000e3011070004c00610188891c06492600c08498ca47039848a22484309a498003282ed4320,0x38001243011070004c00610188891948e92309144490e0324930060424c4309a498003282ed4320,0x64002488850060060801244128070025000c00a140b000640060048a0490c2630b000ea05d460aa498007282465432,0x38001243011070004c00610188891c06492600c08498ca47491848a22484309a498003282ed4321,0x380002c3011070004c00610188891c06492600c08498ca470b1848a22484309a498003282ed5431,0x47001848a242100500000e20110700090000710088180106003080c4459422522b0042845d652381cc245112465310,0x47001848a242100508000e21110700090000710088180106003080c4458ca47039848a2248a1129158021422ee5310,0x980180032112001c00092180882dc06492600c08490861349300065059e061248c2c0112656431,0x3200184601106001180124210892000d000610a04438004a00490142258ca470b1848a225dd06098524c008a463210,0x19000c23008830010c009201844b1c06492600c084bba0c130a498011484309a498003283754310,0x43000c2821112001c000921808839948e92309144490e0324930060424c2243114c282122cd5421,0x3200184601106001180124210892000c8006109044380046004900c2258ca47491848a225dd06098524c008a464310,0x31002486022130058000c2900a87000c800611805418004600490842a49c0c24918580225dd06098524c00aa463210]
def shortcut (u : Bool) (T : Sig) (ws : List Sig) (k v : Nat) : Bool :=
  if v.testBit 62 then
    if v.testBit 61 then SingleRead.hornTest u ws T k (hornCodes[v % 2305843009213693952]?.getD 0)
    else SingleRead.cycleTest u ws T k (cycleCodes[v % 2305843009213693952]?.getD 0) else
  if v.testBit 63 then
    let p := kwProbe v 0
    let n := kwProbe v 1
    bit p T && !bit n T && ws.all (fun w => !(kwEnabled u (bit p w) (bit n w)))
  else kwWord u ((v >>> 8) &&& 134217727) (v >>> 35) T ws k ((v &&& 255)+555810816)
theorem shortcut_sound {u T ws k v} (ok : shortcut u T ws k v=true) : Impossible u T k ws.toFinset := by
  unfold shortcut at ok
  split at ok
  · split at ok
    · exact SingleRead.hornTest_sound ok
    · exact SingleRead.cycleTest_sound ok
  split at ok
  · simp only [Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at ok
    intro j _ h
    cases u with
    | false =>
      obtain ⟨w,hw,hp,hn⟩ := mono_row_difference h rfl ok.1.1 ok.1.2
      have no := ok.2 w (List.mem_toFinset.mp hw)
      rw [hp,hn] at no
      exact (by decide : kwEnabled false true false ≠ false) no
    | true =>
      have diff : bit (kwProbe v 0) T ≠ bit (kwProbe v 1) T := by
        rw [ok.1.1,ok.1.2]
        decide
      obtain ⟨w,hw,hn⟩ := live_row_difference h diff
      have yes := (kwEnabled_iff true _ _).2 ⟨hn,fun q => by cases q⟩
      exact Bool.false_ne_true ((ok.2 w (List.mem_toFinset.mp hw)).symm.trans yes)
  · exact kwWord_sound ok
def shortcutBatch (g : Forest) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun j => shortcut g.mode (targetOf g) (stateSet g k (start+j)) k (packedAt data (64*j) 64))
theorem shortcutBlock {g k start n data} (h : shortcutBatch g k start n data=true) : CutRow g k start n := by
  intro j lo hi
  right
  have hh := List.all_eq_true.mp h (j-start) (List.mem_range.mpr (by omega))
  have sum : start+(j-start)=j := by omega
  change shortcut _ _ (stateSet g k (start+(j-start))) _ _=true at hh
  rw [sum] at hh
  exact shortcut_sound hh
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
theorem lowerMixed {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : mixedTables g g.cap)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (mixedRoot low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def neighbor11008 (i : Fin 9) : Nat := [5, 5, 6, 6, 7, 0, 0, 2, 1].getD i.val 0
def absentRow11008 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor11008 i)
def presentRow11008 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor11008 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow11008 i) graph ≠ bit (presentRow11008 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow11008 i) (inputs.getD j.val zero) =
      bit (presentRow11008 i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) (small : C.size ≤ 14) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 13 else 14) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 14 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 13 else 14) := by
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
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow11008 i) (presentRow11008 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 14 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 13 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 9 edge 14 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run
def g99Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g99C : List ColumnInfo := []
def g99A : List (List Nat) := [[],[80,97]]
def g99D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g99L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g99D3)
  | _ => emptyPacking
def g99I (_ _ : Nat) : Option (Nat × Nat) := none
def g99 : Forest := ⟨99,3,fun i => g99Y[i]?.getD (0,0),g99C,g99A,g99L,g99I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99P3_0 : CutRow g99 3 0 1 := shortcutBlock (data:=fun _ => 0x22021188862120) (by decide +kernel)
theorem g99B3 : CutRow g99 3 0 1 := g99P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99T : mixedTables g99 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g99 0 0)
  · exact (mixedEmpty g99 1 0)
  · exact (mixedEmpty g99 2 0)
  · exact g99B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS99 : Lower true (varsX 99) (graphGoal 99) 4 := lowerMixed (g:=g99) (i:=0) (hints:=85) (before_sound [] baseKnown) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS99 := extendKnown [] 4 [(99,[]),(101,[33,101]),(165,[112,16,33,98]),(166,[112,32,98]),(178,[112,32,50,67,100]),(197,[32,16,101,117]),(225,[80,97,33,50,67,116]),(228,[32,81,49,67,116]),(291,[16,134,118]),(323,[128,16,101,81,117]),(326,[96,32,133,117]),(354,[128,81,32,50,67,116]),(418,[16,112,32,50,67,134]),(452,[96,113,32,49,67,82,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS99 : Known true KS99 := extend_ok (m:=99) baseKnown lowS99 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0)]
def g103C : List ColumnInfo := []
def g103A : List (List Nat) := [[],[33,101]]
def g103D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g103L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g103D4)
  | _ => emptyPacking
def g103I (_ _ : Nat) : Option (Nat × Nat) := none
def g103 : Forest := ⟨103,4,fun i => g103Y[i]?.getD (0,0),g103C,g103A,g103L,g103I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103P4_0 : CutRow g103 4 0 1 := shortcutBlock (data:=fun _ => 0x22021188862130) (by decide +kernel)
theorem g103B4 : CutRow g103 4 0 1 := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : mixedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g103 0 0)
  · exact (mixedEmpty g103 1 0)
  · exact (mixedEmpty g103 2 0)
  · exact (mixedEmpty g103 3 0)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore KS99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS103 : Lower true (varsX 103) (graphGoal 103) 5 := lowerMixed (g:=g103) (i:=0) (hints:=1621) (before_sound KS99 VS99) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS103 := extendKnown KS99 5 [(241,[80,65,98,49,50,112,48]),(422,[80,33,129,48,67,116,97]),(454,[96,114,48,67,133,66]),(481,[113,130,49,66]),(482,[16,96,114,48,66,133,83,67]),(484,[32,81,128,48,65,116,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS103 : Known true KS103 := extend_ok (m:=103) VS99 lowS103 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := []
def g109A : List (List Nat) := [[],[50]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g109L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g109D4)
  | _ => emptyPacking
def g109I (_ _ : Nat) : Option (Nat × Nat) := none
def g109 : Forest := ⟨109,4,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : CutRow g109 4 0 1 := shortcutBlock (data:=fun _ => 0x240121904a4140) (by decide +kernel)
theorem g109B4 : CutRow g109 4 0 1 := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : mixedTables g109 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g109 0 0)
  · exact (mixedEmpty g109 1 0)
  · exact (mixedEmpty g109 2 0)
  · exact (mixedEmpty g109 3 0)
  · exact g109B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore KS103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS109 : Lower true (varsX 109) (graphGoal 109) 5 := lowerMixed (g:=g109) (i:=0) (hints:=26117) (before_sound KS103 VS103) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS109 := extendKnown KS103 5 [(179,[112,33,16,49,67,84,101]),(227,[33,115,67,101]),(327,[128,49,32,33,81,117]),(357,[131,67,116]),(419,[16,32,115,67,133,101]),(453,[32,131,67,117,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS109 : Known true KS109 := extend_ok (m:=109) VS103 lowS109 (by decide +kernel)
def g229Y : Array (Bits × Bits) := #[(0x19e6799e6799e679,0x1866198661986619),(0x0,0x0),(0x1b56d5b56d5b56d5,0x1154551545515455),(0x0,0x0),(0x0,0x0),(0x2759d6759d6759d6,0x2318c6318c6318c6),(0x26b9ae6b9ae6b9ae,0x2689a2689a2689a2),(0x3caf2bcaf2bcaf2b,0xca328ca328ca328),(0x0,0x0)]
def g229C : List ColumnInfo := [(1,0,228,0,4),(4,0,225,0,4),(32,0,197,0,4),(64,0,165,0,4),(128,0,101,0,4)]
def g229A : List (List Nat) := [[],[114,101],[32,117],[32,80,96,112],[80,118],[80,98,112,32],[96,82],[96,114,80,82],[112,32,82,101],[112,98]]
def g229D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30fd20fd10
def g229D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g229H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb6e300a260fe00450000fa0011006b47008
def g229L : Nat → Packing
  | 5 => (2,1,3,0,0,3,0,g229D5)
  | 6 => (1,0,3,0,0,0,0,g229D6)
  | _ => emptyPacking
def g229I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 2 8 1 3 g229H6
  | _ => fun _ => none
def g229 : Forest := ⟨229,6,fun i => g229Y[i]?.getD (0,0),g229C,g229A,g229L,g229I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P5_0 : CutRow g229 5 0 2 := shortcutBlock (data:=fun _ => 0x84040b050a44310408002a144aa042) (by decide +kernel)
theorem g229B5 : CutRow g229 5 0 2 := g229P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P6_0 : CutRow g229 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B6 : CutRow g229 6 0 1 := g229P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229T : mixedTables g229 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g229 0 0)
  · exact (mixedEmpty g229 1 0)
  · exact (mixedEmpty g229 2 0)
  · exact (mixedEmpty g229 3 0)
  · exact (mixedEmpty g229 4 0)
  · exact g229B5
  · exact g229B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229G : graphValid g229 (boundsBefore KS109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS229 : Lower true (varsX 229) (graphGoal 229) 7 := lowerMixed (g:=g229) (i:=0) (hints:=536872453) (before_sound KS109 VS109) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS229 := extendKnown KS109 7 [(229,[]),(355,[33,129,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS229 : Known true KS229 := extend_ok (m:=229) VS109 lowS229 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0)]
def g231C : List ColumnInfo := [(2,0,229,0,7)]
def g231A : List (List Nat) := [[],[112,98]]
def g231D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g231L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g231D7)
  | _ => emptyPacking
def g231I (_ _ : Nat) : Option (Nat × Nat) := none
def g231 : Forest := ⟨231,7,fun i => g231Y[i]?.getD (0,0),g231C,g231A,g231L,g231I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231P7_0 : block g231 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g231B7 : block g231 7 0 1=true := g231P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231T : checkedTables g231 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g231 0 0 0 = true)
  · exact (rfl : block g231 1 0 0 = true)
  · exact (rfl : block g231 2 0 0 = true)
  · exact (rfl : block g231 3 0 0 = true)
  · exact (rfl : block g231 4 0 0 = true)
  · exact (rfl : block g231 5 0 0 = true)
  · exact (rfl : block g231 6 0 0 = true)
  · exact g231B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g231G : graphValid g231 (boundsBefore KS229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS231 : Lower true (varsX 231) (graphGoal 231) 8 := lower_forest (g:=g231) (i:=0) (hints:=536872533) (before_sound KS229 VS229) g231G g231T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS231 := extendKnown KS229 8 [(231,[]),(245,[32,65,49,117]),(359,[33,101,135]),(438,[64,33,48,117,134]),(470,[64,48,133,118]),(483,[16,112,98,50,67,132]),(485,[32,129,80,49,67,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS231 : Known true KS231 := extend_ok (m:=231) VS229 lowS231 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[(0x21f90fc87e43f21f,0x1e80f407a03d01e),(0x344fa27d13e89f44,0x204f027813c09e04),(0x0,0x0),(0x0,0x0),(0x72e3971cb8e5c72,0x62c31618b0c5862),(0x1ed4f6a7b53da9ed,0x1e10f087843c21e1),(0x2e27713b89dc4ee2,0x2e07703b81dc0ee0),(0x2b4b5a5ad2d696b4,0x21430a1850c28614),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,5),(16,0,227,0,5),(64,0,179,0,5),(1,64,178,0,4),(128,16,99,0,4)]
def g243A : List (List Nat) := [[],[112,100]]
def g243D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f731
def g243D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x221c17f
def g243H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa
def g243L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g243D5)
  | 6 => (1,0,3,0,0,0,0,g243D6)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g243H6
  | _ => fun _ => none
def g243 : Forest := ⟨243,6,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 1=true := g243P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 1=true := g243P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact g243B5
  · exact g243B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore KS231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS243 : Lower true (varsX 243) (graphGoal 243) 7 := lower_forest (g:=g243) (i:=0) (hints:=1074200661) (before_sound KS231 VS231) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS243 := extendKnown KS231 7 [(246,[32,65,117]),(373,[33,101,135]),(423,[16,50,66,134]),(455,[32,16,49,65,101,117,133]),(467,[64,133,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS243 : Known true KS243 := extend_ok (m:=243) VS231 lowS243 (by decide +kernel)
def g486Y : Array (Bits × Bits) := #[(0x0,0x0),(0x1724e5c939724e5c,0x132424c90932424c),(0xf2633c98cf2633c,0xd24234908d24234),(0x0,0x0),(0x0,0x0),(0x8f9523e548f9523,0x851521454851521),(0x32d55cb5572d55cb,0x129154a45529154a),(0x399a8e66a399a8e6,0x308a8c22a308a8c2),(0x3c4baf12ebc4baf1,0x2c4a8b12a2c4a8b1)]
def g486C : List ColumnInfo := [(34,0,452,0,4),(68,0,418,0,4),(132,0,354,0,4),(160,0,326,0,4),(258,0,228,0,4),(320,0,166,0,4)]
def g486A : List (List Nat) := [[],[133,118],[33,101,135],[33,117,134],[81,98,135],[81,98,113,130,33],[97,82],[97,82,130,113],[113,130,82,97],[113,130],[129,114,81,98,101],[129,114,101]]
def g486D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc3fa61fd10
def g486D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2b8881bf
def g486H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6f00015e02031d1cc20000000006800003560090
def g486L : Nat → Packing
  | 6 => (2,1,3,0,0,3,0,g486D6)
  | 7 => (1,0,3,0,0,0,0,g486D7)
  | _ => emptyPacking
def g486I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 2 17 4 9 1 4 g486H7
  | _ => fun _ => none
def g486 : Forest := ⟨486,7,fun i => g486Y[i]?.getD (0,0),g486C,g486A,g486L,g486I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486P6_0 : CutRow g486 6 0 2 := shortcutBlock (data:=fun _ => 0x88030380c8844104080032184ca042) (by decide +kernel)
theorem g486B6 : CutRow g486 6 0 2 := g486P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486P7_0 : CutRow g486 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g486B7 : CutRow g486 7 0 1 := g486P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486T : mixedTables g486 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g486 0 0)
  · exact (mixedEmpty g486 1 0)
  · exact (mixedEmpty g486 2 0)
  · exact (mixedEmpty g486 3 0)
  · exact (mixedEmpty g486 4 0)
  · exact (mixedEmpty g486 5 0)
  · exact g486B6
  · exact g486B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486G : graphValid g486 (boundsBefore KS243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS486 : Lower true (varsX 486) (graphGoal 486) 8 := lowerMixed (g:=g486) (i:=0) (hints:=4866442832) (before_sound KS243 VS243) g486G g486T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS486 := extendKnown KS243 8 [(486,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS486 : Known true KS486 := extend_ok (m:=486) VS243 lowS486 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g247C : List ColumnInfo := [(2,0,245,0,8)]
def g247A : List (List Nat) := [[],[32,65,117]]
def g247D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g247L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g247D8)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,8,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 1=true := g247P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact (rfl : block g247 6 0 0 = true)
  · exact (rfl : block g247 7 0 0 = true)
  · exact g247B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore KS486) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS247 : Lower true (varsX 247) (graphGoal 247) 9 := lower_forest (g:=g247) (i:=0) (hints:=537331285) (before_sound KS486 VS486) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS247 := extendKnown KS486 9 [(247,[]),(375,[33,101,135]),(439,[16,66,134]),(471,[32,16,65,101,117,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS247 : Known true KS247 := extend_ok (m:=247) VS486 lowS247 (by decide +kernel)
def g487Y : Array (Bits × Bits) := #[(0x250fb29bea60943e,0x210722806a20841c),(0x1b8443b48b2a6e11,0x98421b0832a2610),(0x2fe301a84a92bf8c,0x2fc301080a02bf0c),(0x0,0x0),(0x0,0x0),(0x26f0744e25659bc1,0x660c44e00451983),(0x6e8d77958401ba,0x28cc77858000a3),(0x10150691563b4054,0x1014029154384050),(0x3d130a40585df44c,0x341302005855d04c)]
def g487C : List ColumnInfo := [(1,0,486,0,8),(2,0,485,0,8),(4,0,483,0,8),(128,0,359,0,8),(256,0,231,0,8),(32,0,455,0,7),(64,0,423,0,7),(132,0,355,0,7),(258,0,229,0,7),(0,2,197,288,6),(0,4,291,192,6),(0,128,323,36,6),(0,256,165,66,6),(3,0,484,0,5),(5,0,482,0,5),(6,0,481,0,5),(32,2,197,256,5),(32,128,323,4,5),(33,0,454,0,5),(34,0,453,0,5),(64,4,291,128,5),(64,256,165,2,5),(65,0,422,0,5),(68,0,419,0,5),(130,0,357,0,5),(160,0,327,0,5),(256,2,197,32,5),(260,0,227,0,5),(35,0,452,0,4),(36,128,323,0,4),(66,256,165,0,4),(161,0,326,0,4),(192,4,291,0,4)]
def g487A : List (List Nat) := [[],[33,101,135],[113,130],[129,114,101]]
def g487D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x56ee5175d0110
def g487D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3a10083085082c120ad6b42cab12beae2b2ab2a6a829aa528ea22829f2769c26a9925e96252932469023a8d22e8a222872168420a811fe7e1f27b1e6781da751ce721c26f1b66c1aa6919e66192631866017a5d16e5a162571565414a5113e4e1324b1264811a4510e421023f0f63c0ea390de360d2330c6300ba2d0ae2a0a2270962408a2107e1e0721b0661805a1504e12030060009ff805d243df8805d2439fd80dc543dfb81dc143df981dc143dfb71dc143df971dc143bfa871c143dfb711c143df9711c1439fd83dd1519fd80dd151ddf7350d51bfb8050d519fd84dc1519fd83dc151fbb8050f41fb88050f41dbd435c3419fd80dd5419ff805d541bef8255141fbb8050d41fb88050d41cff7650d41bfb8050d419fd83dc9419fd80dc941b7f854c941f755454541bf780545419fd83dc141dbd43dc1419ff805d331dfb805d331df8805d3319fd87d0b31df57550731df5415c3319fd84dd5319ff845d5319ff805d5319ff805d131bef8255131b7d85d0d31bfb8050d31b7f854c931df77454531bf780545319fd84dc131bfb8050d219fd83dc121df541dc121dfb805d330fdb8050f30bdd83d0b30bfb8050b30df971d0330dfb805d1309fd87d0d30bf581d0d30bf980d0d30bdd8490d30fdb8050d30bfb8050d309fd87d0930bdd83d0930b7f854c9309fd84dc5309fd87d0530bdd83d0530f9d43d0530aff8650530f9d43505309fd84dd5109ff845d510bef8255110bfb8055110b7d85d0d10bfb8050d10bfb8050910b7f854c910ddf734c910df77550510dfb75d0110bf983d0110fb943d0110bf982d0110ff131d0110fd9434c110bfb8348110bf98348110ff14148110ff13148110f9b8050c43f988050c43d9d435c0439f980dd1519ef825d5419fb805d33197f855cb31bd783507318ff865d1319fb805d13197f855cb30bd983d03309fb805d1309df835d5108ff865d110dbb74d0110f9d434c941df975d0110f9943d0330
def g487H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g487D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x12840c2210984862902801e202862100050d8a8436141820181008a8a0888000302969012261860502820181008888201416140604001290386058504c342e261e160a01789878582810d0a3e261e160c342a00e1226103020181008a88880a02a016120a01110e303600c08060c0a81110e30308900416040186291020389888a44080a142e1058281810a440b0e08203c180442388883001108e20283080f0602203c1888302c4080a0a0110148e283042388081614060480203c3c4058c860a1406040023103818a0e86280d0a101228503018108c4090e160d108e38283004423880a16141206051038389858501810044081022108e20205850301814420099110201e183044388080c0a81110e1e306052302018100888840142c2a2822208c0b00406048200a38a0c91001226223428418161412080604022448a88880a090a0c0a2a242900306020a238e0a16140c06049012383404423888a160c0b01108e203858504a30181440e101a16148c06050110204e188068701108e282028a234004080a0a120010382868042c4230a8c21103820706a3428044238e200b878029903a3c342e4638834190c21818f023fa67a37a079d79a79779479178e78b78878578277f77c77977677377076d76a76776476175e75b75875575274f74c74974674374073d73a73773473172e72b7186fd6e26cf6bc6ad69667f6706416326075e85b959a57b5705415265174fc4f14d24bb4b049148246f45844943a42340c3f93da3cb3ac39d38636735033931a2f72e42c12b229f28425923621b2081fd1d61bf1a418d16e1571381150ee0df0c80b109a08307005103201f0007ff7150ffeb8a87ffdc143ffae0a1ffd54507fea1a83ff95131ffaa898ffd534c7ffa1a63ff50d31ffa6498fff42cc3fea1661ff9d130ffae8987ff434c3fea1a61ff5c930ffe84987fd424c3fe99261ff54530ffe82987fd414c3fe90a61ff95110ffaa8887fd53443ffa1a21ff50d10ffe84887fd42443fe992217f5ca43bfee498dfd73486feba2617f5cd10bfee48879f4390fcea1887ffd0d51ffa86a8ffd32507ffa1663ffd0931ffa8498ffd43487feb1661ff58930bfae921dfd7190efeb84877fdc543bfee0a1ffb7050ffc382877f5c443bfae021dff74546ffb9aa37fdc151bfaeba0dfd73d07dea1e837f5cb41bfae1a0eff76506ffbaa837f5d541bfee6a0fbf43507dea1a837fdc941feaa2a0dff70506febae637f5d331bfae598ff541cc6feb86637fdd531bfaea98dff744c6feba263fd54531bfee098dff73487faa0a437fdc121bfae9987dd43cc2feb96617f5c730ff681985ff744c3ef21a61f750d30bfee4985ff714c2ffbaa217f5d510bfee8885fd74442ffb9a217f5c910fea82887f531443fda0221fe4c110ff240885ed7290efdb82873fdd941 else 0x102223020202c0a0088c080d0886023a14203052140848826)
def g487H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc11b1d0000001804000425245383c833003000000000038cbab60001109a7c0000000000000000000d92000000000042b61200000000004f5c00021b00000008c8e47000000000000000000034040001370000000000b2f80028820000006124000000acd800000126f0000000000000000000000000000000000019a10001364000ab000000000000000000003ed7e6b0000001880000475800000020a000000178600000002dd002000149e8b000000000040db8da000000000000035a00003500019e00001f6955c000a04000162e00f00002f673401dcd12ad0000000b32f818000c6a000000000101365e00000000005768000000bc40000002564000a380000001b2700000000000000000000000000000000000000021800036d1a680000000d2c0002743ba80000003280000000000f03d147c9425800070340000000000003e86000000000249e0001ec8003eb35df8314fb400000000c800258400000000019411600000000000000000219d4a60000000003412000730ca04fd936a84cd10f1360000001930574000000000126f00ed1f411800135700015b4001ca1000000125200030c0000000000890e0c44b9a5200072575c0ae700063b0000000000000000082b92d5cf8000000000181400000000000000000000000000001e540005ab400184b0000000000000ba00001abe0000005a6800081a000000000130e41a80000000007b3f85144e000cdb80000000000000000000000f0bd00c00000000000000002b800000000000000001098000000205800000021c5a95b5c0009eb0005b7c4d86370002fa80000000000000000e590000000000c2a657c84800000000000005c705d0000003c9a000000000347741e6318001420000343c0a207a0000000000001c160000000000000000000287e2b30000002cbd42512ba5b28aab45000000000000095c80038c00000007aec001323a0a8000000000c348000000000000000000000000000000005e800000015b400000000011867e77270000000200368011031104323021110022004000020040001140704
def g487D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10111201a0488e1490100305911c62844a9081223860a4860a62010101c70a508408e2030e182c03c423881c311811c28818305002639c1038f0c14a40202039018890911c0051cf860b20047383860a348008e207992347bdb86054a468e32946e0dc00ff90ffd43ff10ffd51ffd07fd41ffcc7fd31ff487ff30ff4c3fd10
def g487H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x44e63480dd05600072166a8844000518437c81800002e800000000000000f3d3be2ae4b0000000be8c0c1594001e0848e11420bfe3e923dac473ac3500020b8000f1d12000000016cea068003c352030000000000000000301141f01e0001b1206da3aaf48000e7d83322dedc9570000000484871486700061c14a3ade000756400151482b00034c6ed200038f680ce1b223694c000c20c2278015a2927342cb0600f00122d14390bd62400000010960009058002278000276857c001df2b6e9d6d5a802ff073999c77b022309b1ce9955d0000106ea103802539a80002e6f9c0002890e995b5e5c7952b6800000000014d55b65b860861859291d6a8510c8fb37040000014673c4540019ed9de4160000c9062cb9b01c5e176343925ca800023279bc001c2db301aa90da5d400000026aece8bab208d44344d332cd6044c0000000508001e2553718460ae000735f854001a1f90cc0153620327eae873c53e31b748bcbdb284c427d0b12bd05c9aa0000cc4000bdc11c40001310000000000ce500044116c0000b13adb400009a1600003c7e000004904d8e4000e87abc5c680000003a28da600000046a742c000094e2f00000004010001fe3a1d31cc1170150550103049a09000909270a04030103100102120106051c1302001e000006000602010008070000010734000002120a0d000009
def g487D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40e1ff
def g487H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1d622c00f10000d2ca003a30000000000003c9002356440045441997a000000000000000040377002c700000000000000051400001f64c35200003000000000016c0000000690000000085dd890ad4002260000000000000d000327c200000000c18000000014510860
def g487L : Nat → Packing
  | 6 => (1,4,6,0,0,0,0,g487D6)
  | 7 => (113,3,6,0,0,10,0,g487D7)
  | 8 => (115,2,6,0,0,12,0,g487D8)
  | 9 => (12,1,6,0,0,10,0,g487D9)
  | 10 => (1,0,6,0,0,0,0,g487D10)
  | _ => emptyPacking
def g487I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g487H7
  | 8 => lookupWord 45 457 4 13 7 2 g487H8
  | 9 => lookupWord 50 277 8 13 7 2 g487H9
  | 10 => lookupWord 8 83 4 10 4 2 g487H10
  | _ => fun _ => none
def g487 : Forest := ⟨487,10,fun i => g487Y[i]?.getD (0,0),g487C,g487A,g487L,g487I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P6_0 : CutRow g487 6 0 1 := shortcutBlock (data:=fun _ => 0x8000000000000041) (by decide +kernel)
theorem g487B6 : CutRow g487 6 0 1 := g487P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_0 : CutRow g487 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_1 : CutRow g487 7 1 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_3 : CutRow g487 7 3 96 := shortcutBlock (data:=fun _ => 0x2202118886213000420c068304223100a8130380c8853100a8130380c8853100c4240b050a467200c4240b050a464200c4240b050a464200a242118886252000a8130380c8853100a8130380c885312098030380c98452040012110cc4217200642121904a434000c2480c8606263100a2460381822530002206138986212000c4241b0d0e463100c4240b050a464200c4240b050a46720846080c8606623100a8130380c8854100a8130380c885410088030380c8845200c4241b0d0e463100c4241b0d0e463100420c068304223100420c06830422310042080c860622310042080c860622310800440a15824473102c0121904ac1400800112094c84173102c0121904ac1400084040b0d0a443100240121904e41300042080c86062231040012110cc4217200240121904a414000220603818621200846080c8606622000a8130380c885310088030380c884420084040b050a443100a8130380c88541040012110cc42172002202118886213000c4241b0d0e46310486040b050a64310088030380c884420088030380c884310486040b050a643100220211888621300088030380c884420486040b050a64420022021188862130002206038182213000c4241b0d0e463200c4240a850a467200c42c070308464200c4240a850a46720846080c860662310846080c860662310800440a1582447300a8130380c885410486040b050a64420486040b050a64310084040b050a44310486040b050a644200c2482c960e267100c4241b0d0e46310088130380c885410486040b050a6431048602110c8c64610408002a144aa0420088030380c884300088030380c884310486040b050a64310486040b050a64310408002a144aa0310810001c0c874042800000000000842280000000000084228000000000008422400000000000010640000000000001054000000000000104400000000000010380000000000000224000000000000102400000000000010140000000000000ff800000000000806140000000000000fe40000000000000fd40000000000000fc8000000000000041) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_99 : CutRow g487 7 99 14 := shortcutBlock (data:=fun _ => 0x846080c8606623100a8130380c8854100220603818221300486040b050a64310486040b050a64310840312094c843630840312094c8436300a8130380c8854100a8130380c8854100a8130380c8854100420c06830422310084040b050a444200c8230380c88642040012110cc42172) (by decide +kernel)
theorem g487B7 : CutRow g487 7 0 113 := (@joinRow g487 7 0 3 110 (@joinRow g487 7 0 1 2 g487P7_0 g487P7_1) (@joinRow g487 7 3 96 14 g487P7_3 g487P7_99))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_0 : CutRow g487 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_3 : CutRow g487 8 3 61 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_64 : CutRow g487 8 64 9 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_73 : CutRow g487 8 73 42 := shortcutBlock (data:=fun _ => 0x88030380c884520088030380c884520088030380c884520088030380c8845200220211888621300088030380c884521818041e0d87c0641818041e0d87c06400240121904a41400088030380c884520088030380c8845200240121904a41400050030580c502610050030580c502610486040b050a64420486040b050a64420088030380c884520088030380c884520486040b050a64420050030580c502610050030580c502610050030580c502610084040b050a444200c4241b0d0e464200c4241b0d0e464200c4241b0d0e46420408002a144aa0531818041e0d87c0640084040b050a44420088030380c884520088030380c884520408002a144aa0530408002a144aa05308100034188d4064400000000000010c400000000000010b400000000000010a40000000000001094000000000000108400000000000010780000000000002618000000000008422) (by decide +kernel)
theorem g487B8 : CutRow g487 8 0 115 := (@joinRow g487 8 0 64 51 (@joinRow g487 8 0 3 61 g487P8_0 g487P8_3) (@joinRow g487 8 64 9 42 g487P8_64 g487P8_73))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P9_0 : CutRow g487 9 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B9 : CutRow g487 9 0 12 := g487P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P10_0 : CutRow g487 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B10 : CutRow g487 10 0 1 := g487P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487T : mixedTables g487 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g487 0 0)
  · exact (mixedEmpty g487 1 0)
  · exact (mixedEmpty g487 2 0)
  · exact (mixedEmpty g487 3 0)
  · exact (mixedEmpty g487 4 0)
  · exact (mixedEmpty g487 5 0)
  · exact g487B6
  · exact g487B7
  · exact g487B8
  · exact g487B9
  · exact g487B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487G : graphValid g487 (boundsBefore KS247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS487 : Lower true (varsX 487) (graphGoal 487) 11 := lowerMixed (g:=g487) (i:=0) (hints:=4831839829) (before_sound KS247 VS247) g487G g487T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS487 := extendKnown KS247 11 [(487,[]),(499,[16,66,50,134]),(501,[32,16,65,49,101,117,133]),(502,[64,48,133,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS487 : Known true KS487 := extend_ok (m:=487) VS247 lowS487 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0x19b7c447e46b84bb,0x18b7c443e42b8019),(0xc20e188abef9afc,0xc2061808bef8af8),(0x11c3163ea090e34f,0x11c1163ea010230f),(0x0,0x0),(0x20041830d3037f8e,0x2000181091017f8e),(0x21f81e3f1c1c7c0f,0x21401a3c10107506),(0x3e001fc01fe07ff0,0x240029801bc45ce0),(0x3fffe0001fff8000,0xe3ee1010eee8030),(0x3fffffffe0000000,0x13df866f60000001)]
def g503C : List ColumnInfo := [(1,0,502,0,11),(2,0,501,0,11),(4,0,499,0,11),(16,0,487,0,11),(32,0,471,0,9),(64,0,439,0,9),(128,0,375,0,9),(256,0,247,0,9),(33,0,470,0,8),(65,0,438,0,8),(36,0,467,0,7),(48,0,455,0,7),(130,0,373,0,7),(257,0,246,0,7)]
def g503A : List (List Nat) := [[],[33,101,135],[16,66,134],[16,64,32,133,101,118],[32,16,65,101,117,133],[32,65,117],[64,133,118],[64,33,117,134]]
def g503D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18c170fae17659574553c1e5c2ecb2ae8aa7c397659574e0154
def g503D8 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x865d154beee81955d154bcfaa4955d1549efaa7655d1549ef6a7655d154b6f69f655d154bee683655d154bcfaa6655d154bcfaa2655d154f4fe1e655d154f4f21e655d154bcf69a655d154f4fdda655d154bcfaa5655d154dcf2a5655d154f8fe19655d154f8f219655d154f8f9d9655d1549df69b955d154c7fe1f955d154e5fe1f955d154e5fe1c955d1549dfaa6655d1549dfaa5655d1549df2a5655d154f1f5d9655d1549f7e8d97d9154afee8187d9154cbf6a786d9154d9fe1995d9154dcfe9195d9154ddbe8995d9154cbfe1995d91549fbe8995d9154dcf65574d91548ffe9d98591548ffea197591549f7e8d97591549fde8597591548ffea587591548ff6a58759154afee818759154eaf6938659154afee818659154abfaa08659154bbd6848659154cdfe1b9559154d9fe1b9559154d9f21b9559154dcf6939559154cbfe1b9559154cdf6639559154e9fe1b9559154cbfe1995591549efe9195591549fbe899559154e9fe189559154dcfe557459154afe69f96e0154cfee5f96e0154afe6a696e0154ebee5a96e0154cfee5d96e0154ebee5996e0154afe69e76e0154afeea576e0154afeaa576e0154afe6a576e0154afe2a576e0154afee9176e0154e7ee5f74e0154e7e5db74e0154afeea574e0154afe6a574e0154e7ee5d74e0154e7e25d74e0154afee9974e0154e7edd974e0154e7e5d974e0154ebee5b64e0154afeea564e0154afe6a564e0154afee9d64e0154afe69d64e0154ebee5964e0154ebe25964e0154afe69f86e0154ebea5b86e0154ebe65b86e0154afee9586e0154afee9186e0154ebee1986e0154bfae8986e0154afeaa486e0154afeaa086e0154bfc68486e0154bde69676e0154bfc68676e0154afeea176e0154afeaa176e0154afe6a176e0154afe2a176e0154bf6e8d76e0154e7ee1f74e0154bde69774e0154beeaa674e0154beeaa274e0154bee69e74e0154fce99674e0154eee2a174e0154f6ee5d74e0154f6e25d74e0154f6ee1d74e0154f6e21d74e0154f6edd974e0154f6e5d974e0154fcee9574e0154fce29574e0154fce99574e0154fce59574e0154fece8574e0154e7ee1d74e0154bdee9574e0154bfce8574e0154ebee1b64e0154bde69764e0154afe6a164e0154ebee1964e0154bdee9564e01549f7e8d979d8548ff6a5879d854cbfea5869d854cbf65d869d854e3fe9d865d854e3f29d865d854eb761b935d854af7ea57660c54cf7ea57660c54af76a57660c54cf72a57660c54eb7a597660c54eb76597660c54abe6987560064aee6907560064aeb6936560a548fde8597e19548f768e985d954afc68676e0154afce8574e0154afae8986e0154afc68486e0154cbd619919d8548f7ea57660c548fe6a47560064af668c7560064afc6847560064f0f5d9655d154af6e8d76e0154 else (if j<2 then 0xdf1b83646b0d31a0334650c71883045f0bb1702d4590af1582a4530a31402744d0971282444708b1102144107f0f81e43b0730e01b4350670c81842f05b0b01542904f098124230430800f41d0370580840b003000cfee9f9061664cfea9f9061664cfe69f9061664cfe29f9061664cfee9b9061664cfe69b90616649efe91969d6649fbe89969d664cfd6a191a1564cfde1d91a1564cfda1d91a1564dbd69991a1564afe6828761564cfee1f9061564cfea1f9061564cfe61f9061564dbee9b9061564afe6828721564afde858721564cefe91989d5649bfe99949d5649fee81949d5648ffaa2985d564e5fe5d9761464adfaa49761464e5f65c97614648ffe95985d464cdfe95985d464e5fe9d855d464e5f29d855d464cfe681981d464afe69e7560064cfea9b9061654cfe29b9061654cfe9db9061654cfea5b9061654cfe25b90616549f7e8d96dd654cefea194dd654dede8594dd654c7f61f965d654e6f61f945d654cefea194d96549efe9d94d9654afbe999760a54afbe959760a54cfb65e9660a54e7b65f7660a54cfb65d9560a54e7b65f7560a54afbea57560a54afb6a57560a54e7ba5d7560a54e7b65d7560a54afbe997560a548ff69597e19548ff69197e1954cfde8597e1954cfe6a190a1954cfee1d90a1954cfea1d90a1954dde69590a1954dee69190a1954cfee9f9061954cfea9f9061954cfe69f9061954cfe29f9061954cfee9b9061954cfee979061954cfee939061954cfee579061954afe6828761954cfbe1f9261954cfba1f9261954cfb61f9261954cfbe1b9261954debe939261954cfee1f9061954cfea1f9061954cfe61f9061954cfee1b9061954ddee979061954deee939061954afe6828721954afde858721954afee818721954cfdaa19121954cfde1d9121954cfda1d9121954cfd61d9121954cfd21d9121954ddda959121954ddd69591219548ffe95989d954abf69b879d954cdfe1d959d954dcfe91959d954dcf291959d954cfdaa1919d954cfd6a1919d954cfde1d919d954ddda95919d954ddd695919d954cbf69a985d954cf768e985d9548ffaa2985d9549df697945d954a7f69b87dd1548ffaa196dd1548ffea586dd154cbf65986dd154afbe8986dd154afee8186dd154d5fe1d95dd1549dfe9995dd154cfeaa190dd154cfe6a190dd154cfee1990dd154cfe61990dd154ddea9590dd154dde69590dd154dee69190dd154dcf295979d154cefa63879d154cefa61879d154bede85879d154beee81879d154bee682869d154bebe89869d154beee81869d154bed684869d154aefaa2769d154aef6a2769d154bcf696769d154bed686769d154aefea1769d154aef2a1769d1549ef6a7659d154bee683659d154dcfa62659d154bcf69a659d154bee682865d154bebe89865d154beee81865d154bed684 else 0x35c408df10237c40bc3cfcbc4403af758ea5d33a3740e75cd397728e45c738b710e15c137f6f8de5bb3736e0db5b53676c8d85af35b6b0d55a934f698d25a3343680cf59d337668cc59732b650c959131f638c658b313620c3585307608c057f2fb5f0bd5792ef5d8ba5732e35c0b756d2d75a8b45672cb590b15612bf578ae55b2b3560ab5552a7548a854f29b530a554928f518a25432835009f53d2774e89c53726b4d09953125f4b89652b2534a0935252474889051f23b4708d51922f4588a5132234408750d2174288450720b410815011ff3f87e4fb1f33e07b4f51e73c8784ef1db3b0754e91cf398724e31c33806f4dd1b73686c4d71ab350694d119f338664cb193320634c5187308604bf17b2f05d4b916f2d85a4b31632c0574ad1572a8544a714b290514a113f2784e49b1332604b4951272484848f11b2304548910f218424831032003f47d0f71e83c4770eb1d0394710))
def g503H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa2007c960019a000000000b4ea800000064800000048800005080201c8000000000a82
def g503D9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0xeca4ecaa5ffa61765537fd30bb2a9bfd985d954dfe4c2ecaa5ffe5176553bff0fba2a97fd96dd154dffc36e8aa6ff61b74552ffb2bba2a9fbf879d154fdec3ce8aa7efe1a74553f7d0d3a2a9fbd869d154fde434e8aa7ef9da74553f7aed3a2a9fbf659d154fde4c2e8aa7efe1974553f7d0cba2a9fbd865d154fde432e8aa7efe5574553f7b2aba2a9fbf655d154dffc32e8aa5ffe5574553eff2aba2a9f7c955d154fbf32ae8aa7df59574552ffb2fb22a9bff87d9154dfec3ec8aa7bfe1b64552ffb2bb22a9fbd74d9154bffcbac8aa5ff65d645537ff0eb22a9bfd8759154dffc32c8aa7bfe19645537fb0cb22a9efc8659154bffcaac8aa7dfe5564552ffb2ab22a9f7c9559154fbf32ac8aa7df59564553f7ae8b22a9ffb96e0154ffd4b700aa7fe65b80553ff12dc02a9ffb86e0154ffd43700aa7fe61b80553ff10dc02a9ffa76e0154ffdba700aa7fe5d380553ff6c9c02a9ff964e0154dffcbb0c2a6ffa5d861537fb2ec30a9bfc9761854bfecbcec2a6ff61e761537ff30bb0a9bfd985d854dfec32ec2a7f7e4d761537f720c2cc93fd989d6649fecbf0ab26dfe16855936fb0a42ac93fe989d5649fecc4eab24ffa61755927f930baac9b7f9761464dbf4bb0a326df25d851927ff2ec28c93fd989d464cfec3cea326df61675192f7b283a8c93ff9661e549ffcbb0d2a4ff66376952f7b29bb4a99fd87dd654bdfca2eb2a6fba5d829537dd2cc14a9bed9660a54df7bb3052a6fb9d9829537db2ac14a9bef7560a54df7b2b052a6bfe1a865527ff2ec32a93ff9561954dbfcab0caa6fee41865535ff0cc32a9afd86219549fecc4ecaa4ff661765533ff0fba2a9f3e659d154f9fcaae8aa7cf255745527fb30b22a9bfa96e0154dfccb700aa6fe25b805537f4edc02a9bfb74e0154dfdb2700aa6fea1b805537f30dc02a9bf886e01549ffcbb0c2a5fd646761527ff30bb0a93fd985d854befc9aec2a6f7a59831537bb2cc18a9bde7660c54dee3b3062a5ff65e75592ffb2f3b2a9ff976e01549ffcbb0b325fd64685592ff720c2ac9b7d97614649ffcc2ea324ff661751936fb0aba8c93fd981d464dfdbab00326fe9d5801937f2eac00c9bf875600649fecc4ed2a6fee4185952f7b29baca99fd875d654bdeca6cb2a6fb65d829537daeac14a93fd97e1954bfcc850caa5fbe4986552ff720c32a93fe9821954bfac890caa4ffa6276552efb2b3b2a97f5919d9549ff4c2ecaa4ff26176552efb2bba2a97f990dd154bdf4c4e8aa5ef65e74553e7ccaba2a9f3d655d154bbfcaae8aa6bfe1b64552efb2bb22a9aff8659154bbfcaac8aa6fee5b805537f2edc02a9bf974e0154dfcb2700aa6fee1b80553f74e9c02a9fb974e01549fecc4ec2a6bf61a761535fb0cbb0a93fd981d854deebb3062a4fee41859927f720c2ca93fb9061954 else (if j<2 then 0xa8aa453a29114289e44da26112a892447a231112886441a2010fa87a43ba1d10e286e435a1a10ca86242fa1710b2856429a14109a84a423a11108283e41da0e106a832417a0b1052826411a08103a81a40ba05102280e405a02100a8023ff9ff0ff27f63f99fc0fda7ea3f39f90fc27de3ed9f60faa7d23e79f30f927c63e19f00f7a7ba3db9ed0f627ae3d59ea0f4a7a23cf9e70f327963c99e40f1a78a3c39e10f0277e3bd9de0eea7723b79db0ed27663b19d80eba75a3ab9d50ea274e3a59d20e8a74239f9cf0e727363999cc0e5a72a3939c90e4271e38d9c60e2a7123879c30e127063819c00dfa6fa37b9bd0de26ee3759ba0dca6e236f9b70db26d63699b40d9a6ca3639b10d826be35d9ae0d6a6b23579ab0d526a63519a80d3a69a34b9a50d2268e3459a20d0a68233f99f0cf267633999c0cda66a3339990cc265e32d9960caa6523279930c926463219900c7a63a31b98d0c6262e31598a0c4a62230f9854c165f32ebd6f0b41581ab1550ea49509276d34896d49ea4351ac89f43420c4fe67ca3c99d70e4a6e735499acc5a5ef2df9604a9450526e12948ea4372070fb076a3851ae0c5c5c02a213588b43ec1bf0c405282180ce048018006e000dff4ab0d326ff255869937ff2ec2cc9bfe9761664dfecbb0b326ff25d859937fb2cc2cc97fd969d664dfec34eb326ffe5f855937fd2fc2ac9bfd97e1564dfe4bf0ab25ff65f855937ff0fc2ac97fd97a1564dffc3d0ab26ffa1e85593eff0b42ac97ff9761564dffc3b0ab26ffa1d855937fb0ec2ac9f7f8561564fdfca30ab27fee4185592ffd3042ac97fd9721564dffc390ab26ffa1c855937fb0e42ac9bfc8721564fbec290ab25ffa6275592ffb313aac9bff879d564bfeca4eab25ffa61755937fd30baac9bfd985d564dfe4c2eab25ffe51755937ff2ec28c9bfe9761464dfecbb0a326ff25d85192ffb2f3a8c9bfd879d464dffcc2ea326ff661751937fb0aba8c9bff9661e54dff4b30f2a6ff659879537f92cc3ca9bfd9561e54dffcbb0d2a6ffa5d869537fb2ec34a9bfc9761a54dffcab0d2a6ff65586952ffb2bbb4a97fd959da54dff4b30b2a6ff259859537fcecc2ca97fd96dd654dfec36eb2a6ff61d75952fff2cbaca9bfd865d654fdfca2eb2a6ff61f659537ff2fc32a9bfe97e1954dfecbf0caa6ff25f865537fb2bc32a9bfd94e1954bfecbf0caa6ffe1f86552ffb2f432a9bff87a1954dff43d0caa7bfe1a865537ff2ec32a9bfe9761954dfecbb0caa6ff25d865537ff2ac32a97ff9761954dffc3b0caa6ffa1d865537fb0ec32a9bff8661954f7fc330caa7dfe5586553f7f28c32a9fef9261954ffdc830caa5ffa6086552ffb2e432a9bff8721954dff4390caa6ff61c865537f90e432a9efd8621954bff4c4ecaa5ff662765537ff0f3b2a97fd959d954bf else 0x9e0099c0082f3e5c38c418ae6c8c79f2e03d5cd91873e5c476f1a273e5c780f5d355e7cb8f048457aa99273e5c781056ba6e7cb8f0484174dcf971e055210d6373e3ca4371dbc6e5cf8c86a3b78cd79f2e32076f1b9f2e321a8fc39f2e290b0cc22f3e5c620c1e2f3e5c38a41cbf3e2939708a3868bcf8f2e09076ed92f1e1cc50e29bb689cf8f04a473e41b8f0172e4e65b971603d6cb939b2e3c07ad97273e5c580e14207e7c78722c43139972732dcb81014207e7c39712c405e694304e5c78111ce65c9ccb72e040509cb873e23070c14273e5c389097997e5c78441c689cdcd497e5c621214272e3c0508179f2e05f88f13973e1c528c1422589cf971e0425e5c784416271e05844bcf896e1ca20e5b9f2e3c220c97971e11054b41bb649979f2e24a548ddb72e3cc7a0ddb25e5cd27121bb64bcf971483b66f412a4e7c791095bf3a1cb8a41dbd0e7c9225e2385e7cb871485870bc03a4e7cb89620b700e97971e69082e979f2e3c0b24205b76dc22c4e5c48cd579f2e31068bcf971882d6cb91873e5c47916489a44121a90a483a4112028fe47da3e11ea8f2477a3b11d28e6471a3811ba8da46ba3511a28ce465a32118a8c245fa2f11728b6459a2c115))
def g503H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb071203c81100000000030b4e28d00001026048522a500005011c020e513000016bf603540f300000000000020d56492407b00000000000004a9b086a0d3b0680000000000000000f0720000000010ba00f90079e09ea8bf60cd1e7880e0c0f7010362114006c0fff26150fcb0ca90f6a258d243e0eee091a0ebd06e0000f11d80aee01f000040c8603d0012000080ce1a67421000009a85702c70428093e498e00d1113824f000080e4c0dcd03ad12a0000505c2109405aa08b54893ec3e30d02d95058a029528cd003f0bbcc04000060aad49b6037612d12b00070c0a58ecaa08d21244005dc37000080c550080000e0193096d08f2ca6e0516297105ba422e028b295f07f906af018bd081009824040fd8257842a924af00700ec9115b116c129701480443123210b727a20d1e3189080368c0120d885b10c110a3053230c688b1236a01500f2a08c2282d232d052c50fe0df2ac050ab2056d040801e010192e6f0b1b01ac30b403068b7b010509220ef004e110262d825212059603f20c6f0fb20d72319e09ba90fe08e5a667050122a1668f0732107f0020000cea6602300fef2a3582a403300008100f51cb01b011e72afd0a7b047121fa03930d2449a1025848a60a076f560b23488e0bdd0f5407610ac0000c095a06300001c79c0edd51be032825fb0ad62767887a0042038c256ad0f823f60d4700a70b7a685a02ff0fad0b6d04861280e83106f427f0000b02796840000105d128e9021e02b900c00e1a2c27ca5f049c4861013e0550000a0c7402e96c1889c900b111f1054506b028fc1117061c04f806c0000909f707e504d30f8104160bc74a400000000101d0045309d4227705e00b900005060d67300008114aaa40000d0d6129917265ec7b03e18028065b29040e9106202c6e046d03b212b510d8477700ef0b510e2b10e4106aa847117a09460f4c0e3110500000000e2da500f90643069e12c20b38886a125a02d60f10512e29ca000572710a890e7971a1ea5e30a00000000d017b016004bd8f50090a0814a7c30e5000000000000710f4c1cf6c0d04cb001ac5d00005432000010e8dabe8104f11290cbe6b770dde0750000f0b80000000070db40340000630960f0f2cff40410de0000e22460c4b0cc302a0000f274a49750a2242bc122d0310000a06dc6d05253e0ea000040c9107d126cc804004ae2a1489251030055ef0e78a7407f230008001c59034a0d3a11000d07080108741e2a202703000108ce000812221d000c000629080718070d001c00130d110208080d00030d230300021f04011900093c40021f001e210018060d0c662c000f0201
def g503D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5e6c32c73564206117566933cb1c0a5e6932c33c552179a4573c72c085c6126933cb1c152979a4cb0cf15485e6564cf2c702171e6cb0cf1564247157566cf2c7090a5e6cf2c70564216973c31c979085e5cf0cb15a4226585cf0cb15e42665d61f3c7017290a9d7173c72c16909117156973932c70297964cf2c705885e5916cf1cb0217144964cf2c7058a157964cf2c705895d6964cf0cb12169a5173132c705ca1e65a55c5cf2c7010b5e7945cf2c701162a75c6956173cb1c042d7930cb3c655881c65d6c25cb1ce4297972c73c169081c5106cf2c70207566cf1cb01081841d59a4cf1cb0287546cf2c70108197973cb1c042075a5cf1c321081c6105cf2c702051075a5933c72c0a1d6964cf1cb02255c4cf2c311c71445e5cf2c31250964cf2c461d6173cb1c04206105cf2c701c6133cb1c061b3cb12052a5133c70190964cf2c462c5132c701a88277a6a25ca4c23ea31222211a041f69e91da1c99ba9aa19c98f17e96f96215193f92f11d10f8ff0f18e40d68c60b88ab09d89007f87206605704c83f03302881f81500a8003ff9d664fff85593ffa1564ffd85593ff21564ffe75593ff5d564ffe75193ff5d464ffc75193ffdda54ffe76953ffdd654ffd75953ffd9654fff86553ffa1954ffd86553ff21954ffe76553ff5d954fff74553ff5d154fff64553ff59154ffe76153ff5d854ffc76152ff61a64bfd85992ffe1564bfd85192ff61e54bfd86952ff61654bff86552ff61954fbe74553ef5d154ffb80552ff61854b7e85192df61464bf980192fb60a54bfb80552f760c54
def g503H10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x8c5a548a8c00038199000c988368da00f22c7dbbd5830172d400024492008800000002e298000251630a4e148f8473e29de2a2c487424640040001e0b000013be000024ab000014c2400030af4000340a483b80002c8b000003b230333a958411f0ab742918458000180bde13eb06d2301437d91392a6e830c000101c382af78bc00020194000040c40000084c00031466546f03288496ca280001504f730c00025a8f88f2513799a58040000100f85cc00003b3e772780000000000000000c30548200000397800000000000000000003ebefc1e39050000208fbc4d05afbcc4adba13b1e433a02b6c04400000276c91fd45084bac264000204740151147602300a54c14b0839002c000000008051c2340003cb69a95743480003835a83ed42ca8308ca2c00032800401780a204b400008b428858c1c8818a22f4149c84d40cbcc094c1f3c1e400033ad852c45020820c00025032bb08000204c8433c000241ccc48b829c000142db4a3e44be6c7bb0b21055a8b1126743ea413f113de8d583668814014c823cc1838142c46d1416c4668a13c91402fdc1c7e847003c404c406a0bdc0000041802a00001401a0bcba2a9394c447c000154d80001c1440001431783b0aad283bf8c4240b481ac0003683dca4a039883a600cc42d7b3080002031aa3c8000040df80090b25426000000000c2d342dc0000c3600000000041bc00000003142142480002820362b8815e80d1093783694a9c000249a7002b2c4c000104540000c10c0001c865c9180000000000038321442800000002d4bdd0b40003844a8ad5c25a0242420581b40002c12b028e805cc37bb909c38f440b046000008c3fccc18133cb090c4c000000000003e842a8b80000408000000ad00000c21aa138000283e44933c2f282e22a5883a14a7100ac8c3800039c3a8100c024a05682f7882c000171e892a8c0e7c1e8449c0000c2e7a05384c2c4db80100000000043f400030294000230e0000343cc000314df83abc270c0d800014a780000caec000003d0f876c3830824b8b7017804b301a3440344804b4ad141c438cb063873006c0000c34d0176816c0000000001379a72b1fc0003439c023800000000000000005489ca27026c846800000000000331940000ca900000c2218b6e317d81b04a1d62a40387c0e3c32c0000000001dd03348437206000864056c225021d2bba8371c44012270c0807e0408824280e058802eb90105cc207118ccc7360715806260880c5c1d00024100b00800c815458740c5d030ec000104128020b0081804090c8280a0b0002c2e050307c000017800060c00818021b039d01608018780c6611014080d130180612000087a0c0087800020600c1c0906874000a0780014060180436040600c0800000041007000000c010000c7a03020000c01001d8107e else 0x2435c08f40003527b03fb8187841582cd20a2425c417f41a6ca3a5a4e927f58b0546ac24fc4ce81398030020acbd8289ec0390412c1fbd2b00002409c8a1ada9a81fdc2bf89cf42b230fdc3d403e301abc3d8c12fc3c2444c838b90b2028689cb40eb41568a340003419f402000b1c1f60a2069a70a3160a5c444a06501d540fdc22b52c804dfb034e18f43c4082ac3c88327ca9989468912c43d52ad921902c2d2a14aaac062801c4b398159c8540002049a204e6882c1926c39898c803644523a9400924250022f82a5c9ec52a488a14394d29ac4aa8b3f041e7a79ba7e52bb81074bd6834182b990c543ddc3f30255427d81ed81278b92aa538113c28909204478c07b82ab52c140ab6a560a672a860099e2fb91ac017342c7c45f42eec31c0003a96fc2f944071bc5000280edc29aeb6188314c44f319418c0077c42309260122aa5e92be78b0b3d1c1bb04a38164440cea7389284bbc00034216c0c94a76f0ec000044c5010940c08058eaf9b314007f4073a3bf83b5816b529f843033c68350000180f5c36c0002c1d0826942780003c37682e809fb031100bba8b40000000000000002c1140000835604a6c48e8281c1d901180000c425c42c0390000000020a4148800000000300667ad490bcc04a04afc0d5ca1492d3c92f4160000283fccaf3f310021012d8ea98c3adc34500)
def g503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe5346139108394c49ca3020e534e518108398b38c24420e6292728c08398b28c264239ae22970b803ff327fd64ff8c9ff953feaa7fc54
def g503H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c590004814000000000000000000070b20740000000000001c1c00000000070b000080d6928bb762660e6036d20c61f058001808000e2e689c001020641903000000068c8000001e11000415bc962ac6eb10ac8288060000000000000210c8947876847168000000000000716eaac000000506754e000814d75c0010240000000821d57b155923000012d0530a28afeab80b81183450074117a160aaa5da34e68542686680c3aa9c3f794a2f1823436000870d2286425435eab827512000b48807800000072f800000000000002b705c4491018002d5cb22854d23e01e00000010b182a000201419dc460000002a5800000068504d02308c1035d30008890411cb281000
def g503D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc8404ff
def g503H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x431c062f8492f8000f034a003915307a0000000382003ea0c89d0152d000100027183400000019134b76800000f601
def g503L : Nat → Packing
  | 7 => (3,5,4,0,0,4,0,g503D7)
  | 8 => (302,4,4,0,0,11,0,g503D8)
  | 9 => (312,3,4,0,0,13,0,g503D9)
  | 10 => (47,2,4,0,0,12,0,g503D10)
  | 11 => (6,1,4,0,0,8,0,g503D11)
  | 12 => (1,0,4,0,0,0,0,g503D12)
  | _ => emptyPacking
def g503I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 3 31 1 9 2 3 g503H8
  | 9 => lookupWord 93 431 8 16 9 3 g503H9
  | 10 => lookupWord 138 683 9 16 9 3 g503H10
  | 11 => lookupWord 24 149 6 13 6 3 g503H11
  | 12 => lookupWord 6 37 3 10 3 3 g503H12
  | _ => fun _ => none
def g503 : Forest := ⟨503,12,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_0 : CutRow g503 7 0 3 := shortcutBlock (data:=fun _ => 0x20809078260906320220184406221600c1201a4d0e9e076) (by decide +kernel)
theorem g503B7 : CutRow g503 7 0 3 := g503P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_0 : CutRow g503 8 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_5 : CutRow g503 8 5 96 := shortcutBlock (data:=fun _ => 0x840c06830844620846080c860662300846080c860662300846080c860662300846080c860662300846080c860662300846080c86066230040012110cc42173040012110cc421730846080c860662300846080c86066230040012110cc42173040012110cc421730486040b050a6441040012110cc421630846080c860662300846080c860662300486040b050a64410800112494c841640800112094c841740800112094c841640800112094c841640846080e8606623008460c0e8706623008460c0e870662300800112094c841740800112094c841740486040b050a64410800112294c841640846080c8606623008460c0e8706623008460c0e8706623008460c0e870662300486040b050a644108460c0e870662301020528151a085840846080c8606623008460c0e8706623000a8129348ac85400c0c029348e4e04300e8329348ac8740040012110cc421730846080c860662300846080c86066230040012110cc421731021182c570a918404860c0f070a644100a8128340a8854100a8130380c8854100a8128340a8854100a8128340a885410228182e162a91320800112094c8416300a8128340a8854100a8128340a8854100a8128340a8854100a8128340a8854100a8128340a885410c1201a4d0e9608300a8128340a8853108420121104c22700228182e162a913218060291c9a4e07300e8329348ac873004860c0f070a644100a8128340a8854100e8329348ac87400846080e860662300a0c09068260d04208460c0e870662300486040b050a64410a0c09068260d0420243080c8606323100220603818221400022060381822140002206038182214000220603818221400022060381822140022306038182313000220291c8a6213002230291c8a6313000220291c8a6213002230291c8a6313000220291c8a6213000220291c8a62130400000000000012d400000000000012c40000000000001234000000000000121400000000000011d40000000000001184000000000000116400000000000011440000000000001134000000000000112400000000000010e) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_101 : CutRow g503 8 101 96 := shortcutBlock (data:=fun _ => 0x220211888621400a0c08261228d0530486040b050a645208460c06830462410486040b050a645208460c068304624100a2421188862530040012110cc4218304860416090c647202080907826090530846080c86066230040012110cc4217308460c0e8706623008460c0e870662300088028340a884410088030380c884410088030380c8844108420121104c22710846080c86066281202201844062216000c8228340a8864100a8128340a8854100a8128340a885411000428151a0848400a8128340a885410088029348ac84410486040b050a64420486040b050a644218060291c9a4e07400c8229348ac86410022021188862170002202118886217018060291c9a4e08500a8128340a88541020808261228904318060291c9a4e07400a8128340a885411000428151a0848400a8128340a885410088029348ac844100a8128340a885410084040b050a446204860602818864421002082c970aa0753012082c970ba06500a8128340a885410084040b050a446202080826122890430208082612289043202201844062215018060291c9a4e0741818041e0d87e0650084040b050a446208420121104c227102080826122890731024028240a241500c0c029348e4e0860084040b050a44720846080c8606624100240184c062418000240184c06241800084040b050a44720084040b050a447208420121104c22410c1201a4d0e9e0871001082453089085040012110cc42183084608068204624102080826122890730042080c860622610a0c09269268d04208460806820462411000428151a084850a0c09068260d0430846080c860662410022021188862140100108245308908500c8229348ac865100220603818221400846080c860662410800112094c8418408460826120c62610800112094c841840486040b050a64520088029348ac847108460c068304624102080826122890730208082612289073008404028108446208460c068304624108460c0683046241002401028042418008460c06830462410042080c860622711000428151a084850024010280424180) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_197 : CutRow g503 8 197 96 := shortcutBlock (data:=fun _ => 0x642121904a4340002202118886213000642121904a434008460c06830462300800112094c84174040012110cc421730800112094c841740486040b050a64410400160305c021830400280c0e4222830042080c860622710486040b050a64520800112094c8418400220603818221400022021188862140002202118886214000220211888621400022021188862140002202118886214000220211888621400022021188862140040012110cc42183040012110cc42173040012110cc42173040012110cc42173040012110cc42173040012110cc42173040012110cc421730285040b050a54420084040b050a444200c4241b0d0e463108460c068304624100220205008221800042080c86062271008404038108444200a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a242118886253000a24211888625300846080c860662410846080c860662410c04280c0e426283040012110cc421730846080c86066230040012110cc4217300a8130380c8854100a8130380c885410846080c86066230040012110cc421730846080c86066230040012110cc421730846080c860662300846080c860662300486040b050a644108460c068304623008460c0e870662300846082c960e623100a24211888625300846082c960e623108460c068304623100c2482c960e26610846080c86066230040012110cc421730846080c8606623008460c068304623000a8130380c8854100a8130380c88541040012110cc421830400280c0e422283040012110cc4218300642121904a43400c04280c0e42627300220211888621300c04280c0e426273002202118886213000c4241b0d0e466100c4241b0d0e466100840c07030844520846080c860662410846080c860662410042080c8606226108420121104c227100642121904a434000642121904a43400c04280c0e42627300c4241b0d0e466100c4241b0d0e46610846080c860662410a47080c86067231) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_293 : CutRow g503 8 293 9 := shortcutBlock (data:=fun _ => 0x846080c86066230040012110cc421730846080c86066230040012110cc421730846080c860662300846080c860662300042080c860622710800440a1582448404002c060b402273) (by decide +kernel)
theorem g503B8 : CutRow g503 8 0 302 := (@joinRow g503 8 0 101 201 (@joinRow g503 8 0 5 96 g503P8_0 g503P8_5) (@joinRow g503 8 101 96 105 g503P8_101 (@joinRow g503 8 197 96 9 g503P8_197 g503P8_293)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_0 : CutRow g503 9 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_3 : CutRow g503 9 3 53 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_56 : CutRow g503 9 56 3 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_59 : CutRow g503 9 59 96 := shortcutBlock (data:=fun _ => 0x2080826122890830486040b050a645202080826122890830a0c09068260d06300500184c06502610a0c09068260d06300500184c065026100500184c065026100500184c06502610c1201a4d0e960640228182e162a91520a0c09068260d0520a0c09068260d0520228182e162a91520228182e162a91520a0c09068260d0520a0c09068260d0520228182e162a915200701184c065036000a8128340a8855100a8128340a8855100701184c065036000701184c065036000220603818221400022060381822140002206038182214000220603818221400042080c860622410042080c860622410022021188862140002206038182214000220603818221400243080c86063231400000000000017240000000000001714000000000000170400000000000016f400000000000016e400000000000016d400000000000016c400000000000016b400000000000016a4000000000000169400000000000016840000000000001674000000000000166400000000000016540000000000001644000000000000163400000000000016240000000000001614000000000000160400000000000015f400000000000015e400000000000015d400000000000015c400000000000015b400000000000015a4000000000000159400000000000015840000000000001574000000000000156400000000000015540000000000001544000000000000153400000000000015240000000000001514000000000000150400000000000014f400000000000014e400000000000014d400000000000014c400000000000014b400000000000014a4000000000000149400000000000014840000000000001474000000000000146400000000000014540000000000001444000000000000143400000000000014240000000000001414000000000000140400000000000013f400000000000013e400000000000013d400000000000013c400000000000013b400000000000013a400000000000013940000000000001384000000000000137400000000000013640000000000001354000000000000134) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_155 : CutRow g503 9 155 96 := shortcutBlock (data:=fun _ => 0x8460c06830462410088028340a884620a0c08261228d0630a0c09068260d063020808261228906300500184c06502710084040b050a44520084040b050a44520846080c860662410810041e0d87407508460c06830462410088028340a88452002409058242415008460c068304624108460c068304624108460c068304624108460c068304624108460c06830462410486040b050a6452020808261228906308460c06830462410a0c08261228d0630846080c860662410022021188862140020808261228908308460c068304624108460c068304624108460c068304624108460c068304624108460c06830462410a0c08261228d06308460c06830462410486040b050a645208460c068304624108460c068304624102080826122890830a0c09068260d0530a0c09068260d0530a0c09068260d0520a0c09068260d052020808261228906302080826122890630846080c8606624100220211888621400846080c860662410022021188862140020808261228909302080826122890630a0c08261228d0630846080c860662410a0c08261228d06300500184c065027102080826122890630846080c860662410846080c86066241002202118886214006120416092530730088028340a8846206120416092530730486040b050a64520486040b050a64520088028340a884620088028340a884520088028340a8845202080826122890530a0c09068260d0530a0c09068260d05302080826122890533012082c970ba0753012082c970ba07518060291c9a4e0850088028340a8845202080826122890530a0c09068260d0530a0c09068260d05302080826122890530088028340a884520088028340a8845218060291c9a4e0850486040b050a64520088028340a884620084040b050a44720084040b050a44720208082612289053240601a1d26960962098030380c984620846080c860662410846080c8606624102080826122890830a0c09068260d0630c1201a4d0e960642098030380c98462061204160925307304860c070308645204860c07030864520486040b050a6452) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_251 : CutRow g503 9 251 61 := shortcutBlock (data:=fun _ => 0x486040b050a645200500184c065027108460c068304624108460c068304624108460c068304624108460c068304624108460c0683046241102c09058242c15000500184c065027108460c068304624108460c068304624108460c068304624108460c068304624100240905824241500810001c0c8740750486040b050a64520486040b050a645200220603818221400486040b050a64920486040b050a64520486040b050a645208460c06830462410486040b050a64520486040b050a64920486040b050a64420486040b050a644100500184c065027100240905824241500408082e164aa06400220603818221400408082e164aa06400220603818221400486040b050a648200240905824241500486040b050a64520408082e164aa06404860c070308645200240905824241500846080c860662410846080c86066241002206038182214004860c070308645200220211888621400022021188862140002202118886214000220211888621400022021188862140002202118886214000220211888621400022021188862140002202118886214000240905824241500024090582424150002409058242415000240905824241500846080c860662410084040b050a44520084040b050a44520084040b050a44520084040b050a445208460c0683046241) (by decide +kernel)
theorem g503B9 : CutRow g503 9 0 312 := (@joinRow g503 9 0 59 253 (@joinRow g503 9 0 3 56 g503P9_0 (@joinRow g503 9 3 53 3 g503P9_3 g503P9_56)) (@joinRow g503 9 59 96 157 g503P9_59 (@joinRow g503 9 155 96 61 g503P9_155 g503P9_251)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_0 : CutRow g503 10 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_6 : CutRow g503 10 6 13 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_19 : CutRow g503 10 19 28 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B10 : CutRow g503 10 0 47 := (@joinRow g503 10 0 6 41 g503P10_0 (@joinRow g503 10 6 13 28 g503P10_6 g503P10_19))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : CutRow g503 11 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B11 : CutRow g503 11 0 6 := g503P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P12_0 : CutRow g503 12 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B12 : CutRow g503 12 0 1 := g503P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503T : mixedTables g503 12 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty g503 0 0)
  · exact (mixedEmpty g503 1 0)
  · exact (mixedEmpty g503 2 0)
  · exact (mixedEmpty g503 3 0)
  · exact (mixedEmpty g503 4 0)
  · exact (mixedEmpty g503 5 0)
  · exact (mixedEmpty g503 6 0)
  · exact g503B7
  · exact g503B8
  · exact g503B9
  · exact g503B10
  · exact g503B11
  · exact g503B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : graphValid g503 (boundsBefore KS487) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS503 : Lower true (varsX 503) (graphGoal 503) 13 := lowerMixed (g:=g503) (i:=0) (hints:=4832298581) (before_sound KS487 VS487) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS503 := extendKnown KS487 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS503 : Known true KS503 := extend_ok (m:=503) VS487 lowS503 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0)]
def g511C : List ColumnInfo := [(8,0,503,0,13)]
def g511A : List (List Nat) := [[],[16,66,134],[32,65,117],[64,33,117,134]]
def g511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3ff
def g511L : Nat → Packing
  | 13 => (1,0,1,0,0,0,0,g511D13)
  | _ => emptyPacking
def g511I (_ _ : Nat) : Option (Nat × Nat) := none
def g511 : Forest := ⟨511,13,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P13_0 : block g511 13 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B13 : block g511 13 0 1=true := g511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511T : checkedTables g511 13 := by
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
  · exact (rfl : block g511 12 0 0 = true)
  · exact g511B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : graphValid g511 (boundsBefore KS503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 13 inputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=13) (i:=0) (before_sound KS503 VS503) g511G g511T (by decide) (by decide +kernel)
def mo328Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x33cf3cf3cf3cf3cf,0x1145145145145145),(0x0,0x0),(0x0,0x0),(0x3cf3cf3cf3cf3cf3,0x2492492492492492),(0x0,0x0),(0xf3cf3cf3cf3cf3c,0xa28a28a28a28a28)]
def mo328C : List ColumnInfo := []
def mo328A : List (List Nat) := [[],[134],[99],[99,131],[131,99],[131]]
def mo328D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def mo328L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,mo328D3)
  | _ => emptyPacking
def mo328I (_ _ : Nat) : Option (Nat × Nat) := none
def mo328 : Forest := ⟨1352,3,fun i => mo328Y[i]?.getD (0,0),mo328C,mo328A,mo328L,mo328I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo328P3_0 : CutRow mo328 3 0 1 := shortcutBlock (data:=fun _ => 0x4000000000000000) (by decide +kernel)
theorem mo328B3 : CutRow mo328 3 0 1 := mo328P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo328T : mixedTables mo328 3 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo328 0 0)
  · exact (mixedEmpty mo328 1 0)
  · exact (mixedEmpty mo328 2 0)
  · exact mo328B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo328G : graphValid mo328 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM328 : Lower false (varsX 328) (graphGoal 328) 4 := lowerMixed (g:=mo328) (i:=0) (hints:=12935258112) (before_sound [] (known_down baseKnown)) mo328G mo328T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM328 := extendKnown [] 4 [(328,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM328 : Known false KM328 := extend_ok (m:=328) (known_down baseKnown) lowM328 (by decide +kernel)
theorem lowM99 : Lower false (varsX 99) (graphGoal 99) 4 := lower_down lowS99
def KM99 := extendKnown KM328 4 [(105,[49,33,101]),(165,[112,16,33,98]),(166,[112,32,98]),(204,[32,49,101,117]),(228,[32,81,49,67,116]),(298,[16,48,32,133,101,118]),(353,[96,81,33,50,67,64,132,116]),(418,[16,112,32,50,67,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM99 : Known false KM99 := extend_ok (m:=99) VM328 lowM99 (by decide +kernel)
def mo329Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo329C : List ColumnInfo := []
def mo329A : List (List Nat) := [[],[131]]
def mo329D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def mo329L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,mo329D4)
  | _ => emptyPacking
def mo329I (_ _ : Nat) : Option (Nat × Nat) := none
def mo329 : Forest := ⟨1353,4,fun i => mo329Y[i]?.getD (0,0),mo329C,mo329A,mo329L,mo329I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329P4_0 : CutRow mo329 4 0 1 := shortcutBlock (data:=fun _ => 0x4000000000000001) (by decide +kernel)
theorem mo329B4 : CutRow mo329 4 0 1 := mo329P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329T : mixedTables mo329 4 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo329 0 0)
  · exact (mixedEmpty mo329 1 0)
  · exact (mixedEmpty mo329 2 0)
  · exact (mixedEmpty mo329 3 0)
  · exact mo329B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329G : graphValid mo329 (boundsBefore KM99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM329 : Lower false (varsX 329) (graphGoal 329) 5 := lowerMixed (g:=mo329) (i:=0) (hints:=12884926470) (before_sound KM99 VM99) mo329G mo329T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM329 := extendKnown KM99 5 [(329,[]),(330,[16,134]),(332,[32,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM329 : Known false KM329 := extend_ok (m:=329) VM99 lowM329 (by decide +kernel)
theorem lowM103 : Lower false (varsX 103) (graphGoal 103) 5 := lower_down lowS103
def KM103 := extendKnown KM329 5 [(484,[32,81,128,48,65,116,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM103 : Known false KM103 := extend_ok (m:=103) VM329 lowM103 (by decide +kernel)
theorem lowM229 : Lower false (varsX 229) (graphGoal 229) 7 := lower_down lowS229
def KM229 := extendKnown KM103 7 [(229,[]),(355,[33,129,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM229 : Known false KM229 := extend_ok (m:=229) VM103 lowM229 (by decide +kernel)
def mo331Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo331C : List ColumnInfo := []
def mo331A : List (List Nat) := [[],[16,134]]
def mo331D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def mo331L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo331D5)
  | _ => emptyPacking
def mo331I (_ _ : Nat) : Option (Nat × Nat) := none
def mo331 : Forest := ⟨1355,5,fun i => mo331Y[i]?.getD (0,0),mo331C,mo331A,mo331L,mo331I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331P5_0 : CutRow mo331 5 0 1 := shortcutBlock (data:=fun _ => 0x4000000000000002) (by decide +kernel)
theorem mo331B5 : CutRow mo331 5 0 1 := mo331P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331T : mixedTables mo331 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo331 0 0)
  · exact (mixedEmpty mo331 1 0)
  · exact (mixedEmpty mo331 2 0)
  · exact (mixedEmpty mo331 3 0)
  · exact (mixedEmpty mo331 4 0)
  · exact mo331B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331G : graphValid mo331 (boundsBefore KM229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM331 : Lower false (varsX 331) (graphGoal 331) 6 := lowerMixed (g:=mo331) (i:=0) (hints:=4294992006) (before_sound KM229 VM229) mo331G mo331T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM331 := extendKnown KM229 6 [(331,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM331 : Known false KM331 := extend_ok (m:=331) VM229 lowM331 (by decide +kernel)
def mo333Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo333C : List ColumnInfo := []
def mo333A : List (List Nat) := [[],[131],[32],[32,131]]
def mo333D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def mo333L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo333D5)
  | _ => emptyPacking
def mo333I (_ _ : Nat) : Option (Nat × Nat) := none
def mo333 : Forest := ⟨1357,5,fun i => mo333Y[i]?.getD (0,0),mo333C,mo333A,mo333L,mo333I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333P5_0 : CutRow mo333 5 0 1 := shortcutBlock (data:=fun _ => 0x4000000000000003) (by decide +kernel)
theorem mo333B5 : CutRow mo333 5 0 1 := mo333P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333T : mixedTables mo333 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo333 0 0)
  · exact (mixedEmpty mo333 1 0)
  · exact (mixedEmpty mo333 2 0)
  · exact (mixedEmpty mo333 3 0)
  · exact (mixedEmpty mo333 4 0)
  · exact mo333B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333G : graphValid mo333 (boundsBefore KM331) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM333 : Lower false (varsX 333) (graphGoal 333) 6 := lowerMixed (g:=mo333) (i:=0) (hints:=12884928006) (before_sound KM331 VM331) mo333G mo333T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM333 := extendKnown KM331 6 [(333,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM333 : Known false KM333 := extend_ok (m:=333) VM331 lowM333 (by decide +kernel)
def mo361Y : Array (Bits × Bits) := #[(0x3c1e0f0783c1e0f,0x190c86432190c864),(0x0,0x0),(0x0,0x0),(0x1c0e070381c0e070,0x944a25128944a25),(0x0,0x0),(0xc06030180c0603,0x26f379bcde6f379b),(0x273399cce673399c,0x26130984c2613098),(0x0,0x0),(0x383c1e0f0783c1e0,0x10a8542a150a8542)]
def mo361C : List ColumnInfo := [(32,0,329,0,5),(1,32,328,0,4),(8,0,353,0,4),(256,0,105,0,4)]
def mo361A : List (List Nat) := [[],[131]]
def mo361D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30fd41fd31
def mo361D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7089f
def mo361H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb4002a
def mo361L : Nat → Packing
  | 5 => (2,1,2,0,0,3,0,mo361D5)
  | 6 => (1,0,2,0,0,0,0,mo361D6)
  | _ => emptyPacking
def mo361I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 1 1 mo361H6
  | _ => fun _ => none
def mo361 : Forest := ⟨1385,6,fun i => mo361Y[i]?.getD (0,0),mo361C,mo361A,mo361L,mo361I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361P5_0 : CutRow mo361 5 0 2 := shortcutBlock (data:=fun _ => 0x20260141a052413001260141a0524130) (by decide +kernel)
theorem mo361B5 : CutRow mo361 5 0 2 := mo361P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361P6_0 : CutRow mo361 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo361B6 : CutRow mo361 6 0 1 := mo361P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361T : mixedTables mo361 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo361 0 0)
  · exact (mixedEmpty mo361 1 0)
  · exact (mixedEmpty mo361 2 0)
  · exact (mixedEmpty mo361 3 0)
  · exact (mixedEmpty mo361 4 0)
  · exact mo361B5
  · exact mo361B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361G : graphValid mo361 (boundsBefore KM333) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM361 : Lower false (varsX 361) (graphGoal 361) 7 := lowerMixed (g:=mo361) (i:=0) (hints:=12884926469) (before_sound KM333 VM333) mo361G mo361T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM361 := extendKnown KM333 7 [(361,[]),(362,[16,134]),(460,[32,16,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM361 : Known false KM361 := extend_ok (m:=361) VM333 lowM361 (by decide +kernel)
def mo488Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo488C : List ColumnInfo := []
def mo488A : List (List Nat) := [[],[134],[117],[117,134],[99],[99,131],[99,117],[99,117,131],[131,99],[131],[131,117,99],[131,117]]
def mo488D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def mo488L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo488D5)
  | _ => emptyPacking
def mo488I (_ _ : Nat) : Option (Nat × Nat) := none
def mo488 : Forest := ⟨1512,5,fun i => mo488Y[i]?.getD (0,0),mo488C,mo488A,mo488L,mo488I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488P5_0 : CutRow mo488 5 0 1 := shortcutBlock (data:=fun _ => 0x4000000000000005) (by decide +kernel)
theorem mo488B5 : CutRow mo488 5 0 1 := mo488P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488T : mixedTables mo488 5 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo488 0 0)
  · exact (mixedEmpty mo488 1 0)
  · exact (mixedEmpty mo488 2 0)
  · exact (mixedEmpty mo488 3 0)
  · exact (mixedEmpty mo488 4 0)
  · exact mo488B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488G : graphValid mo488 (boundsBefore KM361) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM488 : Lower false (varsX 488) (graphGoal 488) 6 := lowerMixed (g:=mo488) (i:=0) (hints:=14284775424) (before_sound KM361 VM361) mo488G mo488T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM488 := extendKnown KM361 6 [(488,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM488 : Known false KM488 := extend_ok (m:=488) VM361 lowM488 (by decide +kernel)
theorem lowM231 : Lower false (varsX 231) (graphGoal 231) 8 := lower_down lowS231
def KM231 := extendKnown KM488 8 [(231,[]),(237,[32,49,80,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM231 : Known false KM231 := extend_ok (m:=231) VM488 lowM231 (by decide +kernel)
def mo238Y : Array (Bits × Bits) := #[(0x0,0x0),(0x101010101010101,0x39b9b9b9b9b9b9b9),(0x3636363636363636,0x1313131313131313),(0x808080808080808,0x3b3b3b3b3b3b3b3b),(0x0,0x0),(0x1c1c1c1c1c1c1c1,0x646464646464646),(0xe0e0e0e0e0e0e0e,0x4c4c4c4c4c4c4c4),(0x30f0f0f0f0f0f0f0,0x28a8a8a8a8a8a8a8),(0x0,0x0)]
def mo238C : List ColumnInfo := []
def mo238A : List (List Nat) := [[],[49,114,101]]
def mo238D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo238L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,mo238D6)
  | _ => emptyPacking
def mo238I (_ _ : Nat) : Option (Nat × Nat) := none
def mo238 : Forest := ⟨1262,6,fun i => mo238Y[i]?.getD (0,0),mo238C,mo238A,mo238L,mo238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238P6_0 : CutRow mo238 6 0 1 := shortcutBlock (data:=fun _ => 0x6000000000000000) (by decide +kernel)
theorem mo238B6 : CutRow mo238 6 0 1 := mo238P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238T : mixedTables mo238 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo238 0 0)
  · exact (mixedEmpty mo238 1 0)
  · exact (mixedEmpty mo238 2 0)
  · exact (mixedEmpty mo238 3 0)
  · exact (mixedEmpty mo238 4 0)
  · exact (mixedEmpty mo238 5 0)
  · exact mo238B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238G : graphValid mo238 (boundsBefore KM231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM238 : Lower false (varsX 238) (graphGoal 238) 7 := lowerMixed (g:=mo238) (i:=0) (hints:=571500112) (before_sound KM231 VM231) mo238G mo238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM238 := extendKnown KM231 7 [(238,[]),(430,[33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM238 : Known false KM238 := extend_ok (m:=238) VM231 lowM238 (by decide +kernel)
theorem lowM243 : Lower false (varsX 243) (graphGoal 243) 7 := lower_down lowS243
def KM243 := extendKnown KM238 7 [(423,[16,50,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM243 : Known false KM243 := extend_ok (m:=243) VM238 lowM243 (by decide +kernel)
def mo335Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0)]
def mo335C : List ColumnInfo := []
def mo335A : List (List Nat) := [[],[32]]
def mo335D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo335L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,mo335D6)
  | _ => emptyPacking
def mo335I (_ _ : Nat) : Option (Nat × Nat) := none
def mo335 : Forest := ⟨1359,6,fun i => mo335Y[i]?.getD (0,0),mo335C,mo335A,mo335L,mo335I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335P6_0 : CutRow mo335 6 0 1 := shortcutBlock (data:=fun _ => 0x4000000000000004) (by decide +kernel)
theorem mo335B6 : CutRow mo335 6 0 1 := mo335P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335T : mixedTables mo335 6 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo335 0 0)
  · exact (mixedEmpty mo335 1 0)
  · exact (mixedEmpty mo335 2 0)
  · exact (mixedEmpty mo335 3 0)
  · exact (mixedEmpty mo335 4 0)
  · exact (mixedEmpty mo335 5 0)
  · exact mo335B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335G : graphValid mo335 (boundsBefore KM243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM335 : Lower false (varsX 335) (graphGoal 335) 7 := lowerMixed (g:=mo335) (i:=0) (hints:=4294993542) (before_sound KM243 VM243) mo335G mo335T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM335 := extendKnown KM243 7 [(335,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM335 : Known false KM335 := extend_ok (m:=335) VM243 lowM335 (by decide +kernel)
def mo363Y : Array (Bits × Bits) := #[(0x30038f0038f0038f,0x12a2852a2852a285),(0xe0700e0700e070,0x1069a1069a1069a1),(0x0,0x0),(0x31c0031c0031c00,0x3124931249312493),(0x0,0x0),(0x30007f0007f0007f,0x2d145ad145ad145a),(0xc1f80c1f80c1f80,0x459604596045960),(0x0,0x0),(0xfe000fe000fe000,0xa820ca820ca820c)]
def mo363C : List ColumnInfo := [(1,0,362,0,7),(2,0,361,0,7),(8,0,355,0,7),(0,32,328,3,6),(32,0,331,0,6)]
def mo363A : List (List Nat) := [[],[16,134]]
def mo363D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc3faa9fc54
def mo363D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def mo363H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f40000
def mo363L : Nat → Packing
  | 7 => (2,1,3,0,0,3,0,mo363D7)
  | 8 => (1,0,3,0,0,0,0,mo363D8)
  | _ => emptyPacking
def mo363I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 7 0 5 1 0 mo363H8
  | _ => fun _ => none
def mo363 : Forest := ⟨1387,8,fun i => mo363Y[i]?.getD (0,0),mo363C,mo363A,mo363L,mo363I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363P7_0 : CutRow mo363 7 0 2 := shortcutBlock (data:=fun _ => 0x600000000000004d600000000000004c) (by decide +kernel)
theorem mo363B7 : CutRow mo363 7 0 2 := mo363P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363P8_0 : CutRow mo363 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo363B8 : CutRow mo363 8 0 1 := mo363P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363T : mixedTables mo363 8 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo363 0 0)
  · exact (mixedEmpty mo363 1 0)
  · exact (mixedEmpty mo363 2 0)
  · exact (mixedEmpty mo363 3 0)
  · exact (mixedEmpty mo363 4 0)
  · exact (mixedEmpty mo363 5 0)
  · exact (mixedEmpty mo363 6 0)
  · exact mo363B7
  · exact mo363B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363G : graphValid mo363 (boundsBefore KM335) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM363 : Lower false (varsX 363) (graphGoal 363) 9 := lowerMixed (g:=mo363) (i:=0) (hints:=4294991957) (before_sound KM335 VM335) mo363G mo363T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM363 := extendKnown KM335 9 [(363,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM363 : Known false KM363 := extend_ok (m:=363) VM335 lowM363 (by decide +kernel)
def mo365Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo365C : List ColumnInfo := [(4,0,361,0,7)]
def mo365A : List (List Nat) := [[],[131]]
def mo365D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo365L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo365D7)
  | _ => emptyPacking
def mo365I (_ _ : Nat) : Option (Nat × Nat) := none
def mo365 : Forest := ⟨1389,7,fun i => mo365Y[i]?.getD (0,0),mo365C,mo365A,mo365L,mo365I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo365P7_0 : block mo365 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo365B7 : block mo365 7 0 1=true := mo365P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo365T : checkedTables mo365 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo365 0 0 0 = true)
  · exact (rfl : block mo365 1 0 0 = true)
  · exact (rfl : block mo365 2 0 0 = true)
  · exact (rfl : block mo365 3 0 0 = true)
  · exact (rfl : block mo365 4 0 0 = true)
  · exact (rfl : block mo365 5 0 0 = true)
  · exact (rfl : block mo365 6 0 0 = true)
  · exact mo365B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo365G : graphValid mo365 (boundsBefore KM363) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM365 : Lower false (varsX 365) (graphGoal 365) 8 := lower_forest (g:=mo365) (i:=0) (hints:=12884928005) (before_sound KM363 VM363) mo365G mo365T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM365 := extendKnown KM363 8 [(365,[]),(461,[32,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM365 : Known false KM365 := extend_ok (m:=365) VM363 lowM365 (by decide +kernel)
def mo366Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo366C : List ColumnInfo := [(4,0,362,0,7)]
def mo366A : List (List Nat) := [[]]
def mo366D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo366L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo366D7)
  | _ => emptyPacking
def mo366I (_ _ : Nat) : Option (Nat × Nat) := none
def mo366 : Forest := ⟨1390,7,fun i => mo366Y[i]?.getD (0,0),mo366C,mo366A,mo366L,mo366I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366P7_0 : block mo366 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo366B7 : block mo366 7 0 1=true := mo366P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366T : checkedTables mo366 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo366 0 0 0 = true)
  · exact (rfl : block mo366 1 0 0 = true)
  · exact (rfl : block mo366 2 0 0 = true)
  · exact (rfl : block mo366 3 0 0 = true)
  · exact (rfl : block mo366 4 0 0 = true)
  · exact (rfl : block mo366 5 0 0 = true)
  · exact (rfl : block mo366 6 0 0 = true)
  · exact mo366B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo366G : graphValid mo366 (boundsBefore KM365) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM366 : Lower false (varsX 366) (graphGoal 366) 8 := lower_forest (g:=mo366) (i:=0) (hints:=4329596496) (before_sound KM365 VM365) mo366G mo366T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM366 := extendKnown KM365 8 [(366,[]),(377,[16,66,134]),(462,[33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM366 : Known false KM366 := extend_ok (m:=366) VM365 lowM366 (by decide +kernel)
theorem lowM486 : Lower false (varsX 486) (graphGoal 486) 8 := lower_down lowS486
def KM486 := extendKnown KM366 8 [(486,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM486 : Known false KM486 := extend_ok (m:=486) VM366 lowM486 (by decide +kernel)
def mo239Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo239C : List ColumnInfo := [(2,0,237,0,8)]
def mo239A : List (List Nat) := [[],[49,114,101]]
def mo239D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo239L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo239D8)
  | _ => emptyPacking
def mo239I (_ _ : Nat) : Option (Nat × Nat) := none
def mo239 : Forest := ⟨1263,8,fun i => mo239Y[i]?.getD (0,0),mo239C,mo239A,mo239L,mo239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo239P8_0 : block mo239 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo239B8 : block mo239 8 0 1=true := mo239P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo239T : checkedTables mo239 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo239 0 0 0 = true)
  · exact (rfl : block mo239 1 0 0 = true)
  · exact (rfl : block mo239 2 0 0 = true)
  · exact (rfl : block mo239 3 0 0 = true)
  · exact (rfl : block mo239 4 0 0 = true)
  · exact (rfl : block mo239 5 0 0 = true)
  · exact (rfl : block mo239 6 0 0 = true)
  · exact (rfl : block mo239 7 0 0 = true)
  · exact mo239B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo239G : graphValid mo239 (boundsBefore KM486) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM239 : Lower false (varsX 239) (graphGoal 239) 9 := lower_forest (g:=mo239) (i:=0) (hints:=536897109) (before_sound KM486 VM486) mo239G mo239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM239 := extendKnown KM486 9 [(239,[]),(253,[32,49,80,65,96,112]),(443,[16,66,134]),(446,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM239 : Known false KM239 := extend_ok (m:=239) VM486 lowM239 (by decide +kernel)
theorem lowM247 : Lower false (varsX 247) (graphGoal 247) 9 := lower_down lowS247
def KM247 := extendKnown KM239 9 [(247,[]),(439,[16,66,134]),(471,[32,16,65,101,117,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM247 : Known false KM247 := extend_ok (m:=247) VM239 lowM247 (by decide +kernel)
def mo251Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo251C : List ColumnInfo := []
def mo251A : List (List Nat) := [[]]
def mo251D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo251L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo251D7)
  | _ => emptyPacking
def mo251I (_ _ : Nat) : Option (Nat × Nat) := none
def mo251 : Forest := ⟨1275,7,fun i => mo251Y[i]?.getD (0,0),mo251C,mo251A,mo251L,mo251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251P7_0 : CutRow mo251 7 0 1 := shortcutBlock (data:=fun _ => 0x6000000000000001) (by decide +kernel)
theorem mo251B7 : CutRow mo251 7 0 1 := mo251P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251T : mixedTables mo251 7 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo251 0 0)
  · exact (mixedEmpty mo251 1 0)
  · exact (mixedEmpty mo251 2 0)
  · exact (mixedEmpty mo251 3 0)
  · exact (mixedEmpty mo251 4 0)
  · exact (mixedEmpty mo251 5 0)
  · exact (mixedEmpty mo251 6 0)
  · exact mo251B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251G : graphValid mo251 (boundsBefore KM247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM251 : Lower false (varsX 251) (graphGoal 251) 8 := lowerMixed (g:=mo251) (i:=0) (hints:=1074225237) (before_sound KM247 VM247) mo251G mo251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM251 := extendKnown KM247 8 [(431,[16,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM251 : Known false KM251 := extend_ok (m:=251) VM247 lowM251 (by decide +kernel)
def mo367Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo367C : List ColumnInfo := [(4,0,363,0,9)]
def mo367A : List (List Nat) := [[]]
def mo367D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo367L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,mo367D9)
  | _ => emptyPacking
def mo367I (_ _ : Nat) : Option (Nat × Nat) := none
def mo367 : Forest := ⟨1391,9,fun i => mo367Y[i]?.getD (0,0),mo367C,mo367A,mo367L,mo367I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo367P9_0 : block mo367 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo367B9 : block mo367 9 0 1=true := mo367P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo367T : checkedTables mo367 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo367 0 0 0 = true)
  · exact (rfl : block mo367 1 0 0 = true)
  · exact (rfl : block mo367 2 0 0 = true)
  · exact (rfl : block mo367 3 0 0 = true)
  · exact (rfl : block mo367 4 0 0 = true)
  · exact (rfl : block mo367 5 0 0 = true)
  · exact (rfl : block mo367 6 0 0 = true)
  · exact (rfl : block mo367 7 0 0 = true)
  · exact (rfl : block mo367 8 0 0 = true)
  · exact mo367B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo367G : graphValid mo367 (boundsBefore KM251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM367 : Lower false (varsX 367) (graphGoal 367) 10 := lower_forest (g:=mo367) (i:=0) (hints:=4294993493) (before_sound KM251 VM251) mo367G mo367T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM367 := extendKnown KM251 10 [(367,[]),(379,[16,66,134]),(478,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM367 : Known false KM367 := extend_ok (m:=367) VM251 lowM367 (by decide +kernel)
def mo381Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo381C : List ColumnInfo := [(4,0,377,0,8)]
def mo381A : List (List Nat) := [[]]
def mo381D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo381L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,mo381D8)
  | _ => emptyPacking
def mo381I (_ _ : Nat) : Option (Nat × Nat) := none
def mo381 : Forest := ⟨1405,8,fun i => mo381Y[i]?.getD (0,0),mo381C,mo381A,mo381L,mo381I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo381P8_0 : block mo381 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo381B8 : block mo381 8 0 1=true := mo381P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo381T : checkedTables mo381 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo381 0 0 0 = true)
  · exact (rfl : block mo381 1 0 0 = true)
  · exact (rfl : block mo381 2 0 0 = true)
  · exact (rfl : block mo381 3 0 0 = true)
  · exact (rfl : block mo381 4 0 0 = true)
  · exact (rfl : block mo381 5 0 0 = true)
  · exact (rfl : block mo381 6 0 0 = true)
  · exact (rfl : block mo381 7 0 0 = true)
  · exact mo381B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo381G : graphValid mo381 (boundsBefore KM367) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM381 : Lower false (varsX 381) (graphGoal 381) 9 := lower_forest (g:=mo381) (i:=0) (hints:=12885452293) (before_sound KM367 VM367) mo381G mo381T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM381 := extendKnown KM367 9 [(381,[]),(463,[32,65,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM381 : Known false KM381 := extend_ok (m:=381) VM367 lowM381 (by decide +kernel)
theorem lowM487 : Lower false (varsX 487) (graphGoal 487) 11 := lower_down lowS487
def KM487 := extendKnown KM381 11 [(487,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM487 : Known false KM487 := extend_ok (m:=487) VM381 lowM487 (by decide +kernel)
def mo491Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x3fffffffffffffff),(0x0,0x0),(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo491C : List ColumnInfo := [(128,0,363,0,9)]
def mo491A : List (List Nat) := [[],[16,134]]
def mo491D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo491L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,mo491D9)
  | _ => emptyPacking
def mo491I (_ _ : Nat) : Option (Nat × Nat) := none
def mo491 : Forest := ⟨1515,9,fun i => mo491Y[i]?.getD (0,0),mo491C,mo491A,mo491L,mo491I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491P9_0 : block mo491 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo491B9 : block mo491 9 0 1=true := mo491P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491T : checkedTables mo491 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo491 0 0 0 = true)
  · exact (rfl : block mo491 1 0 0 = true)
  · exact (rfl : block mo491 2 0 0 = true)
  · exact (rfl : block mo491 3 0 0 = true)
  · exact (rfl : block mo491 4 0 0 = true)
  · exact (rfl : block mo491 5 0 0 = true)
  · exact (rfl : block mo491 6 0 0 = true)
  · exact (rfl : block mo491 7 0 0 = true)
  · exact (rfl : block mo491 8 0 0 = true)
  · exact mo491B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo491G : graphValid mo491 (boundsBefore KM487) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM491 : Lower false (varsX 491) (graphGoal 491) 10 := lower_forest (g:=mo491) (i:=0) (hints:=5637169237) (before_sound KM487 VM487) mo491G mo491T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM491 := extendKnown KM487 10 [(491,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM491 : Known false KM491 := extend_ok (m:=491) VM487 lowM491 (by decide +kernel)
def mo493Y : Array (Bits × Bits) := #[(0x1fc00003f800007f,0xc65d7918cbaf231),(0x0,0x0),(0x2000078c0000f180,0x22d342945a68528b),(0x7c07000f80e00,0x28c0d195181a32a3),(0x0,0x0),(0x7c03800f807001f,0x239a082c7341058e),(0x3838007f07000fe0,0x1108286a21050d44),(0x3f800007f000,0x1c24b5438496a870),(0x3fc00007f80000,0x6370600c6e0c018)]
def mo493C : List ColumnInfo := [(32,0,461,0,8),(128,0,365,0,8),(0,32,332,129,7),(0,128,329,36,7),(33,0,460,0,7),(132,0,361,0,7),(264,0,229,0,7),(0,8,165,320,6),(1,128,328,36,6),(4,32,328,129,6),(5,0,488,0,6),(32,128,329,4,6),(160,0,333,0,6),(9,0,484,0,5),(129,32,332,0,5)]
def mo493A : List (List Nat) := [[],[131],[32,117],[32,131,117]]
def mo493D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30df87454120fe94254120
def mo493D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x265444c4fde396ccd82d549d2213c6cc15243c03fea9a85ff50d42ffa84a87fd72503fea1281ff5c540ffa82a07fd41483fea12217f1d132bfae8905fc74483f6a1241fe50120bfae8885fd72443fca0221fe54120
def mo493H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x370
def mo493D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb0c8560b15d88914623d68619712192282c32b8545aa411a83d4c41ac52284d9ba9677583e1a00ff54ffd43ff50bfd32ff543fd40ff483fd10
def mo493H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x95a24118000722c8017f0ea0c33653b8195d53fc1184b0af159488b211400005313137078380061a60c0010cb94003478478a0a8a4576af4808f54411904
def mo493D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xca81ff
def mo493H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81000000000001e66c6e0000000c480000000010000a6004d8460000000000000000000000000cbd9005c800000000000002a000000088800000000000010410d1c000d00000000008
def mo493L : Nat → Packing
  | 7 => (2,3,4,0,0,3,0,mo493D7)
  | 8 => (18,2,4,0,0,7,0,mo493D8)
  | 9 => (8,1,4,0,0,8,0,mo493D9)
  | 10 => (1,0,4,0,0,0,0,mo493D10)
  | _ => emptyPacking
def mo493I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 mo493H8
  | 9 => lookupWord 9 41 5 11 5 2 mo493H9
  | 10 => lookupWord 4 67 2 9 3 2 mo493H10
  | _ => fun _ => none
def mo493 : Forest := ⟨1517,10,fun i => mo493Y[i]?.getD (0,0),mo493C,mo493A,mo493L,mo493I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P7_0 : CutRow mo493 7 0 2 := shortcutBlock (data:=fun _ => 0x248c0c0f030a4430058c044b251a4420) (by decide +kernel)
theorem mo493B7 : CutRow mo493 7 0 2 := mo493P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P8_0 : CutRow mo493 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P8_1 : CutRow mo493 8 1 17 := shortcutBlock (data:=fun _ => 0x30324603818221302498130380c88451058c044b251a44413026060381822130302606038182213030260603818221303026060381822130248c030380c884512498102a144aa0534000000000000009400000000000000860000000000000d960000000000000d860000000000000d7400000000000000760000000000000d64000000000000006) (by decide +kernel)
theorem mo493B8 : CutRow mo493 8 0 18 := (@joinRow mo493 8 0 1 17 mo493P8_0 mo493P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P9_0 : CutRow mo493 9 0 8 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B9 : CutRow mo493 9 0 8 := mo493P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P10_0 : CutRow mo493 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B10 : CutRow mo493 10 0 1 := mo493P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493T : mixedTables mo493 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo493 0 0)
  · exact (mixedEmpty mo493 1 0)
  · exact (mixedEmpty mo493 2 0)
  · exact (mixedEmpty mo493 3 0)
  · exact (mixedEmpty mo493 4 0)
  · exact (mixedEmpty mo493 5 0)
  · exact (mixedEmpty mo493 6 0)
  · exact mo493B7
  · exact mo493B8
  · exact mo493B9
  · exact mo493B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493G : graphValid mo493 (boundsBefore KM491) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM493 : Lower false (varsX 493) (graphGoal 493) 11 := lowerMixed (g:=mo493) (i:=0) (hints:=13421798917) (before_sound KM491 VM491) mo493G mo493T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM493 := extendKnown KM491 11 [(493,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM493 : Known false KM493 := extend_ok (m:=493) VM491 lowM493 (by decide +kernel)
def mo494Y : Array (Bits × Bits) := #[(0x0,0x0),(0x703c000703c0007,0x948d1f0948d1f09),(0x380007c780007c78,0x1b154245b154245b),(0x1c003801c00380,0x1b0c40d1b0c40d1b),(0x0,0x0),(0x700380070038007,0x36350a0f6350a0f6),(0x38e0003f8e0003f8,0x2460992a460992a4),(0x3fc00003fc00,0xcab5b00cab5b00),(0xffc0000ffc0000,0x93260409326040)]
def mo494C : List ColumnInfo := [(8,0,486,0,8),(32,0,462,0,8),(128,0,366,0,8),(0,32,332,130,7),(0,128,330,36,7),(34,0,460,0,7),(64,0,430,0,7),(132,0,362,0,7),(256,0,238,0,7),(0,2,204,288,6),(0,8,166,320,6),(2,32,332,128,6),(2,128,328,36,6),(4,32,328,130,6),(6,0,488,0,6),(32,128,330,4,6),(128,32,332,2,6),(64,4,298,128,5),(64,8,166,256,5),(256,2,204,32,5),(76,0,418,0,4),(266,0,228,0,4),(320,8,166,0,4)]
def mo494A : List (List Nat) := [[],[33,117,134]]
def mo494D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30bed8219153bf98019153
def mo494D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4901385262901a2338616313222b3880d9472387012122338623add0e57137db8d96b34da0cd6531d88c15f2ed70b5592bd58a95328d409d4d25d28914722d1085411fcf8793b1cce06d3519ca53a8f801ff5cd64ffae0b27fd6458ffeb22a7ff19153ffac8a1ffd6550bfeaa285ff58d42ffaa6a17fd4350bfeb22c1ff50960ffa82b07fd64543feb12a1ff50950ffac8a07fd62503fea1281ff58540ffa82a07fd61483fea0a41ff59110ffa84887ec72592feb90c97f5c064bfaeca17bd6450bf6b12857f5d940f7ac8a07f960503fca82817f5d920bfae8907ed62483f690a41fe58120ff280905fd74442feb9221fe50110ff2a0905dd73192f6b90c97e5c064
def mo494H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1e4
def mo494D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40c09e55864c40d14a722518920688f8053472060e01c510720688f8053472040c09e55942081a23c558d1c60093275451d32068071441c880c4e714620600c9d61474601c5385841d4691745110e378ae1f85409000ff593fc64ff58ffd53ff50ffd42ff4cbfd60ff543fd40ff483fd10
def mo494H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc24006b0d5c29400381e3ae7c000000004b4d17170011ab87a928a800000670001a140002315e00000000d1016c00000637e0db2800ca0fa56039800091a0018700076570b1cd43e5b6f4cfcced7ed64da7940004f791328002a1000000003d580064c001c725291aeabb15cc00035ec98000d6a19886295dcaa0001c400000237e0b000001c1520d32000000000018100a800d35293854a7e180022a9184d000001c4c020249
def mo494D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ca1ff
def mo494H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1650000001d60065400007245c014754c2245b900003a28bd00035400d90528d210000000a3007cc018
def mo494L : Nat → Packing
  | 7 => (2,3,5,0,0,3,0,mo494D7)
  | 8 => (49,2,5,0,0,9,0,mo494D8)
  | 9 => (12,1,5,0,0,10,0,mo494D9)
  | 10 => (1,0,5,0,0,0,0,mo494D10)
  | _ => emptyPacking
def mo494I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 mo494H8
  | 9 => lookupWord 18 113 5 11 6 1 mo494H9
  | 10 => lookupWord 5 37 1 9 4 1 mo494H10
  | _ => fun _ => none
def mo494 : Forest := ⟨1518,10,fun i => mo494Y[i]?.getD (0,0),mo494C,mo494A,mo494L,mo494I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P7_0 : CutRow mo494 7 0 2 := shortcutBlock (data:=fun _ => 0x18524c0683042220248c2c060b402272) (by decide +kernel)
theorem mo494B7 : CutRow mo494 7 0 2 := mo494P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_0 : CutRow mo494 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_3 : CutRow mo494 8 3 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_4 : CutRow mo494 8 4 45 := shortcutBlock (data:=fun _ => 0x18524c068304223018524c0683042230248c2c070308444118524c068304223018524c06830422302498030380c8845118524c068304223018524c0683042230058c24432118444118524c06830422302498030380c8845118524c068304223018524c068304223018524c0683042230248c2c0703084441248c2453291c4441058c2453291c44412498030380c8845101cc2453291c444101cc2453291c444124980032184ca053248c230380c8845124980032184ca053248c230380c8845124980032184ca053058c2453291c444160000000000000e760000000000000e660000000000000e5400000000000000f60000000000000e460000000000000e3400000000000000e60000000000000e260000000000000e160000000000000e0400000000000000d60000000000000df60000000000000de60000000000000dd60000000000000dc60000000000000db400000000000000c400000000000000b60000000000000da) (by decide +kernel)
theorem mo494B8 : CutRow mo494 8 0 49 := (@joinRow mo494 8 0 3 46 mo494P8_0 (@joinRow mo494 8 3 1 45 mo494P8_3 mo494P8_4))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P9_0 : CutRow mo494 9 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B9 : CutRow mo494 9 0 12 := mo494P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P10_0 : CutRow mo494 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B10 : CutRow mo494 10 0 1 := mo494P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494T : mixedTables mo494 10 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo494 0 0)
  · exact (mixedEmpty mo494 1 0)
  · exact (mixedEmpty mo494 2 0)
  · exact (mixedEmpty mo494 3 0)
  · exact (mixedEmpty mo494 4 0)
  · exact (mixedEmpty mo494 5 0)
  · exact (mixedEmpty mo494 6 0)
  · exact mo494B7
  · exact mo494B8
  · exact mo494B9
  · exact mo494B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494G : graphValid mo494 (boundsBefore KM493) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM494 : Lower false (varsX 494) (graphGoal 494) 11 := lowerMixed (g:=mo494) (i:=0) (hints:=4866467408) (before_sound KM493 VM493) mo494G mo494T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM494 := extendKnown KM493 11 [(494,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM494 : Known false KM494 := extend_ok (m:=494) VM493 lowM494 (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo255C : List ColumnInfo := [(2,0,253,0,9)]
def mo255A : List (List Nat) := [[],[32,65,117]]
def mo255D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo255L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,mo255D9)
  | _ => emptyPacking
def mo255I (_ _ : Nat) : Option (Nat × Nat) := none
def mo255 : Forest := ⟨1279,9,fun i => mo255Y[i]?.getD (0,0),mo255C,mo255A,mo255L,mo255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255P9_0 : block mo255 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo255B9 : block mo255 9 0 1=true := mo255P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255T : checkedTables mo255 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo255 0 0 0 = true)
  · exact (rfl : block mo255 1 0 0 = true)
  · exact (rfl : block mo255 2 0 0 = true)
  · exact (rfl : block mo255 3 0 0 = true)
  · exact (rfl : block mo255 4 0 0 = true)
  · exact (rfl : block mo255 5 0 0 = true)
  · exact (rfl : block mo255 6 0 0 = true)
  · exact (rfl : block mo255 7 0 0 = true)
  · exact (rfl : block mo255 8 0 0 = true)
  · exact mo255B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo255G : graphValid mo255 (boundsBefore KM494) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM255 : Lower false (varsX 255) (graphGoal 255) 10 := lower_forest (g:=mo255) (i:=0) (hints:=537355861) (before_sound KM494 VM494) mo255G mo255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM255 := extendKnown KM494 10 [(255,[]),(447,[16,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM255 : Known false KM255 := extend_ok (m:=255) VM494 lowM255 (by decide +kernel)
def mo383Y : Array (Bits × Bits) := #[(0x3fffffffffffffff,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x0,0x3fffffffffffffff),(0x3fffffffffffffff,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def mo383C : List ColumnInfo := [(4,0,379,0,10)]
def mo383A : List (List Nat) := [[],[16,66,134]]
def mo383D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def mo383L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,mo383D10)
  | _ => emptyPacking
def mo383I (_ _ : Nat) : Option (Nat × Nat) := none
def mo383 : Forest := ⟨1407,10,fun i => mo383Y[i]?.getD (0,0),mo383C,mo383A,mo383L,mo383I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383P10_0 : block mo383 10 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo383B10 : block mo383 10 0 1=true := mo383P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383T : checkedTables mo383 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo383 0 0 0 = true)
  · exact (rfl : block mo383 1 0 0 = true)
  · exact (rfl : block mo383 2 0 0 = true)
  · exact (rfl : block mo383 3 0 0 = true)
  · exact (rfl : block mo383 4 0 0 = true)
  · exact (rfl : block mo383 5 0 0 = true)
  · exact (rfl : block mo383 6 0 0 = true)
  · exact (rfl : block mo383 7 0 0 = true)
  · exact (rfl : block mo383 8 0 0 = true)
  · exact (rfl : block mo383 9 0 0 = true)
  · exact mo383B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo383G : graphValid mo383 (boundsBefore KM255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM383 : Lower false (varsX 383) (graphGoal 383) 11 := lower_forest (g:=mo383) (i:=0) (hints:=4295517781) (before_sound KM255 VM255) mo383G mo383T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM383 := extendKnown KM255 11 [(383,[]),(479,[32,65,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM383 : Known false KM383 := extend_ok (m:=383) VM255 lowM383 (by decide +kernel)
def mo495Y : Array (Bits × Bits) := #[(0x3c3800000787,0x193430515326860a),(0x300003c01e000078,0x347c0a40468f8148),(0x1f0c000003e1800,0x109190fcaa12321f),(0xf0001e001e000,0x103500c86206a019),(0x0,0x0),(0xe0003f801c0007f,0x283c5aea85078b5),(0xffc060001ff80,0x264a4f0204c949e0),(0xff0000001fe0000,0x2d6c2a0155ad8540),(0x30000007fe000000,0x980b03599301606)]
def mo495C : List ColumnInfo := [(1,0,494,0,11),(2,0,493,0,11),(8,0,487,0,11),(4,0,491,0,10),(128,0,367,0,10),(32,0,463,0,9),(132,0,363,0,9),(256,0,239,0,9),(0,32,332,131,8),(0,128,331,36,8),(64,0,431,0,8),(258,0,237,0,8),(264,0,231,0,8),(4,32,328,131,7),(32,128,331,4,7),(65,0,430,0,7),(72,0,423,0,7),(128,32,332,3,7),(160,0,335,0,7),(36,128,331,0,6)]
def mo495A : List (List Nat) := [[]]
def mo495D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x84f1b305490f182430300cfd69d9121576cfd69191215769fd684955d974cfd69d9121572cfd6919121572cfd2919121572af768c855d172afd684855d172afe680855d1729f368c955c9429f9684955c9429fa680955c942
def mo495D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23b1c2b8b831860ac3e2e1e00e1828238b8783186c7e1e010c6171c2b8b83185c7e2e10fc6177ede372db366d835ad534ed2342cf336cc32ac931ec6312c3306c02fabd2eeba2e2b72d6b42cab12beae2b2ab2a6a829aa528ea22829f2769c26a9925e96252932469023a8d22e8a222872168420a811fe7e1f27b1e6781da751ce721c26f1b66c1aa6919e66192631866017a5d16e5a162571565414a5113e4e1324b0f63008a1702e0037fb28c10ebbfc9460875f7ebb2eab2dff255765d37faec42ae9bfd9261474dfec3aeab26ff61d755537fb0cbaaa9bfd861d554bfec90eaaa7df5d565553ef8eab2aa9fbd755d154dfec930e2a6ff61d751537fb0cba8a9bfd7560854efe42aeab977f651755cbbf928baae5dfd7561172efeba908b95ff255745cb7f90aba2e5dfd7555172bfecb8a8b977f5d4545cb7fb28c3aa5bfc9461d52dfec3ae8a95ff6547454b7fb0eaa2a57fd9715152dfec38a8a97fb2617254bfdb2ab92a5fec955c952ff6baae4a97fb6517254bfd928b92a5fed845c952ff6422e4a97fb5d17254bfdaa8b92a5fec545c952dfec3aeaa16ff6157550b7fb0a3aa85fbd7555142fde3aaa8a17fb6557250bfd92ab9285fed755c942df6cb3043aefb651821d77d928c10ebbf99660075dfcca3003aefe649801d6f7b283aacb7dd931d565bf6c90eab2dfd64475596ff3203aacb3fd92215749fe4c2caba6fb655821d27fb2e42ac97dd931d564bf6c90eab25fd64475592ff3203aac93fc985d954b7ecb0eaaa5f764c75552fdb243aaa97f5911d554bfcc80eaaa4ff660545cabfb2e2a2e57ed9215172b7ecb0eaa95ef6507554afbb263aaa57f5911d552bfcc80eaa94ff6607454afdb243a2a57ec985c952ef6baae4a94ff65c8550afbb263aa857ed921d542bfac88eaa15fe6407550afd92ab9285bed855c942ef6baae4a17eb5517250a7eb2242aed2fd96215729deca10ab94f764c855ca7eb2242ae53f99021572
def mo495H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1b76b66c4d2b1c8ad220001ae000000f4a0
def mo495D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x507c5830a622388141f126c380711223a7223b0e2c0988111c3e2c380546203e2c38130e18507238b0e01a38a10143e2c3813109f0e0c51870c9c3e2c38030e1f161c09888e184878a14466c58700a285070b8b0e0129881c1c2e6c58700e1f161c04c5149f160c22230e222e2c3805461d391c58700d183e2c3804261b161c09888e193871b8b0e02238714382e6c58701028385c5870094c40a078b0e0263088e1f161c02a311830e28c2080a9f061c51870e9f062c2186149f062c22230e1f161c02230c222e2c3805461f161c02230a9c3c80d831612640a0f8b0e02630a101f362c3807159b0e01828ac81f161c030acd8b00b14787cd8b08a17207c5870131e3ca3b239a38236a35233a32230a2f22da2c22aa29227a26224a23221a2021ea1d21ba1a218a17215a14212a1120fa0e20ca0b209a08206a051f59e61d69c71bb1ad59dd91d84178165155947d3d92fd2211610a0fe0f04e0cd14c54b5cad49f893885c79c6c061c5244643882e42241800dc003ff21576ffd865d7ff5d975ffd845d7ff21175ffd825d7ff21d65ffd75597ff1d565ffd765d3ff21574ffd755d3ff5d564ffc75593ff21d54ffd75553ff1d554ffd75153ff61572ffc855cbff5d572ffd845cbff21172ffd745cbff55172ffc545cbff61d52ffc8754bff5d552ffc7554bff61152ffc8454bff5d152ffc7454bff55152ffc5454bff5d542ffc7550bff59574ffd76553ff59554bfc855daff61875bfd841d6ff60875bfd87597bf5d965dfd765d2ff21574bfd861d2ff61474bfd821d2ff61d64bfc85592ff61d54bfd86553df59554fbd74552ff61c54bfd86152ff60854bfc855cb7f5d572bfd8754bfb5c952bfd8750aff61542bfc8550bef55142fed7250abf61875bbd841d6f760c75bed821d6fd60475bf9801d6fb60874
def mo495H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x59700000000000e8a6a800000380002cc00000000000000d9e001541884b46f689f5e51e00000000000000006c977e0014e000e41a4800000d160000013100000000000000000006c60000000000000000000000000000003b8000a90000ce0000000000030797f48800000000000000000000000076a0000000000000000000000002a08000000000000000000000000000000000005520010b7db3cc0020f8000000026c36400050fcd00017509c001b6000e8c0000000000000000001e2832800736000998007ce00274000a0e003615e300000000000000000000000000000068e000000000000000000000000000071000000d4800000001abc006816c0001ca800000000000008ae003d6acd74400000000000002643ae000001a880000000000000000000005b200000000000000000000000000000000000000000000001b300063c00000000000000ed1a3c3e001174a58000012400000000134000000000000000000000000000000000000000258000005bb00000280000000000001890009726b0005aa2dc000000000000000024c000a5000000002508000000000000043c0030680000000000000000000000000012500016900014c4c8000000000000094a000000000000000022b0008080000000000000000708000000000016e400000a0c00000000c6000000000dc2710000005b20000031d001e178600000000000000000000001d4000000000000000011600000c48040023009
def mo495D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c53a28601871479a182218a9a28601c61c53a28601871c52268a08473879a28601471d22218221871c52268a180728e9a28601471478228461871628601861d3222860187fc73b4974a2451c8b4421686000ffaedff5d7fe3affd65ffae9ff1d3feb27fd54ff8a9ff5cbfea97fd42
def mo495H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x121ddde2fb3ad0f0fd01f31e23198064204e404dc2201a4ea5784b324841280004e278005c112f922e348ef2ce88170001920035463e00191eca30cb1fa705d51b0012d80043c36eaf400000523ac4000003340010564c000b0000000348c569a000a06002531a0e57437d50b50010fc4158b65800054ec595a000227cb470ccb91f05f252c1b12d1821d44401ad0853010c155d
def mo495D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc20804ff
def mo495H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb4aa00290000e1008b0800435590020627081
def mo495L : Nat → Packing
  | 8 => (12,4,5,0,0,7,0,mo495D8)
  | 9 => (106,3,5,0,0,10,0,mo495D9)
  | 10 => (77,2,5,0,0,12,0,mo495D10)
  | 11 => (12,1,5,0,0,9,0,mo495D11)
  | 12 => (1,0,5,0,0,0,0,mo495D12)
  | _ => emptyPacking
def mo495I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 3 17 3 8 4 0 mo495H9
  | 10 => lookupWord 26 397 3 11 7 0 mo495H10
  | 11 => lookupWord 19 97 6 11 7 0 mo495H11
  | 12 => lookupWord 3 17 4 8 4 0 mo495H12
  | _ => fun _ => none
def mo495 : Forest := ⟨1519,12,fun i => mo495Y[i]?.getD (0,0),mo495C,mo495A,mo495L,mo495I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P8_0 : CutRow mo495 8 0 12 := shortcutBlock (data:=fun _ => 0x30324211888621301172421188862130302c2121904a4140303242118886213011724211888621303032460381822130302c2141a0524140302c2141a052414018581140a4d04184600000000000000340000000000000106000000000000002) (by decide +kernel)
theorem mo495B8 : CutRow mo495 8 0 12 := mo495P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_0 : CutRow mo495 9 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_6 : CutRow mo495 9 6 96 := shortcutBlock (data:=fun _ => 0x303242108886214030324211888621403032461389862140303242118886214030324211888621403032421188862140058c2925925848531858130580c50261058c2921925848832498130380c88452303242108886214030324210888621403032421088862140303242108886214030324211888621403032421188862140303242108886214001f2480c8606224130324211888621403032421088862140302c2141a052415001f81164b05d02913032421088862140303242108886214030324211888621403032421088862140302c2121904a41503032421188862140058c29058250485330324210888621403032421088862140303242118886213030324211888621303032421188862130303242118886213001f2480c86062231303242118886213020b2421188862130303242108886213020ac2121904a4140058c292592584842303242108886213001f2480c8606224120b242118886214020b242118886214001f2482c960e228101f2482c960e228101f2482c960e223101f2482c960e223101f2482c960e2231600000000000002e600000000000002d400000000000001c600000000000002c600000000000002b600000000000002a60000000000000286000000000000027600000000000002660000000000000256000000000000024400000000000001b400000000000001a4000000000000019400000000000001860000000000000236000000000000022600000000000002160000000000000204000000000000017600000000000001e600000000000001d600000000000001c600000000000001b600000000000001a400000000000001660000000000000136000000000000012600000000000001140000000000000156000000000000010600000000000000f600000000000000e40000000000000134000000000000012600000000000000d600000000000000c4000000000000011600000000000000b600000000000000a600000000000000960000000000000086000000000000007600000000000000660000000000000056000000000000004) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_102 : CutRow mo495 9 102 4 := shortcutBlock (data:=fun _ => 0x1f2482c960e224130324211888621403032421188862140302c2121904a4150) (by decide +kernel)
theorem mo495B9 : CutRow mo495 9 0 106 := (@joinRow mo495 9 0 6 100 mo495P9_0 (@joinRow mo495 9 6 96 4 mo495P9_6 mo495P9_102))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_0 : CutRow mo495 10 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_7 : CutRow mo495 10 7 29 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_36 : CutRow mo495 10 36 3 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_39 : CutRow mo495 10 39 38 := shortcutBlock (data:=fun _ => 0x60000000000000494000000000000028600000000000004840000000000000274000000000000026400000000000002560000000000000476000000000000046600000000000004560000000000000446000000000000043600000000000004260000000000000416000000000000040600000000000003f600000000000003e600000000000003d4000000000000024600000000000003c600000000000003b600000000000003a600000000000003960000000000000386000000000000037600000000000003660000000000000354000000000000023600000000000003460000000000000336000000000000032400000000000002240000000000000214000000000000020400000000000001f400000000000001e400000000000001d60000000000000316000000000000030) (by decide +kernel)
theorem mo495B10 : CutRow mo495 10 0 77 := (@joinRow mo495 10 0 36 41 (@joinRow mo495 10 0 7 29 mo495P10_0 mo495P10_7) (@joinRow mo495 10 36 3 38 mo495P10_36 mo495P10_39))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P11_0 : CutRow mo495 11 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B11 : CutRow mo495 11 0 12 := mo495P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P12_0 : CutRow mo495 12 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B12 : CutRow mo495 12 0 1 := mo495P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495T : mixedTables mo495 12 := by
  intro k hk
  interval_cases k
  · exact (mixedEmpty mo495 0 0)
  · exact (mixedEmpty mo495 1 0)
  · exact (mixedEmpty mo495 2 0)
  · exact (mixedEmpty mo495 3 0)
  · exact (mixedEmpty mo495 4 0)
  · exact (mixedEmpty mo495 5 0)
  · exact (mixedEmpty mo495 6 0)
  · exact (mixedEmpty mo495 7 0)
  · exact mo495B8
  · exact mo495B9
  · exact mo495B10
  · exact mo495B11
  · exact mo495B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495G : graphValid mo495 (boundsBefore KM383) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM495 : Lower false (varsX 495) (graphGoal 495) 13 := lowerMixed (g:=mo495) (i:=0) (hints:=4831864405) (before_sound KM383 VM383) mo495G mo495T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM495 := extendKnown KM383 13 [(495,[]),(507,[16,66,134]),(509,[32,65,117]),(510,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM495 : Known false KM495 := extend_ok (m:=495) VM383 lowM495 (by decide +kernel)
theorem lowM503 : Lower false (varsX 503) (graphGoal 503) 13 := lower_down lowS503
def KM503 := extendKnown KM495 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM503 : Known false KM503 := extend_ok (m:=503) VM495 lowM503 (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0x383e000000003c1f,0x86d56909a902436),(0x7c000f0000003e0,0x2d440235b1b156a2),(0xfc3c000,0x8dacd581646046d),(0x1f00003c0000,0x8c6031090d40463),(0x1e001f0000000,0x1bc22112704ccde1),(0x7fe000e000003ff,0x1292a94a444e8949),(0x38000000003ffc00,0x370020276129db80),(0xfffc00000,0x242512a589b13212),(0x1fff000000000,0x39dcc80e02201c)]
def mo511C : List ColumnInfo := [(1,0,510,0,13),(2,0,509,0,13),(4,0,507,0,13),(8,0,503,0,13),(16,0,495,0,13),(32,0,479,0,11),(128,0,383,0,11),(33,0,478,0,10),(64,0,447,0,10),(132,0,379,0,10),(256,0,255,0,10),(40,0,471,0,9),(48,0,463,0,9),(65,0,446,0,9),(68,0,443,0,9),(72,0,439,0,9),(130,0,381,0,9),(258,0,253,0,9),(264,0,247,0,9),(272,0,239,0,9)]
def mo511A : List (List Nat) := [[],[16,66,134],[32,65,117],[64,33,117,134]]
def mo511D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf6f0eae4ded8d2ccc6c0bab4aea8a29c96908a847e78726c66605a544e48423c36302a241e18120c0600d75dc66cca765486d779c86c0a765486d779c66c0a765486b75dc329d8665486b76dc229d8665486b779c029d8665486d6dda86cca865875d6f5a86c4a865875d6f9a86c0a865875e67dc8659a521875e6ddc8659a321875e3f9c6661a021875e6f9c8659a021875c7ddba6988664c75c7ddba6188664c75d75da66d48664c75d75d866d48664c75d7d9ca6c08664c75d7d9a86c08664c75d7d9a66c08664c75d7d9866c08664c75c7f9ba6188664075d5f9b76188664075d779866d48664075d7b9866d08664075d7d9866cc8664075d7e9866c88664075d7f1866c48664075b73dc42dca961565b75dc32dca961565b76dc22dca961565b775c12dca961565b779c02dca961565f87dc961d7661565f87cc961d7661565f87cb961d7661565f87ca961d7661565f87d876997661565f87d876d57661565d7b9ca6c08765065d7b9c66c08765065b7b9c021d8665065
def mo511D10 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x61994197bdedc2ecca0cbdef2e17665065ef7b50bb32832f7bda75d994197bdec3aecca0cb5df2e98665486eaf974cbb2a43757db565d9521babe5ab2eca90d9f769da564c86eebb6ecab2643775cb76559321abfcdc34ec810d5fe6e1a564086cff34ed2b204375f9b565d9021bafc5ab2ec810ddde6dd9564086eef16ecab204347fdb66a4865d73eedcb46432eb9f76a5a321975debb4ad190cbae7f9b9680865d76fcdbb40432eb9fe6a5a021975dbf34ed010cbaef79a5680865d77dcd2340432ebbf668da021975dfd344d010cbaeff1a1680865d7b3eda950cb0ebdb76cca865875edeb625432c3af6f9b02a1961d73eed9b52430eb9fe6c1a921875cefb2cd290c3ae77da9694861d7b3ecb34a430eb9f76e5a321875cfbb2cd190c3af6dd9668c861d77aed2b46430eb9fe6e5a021875cff330d010c3ae7f996680861d79fccc340430ebb7e69da021875edf32cd010c3aef79a5680861d77dcd2340430ebbf668da021875dfd344d010c3aeff1a1680861d6bee5c34cc98eb9f76a1a664c75afbb74c33263ae7dcba619931d7b6ed330cc98eb5f76e88664c75cfbb74433263af75db5219931d7becd810cc98eb9fe6e88664075ebf36e433203af779b5219901d7bdcda10cc80ebdf66cc8664075efd364433203af7f1b1219901d63fedb34e4c2cb9fb6dda226165cfd96ed1130b2e7edb6688985973f65b3444c2cb9fb6d5a226165cfdb30d1130b2ef6db568898596bf6d9130cbacb5fb6c89825d65cfeb30d092eb2e7f4986849759777adb3424bacb97f2e5a721965cbfb30d390cb2e7dd9868c865973eecbb46432cb9fb661a221965cfeb2ed090cb2e7f998680865973fccbb40432cb7bb6c8985d965afdb644c2ecb2deddb321976596f7ad890cbb2cb7be6c0865d965cefb6e54b0ab2e77cb72a5855967be5d32ec2acb9df2a59761565cef9524bb0ab2df75b125d855973be54b4cc2acb7cf6d0a661565bafb6e4330ab2df5db321985596fb6d910cc2acb7de6c08661565dcf952bb30ab2f97d875d985597c7ec3aecc2acb1ff6e9985d5658ffb744c2eab2d7edb226175596bbe5cb0abaacb3fe6c0a85d8658ffb74cc2ec32f1fd9861d76196bdedb350ca0cb5ef2e1a765065af7b6cd3b2832d7bdba61d941973de5d30eca0cbcef6a18765065eb7b4ec3b2832d7bdba21d94196bdedb10eca0cb5ef6e17665065af7970bb32832f5bd875d994196baed994eca90d5db6c8a765486aef36053b2a4356ddb32a1961d6b7ad8950cb0eb5be6c0a865875ccfb2cd290c3ae6dd9668c861d71fccc340430eb9be659a0218758fbb74433263ad75db5219931d6becd810cc98eb1fe6e88664075abf36e433203ad779b5219901d6bdcda10cc80eb5f66cc8664075afd364433203ad7f1b1219901d7c3ec3aecc2acb5ee6c08765065 else 0xeb5ff6e58621875cffb52c310c3aef7d86694861d77eec3346430ebbfe619a021875efbb70d33263af7dcb8699931d7beedd30cc98ebdf76998664c75efbb74433263af7dda6219931d7beec310cc98ebdfe6188664075cffb6cd3930b2e7fcb669c985973fedab4e4c2cbbfb661a226165dfdb6ed1130b2efecb7688985977f6db3444c2cbbfb2d9a226165dfdb6ad1130b2dfedb226197596ff6d91304bacbbfd6e1a125d65dfeb30d092eb2eff498684975977fadb3424bacbbfd6d5a125d65cffb6c54b0eb2e7fdb52a5875973fe5494cc3acb7fd6c4a661d65bfdb644c30cb2dff5b125d86596bfedcb0ec32cb5ff2e58761965dbf972d390cb2edfd9869c865976fedab4e432cbb7f69d9721965bfeb624b90cb2d7fdb961c86596bfe5cb0e432cbbef661a421965df7b6ed210cb2efbd97690865977de4bb48432cbbef6d5a421965dfbb30d190cb2efdd9768c865977ee4bb46432cbbf761da321965dfdb30d110cb2efed97688865977f64bb44432cbbfd661a121965dfeb6ed090cb2eff597684865977fa4bb42432cbbfd61da121965dfeb6ad090cb2eff998680865977fccbb40432cbbfe25da021965dff30ed010cb2dfedb226176597bbedb952c2acbddf2dca961565def952cbb0ab2ef7ca925d85597bbe54b4cc2acbf9f6e97661565fcf974bb30ab2fe7cb95d985597f3e54aecc2acbf9f6e17661565fcf970bb30ab2fe7c985d985597f3ed3aecc2acb7df6e97661565bef974bb30ab2f77ca95d985596fbedc2ecc2acbf5f61d7661565fcfb4cbb30ab2fe7ca65d985597f3ec32ecc2acbf9f2197661565cff96ed4b0ab2e7fdb72a5855973fe5b952c2acb3ff2e99761565bfeb624bb0ab2dfbdb429985596fbedab0cc2acb77f6dc8661565bfbb664330ab2dfedb221985596ffcd810cc2acbf9f6d576615659ff974bb30ab2e7fda95d985597cfec3aecc2acb9ff2e1a95d565cffb72d42eab2cffdb62a1755973fedd330baacb5ff6dc985d565bfdb644c2eab2d7fdb961d75596bfe5cb0ebaacb3ff6e9865d5659ff974c32eab2e7fda9619755967fedd10cbaacb77f6dc865d565bf7b68432eab2dfddb321975596ff6d910cbaacb7fd6c4865d565bff360432eab2f77cb9615755977bed330abaacb9ff6dda666065cff96ed333032f5fcb865d871973fed4b4cc38cbcff661a661c65ebfb2ed330e32d7fdb961d861979fecc30ec30cbd7f65d8761865affb7243b0c32dff9b02a176196bfedcb0ebb0cbcff661875d865ebfb2ec3aec32f7bdb76a194197bde5bb50ca0cbdef6d9a865065ef7b70d3b2832f7bcb869d94197bdedb34eca0cbdef6e98765065ef7b50c3b2832f7bda761d94197bdedb30eca0cbdef6a08765065ef7b50c332832f7bdb761994197bde5bb0cca0cbdef69d8665065ef7b0ec332832f7bc87) else (if j<3 then 0xc662f93c7e2f08e6a3461b0be4f1787c041a8d1a342e1bc9e2f0f809c5b830d85f278bc23e1bc9e3f17850e321bc9e3f17870e361bc9e3f17850e33930de3f17870e338f0de4f17870e338b0de4f1f870e33870de4f1f8b0e378fc9e2f0f805d2631c18833617c7e2f093bc1bb5ba9b9db91b85b79b6db61b55b49b3db31b25b19b0db01af5ae9addad1ac5ab9aadaa1a95a89a7da71a65a59a4da41a35a29a1da11a059f99ed9e19d59c99bd9b19a599998d98197596995d95194593992d9219159098fd8f18e58d98cd8c18b58a989d89188587986d86185584983d83182581980d8017f57e97dd7d17c57b97ad7a179578977d77176575974d74173572971d7117056f96ed6e16d56c96bd6b16a569968d68167566965d65164563962d6216156095fd5f15e55d95cd5c15b55a959d59158557956d56155554953d53152551950d5014f54e94dd4d14c54b94ad4a149548947d47146545944d44143542941d4114053f93ed3e13d53c93bd3b13a539938d38137536935d35134533932d3213153092fd2f12e52d92cd2c12b52a929d29128527926d26125524923d23122521920d2011f51e91dd1d11c51b91ad1a119518917d17116515914d14113512911d1111050f90ed0e10d50c90bd0b10a509908d08107506905d05104503902d021015008ffcff0fe4fd8fccfc0fb4fa8f9cf90f84f78f6cf60f54f48f3cf30f24f18f0cf00ef4ee8edced0ec4eb8eacea0e94e88e7ce70e64e58e4ce40e34e28e1ce10e04df8decde0dd4dc8dbcdb0da4d98d8cd80d74d68d5cd50d44d38d2cd20d14d08cfccf0ce4cd8ccccc0cb4ca8c9cc90c84c78c6cc60c54c48c3cc30c24c18c0cc00bf4be8bdcbd0bc4bb8b1ca929f696c8e28587ce7446ba6305944e645c3e436c2f427c20418c1140ae001ddf6d9a765486eef974c332a43777db76199521bbbe5bb0cca90dddf69d8665486eef94ec332a43777db56199521bafe5d32eca90dddf6d59765486efbb6ac33264377dcb56199321bbeedbb4ac990ddf72dda564c86efbb6ecab264377dcb76559321bbfcdc34ec810ddfe6d5a764086eff16ad3b204377f9b76199021bbfc5bb0cc810ddfe6d58664086eff16ac33204377f9b86959021bbfcdbb4ac810ddfe2dda564086eff36acbb204377f8b565d9021bbfcdbb2ac810ddfe2dd9564086cffb6ad412cbae7fdb62a5865d73feda952c32eb9ff2a49661975cffb52cb10cbad7fcb9618865d73fed4b0c432ebbdf2e5a521975defb2cd290cbaef7d86694865d77bed4b4a432ebbf76e5a321975dfbb2cd190cbaefdd8668c865d77eedab46432ebbf7695a321975dff372d010cbaeff998680865d77fcdbb40432ebbfe659a021975dff30cd010cbaeff9b5680865d77fcd3b40432ebbfe695a021975edfb505432c3af6fcb8659861d7b7edc32c430 else 0x18ac438ccde4f1787c0462b11e4f1f87c0691f15887019bc9e3f1784871e1b0be4f1787c03b870d85f278fc5e01dc186c2f93c7e2f08e45f278fc5e1f03187b1b198be4f1787c03d818cc5f278fc5e11ec0))
def mo511H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa02000000c48a4a001e306946b541e2d2a0ea2d028000000001033826c4c0b884e000698000400000212000a36a2543c109e4000000044700800088e22f90a000218a0400001649b034c2a001982823011a3a000000000000001e42000c5200000000000045000060a41d83e420a39e8dc06e45a8600c0305010570230009
def mo511D11 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x7ffd9761565fff25d85597ffda661565fff29985597ffd8661565fff21985597ffd7661565fff2a575597ffda85d565fff2a175597ffd985d565fff26175597ffd875d565fff69975597ffca65d565fff61975597ffc865d565fff5d975597ffda661c65fff69d86197ffca761865fff61d86197ffc8761865fff6a176197ffca85d865fff61d761977fd9765586bff69c9561b7fd9725586dff25c9561b7fda765486dff29d9521b7fd8665486fdf69d9521bf7ca765486dff65d9521affca865975dff661965d6ffda825975dff660965d77fc9825975dff658965d6ffda961975dff6a5865d6ffca961975dff2a5865d6ffda921975dff6a4865d6ffca921975bff694865d7f7da521975ff768c865d7ff9a021975dff6a1961d77fca865875dff6a5861d77fd9661875dff6a4861d77fd9621875fdf694861d7fdda321875ffe680861d77fda766165dff29d985977fd9826165bff69c98597f7da526165ffb688985977fda865d65dff2a197596ffca865d65dff661975977fc9865d65bff6a0975977fd9825d65dff260975977fda961d65dff2a5875977fd9861965dff65d865977fd9821965bff69c865977fd9721965fbf2a576597efd985d965fbf26176597efda55d965dff661765977fc985d965fbf61976597efc865d965fdf2a585597f7d9761565fdf25d85597f7da661565fdf29985597f7c8661565dff2a585596ffda661565fbf5d985596ffda85d565bff2a1755977fd985d565dff261755977fd975d565bff69975597efd765d565fdf615755977fda766065dff29d981977fda865c65dff2a1971977fda961c65dff661871977fd9761c65bff698871977fd9861865dff65d86196ffda85d865bff2a1761977fd985d865dff65d76197dfd875d865fff61d86597f7d8661565fdf5d98559777da765486ddf29d9521b77d8665486d7f65d9521b7dd8664c86df76959321b7dd9564c86dfe69d9021b7f98664086dfe6959021b7f99764086dfe6559021a7fda8259759ff2a5865d67fda921975bdf694865d6fdda321975bfe680865d76fda865875dbf2a1961d67fda961875dbf659861d67fda921875dbf658861d6f7da521875bf768c861d6ff9a021875df7699931d77dd8664c75df7219931d77f98664075dfe219901d67fda726165bfb68898596ff5a125d659ff6a5875967fca961d65b7f69c86596fbda421965bf768c86596feda221965bfd68486596ff9a021965ddf2a585597e7d76615659ff6a5855967fca9615659ff6a5755967fda6660659ff6a5871973fd9861c65d7f65d871967fda921c65def6a1941977bda765065def61d941977bc8765065def619941977bd7665065d5f65d9521b75d9564c86d7e65d9021b7799564086dee6519021b7d99364086dfa6499021b7f191640869fb6889859677ca961565 else (if j<2 then 0x808a6c5e4e3e2e1e01c181428229b17938f8b8780bc52a08e4e3e2e1e0231b159020cf8f8b87809c6c52ae4e2e1e00f231b14ab938f8780388c6c5610831e4e3e2e0271b14ab938f8b843480a48e2e4e3e0e11c159b938f8b878072a064885e4e2e3e1e024182823938f8b87821490a482685e4e3e1e2e02418282217938b87838c9a64845e0e3e2e1e4229923838f8b87911480648e0e3e2e1e44521209b938f8b878114866a488e2e0e3e10c219a238f8783883070c66a48c8885e0e3e2e129aa92178f8b8781988668c08a485e2e1e0e32630219a9217878f838890a08e4e3e2e1e01c2b938b87803c60ae4e3e2e10d182b938f8b84346e3e2e1130d143c2b938b843460e0ae4e3e10d1b938f8844345c50ae4e3e1e0182823938f8b87807bb15d72ead750ba55d12e7d738b995cb2e4d720b8d5c52e1d708b815bf2ded6f0b755b92dbd6d8b695b32d8d6c0b5d5ad2d5d6a8b515a72d2d690b455a12cfd678b3959b2ccd660b2d5952c9d648b2158f2c6d630b155892c3d618b095832c0d600afd57d2bdd5e8af15772bad5d0ae55712b7d5b8ad956b2b4d5a0acd5652b1d588ac155f2aed570ab55592abd558aa95532a8d540a9d54d2a5d528a915472a2d510a8554129fd4f8a7953b29cd4e0a6d535299d4c8a6152f296d4b0a55529293d498a49523290d480a3d51d28dd468a3151728ad450a25511287d438a1950b284d420a0d505281d408a014ff27ed3f09f54f927bd3d89e94f3278d3c09dd4ed275d3a89d14e7272d3909c54e126fd3789b94db26cd3609ad4d5269d3489a14cf266d3309954c9263d3189754a7249d2088e145f226d0f0855419202cfd07c53d11dfceb872d3851b7cd7869933d196cc7861d2fd176cb7859d2bf158ca8051927f138c97849d23d116c8584091f10efc7383751a90ccc6282ed1630a7c4f0255119083c3d81c90d505fc2b813508703bc1a80b904f021c0d805101d007c000fff69d9561bffca765586fff65d9561bffd9725586fff25c9561bffda561886fff2958621bffda765486fff29d9521bffda865975fff2a1965d7ffd9865975fff6a0965d7ffd9825975fff260965d7ffd9625975fff694965d7ffda961975fff2a5865d7ffd9661975fff259865d7ffda561975fff6a4865d7ffd9621975fff618865d7ffda521975fff618861d7ffda766165fff29d98597ffd9826165fff69c98597ffda626165fff69498597ffda865d65fff2a197597ffd9865d65fff26197597ffd9825d65fff26097597ffda961d65fff2a587597ffda661d65fff29987597ffda561d65fff2a586597ffc9861965fff69d86597ffca761965fff65d86597ffc9761965fff69586597ffd9821965fff65c86597ffc9721965fff61c86597ffca95d965fff66176597ffc985d965fff61976597ffda55d965fff2a58559 else 0x268564a3c01429982017938b878f8092a660508e4e3e1e2e0259a2a238f938b878088a88e4e3e2e1e06621982823938b87838c8a50a08e4e3e2e1e02199942b938b87803c86665e4e212e1e00f2199942b938b87803c86665a08ae1e4e3e20d2599942b938b878c34866658ae4e3e2e10d2199942b938f8b8434866650ae4e3e2e10d231b142393878f8b80806050a08c6c5e4e3e2e1e02f14a8a38f938b8780808c6062a28e3e4e2e1e02b158ca8bf938b87808c5602a2de3e4e2e1221a17938b87838c78685e4e3e2e1e01d1917938b87838c746e4e2e1e0e3451c211b938f8b87811484645e4e3e2e1e01d17938f8b878318763c6e4e2e1e0c51d831b938f8b8714786e4e1e2e00b182e2e1a17938b878080b6a688685e4e2e1e0261b938b878e1c686e4e3e2e18718219b142b8b938f878092ac562e4e3e1e01f1584c09b938f8b))
def mo511H11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x6783e86ad099236c4850898b0e6a1f94a1d94f60ac216e2a686bf7183c37ec24006cb1b843c9882e099f5ba239d496fa064873a28107ad939810dc46177c493d92511339861800014051967074284e00012cb3815c161000033740005f16a2b2000209d80002173c0580003920000003acc21800011f582840000034086e0001064d86e305d85480002c092e29801d920504f0001ebc405b0c7230f200000007072317402d511ff233000108398aa18c211ef1305c2f780550a4f30d89b142428ce000000058ce11f8000288998d30076046e449903d41ec0003915695b40f4827800048c820b5024b97ba00b1026000281690d5504fa42e915894800001436977e0af8d82c08d55e292989c5a53a8760000000164d40a4c564717d6b38000000051cc43d000000e18037e0ffd398038a1a52596f798031509b1029f61ba3072c481662020a59a289422b41bb0823ce8838fc404806f82220740000933e17a000000078f9d073d10c0007058515a2254000254122756259d6b088c82d01c36f04a8e01170a044435f874897c82a0766e8da7988c2384368000000111d081f12510881a1874080000003c42cc08a915c0001a0bf9a3a131d583659b8072028d106b1c4000022d00016288c8498a4e08e0002c63b0e9800523740007a3e92d40002334f0e47110000252eb2ee0001e4bdd099864424600020930000723440498af46bed1a9851f4a9c851d14e000244dfb4cbc0ea02b4ac38f30001a2c81692c0c569d8b0cc4e400000000003081791100000000000000050400000000595a00000001ca8813e0001a2d000000000001b815437d0635c1162340a100002ac5c4f000040ed41f00003c1120bfd281a33204b80540001c005c04f91720e2ebc0404710751e200000004a044153e5040000000904c000000000000001e1f0c7f48450000429aa04113fe86b644b50a6abeb24a753cd3a1050a8218cab120a0674413bc54000000072bae2ac80d792ae0e1251500a6103508d333e051a07731160003162602ce8eee14c000011e00000002820c40f0001e83f80f8000000142a983d8000000000000000000413b7836caaa836000029a743410acf257440400060769459cae800060d162ac027e01d282a31ff00c80000000f80f843c40680c61853c49c08cd8e21e0800000000065b14ac4328750000bca39b2bcabc34b0001847061e800060c08367c584ad19121bc5c0000124b079e12a06bb14b122021e005d8000097a5164000200fd09223f747dfc38920c000242160bc1d91788684e90522112157a3401888000010400280482c1cf2401485d60460c2400402281cb1332d44890e1c0040c1c411040409c3210210140d7812854a05081c2010000e04141c01b6800084220c0876c00304063408304001030eec3080400010143160c0618200 else 0x4d8c26e100e0a68c2b84de00000004857a26440100003084e134f109c4a7b6c4c080000072f4c04410a176458e055e1a1a5300003081000101ffc8fd825f1bda477cb38000799a24bb4b64866521ce245c90d87dc2580001c0e0000903044110b1c844016f845b843d05fe11f84c091a0040ed8111da031216058b4c03380bc80382102317842eacfe200252b4259c34c2444437078116b0594c4d2943488968f2558d8a31075e2a1e055da1c1695271c57d57da2cb10b92065a1fa4aea042683)
def mo511D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1325c98b0e0c63e4c5870634a3264a2b262c3831882532515931e2c3804131a2e3c9871601e3050d15463c98b0e0285088d17262c3831922034554a31e4c5870151b262c3831c51e364c78b0e08a3a68b93163c380710982c555931e2c380a8a9b263c38b00f142e4c78b0e04c40a109a2e3c587260245464c202c5c987163c05c68aab263c587008244060a9a2e4c38f160285088c982e4c78b0e0284060a9b263c5870129a460c78b0e48a448c98f161c09a29098464c5870638a4261187263c18a290192851423263c5870142b263c5870081c564c58700f18564c78b08d1a3060b17263c587008285060b931e2c38080d17262c78700e162e4c78b0e01440a4d17263c38b010193058b930e3c5809c98b1e1c02861017263c587010293061017263c58701428464c78b0e01d18a1f93161c03a01437263c58470c17263c58700e2c305c98b0e01c364c78b0871920c10171e2c3808a7fa4fa0a9c598e9428fd8b187a84380c7c078974b7066b366e6225d65915535154d749944d4163e63b636a32c2f52b727923420b1cd18114a1130dc0a506e03e000ffecab0dffc9561bffb0c437ff65486ffecb2ebffc965d7ffb0cbafff21975ffec30ebffc861d7ffb30b2fff26165ffecbacbffc97597ffb0eb2fff61965ffe432cbffd76597ffb0ab2fff5d565ffec38cbffc87197ffb0c32fff5d865bfeca90df7d9521bfbb26437fe64086bfe4b2eb7fd961d6ffb30b2dff26165bfecbacbefd76597efb0ab2dff66065bfecb8cb77d9521afbb26435fe64086b7ecb0eb7dd931d6ff3203adef65065
def mo511H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c6e1863d2983526b252598ee0003c7fc08882700014c93596421326d03b5dc486b906dc1511a6e6a4ad68ca00010ec022f15dc14f7d5c1998e010d8cb852c6c4ca113aa90000000200f1ec63055b3dbbc87430f51667222f1e236500e118866de0134f252ce03e0048000d3563d6938c8ddd368b8eaaf24e700005195aae46fb3960f8dcf3c7100018b4334c93c53c208d66e6076326202a106562c00020fbb207ac7a11f7a92029c4370a34304e15a256eb400038d445ab253cce366cafaa2c163f958c0f9e07382eeacf850c3a9deb8a89846f05d05da87f8d1c22acc3202db5e763800041913b06114000904086310514f7db99cdf0003c908160000fad2842eabc7d123f8f07862195f104d4fda230000d97c000000245c96156d0d2480000002e080001439908c000e16c000f3ac04af9cb5f2a0b43ba121c000ca3a029913c00012d804e00034deb9ae0380000000e2e400022b94a5b89a30c0000000a07400081dd7b200000000002c32f122106debf96bf20e91d0001e3c4ccdc00092c841953a07d00028a4000066e63cce1dea14056e269375e904c78000247c0002e4c032c000000042447080000000000c3080003706007d6288a80149b2a12f475d1587c2fe9254e49063caa00000000000000118400022700000003431823e0db0002a7123d4000ad3330494ccc400001c1a728e8d61c94cdc83c4000fa440005310435d81c0000000945d15c00096fc0006c7c0005496886e034c7e8330000aecc7d000010baf006d2a533c8c6f39b52da580000430000062f000022fd8be30b0cd7f920000ebaa0bb746f8ffbee40009015c65a288f3a000050400000e223400004dd9af90000000f255e3e0003e45902000023480006c9b04be8cf4c708a901f024f0510871855000280c000282000024a1a49baae84e74cd523bb48a17a49df0fc000f31587021644fae5c0c1170966fc53f0000d25c00000f3cabaaa8000d73492fb2a6e59257ac84fb19c16b2b74f6729ee5ce1eb0670000c4981b24ed51b77ae2a42834e27da0472158a091ee00fe1c80006b44c4da183468d22400006cb037c2d5cc8a3a48ef35ce0800003f1d3153642000245f336234f33d20b72298000e00a49ec0ac0e87463cafc09a1e800008e10002c7362b18062025c6a6a984b221e71ba40e87d44a1d48260ce4755078491d8e85bcb2640003c140216272100070000150002020b010c041c041009000104280a0627200d22260d0c34061f00029d1a180000010b0404002c03011000011101031109090f001a083a16040022020806060b041e120430003802131a0200080603060f000416030901
def mo511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1859228608c71852889238a18091858e48a18071a48e28601471859238a18072248e2860147fcc090603000ffd86ffc86ffd75ffc75ffd65ffc65
def mo511H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xad7b12000429000c2b000d21bd02dbfd839460be23000b13a4e40551b21800029000600031ed4100000061429b000a92204f98f86000708d161240009557840c420200c64bd103dc000e2288d0005034abd81f2a61c00000010f743007a6610d00081531fc19000b5c5500007580a810992631a62839c24fc2041d30a125faaa5bf27e0160e617e67a44395011593ad58c18011805929078ce680001003012003
def mo511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20c4100bff
def mo511H14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe0002a36994216a1840000143a22c8000198f18050
def mo511L : Nat → Packing
  | 9 => (42,5,5,0,0,8,0,mo511D9)
  | 10 => (365,4,5,0,0,12,0,mo511D10)
  | 11 => (256,3,5,0,0,13,0,mo511D11)
  | 12 => (44,2,5,0,0,12,0,mo511D12)
  | 13 => (6,1,5,0,0,8,0,mo511D13)
  | 14 => (1,0,5,0,0,0,0,mo511D14)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 13 79 5 12 6 2 mo511H10
  | 11 => lookupWord 120 593 7 15 9 2 mo511H11
  | 12 => lookupWord 99 491 8 14 8 2 mo511H12
  | 13 => lookupWord 20 97 6 12 6 2 mo511H13
  | 14 => lookupWord 3 17 5 9 3 2 mo511H14
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,14,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : CutRow mo511 9 0 42 := shortcutBlock (data:=fun _ => 0x30324211888621701852480c860622700e1812110cc4218730324211888621703032421188862170249812110cc4219730324211888621403032421188862140249812110cc4218430324211888621703032421188862140249812110cc42174249812110cc4217430324211888621403032421188862140303242118886218030324211888621801852480c86062230249812110cc42183249812110cc42183249812110cc42183249812110cc42194249812110cc421743032421188862187249812110cc42173249812110cc42173249812110cc42173249812110cc42173302c2121904a4140302c2121904a4140302c2121904a4140302c2121904a41401858112094c84194116c280c86124853116c2808861248530e0c229348e5e086078c290782504873078c282e161a4873078c2907825048730e1812914ce421830e1812110c442183249812110c442193) (by decide +kernel)
theorem mo511B9 : CutRow mo511 9 0 42 := mo511P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : CutRow mo511 10 0 22 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_22 : CutRow mo511 10 22 96 := shortcutBlock (data:=fun _ => 0x6000000000000099600000000000009840000000000000a7600000000000009740000000000000a640000000000000a540000000000000a440000000000000a36000000000000094600000000000009340000000000000a240000000000000a140000000000000a06000000000000091400000000000009f6000000000000090600000000000008f600000000000008e600000000000008d600000000000008c400000000000009e400000000000009d400000000000009c400000000000009b400000000000009a4000000000000099400000000000009840000000000000974000000000000096600000000000008b600000000000008a6000000000000089600000000000008860000000000000876000000000000086600000000000008540000000000000954000000000000094400000000000009340000000000000924000000000000091600000000000008440000000000000906000000000000083400000000000008f6000000000000081400000000000008d6000000000000080400000000000008c600000000000007f400000000000008b400000000000008a40000000000000894000000000000088400000000000008740000000000000864000000000000085600000000000007e600000000000007d600000000000007c600000000000007b600000000000007a4000000000000083400000000000008240000000000000814000000000000080400000000000007f400000000000007d400000000000007c60000000000000796000000000000078600000000000007760000000000000766000000000000075400000000000007b400000000000007a40000000000000794000000000000078400000000000007760000000000000744000000000000076400000000000007340000000000000724000000000000070400000000000006f400000000000006e400000000000006d400000000000006c400000000000006b400000000000006a400000000000006940000000000000684000000000000067400000000000006640000000000000654000000000000064) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_118 : CutRow mo511 10 118 96 := shortcutBlock (data:=fun _ => 0x78c290582504853078c2921925848631843c924b0c848a5078c292592584852078c292192584852078c290582504893078c29211258486330324211888621500798130700d108a3303242118886215030324613898621502498130380c8847230324211888621503032461389862150078c29259258485230324613898621503032461389862150078c290582504863078c2905825048633032421188862150078c290582504863078c292192584863078c2921925848531843c924b0c848a5078c292592584852078c292192584852078c292192584852302c2121904a4150078c2905825048533032421188862150303242118886215030324210888621503032421088862150303242108886215030324210888621503032421088862150303242108886215030324210888621503032421088862150249812110c4421a4303242108886215030324210888621503032421088862150303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214030324210888621403032421088862140303242108886214040000000000000ba60000000000000b060000000000000af60000000000000ae60000000000000ad60000000000000ac60000000000000ab60000000000000aa40000000000000b560000000000000a960000000000000a860000000000000a760000000000000a660000000000000a540000000000000b340000000000000b060000000000000a360000000000000a240000000000000af60000000000000a160000000000000a0600000000000009f600000000000009e600000000000009d600000000000009c600000000000009b600000000000009a40000000000000ae40000000000000ad40000000000000ac40000000000000ab) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_214 : CutRow mo511 10 214 96 := shortcutBlock (data:=fun _ => 0x30324211888621503032421188862150303242118886215030324211888621903032421188862140249812110cc421943032421188862140303242118886214030324211888621403032421188862140303242118886214030324211888621403032421188862140249812110cc42184303242118886215030324211888621503032461389862150078c292592584852078c292592584852078c292592584852078c2925925848520e18192692689063078c292592584852078c292592584852078c292592584852078c290582504852078c290582504852078c2905825048522498138240e88461078c2905825048523032421188862150302c2121904a41603032421188862150078c2921925848523032430191c084a62498138240e8846130324211888621503032421188862150078c292192584863078c292192584863078c292192584863078c292192584863078c29219258485230324211888621503032421188862150078c292192584853078c292192584853078c292192584853078c292192584853078c2921925848531843c924b0c848951843c924b0c848951843c924b0c848951843c924b0c84895078c292592584852078c292592584852078c292592584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c292192584852078c2921925848520e0c229348e4a064302c2121904a4150302c2121904a4150078c290582504853078c290582504853302c2121904a4150116c280c86124873116c280c8612487318470291c9a4e085078c290582504893116c280c86124873116c280c86124873116c280886124873116c280c86124873078c290582504853078c292112584853116c2c0b071248532498130380c884622498182e164aa097078c290582504893116c280c8612487318470291c9a4a085116c280c861248733032421188862150302c2121904a4160302c2121904a4160078c290582504863078c290582504852078c292112584853) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_310 : CutRow mo511 10 310 55 := shortcutBlock (data:=fun _ => 0x3032461389862180303242108886218030324211888621803032421188862180303246138986218030324211888621803032421188862180302c2121904a4160303246138986218030324211888621403032421088862140302c2121904a4150302c2121904a4150302c2121904a4150302c2121904a41501852480c860622401852480c86062240248c241b0d0e4451249812110cc42184249812110cc42184249812110cc42184249812110c4421841172480c860622401172480c860622401172480c86062240249816130dc42184249812110cc421841858112094c841851858112094c841853032461389862150303242108886215030324613898621503032421088862150303246138986215030324210888621503032461389862150302c2121904a4150303246138986219030324613898621903032461389862190303246138986214030324613898621403032461389862140302c2121904a4150302c2121904a4150249816130dc42194249816130dc4219418524c0e87062240249816130dc42194249816130dc4219411724c0e87062240249816130dc421941858112094c8419530324211888621503032421188862150) (by decide +kernel)
theorem mo511B10 : CutRow mo511 10 0 365 := (@joinRow mo511 10 0 118 247 (@joinRow mo511 10 0 22 96 mo511P10_0 mo511P10_22) (@joinRow mo511 10 118 96 151 mo511P10_118 (@joinRow mo511 10 214 96 55 mo511P10_214 mo511P10_310)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : CutRow mo511 11 0 10 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_10 : CutRow mo511 11 10 59 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_69 : CutRow mo511 11 69 2 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_71 : CutRow mo511 11 71 1 := by
  apply checkedRow
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_72 : CutRow mo511 11 72 96 := shortcutBlock (data:=fun _ => 0x60000000000000d340000000000000f940000000000000f840000000000000f740000000000000f660000000000000d260000000000000d160000000000000d060000000000000cf60000000000000ce40000000000000f560000000000000cd40000000000000f440000000000000f340000000000000f240000000000000f140000000000000f040000000000000ef40000000000000ee40000000000000ed60000000000000cc40000000000000ec40000000000000eb60000000000000cb60000000000000ca60000000000000c940000000000000ea40000000000000e940000000000000e840000000000000e760000000000000c840000000000000e660000000000000c760000000000000c660000000000000c540000000000000e540000000000000e440000000000000e340000000000000e260000000000000c460000000000000c340000000000000e140000000000000e060000000000000c240000000000000df40000000000000de60000000000000c140000000000000dd60000000000000c040000000000000dc40000000000000db40000000000000da40000000000000d940000000000000d860000000000000bf40000000000000d760000000000000be40000000000000d660000000000000bd40000000000000d560000000000000bc60000000000000bb60000000000000ba60000000000000b940000000000000d440000000000000d340000000000000d240000000000000d160000000000000b860000000000000b740000000000000d040000000000000cf40000000000000ce40000000000000cd40000000000000cc40000000000000cb60000000000000b640000000000000ca40000000000000c940000000000000c840000000000000c740000000000000c640000000000000c540000000000000c440000000000000c340000000000000c260000000000000b540000000000000c140000000000000c040000000000000bf60000000000000b440000000000000be40000000000000bd60000000000000b340000000000000bc40000000000000bb) (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_168 : CutRow mo511 11 168 88 := shortcutBlock (data:=fun _ => 0x3032421188862150303242118886215030324211888621503032421088862150303242108886215030324211888621503032421088862150302c2121904a4160302c2121904a41603032461389862150303246138986215030324613898621503032461389862150303246138986215030324613898621503032461389862150302c2121104a416030324613898621503032461389862150303246138986215030324613898621503032461389862150303246138986215030324613898621503032461389862150302c2121904a41603032421188862150078c290582504863078c290582504863078c290582504863078c2905825048632498130380c88472078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c2905825048631178161709950883078c292192584863078c2905825048632498130380c884722498130380c884722498130380c884722498130280c884722498130380c884722498138240e884722498130380c88472078c292192584863078c292192584863078c292192584863078c2921925848630e0c229348e4a0750e0c229348e4a0750e0c229348e4a0750e0c229348e4a0750e0c229348e4a075078c290582504863078c290582504863078c290582504863078c290582504863078c2921125848632498130380c88472078c2921925848630798130580d10883078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c290582504863078c2905025048632498130380c88472078c29219258486318581144a05502813032421088862150303242108886215030324210888621503032421088862150303242108886215030324210888621503032421088862150303242108886215040000000000000fa) (by decide +kernel)
theorem mo511B11 : CutRow mo511 11 0 256 := (@joinRow mo511 11 0 71 185 (@joinRow mo511 11 0 10 61 mo511P11_0 (@joinRow mo511 11 10 59 2 mo511P11_10 mo511P11_69)) (@joinRow mo511 11 71 1 184 mo511P11_71 (@joinRow mo511 11 72 96 88 mo511P11_72 mo511P11_168)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : CutRow mo511 12 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_7 : CutRow mo511 12 7 13 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_20 : CutRow mo511 12 20 24 := by
  apply checkedRow
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : CutRow mo511 12 0 44 := (@joinRow mo511 12 0 7 37 mo511P12_0 (@joinRow mo511 12 7 13 24 mo511P12_7 mo511P12_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : CutRow mo511 13 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : CutRow mo511 13 0 6 := mo511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P14_0 : CutRow mo511 14 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B14 : CutRow mo511 14 0 1 := mo511P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511T : mixedTables mo511 14 := by
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
  · exact (mixedEmpty mo511 8 0)
  · exact mo511B9
  · exact mo511B10
  · exact mo511B11
  · exact mo511B12
  · exact mo511B13
  · exact mo511B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511G : graphValid mo511 (boundsBefore KM503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511R : Impossible false graph 14 inputs.toFinset := by
  rw [show graph = targetOf mo511 by decide +kernel]
  exact mixedRoot (g:=mo511) (top:=14) (i:=0) (before_sound KM503 VM503) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_11008
open PEqualNP.Outside.L_meta_11008 in
theorem PEqualNP.Outside.L_meta_11008 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 15 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo511R g511R ⟨C,hf,by omega,heq⟩
