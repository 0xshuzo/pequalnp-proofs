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


abbrev Bits := BitVec 118
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 118 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 118 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 118 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 118 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 118) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 118) (j : Fin 9) :
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
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 118) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 118) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 118 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 118) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 118 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 118) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 118) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 118) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^119*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^119 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<119 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<119 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<119 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 118) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (119*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^119)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 119*(i+1)-119=119*i := by omega
      have ge : ¬119*(i+1)<119 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 118 = (a==BitVec.allOnes 118) := by
  by_cases h : a=BitVec.allOnes 118
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^118-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^118 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (119*i) =
      (f xs[i]==BitVec.allOnes 118) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^119*u+x+(2^119*v+1)=2^119*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^119 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬119*(i+1)+118<119 := by omega
      have di : 119*(i+1)+118-119=119*i+118 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 119) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (119*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 119) (i:=i) (by simpa using hi) _ ok.2
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 118 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 118
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
def g99Y : Array (Bits × Bits) := #[(0x1f7df7df7df7df7df7df7df7df7df7,0x134d34d34d34d34d34d34d34d34d34),(0x29a69a69a69a69a69a69a69a69a69a,0x29a69a69a69a69a69a69a69a69a69a),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x269a69a69a69a69a69a69a69a69a69,0x41041041041041041041041041041),(0x39e79e79e79e79e79e79e79e79e79e,0x28a28a28a28a28a28a28a28a28a28a),(0x0,0x0),(0x0,0x0)]
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
theorem g99P3_0 : block g99 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g99B3 : block g99 3 0 1=true := g99P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99T : checkedTables g99 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g99 0 0 0 = true)
  · exact (rfl : block g99 1 0 0 = true)
  · exact (rfl : block g99 2 0 0 = true)
  · exact g99B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g99G : graphValid g99 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS99 : Lower true (varsX 99) (graphGoal 99) 4 := lower_forest (g:=g99) (i:=0) (hints:=85) (before_sound [] baseKnown) g99G g99T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS99 := extendKnown [] 4 [(99,[]),(101,[33,101]),(105,[49,33,101]),(165,[112,16,33,98]),(166,[112,32,98]),(178,[112,32,50,67,100]),(197,[32,16,101,117]),(225,[80,97,33,50,67,116]),(228,[32,81,49,67,116]),(291,[16,134,118]),(323,[128,16,101,81,117]),(326,[96,32,133,117]),(354,[128,81,32,50,67,116]),(418,[16,112,32,50,67,134]),(452,[96,113,32,49,67,82,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS99 : Known true KS99 := extend_ok (m:=99) baseKnown lowS99 (by decide +kernel)
def g103Y : Array (Bits × Bits) := #[(0x194ca6532994ca6532994ca6532994,0x104824120904824120904824120904),(0x3a9d4ea753a9d4ea753a9d4ea753a9,0x3a9d4ea753a9d4ea753a9d4ea753a9),(0x7a3d1e8f47a3d1e8f47a3d1e8f47a,0x32190c86432190c86432190c86432),(0x0,0x0),(0x0,0x0),(0x2753a9d4ea753a9d4ea753a9d4ea75,0x5028140a05028140a05028140a050),(0x1cae572b95cae572b95cae572b95ca,0x2c964b2592c964b2592c964b2592c9),(0x0,0x0),(0x0,0x0)]
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
theorem g103P4_0 : block g103 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g103B4 : block g103 4 0 1=true := g103P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103T : checkedTables g103 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g103 0 0 0 = true)
  · exact (rfl : block g103 1 0 0 = true)
  · exact (rfl : block g103 2 0 0 = true)
  · exact (rfl : block g103 3 0 0 = true)
  · exact g103B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g103G : graphValid g103 (boundsBefore KS99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS103 : Lower true (varsX 103) (graphGoal 103) 5 := lower_forest (g:=g103) (i:=0) (hints:=1621) (before_sound KS99 VS99) g103G g103T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS103 := extendKnown KS99 5 [(230,[112,98,48,67]),(241,[80,65,98,49,50,112,48]),(422,[80,33,129,48,67,116,97]),(454,[96,114,48,67,133,66]),(481,[113,130,49,66]),(482,[16,96,114,48,66,133,83,67]),(484,[32,81,128,48,65,116,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS103 : Known true KS103 := extend_ok (m:=103) VS99 lowS103 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[(0x11e8f47a3d1e8f47a3d1e8f47a3d1e,0x160b0582c160b0582c160b0582c16),(0x0,0x0),(0xbc5e2f178bc5e2f178bc5e2f178bc,0x9c4e271389c4e271389c4e271389c),(0x25d2e974ba5d2e974ba5d2e974ba5d,0x5c2e170b85c2e170b85c2e170b85c),(0x0,0x0),(0x5a2d168b45a2d168b45a2d168b45a,0x48241209048241209048241209048),(0x3e5f2f97cbe5f2f97cbe5f2f97cbe5,0x32190c86432190c86432190c864321),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(4,0,105,0,4)]
def g109A : List (List Nat) := [[],[50]]
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g109L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g109D4)
  | _ => emptyPacking
def g109I (_ _ : Nat) : Option (Nat × Nat) := none
def g109 : Forest := ⟨109,4,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P4_0 : block g109 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B4 : block g109 4 0 1=true := g109P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact g109B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore KS103) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS109 : Lower true (varsX 109) (graphGoal 109) 5 := lower_forest (g:=g109) (i:=0) (hints:=26117) (before_sound KS103 VS103) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS109 := extendKnown KS103 5 [(179,[112,33,16,49,67,84,101]),(227,[33,115,67,101]),(327,[128,49,32,33,81,117]),(357,[131,67,116]),(419,[16,32,115,67,133,101]),(453,[32,131,67,117,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS109 : Known true KS109 := extend_ok (m:=109) VS103 lowS109 (by decide +kernel)
def g229Y : Array (Bits × Bits) := #[(0xf0e9e1d3c3a7874f0e9e1d3c3a787,0x30886110c22184430886110c22184),(0x0,0x0),(0x1ae9b5d36ba6d74dae9b5d36ba6d74,0xaab15562aac5558aab15562aac555),(0x0,0x0),(0x0,0x0),(0x3a927524ea49d493a927524ea49d49,0x1896312c6258c4b1896312c6258c4b),(0x35f46be8d7d1afa35f46be8d7d1afa,0x345468a8d151a2a345468a8d151a2a),(0x2519ca33946728ce519ca33946728c,0x2500ca0194032806500ca019403280),(0x0,0x0)]
def g229C : List ColumnInfo := [(1,0,228,0,4),(4,0,225,0,4),(32,0,197,0,4),(64,0,165,0,4),(128,0,101,0,4)]
def g229A : List (List Nat) := [[],[114,101],[32,117],[32,80,96,112],[80,118],[80,98,112,32],[96,82],[96,114,80,82],[112,32,82,101],[112,98]]
def g229D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g229D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g229H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50
def g229D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g229H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb6e300a260fe00450000fa0011006b47008
def g229L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g229D4)
  | 5 => (2,1,3,0,0,4,0,g229D5)
  | 6 => (1,0,3,0,0,0,0,g229D6)
  | _ => emptyPacking
def g229I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g229H5
  | 6 => lookupWord 2 17 2 8 1 3 g229H6
  | _ => fun _ => none
def g229 : Forest := ⟨229,6,fun i => g229Y[i]?.getD (0,0),g229C,g229A,g229L,g229I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P4_0 : block g229 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B4 : block g229 4 0 1=true := g229P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P5_0 : block g229 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B5 : block g229 5 0 2=true := g229P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P6_0 : block g229 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B6 : block g229 6 0 1=true := g229P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229T : checkedTables g229 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g229 0 0 0 = true)
  · exact (rfl : block g229 1 0 0 = true)
  · exact (rfl : block g229 2 0 0 = true)
  · exact (rfl : block g229 3 0 0 = true)
  · exact g229B4
  · exact g229B5
  · exact g229B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229G : graphValid g229 (boundsBefore KS109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS229 : Lower true (varsX 229) (graphGoal 229) 7 := lower_forest (g:=g229) (i:=0) (hints:=536872453) (before_sound KS109 VS109) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS229 := extendKnown KS109 7 [(229,[]),(355,[33,129,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS229 : Known true KS229 := extend_ok (m:=229) VS109 lowS229 (by decide +kernel)
def g231Y : Array (Bits × Bits) := #[(0xcd866c33619b0cd866c33619b0cd8,0xc486243121890c486243121890c48),(0x2f557aabd55eaaf557aabd55eaaf55,0x2c5562ab1558aac5562ab1558aac55),(0x1d8aec5762bb15d8aec5762bb15d8a,0x58a2c51628b1458a2c51628b1458a),(0x0,0x0),(0x0,0x0),(0x33af9d7cebe75f3af9d7cebe75f3af,0x13a29d14e8a7453a29d14e8a7453a2),(0x127693b49da4ed27693b49da4ed276,0x123491a48d246923491a48d2469234),(0x2c7563ab1d58eac7563ab1d58eac75,0x285542aa1550aa85542aa1550aa855),(0x0,0x0)]
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
def KS231 := extendKnown KS229 8 [(231,[]),(245,[32,65,49,117]),(359,[33,101,135]),(435,[16,66,50,134]),(438,[64,33,48,117,134]),(469,[32,16,65,49,101,117,133]),(470,[64,48,133,118]),(483,[16,112,98,50,67,132]),(485,[32,129,80,49,67,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS231 : Known true KS231 := extend_ok (m:=231) VS229 lowS231 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[(0x133f267e4cfc99f933f267e4cfc99f,0x13d027a04f409e813d027a04f409e),(0x3989f313e627cc4f989f313e627cc4,0x3109e213c427884f109e213c427884),(0x0,0x0),(0x0,0x0),(0x22e5c5cb8b97172e2e5c5cb8b97172,0x2c5858b0b16162c2c5858b0b16162),(0xcda99b5336a66d4cda99b5336a66d,0xcc2198433086610cc219843308661),(0x37c4ef89df13be277c4ef89df13be2,0x36c0ed81db03b6076c0ed81db03b60),(0x35696ad2d5a5ab4b5696ad2d5a5ab4,0x31286250c4a189431286250c4a1894),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,5),(16,0,227,0,5),(64,0,179,0,5),(1,64,178,0,4),(128,16,99,0,4)]
def g243A : List (List Nat) := [[],[112,100]]
def g243D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f731
def g243D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x222317f
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
def KS243 := extendKnown KS231 7 [(246,[32,65,117]),(373,[33,101,135]),(374,[16,64,32,133,101,118]),(423,[16,50,66,134]),(455,[32,16,49,65,101,117,133]),(467,[64,133,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS243 : Known true KS243 := extend_ok (m:=243) VS231 lowS243 (by decide +kernel)
def g486Y : Array (Bits × Bits) := #[(0x0,0x0),(0x9cb9c9cb9c9cb9c9cb9c9cb9c9cb9,0x84984849848498484984849848498),(0xc6784c6784c6784c6784c6784c678,0x8468c8468c8468c8468c8468c8468),(0x0,0x0),(0x0,0x0),(0x32a47f2a47f2a47f2a47f2a47f2a47,0x22a43a2a43a2a43a2a43a2a43a2a43),(0x2ab962ab962ab962ab962ab962ab96,0x22a9522a9522a9522a9522a9522a95),(0x351cc351cc351cc351cc351cc351cc,0x151841518415184151841518415184),(0x175e2175e2175e2175e2175e2175e2,0x151621516215162151621516215162)]
def g486C : List ColumnInfo := [(256,0,230,0,5),(34,0,452,0,4),(68,0,418,0,4),(132,0,354,0,4),(160,0,326,0,4),(258,0,228,0,4),(320,0,166,0,4)]
def g486A : List (List Nat) := [[],[133,118],[33,101,135],[33,117,134],[81,98,135],[81,98,113,130,33],[97,82],[97,82,130,113],[113,130,82,97],[113,130],[129,114,81,98,101],[129,114,101]]
def g486D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9fd9530
def g486D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40c3fa61fd10
def g486H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x70
def g486D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x34ad11bf
def g486H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6f00015e02031d1cc20000000006800003560090
def g486L : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,g486D5)
  | 6 => (2,1,3,0,0,3,0,g486D6)
  | 7 => (1,0,3,0,0,0,0,g486D7)
  | _ => emptyPacking
def g486I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g486H6
  | 7 => lookupWord 2 17 4 9 1 4 g486H7
  | _ => fun _ => none
def g486 : Forest := ⟨486,7,fun i => g486Y[i]?.getD (0,0),g486C,g486A,g486L,g486I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486P5_0 : block g486 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g486B5 : block g486 5 0 1=true := g486P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486P6_0 : block g486 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g486B6 : block g486 6 0 2=true := g486P6_0
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
  · exact g486B5
  · exact g486B6
  · exact g486B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g486G : graphValid g486 (boundsBefore KS243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS486 : Lower true (varsX 486) (graphGoal 486) 8 := lower_forest (g:=g486) (i:=0) (hints:=4866442832) (before_sound KS243 VS243) g486G g486T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS486 := extendKnown KS243 8 [(486,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS486 : Known true KS486 := extend_ok (m:=486) VS243 lowS486 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0xdb148db148db148db148db148db14,0xd1048d1048d1048d1048d1048d104),(0x3ad073ad073ad073ad073ad073ad07,0x3a9063a9063a9063a9063a9063a906),(0x92af492af492af492af492af492af,0x12a7012a7012a7012a7012a7012a7),(0x0,0x0),(0x344f0f44f0f44f0f44f0f44f0f44f0,0x144b0544b0544b0544b0544b0544b0),(0x66bb066bb066bb066bb066bb066bb,0x6b9006b9006b9006b9006b9006b9),(0x32d8c72d8c72d8c72d8c72d8c72d8c,0x32c0872c0872c0872c0872c0872c08),(0x3b960bb960bb960bb960bb960bb960,0x2a940aa940aa940aa940aa940aa940),(0x0,0x0)]
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
def g487Y : Array (Bits × Bits) := #[(0x14df2944250783bc537ca510941e0e,0x140328442103ed18500ca110840fb4),(0x1da42c589b8240427690b1626e0901,0xd840c5089822f08361031422608bc),(0xd426aa1aff18c023509aa86bfc630,0x8406880afc1cc322101a202bf0730),(0x0,0x0),(0x0,0x0),(0x227115ca66d8307c89c457299b60c1,0x2270018a465010e089c00629194043),(0x2bbc960700570781aef2581c015c1e,0x23bc1601001412c18ef0580400504b),(0x348ad8f1d02ab800d22b63c740aae0,0x148a9071102a2300522a41c440a88c),(0x1202a1ba7d09c003480a86e9f42700,0x1002a1aa7409c002400a86a9d02700)]
def g487C : List ColumnInfo := [(1,0,486,0,8),(2,0,485,0,8),(4,0,483,0,8),(128,0,359,0,8),(256,0,231,0,8),(32,0,455,0,7),(64,0,423,0,7),(132,0,355,0,7),(258,0,229,0,7),(0,2,197,288,6),(0,4,291,192,6),(0,128,323,36,6),(0,256,165,66,6),(3,0,484,0,5),(5,0,482,0,5),(6,0,481,0,5),(32,2,197,256,5),(32,128,323,4,5),(33,0,454,0,5),(34,0,453,0,5),(64,4,291,128,5),(64,256,165,2,5),(65,0,422,0,5),(68,0,419,0,5),(130,0,357,0,5),(160,0,327,0,5),(256,2,197,32,5),(260,0,227,0,5),(35,0,452,0,4),(36,128,323,0,4),(66,256,165,0,4),(161,0,326,0,4),(192,4,291,0,4)]
def g487A : List (List Nat) := [[],[33,101,135],[113,130],[129,114,101]]
def g487D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x319a98e1c8050c43
def g487D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x70017001b00c00ac0040b00100003400540040000000000000000b001fcf6f0eae4d4c4aa9a94847e787262524c46403a342e28221c161000a7dcb303b82874fb965c77050e3f730b88e0a1d3ee59711c143ccfc870ea188799d90e1d4310eb3b21c3a8621f66e5f8050c43ecdc3f00a188799f87e014310eb3f2ec028621e67e1d8050c43bcd4c100a1887d9b872014310f33f30a1ae021f66e41435c043c77bb704aa2838fb76e01435063f720c1ee4a0e1fddb854c9418fdc830fa16631fb90613754c67b327c02859847ee4187d0d308fdc8309b8a615bb945d7404433370fc028621e66e1c8050c43
def g487H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3
def g487D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x35881000101880c1580130010180420280060800000000000309810a0b810a0a0c1a80161010002061010e8402c200d840113080840108020000100000d1016202000400000000302080c10012080000020010b41500180000414080064284004810300081810300028320020902000000700080010000080004820100010c02000410002080410286020a8808018428401041a08013000410069183008201041c4662060e4284150a04789c3e17078010260ac00a0ac0082a140884280280000140420080000005810b0482000002808348c105022150870391c71fa573be6bc9b876ffdcfb8764ebad69a9746e7eccd98324642c798db1862ac4987b0c600bd1766e0db2b47676c7576a994f69751fa3342a824f59cd35e644c29792da584aa949256434808e31ae32c5f8b312a14c23829015ffbe77c2f49e63bd75ce59bf36f6d2d8daa34566ccc190b1b62abf5772df5b2b29622b554ca81442794e696d2623d46e87cff1ef3c06fcd3950270480768e71c236c660bd16e2c4558a512c1f83c0720d8174228009ff805d243df8805d2439fd80dc543aff865c543bfb805c543dfb81dc143df981dc143dfb71dc143df971dc143bfa871c143dfb711c143df9711c143f9f8050c43f9d8050c439fd83dd1519fd80dd151ddf7350d51bfb8050d519fd84dc1519fd83dc151fbb8050f41fb88050f41dbd435c3419fd80dd5419ff805d541bef8255141fbb8050d41fb88050d41cff7650d41bfb8050d419fd83dc9419fd80dc941b7f854c941f9d434c941f755454541bf780545419fd83dc141dbd43dc1419ff805d331dfb805d331df8805d3319fd87d0b31df57550731df5415c3319fd84dd5319ff845d5319ff805d5319ff805d131bef8255131b7d85d0d31bfb8050d31b7f854c931df77454531bf780545319fd84dc1319ff805cd21bfb8050d219fd83dc121df541dc121dfb805d330fdb8050f309fd87d0b30bdd83d0b30bfb8050b30df971d0330bdd839d130bf5819d130dfb805d1309fd87d0d30bf581d0d30bf980d0d30bdd8490d30fdb8050d30bfb8050d30b7f855c9309fd87d0930bdd83d0930b7f854c9309fd84dc5309fd87d0530bdd83d0530f9d43d0530aff8650530f9d43505309fd84dd5109ff845d510bef8255110bfb8055110b7d85d0d10bfb8050d10bfb8050910b7f854c910ddf734c910df77550510dfb75d0110df975d0110bf983d0110fb943d0110bf982d0110ff131d0110fd9434c110bfb8348110bf98348110ff14148110ff13148110d9f8750c43f9b8050c43f988050c43d9d435c0439f980dd1519ef825d5419fb805d33197f855cb31bd783507318ff865d1319fb805d13197f855cd2197f855cb30bd983d0330f9943d03309fb805d1309df835d5108ff865d11097d85dc910dbb74d011099f8750c43 else 0x8282004010800026082c46084)
def g487H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x25bd0c1187002430024f008d4d39e5a2b4c444cbb634653689001c5c6455f4f5a000000034012197003c156c0000000b480038c40401e41c0
def g487D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x85c4c3c2c1402f130f0b05021a147c4c3c2c18685401c244c206040302011511101405402c241402221c606c018100c181502221c6061120082c08030c5220407131114881014285c20b0503021488161c104078300884711106002211c40506101e0c0440783110605881014140220291c506084710102c280c090040787880b190c14280c08004620703141d0c501a14202450a0603021188121c2c1a211c7050600884710142c28240c0a20707130b0a03020088102052211c70411084710102c28180c0a21004c888100f0c3c02221c5050608871010181502221c3c60c0a46040302011110802858545044411a001480c0904014714192200244c4468508302c2824100c080448916120c0b0a09040302012854444050485060515121480183010511c7050b0a06030248091c1a011e204450b0605808847101c2c2825180c0a207080d0b0a460302808810270c40343091c0a20511c704808847141014511a0020405050900081c14340216211854610881c1038351a14011e20714111510c0c8c706052440170f0053207478685c8c710504454430017231c81a0c8610c0c7811e9c94aea4851ca8994169f04eca6f93569984c0a5b92be94c49ca4a92268fc472a3491768a844ea2290f686442aa11906e82840ca028ff67ec3ec9ef8f4e7903c09da8eae7383849bf8dde6c435299d8cae63831697f8bc65d42dc96b8b1e5782b69538a7e52c28a94189ee4e026492d892e48823491688864242068fd87ae3b41d08e386d635c1a28cc862e2ec1648ab853629013488f844e20c0fa875837e1a00be855828e13c09484481f60e406682e813607402a810803e0007ff7150ffeb8a87ffdc143ffae0a1fff43547fea1aa3ff55141ffa86a0ffd32507ffa1663ff95131ffaa898ffd534c7ffa1a63ff50d31ffe8498ffd424c7fe99263ff50d21ffac5987ff42cc3fea1661ff9d130ffae8987ff434c3fea1a61ff5c930ffac4987ff424c3fea1261ff4c930ffaa2987ff414c3fea0a61ff48530ffca8887fd54443fea9a21ffd0d10ffa86887ff42443fea1221ff4c910bfae921dfd7290efeb8c877f5c243bfee2a1dff7050ffdb8287fe1c143bfae221dfd7010effba2a37fdcd51bfee0a8dfd75d06feb9e83ef50f41bfae5a0dfd70d077fbb2837fdd541bfaeaa0dff73507dfa1a83ef50d41bfee4a0ff551506ffb82837f5d731bfae998dfd72cc7faa0e637f5c331bfeea98dfd754c6ffba2637f5d131bfee498ff5514c6ffb82637fdcd21bfae690ff541486ffb82437f5d330fba87985fd72cc2feb8e61fed0330bfee8985fd744c3ef21a61f750d30bfee4985ff714c2ffbaa217f5d510bfee8885fd74442ffb9a217f5cd10bfee4885fd72443faa0a21fd4c510ff680887f930443fc90221e7d0e43bdae521dfb7050fcea18873fdd941 else 0x411008784d1100410460605400c5849003811118101016050044604060b0984424381181a1100247858443011d0a1018290a0424413094306104c240d084450b031081110c244c381400913104c25081844213090c28250d0a0451481400f1014310800286c50a054246105c290800145854341121058482434180121018144830e0a43421d15086c2830642120d085c283430a1d0d04604030641120d1078403410f090d0e00342440d090342800b183426010c2c543800d461016003440342800d0946150a00243440d09054302800a1c100c080454504440001814b0a1d0920244c30c0a0504030201111040282c280c0800252070c0b0a0986)
def g487H8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x1658000000000000000042f4000000000000000000000078000000000000000000000000000000002e000000000000000000000000000000000000000000000000000000000038f200069e8000000000c2ef0f0000000224000000000073580024ee000136800240400000000000000000000000000000000000000000000000000000000006118000000000626800000000000000000000000000000000000427800000000038c00000000006940001e180000000000000000000258200021162f800102100000000010b60000ca80000000000000000000709b1a0000000000000056800000000012ee000d5f8000001e1fa612818000000858000000000000000000004a400000000000000006bcc00044a00000000012a2000000000097300000000000000002ad4001360627301d64800000008bc0000000000000000000f05e49c2c80002d239e000000000000000012a30000000000000958a9940000000000000000d2600000004de0002080000001b630000000000000000000000000000000000000000000000000a140000000000000520800000161700000021d2bcb00000000000006baf17800000000000000000000006865fd2000000000000000000000000012670000000000000000000000000000070f4001a5c0ad000181c000000000000000000000038e0000000706c000000062000000000000000000000000000000000000000000000000000000000006750005848001de000000000000000000000000000000000240a000000000000000000070340009f5596701352c00000023e00000008f180000018c300058580000000000000000000000000288729700000000000000005a6c07e00024a8000c54000000000000000000000000000000002068000000000000000065b8228000002c76070000350e0000000000000000000000000000076e80029ee89c0000d8800000000029e8000000565f93d077df629c00029c600000000008060001148000001660c6520b71d000000000006d3a250000000000000ab90000000a094ce00000000000006082fd0636000000000000000070f800000000000035d9e6310a800000000000000000004660000000000000000000000045961a6930000000d040000000000000690b456a7101c80013ee00000000004480000000000000e72000000141e00002f800006a0000000001c1800000041500000000000000000000000000000000000047ca46400000000000000000006788000000000014800000012580000018f50000000001a3a0000003ce8000000594c000e28000000000000000000018c2000000000000000000000000012330000000000000000000000006e00051cc0000009050002ca20000001cc120800801300064906a000051040088291008 else 0x52cb0ac00000000000000000000000000000000000000000000031ed8583f30006b8800000000000000000006a580000000000005c3e84c00060e25a07f0000000000369a00000002dc000000e1c0000001431b5c00018920000000000000000c32195e4800000007cec000000000000393000070e918ad3a00000000000000000000000000000000000000000000000000003bd00075e000000000000000000000000000000000000000000125563e800343c000000000000179dcd291a400086a18c800000185a5220000000000000000188e4270000000001b4800000000000000000000000000000000000000000000000012f6f7929b342200000000008f800000005d8c4600000000000000000000001c6e5450007f300000000001134000)
def g487D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10111201a0488e1490100305911c62844a9081223860a4860a62010101c70a508408e2030e182c03c423881c311811c28818305002639c1038f0c14a40202039018890911c0051cf860b20047383860a348008e207992347bdb86054a468e32946e0dc00ff90ffd43ff10ffd51ffd07fd41ffcc7fd31ff487ff30ff4c3fd10
def g487H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x41f63280f906400073066c485200051bc35882000002a0000000000000010fd49e31e4d8000000be4c0e9574001e0a491111a0ade45936dae0748c3c00020d4000f2412b800000169fa088003c41205000000000000000030194270250001b8e07ba41af28000e8b83a2296dc957e000000485c71c86100061c1491ad5000754000151982680034b6ec90003912810e212356928000c27c31f80159092e343cb7e01300222894490ab62b000000101600090780022860002758558001df2b6a1d49596036f093979c85b0322c9bb4e19554000017ee8d03f00239980002def9f80028dce9e5b3e5c7960b6400000000014cc5b45b660c41879249d4685f0eefaf7050000019670c4680019eb9e1c13c000c9462839a01b5e1c6323805c9600022e79bc001c34b2c1ac50d65cb000000269cce4ba6a0a945141632ecd3c45a0000000580001e2c536185609c000733f868001a2690f401d3700397e6688bc61e38b728bcbda080c411d0cd2ab0539a58000cb4000bdf91c40001380000000000cdd00044196b0000b172dac0000a016b8003c8e00000690618e4000e89abc5c760000003a38d9400000046c3436000098630c0000004018001fe3a2432041a701d04c0103049a09000909270a04030103100102120106051c1302001e000006000602010008070000010734000002120a0d000009
def g487D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40e1ff
def g487H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1d622c00f10000d2ca003a30000000000003c9002356440045441997a000000000000000040377002c700000000000000051400001f64c35200003000000000016c0000000690000000085dd890ad4002260000000000000d000327c200000000c18000000014510860
def g487L : Nat → Packing
  | 5 => (1,5,6,0,0,0,0,g487D5)
  | 6 => (28,4,6,0,0,8,0,g487D6)
  | 7 => (126,3,6,0,0,11,0,g487D7)
  | 8 => (115,2,6,0,0,13,0,g487D8)
  | 9 => (12,1,6,0,0,10,0,g487D9)
  | 10 => (1,0,6,0,0,0,0,g487D10)
  | _ => emptyPacking
def g487I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g487H6
  | 7 => lookupWord 7 41 6 10 5 1 g487H7
  | 8 => lookupWord 53 797 3 13 7 2 g487H8
  | 9 => lookupWord 50 277 8 13 7 2 g487H9
  | 10 => lookupWord 8 83 4 10 4 2 g487H10
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
theorem g487P6_0 : block g487 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P6_2 : block g487 6 2 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B6 : block g487 6 0 28=true := (@block_merge g487 6 0 2 26 g487P6_0 g487P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_0 : block g487 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_1 : block g487 7 1 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_21 : block g487 7 21 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P7_117 : block g487 7 117 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B7 : block g487 7 0 126=true := (@block_merge g487 7 0 21 105 (@block_merge g487 7 0 1 20 g487P7_0 g487P7_1) (@block_merge g487 7 21 96 9 g487P7_21 g487P7_117))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_0 : block g487 8 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_5 : block g487 8 5 67=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P8_72 : block g487 8 72 43=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B8 : block g487 8 0 115=true := (@block_merge g487 8 0 5 110 g487P8_0 (@block_merge g487 8 5 67 43 g487P8_5 g487P8_72))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g487P9_0 : block g487 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g487B9 : block g487 9 0 12=true := g487P9_0
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
theorem g487G : graphValid g487 (boundsBefore KS247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowS487 : Lower true (varsX 487) (graphGoal 487) 11 := lower_forest (g:=g487) (i:=0) (hints:=4831839829) (before_sound KS247 VS247) g487G g487T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS487 := extendKnown KS247 11 [(487,[]),(499,[16,66,50,134]),(501,[32,16,65,49,101,117,133]),(502,[64,48,133,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS487 : Known true KS487 := extend_ok (m:=487) VS247 lowS487 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0x83001807c00f6084f7e910807d520,0x25000044003008453c910803d520),(0x1c20002800010088c20de9207d1,0x1c00802008010088c20c80203d1),(0x3e000200010803b00bf985205072,0x16000120000000000ae185205072),(0x0,0x0),(0xc000038102001c000a46e20ff324,0x380000000000a42e207332c),(0xf003c03fdfc0fe040f6cda3d42381,0x1002423b908044010424c23d4200e),(0x30003ffc01fff0007f094a42662a1a,0x1000081801d2c0c42a810a4244220d),(0x3fffc00001ffffff800510714184e0,0x3c69805042e2e19b03151010008481),(0x3ffffffffe0000000000271d38fc0c,0x2ebe3160700001020460051538cc02)]
def g503C : List ColumnInfo := [(1,0,502,0,11),(2,0,501,0,11),(4,0,499,0,11),(16,0,487,0,11),(32,0,471,0,9),(64,0,439,0,9),(128,0,375,0,9),(256,0,247,0,9),(33,0,470,0,8),(34,0,469,0,8),(65,0,438,0,8),(68,0,435,0,8),(258,0,245,0,8),(272,0,231,0,8),(36,0,467,0,7),(48,0,455,0,7),(129,0,374,0,7),(130,0,373,0,7),(257,0,246,0,7)]
def g503A : List (List Nat) := [[],[33,101,135],[16,66,134],[16,64,32,133,101,118],[32,16,65,101,117,133],[32,65,117],[64,133,118],[64,33,117,134]]
def g503D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x21fcdd50fc830ab253e9b2a1f9061564a7b766c3f20c2ac94fcec587e41855931bdd4f40c290ab263eba2e81989d56492ff74cb92ec28c9a5e65da025d851920ffdd32e4bb0a3261f997680976146486fb73d2b0f3a8c94dd6c7a9616751929bcd8752c2cea32517eb929d855d464b2f36053b0aba8c98f668da0660751931f8d0b40cc0ea3252bfb8699941d464d5736cd20eac00c90bfee996259879520ffdd32e4bb0d2a43fbb06a6966165485ff74cb12cc2ca94fc6c4a6e41859521fcdd52dc830b2a53f1b125b906165487db65d4b0fb2ca92f3ecda7a59829525e7d9b4f3b3052a4bcfb369b7560a54975f68d4aeac14a92f9ec5a95d5829525f5d8352bab052a59e9b0a5d7560a5487f760d2b2fc32a907fee99725f8655297ddb350c850caa53ebb26a190a195483ff74cb92ec32a94fcec5a7e41865521fcdd52fc830caa53e9b2a5f9061954a7b766cbf20c32a94faec997e41865529f9d8b2fc830caa43fab96828761954a7d36143f24c32a94f9ec587e49865521fcdd50fc830caa53f3b161f9061954c5df53d130c432a98beea7a06188655297adb550c890caa53f1b0a1d912195487ef74c3b22432a94fcec1876448655297adb10ec890caa53e5b221d9121954aceb6d52b22432a94fcec1a864676552b3adb54ac8cecaa63dba3e81985d954c7e743d0330bb2a90fd6c4a865b745521fbd8b53c36e8aa43f9b9e8186dd154a3f76ed4321ba2a94fcec5a8643745521fddd30cc86e8aa53ebb261990dd154e27931c3f2aba2a970f6dc8659574552e1edbcecb2ae8aa5c3eb85d9655d154f07970bb2caba2a90fe6c2a9e19745521eed9d50cbec8aa43efb26a787d9154c7d745d0330b22a90fe6c3a865d645521fdd8352c3ac8aa4bf3b169f96e015497d764d4d2dc02a92faec9a5a5b8055257ddd32c4b700aa4bdbb369e76e015497b36754aedc02a92f6ecda95db805525f9d8b52bb700aa63f3b16a774e015497e762d4ee9c02a987e6a797dd3805525f9d8b52ba700aa61fba9e5d74e015497d764d4ec9c02a92f6ecda7d93805525f5d9352b2700aa4bdbb369d64e015497e762d3ac9c02a96bc6c496593805525f8d8d51cb700aa4bf3b169f86e0154c7d764d4d0dc02a92faec9a9a1b8055317cd4f2d43700aa4bebb269686e0154c5f353c350dc02a98beea79661b8055257d5d12cc3700aa63eba9e8986e0154c5f753c330dc02a92beee99621b8055257ddd30c43700aa43f9b9ea176e015497b367542edc02a90feee5a85db805525edd9b50bb700aa4bf3b16a176e0154c3f353c3ee9c02a966eae3975d380552cdd5c12eba700aa7c397659574e0154d76151d0ae9c02a92faec9a859380552d78d890cb2700aa41ffba65c976185487bb71d1b2f3b0a90f7ecda961e761521ef5d152bb3062a70de97a597660c54 else 0xdcb6cd9b60d6b54d3b48d0b3ccdb30cab24c7b18c4b0cc1b00beaf4bbae8b8adcb5ad0b2ac4afab8acaaca9aa0a6a94a3a88a0a7c9da709aa6497a5894a4c91a408ea348ba2888a1c85a1082a047f9f87c9ec799e0769d4739c8709bc6d9b06a9a4679986498c619805e9745b9685895c55950529444f9384c92c499204691443908408fc3d8f03a8e4378d8348cc318c02e8b42b8a82889c25890228841f8781c86c1986016854138481083c0d8300a824078180480c0180086ff74ca92ac34c907fee99725d859929f9d8b4fc830b3252f9b629f9061664a7d36453f20c2cc94faec9a6e41859921fcdd52fc830b3253f3b165f9061664a5f36c4bf20c2cc94fa6c897e41859929f5d932dc830b3241ffba65c97e1564a6ef6ad432342ac94f9ec9a8646855929f9d8350c8d0ab25375b5a1d91a1564a7cb6543b2342ac94fc6c2876468559)
def g503D8 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then 0x96e0154bfae8996e0154afeaa096e0154bfc68496e0154afe69f86e0154ebea5b86e0154ebe65b86e0154afe6a686e0154afe69e86e0154ebee5a86e0154afe69686e0154afe69286e01549fe6a686e0154ebee1a86e0154afeea586e0154cfeea586e0154afee9d86e0154ebee5986e0154ebe25986e0154afee9586e0154edee9586e0154afee9186e0154eeee9186e0154efae8986e01549feea586e0154ebee1986e0154bfae8986e0154afeaa486e0154afe69c86e0154ebe65886e0154afeaa086e0154ebe61886e0154bfc68486e0154afeaa276e0154afe6a276e0154bde69676e0154bfc68676e0154afeea176e0154afeaa176e0154afe6a176e0154afe2a176e0154bf6e8d76e01549fe6a774e0154e7ee1f74e0154bde69774e0154beeaa674e0154beeaa274e0154bee69e74e0154fce99674e0154eee2a174e0154f6ee5d74e0154f6e25d74e0154f6ee1d74e0154f6e21d74e0154f6edd974e0154f6e5d974e0154fcee9574e0154fce29574e0154fce99574e0154fce59574e0154fece8574e0154e7ee1d74e0154e7e21d74e0154bdee9574e0154bfce8574e0154ebee1b64e0154bde69764e0154afe6a164e0154ebee1964e0154ebe21964e0154bdee9564e0154c7fe5e9761854abf69a9761854afb68a9761854abfe999761854af7e8d9761854c7f65c9761854afe68097618548ffea1979d8549f7e8d979d8548ff6a5879d854abfe99879d854cbfea5869d854cbf65d869d854cfd6a1919d854cfd61d919d854cf7e8f985d8548ffe99985d854cbfe99985d854cf7e8d985d854af7e8d985d854e3fe9d865d854e3f29d865d854a7fe9d865d854cf7ea3935d854cf76a3935d854cf761b935d854af76a3935d854cf7e63935d854cf7663935d854eb761b935d854af769e9660c54cf7a5e9660c54af7e9d9660c54af76a67660c54af769e7660c54eb765a7660c54af7ea57660c54cf7ea57660c54af76a57660c54cf72a57660c54eb7a597660c54eb76597660c54af76a47660c548fee81989d6648dfea585215648fee81989d564add6849761464ade6809761464ccf615941d4648fe6a47560064abe6987560064aee6907560064af668c7560064afc68475600648fb68b9661e54abba9a9760a54abb69a9760a54aeb6929760a54afa6829760a548fb6a77660a54af96867660a54afae819560a54aeb6936560a54afa6836560a548fde8597e1954cfae4b90619548bfea586219548fee81989d9548f768e985d9548fee81985d954f0f5d9655d1548fee819859154afae8996e0154afc68496e0154afc68676e0154af6e8d76e01548fe6a774e0154afce8574e01548fe6a686e0154afae8986e0154afc68486e0154cbd619919d8548f7e8d985d8548f76a3935d854af56867660c548f7ea57660c54af66807660c54 else (if j<2 then 0x4cefa63879d154cefa61879d154bcfe95879d154bede85879d154beee81879d1549ef6a6869d154bcf696869d154bee682869d1549efea5869d154bcfe95869d154bebe89869d154beee81869d154bed684869d154aefaa2769d154aef6a2769d154bcf696769d154bed686769d154aefea1769d154aef2a1769d1549ef6a7659d154bee683659d154dcfa62659d154bcf69a659d154b6f69e865d154bee682865d154b6fe9d865d154bebe89865d154beee81865d154b6f69c865d154bed684865d154dcf263955d154f4fe1f955d154bcf69b955d154beee81955d154bcfaa4955d154bcfaa0955d154f4fe1c955d154f4f21c955d154bcf698955d1549efaa7655d1549ef6a7655d154b6f69f655d154bee683655d154bcfaa6655d154bcfaa2655d154f4fe1e655d154f4f21e655d154bcf69a655d154f4fdda655d154bcfaa5655d154dcf2a5655d154f8fe19655d154f8f219655d154f8f9d9655d1548ffaa7865d1549df69b955d154c7fe1f955d154e5fe1f955d154e5fe1c955d1549dfaa6655d1549dfaa5655d1549df2a5655d154f1f5d9655d1548ffaa197d91548ff2a197d91549f7e8d97d91548ff6a787d91548ffea587d9154abfe9987d9154afee8187d9154cbf6a786d9154d9fe1995d9154dcfe9195d9154ddbe8995d9154cbfe1995d91549fbe8995d9154dcf65574d91548ffe9d9859154cfee8198591548ffaa397591548ffea197591549dfe9597591549f7e8d97591549fde8597591548ffaa787591548ffea587591548ff6a58759154abfe998759154afee818759154eaf6938659154afee818659154abfaa08659154bbd6848659154cdfe1b9559154d9fe1b9559154d9f21b9559154dcf6939559154cbfe1b9559154cdf6639559154e9fe1b9559154cbfe1995591549efe9195591549fbe8995591549fee8195591549dfaa49559154e9fe189559154dcfe557459154afe69f96e0154cfee5f96e0154afe6a696e0154afe69e96e0154ebee5a96e0154afe69696e0154afe69296e0154afee9d96e0154cfee5d96e0154cfe65d96e0154ebee5996e0154afee9596e0154afee9196e0154efae8996e0154afe69c96e0154ebe65896e0154afeaa676e0154afe6a676e0154afe69e76e0154afe69676e0154afe69276e0154afeea576e0154afeaa576e0154afe6a576e0154afe2a576e0154afee9176e0154afe6a774e0154e7ee5f74e0154afe69b74e0154e7e5db74e0154afeea574e0154afe6a574e0154e7ee5d74e0154e7e25d74e0154afee9974e0154e7edd974e0154e7e5d974e0154afe6a764e0154afe69f64e0154ebee5b64e0154afeea564e0154afe6a564e0154afee9d64e0154afe69d64e0154ebee5964e0154ebe25964e0154afeaa396e0154bde69696e0154bee69296e0154bdee9596e0154beee91 else 0xf7660a54afb6977660a54afb6a67660a54afb69e7660a54afb6967660a54afbe9d9560a54cfb65d9560a54afbe999560a54efae819560a54afb6a77560a54e7b65f7560a54afb69b7560a54afbea57560a54afb6a57560a54e7ba5d7560a54e7b65d7560a54afbe997560a54afb6a76560a54afb69f6560a54ebb65b6560a54af768f97e1954c7fe5e97e1954afe68297e19548ff69597e19548ff69197e1954cfde8597e1954afde8597e1954c7f65c97e1954afb68897e1954afee8195e19549dfe9597e19549fde8597e1954abf69b87e1954abf69a87a1954cbf6a786a1954cfe6a190a1954cfee1d90a1954cfea1d90a1954dde69590a1954dee69190a1954c7fe5e9761954adf6969761954afe6829761954adfe959761954afde859761954afee819761954c7f65c9761954cfee9f9061954cfea9f9061954cfe69f9061954cfe29f9061954cfee9b9061954cfee979061954cfee939061954cfee5f9061954cfea5f9061954cfe65f9061954cfe25f9061954ebee9b9061954cfee579061954edee579061954efae4b9061954c7fe5e8761954abf69a8761954afe6828761954abfe998761954e9fe1b9561954eafe1b9461954dcfe579461954cfbe1f9261954cfba1f9261954cfb61f9261954cfbe1b9261954debe939261954ebbe1b9261954ddbe579261954debe539261954cfee1f9061954cfea1f9061954cfe61f9061954cfee1b9061954ddee979061954deee939061954ebee1b9061954ddee579061954deee539061954dfae4b9061954c7f65f8721954abf69b87219548ff6a68721954afe68287219548ffea58721954afde858721954afee818721954abf6988721954cbfea58621954abfe958621954e9fe958621954abfe918621954eafe918621954ebbe898621954ebee8186219549bfea58621954cfdaa19121954cfde1d9121954cfda1d9121954cfd61d9121954cfd21d9121954ddda959121954ddd69591219548ffe95989d954cdfe95989d954cefe91989d954cfee81989d9549fee81989d954abf69b879d954cdfe1d959d954dcfe91959d954dcf291959d9549efe91959d9549dfe95949d954cfdaa1919d954cfd6a1919d954cfde1d919d954ddda95919d954ddd695919d954cbf69a985d954cf768e985d9548ffaa2985d9549f768e985d954af768e985d954cefe91985d954cfee81985d954af7e8d985d954afde85985d954afee81985d9549df697945d954c7f6a787dd154a7f69b87dd1548ffaa196dd1548ff2a196dd1548ff6a786dd1548ffea586dd154a7fe9d86dd154cbf65986dd154afbe8986dd154afee8186dd154d5fe1d95dd1549dfe9995dd154c7fe1d95dd154cfeaa190dd154cfe6a190dd154cfee1990dd154cfe61990dd154ddea9590dd154dde69590dd154dee69190dd154dcf295979d15)) else (if j<5 then (if j<4 then 0x64afee819661664cfee9f9061664cfea9f9061664cfe69f9061664cfe29f9061664cfee9b9061664cfe69b9061664cfee5f9061664cfea5f9061664cfe65f9061664cfe25f9061664cfe65b9061664cfee81989d6649efe91969d6649fbe89969d6648ffea5869d664c7fe5e97e1564aef69297e1564afe68297e1564c7f65c97e1564adf69787e1564adf69687a1564cdf6a785a1564cfd6a191a1564cfde1d91a1564cfda1d91a1564dbd69991a1564c7fe5e8761564afe6828761564dafe5b9461564cfee1f9061564cfea1f9061564cfe61f9061564dbee9b9061564dbee5b9061564deee539061564dfae4b9061564c7f65f8721564adf69787215648ff6a68721564afe68287215648ffea58721564afde858721564adf6948721564cdfea58521564adfe918521564ecfe918521564edee8185215649dfea58521564cefe91989d564cfee81989d5649fee81989d564adf697879d5649bfe99949d5649fee81949d564cdf696985d5648ffaa2985d564afee81985d5649bf69b945d564e5fe5e9761464e5fe5d9761464adfaa49761464e5f65c9761464c7fe5e9761464adf6969761464adfe959761464c7f65c9761464afd6849761464afe6809761464c7f69d989d4648ffea1979d464c7f6a5879d464e5fe95879d4648ff6a5879d464adfe95879d464cdfea5859d464e5fa9d859d464e5f69d859d464cdf65d859d4648ffe95985d464cdfe95985d464e5fe9d855d464e5f29d855d464a7fe9d855d464cfe681981d464cefea1941d464daf699941d464afe69e7560064cfb68b9661e54afb68b9661e54a7f69e9661e54cbfe5a9661e54afd6869661e54a7fe9d9661e54af7e8d9661e54cbf6589661e54afe6809661e54a7fe9d9561e54afde859561e54afee819561e54c7fe5e9761a54abf69a9761a54afb68a9761a54afe6829761a54abfe999761a54af7e8d9761a54c7f65c9761a54abfe999561a54afbe899561a54afee819561a54cfb68998dda549efe9195dda54cefea194dda54cef61994dda549efe91959da548ff6a69661654cbfe5a9661654adf6969661654aef6929661654afe68296616548ffaa49661654cbf6589661654afd68496616548ffaa67661654adf6967661654cfea9b9061654cfe29b9061654cfe9db9061654cfea5b9061654cfe25b9061654c7fea587dd6548ffea196dd654c7f61d96dd6549f7e8d96dd6548ffea586dd654cefea194dd654dede8594dd6548ff6a3965d654c7f61f965d6548ff2a5865d654cef6a3945d654cef61f945d654e6f61f945d6548ffea587d9654c7f65d87d9654cefea194d96549efe9d94d9654afb69a9760a54afb6969760a54afbe999760a54afbe959760a54afb69e9660a54cfb65e9660a54afb6969660a54afbe9d9660a54afbe959660a54afb6a77660a54e7b65 else 0xb383bc0ee04700b7e7be4deaef3f793bc3ddeee076f7b6cdaeed3b67fb30d956c6f5adac7d60eaef559aa6d4bea47517a7cd3b69c34d5a5bd2ae93f493a3ad1a68bb43fa19d09e8133fd9f8cf4e78f3bb9d7ce8e6e73679a4ccae61b30197acb5e59729b947c93645f2238f9c7563931ab8c6c6062eb1698aec54628b139896c4861e30d3863c2ee15f0a3842c1e60b703d80fc005feafe97e5befdf42f837bbbdade9af41788bc15df2edb767ba7dd26e75734b975ca2e4571cb86dc1eddf6e0b68db2ed8b6bfb5cdaaad3768cb435a02cd1662b29d912c6b62fb105822bf35e1ae4d70eb7b5b7ad4568ab39596ac8562aaf7551aa5d4f2a6d530a8c544aa074eba6e533698f4c1a5dd2b292948ea3fd1e68e746da33d18688143aa15d07282d410a054fee7d93e69f04f227733a19c4cdea6c535c9ab4d4269534499f4cbe64131a985cbce5a52c3955ca9652d28793c49a64b5254927492247322a90dc80e3fb1ee8efc7423831bb8d6467631d1648aac51a26f128891447222d0f586ec33a1910b0850c26e12b08f844c20e0d7065826c0fa05f02080d405200afff7fcbfcdfdafe77f0bf6dfaafcf7e4bee9f68fae7d43e89f38f967c83e05ef6f757b7bd81eb4f4b79e3cb5e18efd77bbbc5dc4edc766bb1dd82ebb75aba99d40e8873cb9cdcdae67730b96dcaae4f724b90dc7ae2570fb865c26e0d703b7e1be4dec6eeb75db90db96d9b6b5b4eda16cdb655b0cd806b8b5adacad4d6a3b4e1a52d1a685b4159fecd56633301974cb4652b259920c8163db1d58dec6062d312d878c2d60f303d812c035fa2f957acbd05e52eed76abaf5d4ae69716b7c5bb2d9d6c2b5b5aaad3d680b3a59a2cb963eafe57c2bc95b4ad45672afd560aa15492a0d4faa7752fa91d470a32511a85141c9f64f3a7853809b14d1264d3089754aea53927e939495244921890647ba3c51b28d345da2b114c89744422090e686d42f213d06e82840ca04d01a8074009fc8fc67dd3e71ed8f4e7a13c91dc4ed675c3a21cf8e5e72038d1c2ce0a6f63739b84db66d53679b24d866bd35b9ac4d5669c34b1a1ccf0672331992cc786363139884c2460c2fe97dcbe25eb2ee1758b8e5c12dd96b0b4c5a02c8962caf856d2af1560aa454329e94dca6252228994109ea4ef274938c9ba4ce26413089664ad2539260912483235912886441a1fc8f8475c38d1b60d2c6543121740b4055e28e13b097848c22e10b081c3de1ce0db069c31e1650a684d423a10e07f835418c09c04201b009603c016807801e000cdfe569561a64aef6929561a64afd6869561a648ffaa49561a64cdf6549561a64c7fe5e9761664adf6969761664afe6829761664adfe959761664afde859761664afee819761664c7f65c9761664abf6989761664afb6889761664adfe959661664afbe8996616) else (if j<6 then 0x82040408080000001146a250a804a300040408081010002a0040000327f1f8bc200a34947028200002040318200000040000000200000001000000200000040000408000000080010000040009801000f0020013001008542384370820211c2128c102460f081000000000000000a020808080000019c100c6099c1d1030e040001c0806604c60800114102166008000c60806130040088100000001c608001000401040208000000101f0020004001c42008008026004c00800007c40008000f8bc0178800100000e104000000071021271b89c22006004001c560080d10210d1040007c0080000e005c2e0080310200000000494ce10c0300260040000b002000400309a108020e114216134216101f17802000000000f002c504070026170040662b883620209b084000010002000440090810000000080011882316004031011882000406081e0048608001f1f8bc20010860f8c1f18200040000028100218100210001000b420b400800000000a6084004984102812502c5040000e08000000000000007801000000000001008000185040c28385070a08c70be00ec008005141000a080000001410011050bc2080000000000000001000100000000040400006081c004040800000000700103800800788001000004000f001e0020000301004002000100000000f80103c00800000004000020007800880100020006104cc098810003102000019811002a00403102000000630400003182633118430003099c200071822004c20910122020004471846233046304010026204031984222020110c3a00c40088011002200740091440168013082008013119820003102019840100101005e2040100210040100200801310210100420074008000000401d00200401226002c002018c131988c21818004ce200801002a0040228207841a202000000000000000200401003800401002103104200401002000010000080000030400182000040400006080000406090c10000002000010c101820f0588080000003c100007820000f041e081e3f085e2f1f843f1f842f19b02f1f84ce1f8fc2119f09e3f09945c278fc21e1bc7e10f09e1368784f19b03f1f84233f8fc26613c7e108cfe3f08667f1f843f1f842f1f802f1f842f1f802f1f842f183e3f085e3f17843f1f842f083e3f085e3f1787c0278fc2178fc2178ccc178c1f083e3d078bc2278c1f1f8741e213c7e10bc6660989e3f007e107c20f801f083e107f49f95fc7fe27f07f7dfb77d7fea1f41f997cb3e4df17f847be7dd5ee4f6f7b3fd5dea8f4cfa4fd1be75f2ef917c6de30f157893c3de18f097833bfbdf7ef8f767ba7db2ed1f677b0bd7febcf587a93d3ae9a74bba51d19e89f437a0fd01e7df3d79bbcd7e68f32f98bcb6e4f7263925c83e3ef1bb8d1c62e29f13787dc38e197 else 0x800000000130020007c009801000f0020007c00980100070828471294301c40800049c213894a1029c41000100000000000000800389c010005713803b0820688541000295c4138dc213101000000a080000000078bc010000000001f1000200000020000100000020180100000080810100033)))
def g503H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5123a09940a606d00000003435000e14bef8e0000000000000000819d086e01481f40000000c053003c0005879e07bc14b80000001aede134000604ac0f776000001006000168de0b8a08ec2128180c1d457800000001810b864c11800000000000cc620000c2f000000000003c1b28459af540af402e031dad8e13d816b07c0001c0cbc49a818700fe0c00000000fe8a00000000000006961a2c1f007871030154000002800010120000087ab0bef83711c000090b40000413b84070c60000000400c60e30225daa0000505c0151e1c502a000160540000000000101580000370000000012ba887500000000c2c0000000000000000000b0ecc1d20860000cae60000d18c8840000200a81c00000001c09400d8000c0b20000000288b504542480280008f08dcce8000701a710fe1b800000000001c0d40000c370000e1bc00000003863d8309042073f085213aac2581cc2520002408f86c10d3e111c1f8000c0960003fb2e082712060418393041b072c16c00000000000e0efc308000dc6e1558000585dc046d8200001d7d10e00001eac18010001602c4098000000000000000000000000000006880000000010358017a059e1880006077000000000005053b0cdc0f0000000060fe81f900f8000e11e000240e8000208fa19c401d065a02c24280000000000000000000009604189bc00000006087820e0454812000130230020000f05ec2340003d579032613282e78850000000000000000001414400000000048000000021500000622081b80006286e1240000857101be0780000049300c118cc07088502964090a600c641002008422092a20106001044
def g503D9 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0xfc3cecaa5ff65676552ffb293b2a97fe985d954dff4c2ecaa6ff661765537f930bb2a97ff945d954effc3ee8aa5ff65b745537ff0dba2a9bfd86dd154bfecaee8aa7efe1e74553f7b0f3a2a9fbf869d154fdf434e8aa7ef61a74553f790d3a2a9fbe769d154fdebb4e8aa7efd9674553f7930ba2a9fbf865d154fdf432e8aa7ef61974553f790cba2a9fbf955d154fdecaae8aa7efd95745537ff0cba2a97ff955d154fbfcaae8aa7df25574553efccaba2a9f7d655d154bfecbec8aa6ffe1f645537fb0fb22a9eff86d9154bfecaec8aa7ef5d364552fff2eb22a97fd9759154dffc3ac8aa6ff61d645537ff0cb22a9eff8659154dfec32c8aa7bf21964552fff2ab22a9f7f9559154bfecaac8aa7df25564553efccab22a9f7d6559154fdeba2c8aa7fee5b80553ff52dc02a9ff996e0154ffc4b700aa7fee1b80553ff50dc02a9ff986e0154ffc43700aa7fe9db80553ff2edc02a9ffb74e0154ffcba700aa7fed9380553ff2c9c02a9bff9761854dff4bb0c2a6ff65d861537f92ec30a97fd979d854dfec3cec2a6ffe61761537fb30bb0a9bfd865d854fefc9aec2a4ffe5d859937f720c2cc93fd989d6649fecbf0ab26dfe1685592feb2342ac97fb9061564dbec290ab24ffa62755927fb313aac93fe985d5649fe4c2eab26dfe5d851936fd2ec28c9b7d9761464dbe4bb0a324ffe5d851927fb313a8c99fd879d464dbec2cea324ffe61751927fb30ba8c9b7d855d4649fecc0ea325ef650751937f6eac00c9bfa7560064dfcbab00326fe1d5801927ff2cc3ca93ff9761a549fecc6ed2a5ef653769527fb313b4a9bfb9061654cfec3eeb2a5ef653759533fb0ebaca97bf945d654bdeca6cb2a6fba5d829537db2ec14a9bee9660a54df6cb3052a6fbdd9829537dcecc14a9bed9560a54df7bab052a6fb5d5829537decac14a93fd97e1954d7fc350caa5fe642865527ff2ec32a93ff9561954dbfcab0caa6fee41865535ff0cc32a97ef9261954bfdc830caa4ffa60865535fb0c432a97f591219549ff4c4ecaa4ff66276552efb2b3b2a97f5919d9549ff4c2ecaa4ff661765527f930bb2a99ff87dd154bbecaee8aa5fe64374552f7d313a2a97bd979d154f9f32ce8aa7cfe5574553e792aba2a9f3e655d154f9eb2ae8aa5dfe55745535ff0db22a977d95d91549fecc2c8aa6bfe1964552eff2ab22a9bfb96e0154dfd4b700aa6fe65b805537f12dc02a9bfa76e0154dfcbb700aa6fedd3805537f2e9c02a9bfb64e0154dfcb2700aa6fee1b805537f50dc02a9bf986e0154dfc43700aa7ee9d380553f72e9c02a93ff97618549fecc4ec2a6bf61a76152feb233b0a93ff985d8549fecc2ec2a6bf61976152fbf26bb0a93fd981d854def4b3062a6f7659831537bcecc18a9bdd7660c54dee3b3062a4fee41859927f720c2ca93fb9061954 else 0x80ad8ab54acbab18ac2aaf4ab5aab8aa6aa84a95aa30a82a9fca79a9c8a70a9b4a65a980a5aa954a4ba910a3ea8d4a2fa8a8a26a874a17a840a08a7f49f5a7c09e8a78c9d7a7289c4a7049bba6d89aea69c99fa668990a62497fa5c896ca58c95da560950a51c93fa4e8936a4b4929a49091ea45c911a4188fca3dc8eda3a88e6a3848d7a3488cea3248bda2d88aea294899a25088aa20c879a1c886aa18c85ba15884ea12c843a0f8834a0a4821a060814a034807a0087fa9fd47ed9fa07de9f647d39f387c49eec7b59eb87a29e6c7959e407849dec7759db87649d747559d4074a9d1473b9cc07269c747179c387049bdc6e99b706d09b1c6b79aa069c9a2c67f99c8660994464198c862298445ff97c05de97345bb96a8598962457995a855a952c53b94b8520944450393d84e6935c4c792e84ac927448d91f046c916c44990e8428905c4058fe83ee8f7c3cf8ef83b48eac3a18e483828dc43658d503428cdc3258c503068bf42eb8b782ce8aec2ad8a782908a0c27589a0256892423d88b8220884c20587c81e487541c586d81a6865c18585d8166855c14b850012e847c10f84000f0837c0cd82f00ae827408d81f006c817404b80e8028806c00f8000dff4ab0d326ff255869937ff2ec2cc9bfe9761664dfecbb0b326ff25d859937fb2cc2cc97fd969d664dfec34eb326ffe5f855937fd2fc2ac9bfd97e1564dfe4bf0ab25ff65f855937ff0fc2ac97fd97a1564dffc3d0ab26ffa1e85593eff0b42ac97ff9761564dffc3b0ab26ffa1d855937fb0ec2ac9f7f8561564fdfca30ab27fee4185592ffd3042ac97fd9721564dffc390ab26ffa1c855937fb0e42ac9bfc8721564fbec290ab25ffa6275592ffb313aac97fd979d564dffc3ceab25ff65275592ffd30baac9bfe985d564dfecc2eab26ff26175592fff28baac9bff9761464dff4bb0a326ff65d851937f92ec28c97fd979d464dfec3cea326ffe61751937fb30ba8c9bfd855d464dffcb30f2a6ffa59879537fb2cc3ca9bfc9661e54dfecab0f2a6ffe5d869537fd2ec34a9bfd9761a54dfe4bb0d2a6ffe55869537fb2ac34a97fd95dda54bfecaced2a6ffa59859537f92cc2ca9bfe7661654bfecb6eb2a6ff61b759537fb0ebaca97ff965d654dfec32eb2a7efe51759537fb0fb2ca9bff97e1954dff4bf0caa6ff65f865537f92fc32a9bfd95e1954dfeca70caa5ff65f865537ff0fc32a97fd97a1954dffc3d0caa6ffa1e86553dff0d432a9bff9761954dff4bb0caa6ff65d865537f92ec32a9bff9561954bffcbb0caa6ffe1d865537fd0ec32a9bfd8761954dffc330caa7bfe1986553eff2ac32a9fbf9461954ff7c930caa7fee4186552ffd30432a97fd9721954dffc390caa6ffa1c865537fb0e432a9bfc8721954f7ec310caa5ffa6276552ffb313b2a97fd979d954df) else (if j<3 then 0x101c1b0c8c1052706a144101c1b8d10404e308128c981c4878623c410178b8f8386106c660e3e2e18418138f878388946e3e105e2e0178b8c9784425c6c461e2e0e31e971b11838b8f84725e0e3e2e11418101f8f87809788807e3e1e0e21418138b8f8780607060504e2e0e3e1219e1a138b838f8478684e3e0e2e1671d9e1a138b8f838478684e2e0e3e1671c18159f8b838f86108a706e2e044e3e125211b8b81138f86947074644e2e0e3e125229d1a978b8f8385108a7a54644e2e3e0e120969d1b89138f838482746e2e0e3e12544209c978b838f871876586e3e2e188671d9e1b8b8f8621947678665e2e3e1881d9e1b8b8f86219470605e3e1e084e21c1b8b8f821384604e3e1e0e227181c178f878389107e3e044e1e2261a11838f8a178468504e3e0e2e1271c1e178f838b851072744e3e2e085e11e178f838b8510606e1e3e0e2441999178f8780399c7676645e0e3e10e1d9d168b8f878039988676645e0e3e10e1d99143a1383878d9c86745848ee0e3e166219d982f8f87803870e664584e0e3e16720399d9a138f81178480e674584e3e1e066201b8b838f845e3e226e1e01717109b8f8b85807060504e2e3e0e11c18101f8f878117888e3e1e0e211838f87884e3e1e0e2129b17118b8f87807a6c5c4e3e2e1601c14101f838f889b848e3e0e1e2261584c717138c9b8b808050407e0e3e2e126201f8f8b878050545e30604e2e1e0221cc717138c9b8b8080504e2e0e3e11b8f8b8780407060504e2e0e3e122138f838b849c645e2e32784e1e01c482b19289f8f8b86109e305e204e1e01810178b8f83849c7e24584e0e3e11916138f8b8780684e2e3e1e0451a138b8f811784645840504e3e2e1e021178f8a1387806e3e226e0e115178c9b8b87821078407e3e1e0e2189b8b838f8610645e3e2e1e0841916819d9913178b8f84967e220e3e1661b159d9b8f868388767e24544e3e1661d9d15138b8f8598745446766e1e2e31d9911178b8f859c7a0676645e244e3e1219d15138b8f85987676645e244e3e11d9c8115138f8b84767e2e3e16614419f8f87885672045e244e3e1662117899e838f8510767a0e244e345e11c1a178b82138f84705e244e0e3e1261c141d138b838f849881187c5e226e0e3c4201c19178b8781138c84544e2e1e0e318981d1787838b8d1088786c5e2e0e1c41c9d178b838f849910867e2e085e10f661d9d9a17838b843c70f678485e2e0e166203d9d9a161387838880f678584e2e0e166231a978a138f84685e284e3e1169b1711838b8f847c3ab0dcc31b0b0c24b064c11b028c06b00cbf9afd8bf2afb4be7af90bdeaf44bcdaf20bc2aed4ba7ae90b9eae5cb93ae40b8aae14b7fade8b76adccb6bada8b66ad74b5bad68b50ad3cb4bad10b40acf4b2bac70b14ac34b05abf0af4abbcae9ab else 0x563610c14107e0081f8020761e00c1c118b809450562e00c148810305041c107626025101c10704149c22725089c1a3a10a8d8a85801c1460504149c2a2a00896898a81801c663a261a0272518801e2e00a978880360049c1270509898026361081c14205041410522200c005041510801840004342414010006041c9610367041c10663626160672584201c170f0b07001072704a50e9e95103a7a5040e9c10941c40662840c198420663089c18118040561600c1c107046260101d8c20704111420562600f081c10306c2040c1b80206050461e0141586001840723c204101c144270a1f081030110127a0060c1d8c20760081d8420745446210118114305440887809c98427260b809c2a00681801c18406e0081f8b80307e2e00c1d8d878b80507e2e00f8b80206e0270e8a80226a2a0600716898681809c986a2a00b801e2e00b8b802a622e00e9b898030504e00f809c284a1270612128580384a161601116118a841c18606e00818141380406e0088f00285a1060c19170010406c0050c8f802e3050905038c4e30700142e027091817003a00708990a81001c50784c045101c1420561602712101e00589802450461e01115842630411802e1e0050427149e141038527e00e1589809c427850461e0141d14207616045109c158030785a14513021d143e145840f851610305a1840e861020423c00d1414140060c1b8020622c045109d15870214504c0860c8c87001448505050018326840b809820542400f8098245c0840c161020622c02010161020604081a102278545261315151280466a00b158a80366454461a015151280366a0098a80266454461a0151586019846380099e0114361804544119a011434480450c1e1020762081d8c20726046))
def g503H9 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x4c065fbab8000090920000040890a2bc8f5c063800000000c12b198fe414de1082133a8463002be14b704700000544a00004038043b442612580212aaf5aa04b7663bf11e00003c3f96037c0351035044a1f13c92558a1b8049040c0f13228514841780876885ad414c35c0000b07fd00cc221200008c7dd8858000080f2501c7830c84f80000c132a05e2808a2a4c80a6f830983b20000e0b3d81a6d4b800005510eda0f22a9e0d6027b9803e8bef116aa078783b20424c25ea119228f80000285da10a347b78075c19480657944000010066a2639079329e4a11e20a75808f3a598a4f704b500fba9b58120923f8000101b20000210f302f6802880c1605d206746ca65148c02f00000041f627a802ec0089021601dc80528000081bbc09a0000205bc00000000b0ef2843cc252c01a0000758c800000000205f0929381680000067e1780f424b0115003b80002c1fba165f113206cebc79f65600000000000000000c09ba03a800000000b0e2661d7800c000000003338c00000000000048950000000000000409990402000000002d954000000000000723b884a622380000506b3902314df50e480000013a0000b13a80000000000007047d05332a8f21ee900f591bb002144631122388614450e04040f48869a816c000020309820c00fdfd2a2a765062982fee02cad03301944b82d40fb0ebb919adc89201780155a471ca22e09b32a6a44511258e9190000180ba921a82490065a94200000000000000000343776111000048263f9d2e08c413872098833e555540a800213e9a4000000670000081b6aa27500e608898390f59d241180002422780310000175a34507225f950f30510000185f970f8000000001416cda13e8289c1660000eacb403cc000040dc5b241419b489400000000302824405c42d827a80001c03b800900000000000000000fb1e0000301d04184503100000000160e20000000000000b0264040c870744ec400d000050794fad241b52040494156cb221a280de70a0bfa50e0f141312838c0000c17e4d10a094684fe00008436486810120615d12490825c8a6ca078001b98090025251c001000020c060210030301002b1d033200010c165200280e271f14020001012d1213040032091b011a090d00190124090b000008102315030106522d0107181f03051e030100060c0012021310030601010702032310230005201806010400030a0b0509372002420b05000400000013011a2100010d051a00200901000c0000211f18060101010500050588010100041e04330f0d0400000001051e02280302050203300004191600000b010812001b04020a00010203000106170e0a090e000200010d05111b04040004030b0200161207040a03000700040b041300011202080006060108000c0b0117070f0b010904020209 else 0x1c4d80000d11480003515b8d5560e18000319fa000036a50000000000000e0dd0000000011e5c0000000000000000080a7982bf8503a1bd60b0397d18a24e00000001d3c48356c011e10500000c1880000e1043087c00000000000048030000001f7c044807080000e1ff000000000000161d11af18292842eaa2067039a0630000161012a6a68692049854d500005143a028355279002780b5842e000080eb00003c96c0000000017588000000001ac700002036835c6b064f872c0000607580b8413b40001ea4e24808000000000000a01f9f4ac432ae09280c84012fc330c1493cf83111481ca00000000228b931d20000813780000000000001c089857d223560d5b67de93600001a17a60e3104edc3dbc0cfdb2e789776b594e3b10688000000000000303a00003f4080000000000000000121ad6aa52031dfac2000082b6b10e400012103f22d091ab6b3200002259201acc8bfe1fd00007b99ef9d050ea2ca8309074b03e24de02958222544480480a937062e83d6000000003092cc2f98199a11ae05694457a2574c12988c25a0fa09c00006046c0001c12c22410000000000000f8e000002204aea2611048000343a95642404cf938cc43a000070f1800000000623e0000794300000000050b1216cc43dee091000041597013e113b90d800000413c00003001800028bcf3d60d09b524090280c1e77520a09c80001047100006c79c00000000a257d8028000000000000580f72cc9012e50260000250c008fe000019181b380e053c0861846a0b2f21fbb10cf9436c30ee0390000044600000d01100000146703720000000000000000181540000404cd42e7650790ff2949400002927000040608000055ab000038214c4740000000000000a1fc2055a0c0c53f143c4c1529489202b67ac60000a13eb81500000246900fa000000001845eec9400001c28708e7000000003033c0000c136f868c000174d650c29880e820c606410c9d01bc0000000060015d8c7825ea1d80b2bb83dc0000e00b8455b820800010119748600000436ee0fc00007834c00014918003f80000d0d20000946870960400be227810d05364000120a1308e8000000010026e2441848a820ee5990000000000000e03b7485d04e2c15cc1728024f03bf30ec0000289f000018a50007b50d7c056c01fce1120087783333848290910e71b52003cde1f1500cbe55244e80000a03e99554030d64d560d480003005e2468b0b1f097280c061f2a69f897e381cc00003f0f5888784a40000b0044451369bb154de2c488039c156443d0000382d4e232008bfc750000202e8422a70ed92198000125eb7a785881114b2000000000000208d60000000078a16423e000060bc80000000000006119b808400000000a1170005a81b4000000004066cc1e80000a08) else (if j<3 then 0x704e56b5d613c2121e02a7027b21b21b31800000000857f60b6902192b3fa04aa456109e41200c0070000380ad8afc000000ab0000000008215000000001c2cc0000000000000000141590000189e00000000020a3182df0148012d705600000000000000000000000001e237000000000048e000034aa7c7a30284000061099898c00000000a10e085dc01c2822d6118a0634b9f38168bad0004d0000041f8e0148a8b60031215c3ad1507370243205aa11cdd522031e00009528580a2922c21fa709398880432d0260c530a8523ca15e25a2130e15ec426b8058cb26a837b0257c16e3256294dfc1f28093c26d508b3409e219ce0451b9a2c1a4a114443385490888c220000000029e8263c15180e9df95549ac00004eeafd0a000008072a2be90814439fa1f90000002f38b3021e800007b7020048612ae038f2936c9c4000050d4503b4000041e10000404104164a1a10000103900000000080806150fc4d6000040abda44f02d2000060e97538080820908a2dc2a6b4048b427e000010700000001763134a02e0000060a32887f07d600cf001b1021808eec246000060df8c40b00b220bf00003f541428e0000000030842c1dc01f6000020624d1fb60cd9283415e80001410550af5013a0469416b1a14895687abcc22fb476e092aa9aec5f6302e502a16c8085f5811e8869c000005023000800000500a0d0c525d804c4a4cc126a0aa800002b20407c0000409c79220000070ee80000000160257488c854c0001c0e7e0234876bcaf800006292000012c8e000000003da1083aa0cd60000328f29380000000002567102f6b0fbd89fad90c0001a14a4123511034a8a246700002c3f41a9a00003b0f0000080b7c0328c3c50a12a286801f0000382ef81af22363a7ec8458ec9728e2001b78109009b005f0000782e72849a27b80283a3a8620115a14eade187d00d9d65da1118000300afc07a668300001c898c85f512780003433480c86058fc42209e4a079f05500002c1b00000047ac05aac11a41be0000000000000000050efa8891447fe13ec0c0181d800004158e112a090300dbf549e1343440c0001c54a70c8aa095020500120000084406202000000002c4f4c9680000c239285c4c4222183ec27084a101f60000b01e0000259c2e6400000580d4000181b80000707cf69a325095127000000000000000000000000018a60000000003034a000000007154804dc690550c4686ab038e00000000000000000e2420000483a540ac0000a04a8e2c999ee49af0000162f4000064aee0e5000000000f646000000002fa940000a103b896582c364f6000070318000185b77031c04e80000e17d8013fe1d100600000713b80003036c08684023f13940001ca55c266d842a83d97d2900006b5a8000120689028b09aa09fd420d000000000000 else 0x1e1179a77d83dac12820fa107ae97a02b2f620c8075e8437427f81647910c074104e61021c2c8e886c041da42efb2220080e28300c5907c6064800000000f2a7181bad1d290ff000053414000000000000000000001592980e600002c1c141e020997071603d521b1b06f900d3023920b00000))
def g503D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x13c6c5830e3889480c113a58d13160c784a4f1a262c18f0a5213c64b131e0c58484e18246898b063c294a4f1a262c18f0a5213a5891b163c18484e1e362c18f0a5884870a9d2c4c58f0618c5278d8b063c2962109a2e1c7831444e4278b8f061c51131119305c7870624f1098c9d3070b8f160c310a8e9c2e3c383126884844e15345898f161c05278b131e2c3813109d345898f0e2c04270a122c4c78b0e04c5054f16263c587026253a689170e3c58084d1a285098f161c09ca4f193450e17163c1842169e3c50b8b184c3813151d3a68a182e2c7870042d3c4c5831e18a9880e193a68987062c714a4f17160c38d34420385081b160c78480e96363c587004203040e96344c787062283a50d8b004c78480c9e2e2c0131e1203a68b8f160c21080e18205c78b0e0202840e9a2c4c18f161283a68b131e1c18888a9c262c78308e1c2844f17163c18494116263c58460e982e2c18f084203040b8b063c2386098b063c2306c58f0881474509831e119045898b1e118785098b0611ae8ad5ac62b6aa3a94284a73660650e41631e20a0d9fc5e95d9dca5b75a619698396ed5bd471379249151058f60e30d38c40b48a5092082874c6385784803a42e42401800c0003ff9d664fff85593ffa1564ffd85593ff21564ffe75593ff5d564ffe75193ff5d464ffc75193ffdda54ffe76953ffdd654ffd75953ffd9654fff86553ffa1954ffd86553ff21954ffe76553ff5d954fff74553ff5d154fff64553ff59154ffe76153ff5d854ffc76152ff61a64bfd85992ffe1564bfd85192ff61e54bfd86952ff61654bff86552ff61954fbe74553ef5d154ffb80552ff61854b7e85192df61464bf980192fb60a54bfb80552f760c54
def g503H10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x85a4c8a840003815d001098eb69c600162c7dbbd182f972cc0002449200f000000002e290000251030a46148f8473e295e29ac487423e40040001e16800013bdc00024aa800014c2000030aec0003414883b40002c96800003b1b032fa8f840630aaf4289845800018175e0aab0cd22f9437990a52a668304000101ab82a7797400020158000041800000089800031466546f03248496ca200001509b730400025a878816508f997980880001001c5cc00003b3e372700000000000000000c2fd48440000392400000000000000000003ebebc1d3909c0002081fc4d05af3cc46db9d3b16433602aec0900000026ec863d44c84bac25c0002047400e5147602280a4cc0cb0881005c00000000809dc22c0003cb65a8f743440003835683e942c28300ca2400032800402b814604b400008b3e88b0c1b0813a22ec149c84d40cbcc118c1e7c1d400033ad052bc5044820000025066bb00000204c84338000241b4c48b8294000142d34a3644be6c7bb16a10a1a969125f43e640ab10a9e9c18362882800d88234c12f80aec46d1412c4668a07c85002f5c1afe8930084409840c60bd80000041402980001403a0bc7a2a138d8447c000154d80001c0c00001430f83acaaca83bb8c3e416c819000036885ca42039483a2018842cfb30000020312a3c4000041db80090b1d425800000000c2cb42d40000c35c0000000041a400000003141d4240000281f762b080fe81a1088f83654a940002497b005b2c48000104540000c0400001c8bdc8540000000000038319442400000002d4bdd16c000384468acdc252023a41f981980002c077028680b4c377b835c38b4407046000008c3bccc1807fcb010c48000000000003e88aa970000040e800000ac80000c20ea0a4000283e0487fc2ea82da2a50839d4a6901548c3400039c36802cc048a0a282ef885c000171dc92a0c323c1dc449c0000c2dfa09f84c2c4db80200000000043f00003028c00023214000343c8000314df83a7c268c1c400014a700000cae4000003ccf8d6c37f0848b96f012404b3016743ff44804b46d0adc434cafe38d300cc0000c3490122811400000000008f9a6ab1f000034398023000000000000000005489ca1f0264846800000000000331580000ca880000c2198b6a312981944a11629c0383c217c3280000000001cd0330843320b800ee40a2c21d02112bb6836dc43c12270c0807e0408824280e058802eb90105cc207118ccc7360715806260880c5c1d00024100b00800c815458740c5d030ec000104128020b0081804090c8280a0b0002c2e050307c000017800060c00818021b039d01608018780c6611014080d130180612000087a0c0087800020600c1c0906874000a0780014060180436040600c0800000041007000000c010000c7a03020000c01001d8107e else 0x2435808180003527303f78133841182c521464254412b417aca325a4692775968546ac247c4ce80a5806401fecbd4293ec081040ec1efd2a80002413c8a0eda9281f1c2b789b742aa3025c3d003df018fc3d4c07bc3be44488387916a027e89b3445340f68a2c0003416340440169c1ea0a18697b0a296149c440a0bd01bd4025c22352c004dfb06ce14343c0085ac3c4831fca9188c2884ec43952a5920d02bad2994aa2c0ba803c4b3580f9c8a00002049a209a68eac14e6c358940806e444e3a8c011242480227829dc9e0529c89454390d292c4aa8b3b041a7a71ba7652b380334bd2833d82b1918143d9c3ef024d427581e180738b8eaa4b804fc28108684478c0df82a352b941536a4e0a5f2a7e0135e2f39190011f42bfc45f42e6c3140003a917c2f144031bc10002800dc292eb5d88654c40f311414000d7c41f0872006aaa5692b67968b3cdc19f04a381044408ea6b88744bb80003420ac1854a6ef00c000044c50035417c80b0eaf1b30c00e340d3a3bb83b1810f5297842c33c2834c00018019c3680002c1b8826142700003c37282e009ef03090173a96c0000000000000002c0500000835204a6c48e8279c1c900540000c421c428038c000000020a3948e80000000300be7acc9174c09604afc1c1ca0892cbc87b4100000283f8caebf308020412d0ea90c3a9c34101)
def g503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c51a08638842071461228238481c51a28238442071858e18221081c61448e28602071858a086310887361446c1b003ff327fd64ff8c9ff953feaa7fc54
def g503H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c590004814000000000000000000070b20740000000000001c1c00000000070b000080d6928bb762660e6036d20c61f058001808000e2e689c001020641903000000068c8000001e11000415bc962ac6eb10ac8288060000000000000210c8947876847168000000000000716eaac000000506754e000814d75c0010240000000821d57b155923000012d0530a28afeab80b81183450074117a160aaa5da34e68542686680c3aa9c3f794a2f1823436000870d2286425435eab827512000b48807800000072f800000000000002b705c4491018002d5cb22854d23e01e00000010b182a000201419dc460000002a5800000068504d02308c1035d30008890411cb281000
def g503D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x401844ff
def g503H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x431c062f8492f8000f034a003915307a0000000382003ea0c89d0152d000100027183400000019134b76800000f601
def g503L : Nat → Packing
  | 7 => (148,5,5,0,0,10,0,g503D7)
  | 8 => (646,4,5,0,0,13,0,g503D8)
  | 9 => (312,3,5,0,0,14,0,g503D9)
  | 10 => (47,2,5,0,0,12,0,g503D10)
  | 11 => (6,1,5,0,0,9,0,g503D11)
  | 12 => (1,0,5,0,0,0,0,g503D12)
  | _ => emptyPacking
def g503I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 47 307 5 15 8 3 g503H8
  | 9 => lookupWord 252 1381 8 17 10 3 g503H9
  | 10 => lookupWord 138 683 9 16 9 3 g503H10
  | 11 => lookupWord 24 149 6 13 6 3 g503H11
  | 12 => lookupWord 6 37 3 10 3 3 g503H12
  | _ => fun _ => none
def g503 : Forest := ⟨503,12,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_0 : block g503 7 0 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_96 : block g503 7 96 52=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B7 : block g503 7 0 148=true := (@block_merge g503 7 0 96 52 g503P7_0 g503P7_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_0 : block g503 8 0 44=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_44 : block g503 8 44 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_140 : block g503 8 140 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_236 : block g503 8 236 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_332 : block g503 8 332 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_428 : block g503 8 428 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_524 : block g503 8 524 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_620 : block g503 8 620 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B8 : block g503 8 0 646=true := (@block_merge g503 8 0 332 314 (@block_merge g503 8 0 140 192 (@block_merge g503 8 0 44 96 g503P8_0 g503P8_44) (@block_merge g503 8 140 96 96 g503P8_140 g503P8_236)) (@block_merge g503 8 332 192 122 (@block_merge g503 8 332 96 96 g503P8_332 g503P8_428) (@block_merge g503 8 524 96 26 g503P8_524 g503P8_620)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_0 : block g503 9 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_3 : block g503 9 3 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_99 : block g503 9 99 20=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_119 : block g503 9 119 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_215 : block g503 9 215 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_311 : block g503 9 311 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B9 : block g503 9 0 312=true := (@block_merge g503 9 0 119 193 (@block_merge g503 9 0 3 116 g503P9_0 (@block_merge g503 9 3 96 20 g503P9_3 g503P9_99)) (@block_merge g503 9 119 96 97 g503P9_119 (@block_merge g503 9 215 96 1 g503P9_215 g503P9_311)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_0 : block g503 10 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_6 : block g503 10 6 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_19 : block g503 10 19 28=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B10 : block g503 10 0 47=true := (@block_merge g503 10 0 6 41 g503P10_0 (@block_merge g503 10 6 13 28 g503P10_6 g503P10_19))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : block g503 11 0 6=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B11 : block g503 11 0 6=true := g503P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P12_0 : block g503 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B12 : block g503 12 0 1=true := g503P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503T : checkedTables g503 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g503 0 0 0 = true)
  · exact (rfl : block g503 1 0 0 = true)
  · exact (rfl : block g503 2 0 0 = true)
  · exact (rfl : block g503 3 0 0 = true)
  · exact (rfl : block g503 4 0 0 = true)
  · exact (rfl : block g503 5 0 0 = true)
  · exact (rfl : block g503 6 0 0 = true)
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
theorem lowS503 : Lower true (varsX 503) (graphGoal 503) 13 := lower_forest (g:=g503) (i:=0) (hints:=4832298581) (before_sound KS487 VS487) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KS503 := extendKnown KS487 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VS503 : Known true KS503 := extend_ok (m:=503) VS487 lowS503 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0x785831e160c785831e160c785831e,0x58482161208584821612085848216),(0x182691609a4582691609a458269160,0x182681609a0582681609a058268160),(0x1708e45c2391708e45c2391708e45c,0x1308a44c2291308a44c2291308a44c),(0x13ca804f2a013ca804f2a013ca804,0x10c8804322010c8804322010c8804),(0x18dccd6373358dccd6373358dccd63,0x18d8c96363258d8c96363258d8c963),(0x2258dc896372258dc896372258dc89,0x2585c0961702585c0961702585c09),(0x18315b60c56d8315b60c56d8315b60,0x8315120c5448315120c5448315120),(0x256700959c0256700959c025670095,0x242700909c0242700909c024270090),(0x2c8a24b22892c8a24b22892c8a24b2,0x240024900092400249000924002490)]
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
def mo328Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x3cf3cf3cf3cf3cf3cf3cf3cf3cf3cf,0x145145145145145145145145145145),(0x0,0x0),(0x0,0x0),(0xf3cf3cf3cf3cf3cf3cf3cf3cf3cf3,0x92492492492492492492492492492),(0x0,0x0),(0x33cf3cf3cf3cf3cf3cf3cf3cf3cf3c,0x228a28a28a28a28a28a28a28a28a28)]
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
theorem mo328P3_0 : block mo328 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo328B3 : block mo328 3 0 1=true := mo328P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo328T : checkedTables mo328 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo328 0 0 0 = true)
  · exact (rfl : block mo328 1 0 0 = true)
  · exact (rfl : block mo328 2 0 0 = true)
  · exact mo328B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo328G : graphValid mo328 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM328 : Lower false (varsX 328) (graphGoal 328) 4 := lower_forest (g:=mo328) (i:=0) (hints:=12935258112) (before_sound [] (known_down baseKnown)) mo328G mo328T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM328 := extendKnown [] 4 [(328,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM328 : Known false KM328 := extend_ok (m:=328) (known_down baseKnown) lowM328 (by decide +kernel)
theorem lowM99 : Lower false (varsX 99) (graphGoal 99) 4 := lower_down lowS99
def KM99 := extendKnown KM328 4 [(105,[49,33,101]),(165,[112,16,33,98]),(166,[112,32,98]),(178,[112,32,50,67,100]),(204,[32,49,101,117]),(228,[32,81,49,67,116]),(298,[16,48,32,133,101,118]),(353,[96,81,33,50,67,64,132,116]),(418,[16,112,32,50,67,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM99 : Known false KM99 := extend_ok (m:=99) VM328 lowM99 (by decide +kernel)
def mo329Y : Array (Bits × Bits) := #[(0x3060c183060c183060c183060c183,0x19b366cd9b366cd9b366cd9b366cd9),(0x0,0x0),(0x0,0x0),(0x1c3870e1c3870e1c3870e1c3870e1c,0x91224489122448912244891224489),(0x0,0x0),(0x0,0x0),(0x27cf9f3e7cf9f3e7cf9f3e7cf9f3e7,0x264c993264c993264c993264c99326),(0x0,0x0),(0x38f1e3c78f1e3c78f1e3c78f1e3c78,0x10a142850a142850a142850a142850)]
def mo329C : List ColumnInfo := [(1,0,328,0,4)]
def mo329A : List (List Nat) := [[],[131]]
def mo329D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def mo329L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,mo329D4)
  | _ => emptyPacking
def mo329I (_ _ : Nat) : Option (Nat × Nat) := none
def mo329 : Forest := ⟨1353,4,fun i => mo329Y[i]?.getD (0,0),mo329C,mo329A,mo329L,mo329I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329P4_0 : block mo329 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo329B4 : block mo329 4 0 1=true := mo329P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329T : checkedTables mo329 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo329 0 0 0 = true)
  · exact (rfl : block mo329 1 0 0 = true)
  · exact (rfl : block mo329 2 0 0 = true)
  · exact (rfl : block mo329 3 0 0 = true)
  · exact mo329B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo329G : graphValid mo329 (boundsBefore KM99) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM329 : Lower false (varsX 329) (graphGoal 329) 5 := lower_forest (g:=mo329) (i:=0) (hints:=12884926470) (before_sound KM99 VM99) mo329G mo329T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM329 := extendKnown KM99 5 [(329,[]),(330,[16,134]),(332,[32,16])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM329 : Known false KM329 := extend_ok (m:=329) VM99 lowM329 (by decide +kernel)
theorem lowM103 : Lower false (varsX 103) (graphGoal 103) 5 := lower_down lowS103
def KM103 := extendKnown KM329 5 [(230,[112,98,48,67]),(236,[32,49,80,16,65,100,116]),(299,[16,50,134,118]),(422,[80,33,129,48,67,116,97]),(426,[16,48,114,66,133,101]),(484,[32,81,128,48,65,116,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM103 : Known false KM103 := extend_ok (m:=103) VM329 lowM103 (by decide +kernel)
theorem lowM229 : Lower false (varsX 229) (graphGoal 229) 7 := lower_down lowS229
def KM229 := extendKnown KM103 7 [(229,[]),(355,[33,129,113])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM229 : Known false KM229 := extend_ok (m:=229) VM103 lowM229 (by decide +kernel)
def mo331Y : Array (Bits × Bits) := #[(0x30303030303030303030303030303,0x39b9b9b9b9b9b9b9b9b9b9b9b9b9b9),(0x181818181818181818181818181818,0xf4f4f4f4f4f4f4f4f4f4f4f4f4f4f),(0x0,0x0),(0x242424242424242424242424242424,0x90909090909090909090909090909),(0x0,0x0),(0x0,0x0),(0x7c7c7c7c7c7c7c7c7c7c7c7c7c7c7,0x64646464646464646464646464646),(0x0,0x0),(0x38f8f8f8f8f8f8f8f8f8f8f8f8f8f8,0x30b0b0b0b0b0b0b0b0b0b0b0b0b0b0)]
def mo331C : List ColumnInfo := [(1,0,330,0,5)]
def mo331A : List (List Nat) := [[],[16,134]]
def mo331D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo331L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo331D5)
  | _ => emptyPacking
def mo331I (_ _ : Nat) : Option (Nat × Nat) := none
def mo331 : Forest := ⟨1355,5,fun i => mo331Y[i]?.getD (0,0),mo331C,mo331A,mo331L,mo331I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331P5_0 : block mo331 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo331B5 : block mo331 5 0 1=true := mo331P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331T : checkedTables mo331 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo331 0 0 0 = true)
  · exact (rfl : block mo331 1 0 0 = true)
  · exact (rfl : block mo331 2 0 0 = true)
  · exact (rfl : block mo331 3 0 0 = true)
  · exact (rfl : block mo331 4 0 0 = true)
  · exact mo331B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo331G : graphValid mo331 (boundsBefore KM229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM331 : Lower false (varsX 331) (graphGoal 331) 6 := lower_forest (g:=mo331) (i:=0) (hints:=4294992006) (before_sound KM229 VM229) mo331G mo331T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM331 := extendKnown KM229 6 [(331,[]),(334,[16,32,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM331 : Known false KM331 := extend_ok (m:=331) VM229 lowM331 (by decide +kernel)
def mo333Y : Array (Bits × Bits) := #[(0x30303030303030303030303030303,0x296969696969696969696969696969),(0x0,0x0),(0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c,0x296969696969696969696969696969),(0x307070707070707070707070707070,0x212121212121212121212121212121),(0x0,0x0),(0x0,0x0),(0x1f9f9f9f9f9f9f9f9f9f9f9f9f9f9f,0x169696969696969696969696969696),(0x0,0x0),(0x20e0e0e0e0e0e0e0e0e0e0e0e0e0e0,0x84848484848484848484848484848)]
def mo333C : List ColumnInfo := [(1,0,332,0,5)]
def mo333A : List (List Nat) := [[],[131],[32],[32,131]]
def mo333D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo333L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo333D5)
  | _ => emptyPacking
def mo333I (_ _ : Nat) : Option (Nat × Nat) := none
def mo333 : Forest := ⟨1357,5,fun i => mo333Y[i]?.getD (0,0),mo333C,mo333A,mo333L,mo333I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333P5_0 : block mo333 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo333B5 : block mo333 5 0 1=true := mo333P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333T : checkedTables mo333 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo333 0 0 0 = true)
  · exact (rfl : block mo333 1 0 0 = true)
  · exact (rfl : block mo333 2 0 0 = true)
  · exact (rfl : block mo333 3 0 0 = true)
  · exact (rfl : block mo333 4 0 0 = true)
  · exact mo333B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo333G : graphValid mo333 (boundsBefore KM331) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM333 : Lower false (varsX 333) (graphGoal 333) 6 := lower_forest (g:=mo333) (i:=0) (hints:=12884928006) (before_sound KM331 VM331) mo333G mo333T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM333 := extendKnown KM331 6 [(333,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM333 : Known false KM333 := extend_ok (m:=333) VM331 lowM333 (by decide +kernel)
def mo361Y : Array (Bits × Bits) := #[(0x203f01f80fc07e03f01f80fc07e03f,0x251528a9454a2a51528a9454a2a515),(0x0,0x0),(0x0,0x0),(0x7c03e01f00f807c03e01f00f807c0,0x23531a98d4c6a63531a98d4c6a6353),(0x0,0x0),(0x200f007803c01e00f007803c01e00f,0x1aead756bab5d5aead756bab5d5aea),(0x18f0c7863c31e18f0c7863c31e18f0,0x8a045022811408a045022811408a0),(0x0,0x0),(0x1f00f807c03e01f00f807c03e01f00,0x140ca06503281940ca06503281940c)]
def mo361C : List ColumnInfo := [(1,32,328,0,4),(8,0,353,0,4),(256,0,105,0,4)]
def mo361A : List (List Nat) := [[],[131]]
def mo361D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x828190fd41fd31
def mo361D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1207f
def mo361H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb4002a
def mo361L : Nat → Packing
  | 5 => (2,1,2,0,0,4,0,mo361D5)
  | 6 => (1,0,2,0,0,0,0,mo361D6)
  | _ => emptyPacking
def mo361I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 1 1 mo361H6
  | _ => fun _ => none
def mo361 : Forest := ⟨1385,6,fun i => mo361Y[i]?.getD (0,0),mo361C,mo361A,mo361L,mo361I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361P5_0 : block mo361 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo361B5 : block mo361 5 0 2=true := mo361P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361P6_0 : block mo361 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo361B6 : block mo361 6 0 1=true := mo361P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361T : checkedTables mo361 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo361 0 0 0 = true)
  · exact (rfl : block mo361 1 0 0 = true)
  · exact (rfl : block mo361 2 0 0 = true)
  · exact (rfl : block mo361 3 0 0 = true)
  · exact (rfl : block mo361 4 0 0 = true)
  · exact mo361B5
  · exact mo361B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo361G : graphValid mo361 (boundsBefore KM333) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM361 : Lower false (varsX 361) (graphGoal 361) 7 := lower_forest (g:=mo361) (i:=0) (hints:=12884926469) (before_sound KM333 VM333) mo361G mo361T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM361 := extendKnown KM333 7 [(361,[]),(362,[16,134]),(460,[32,16,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM361 : Known false KM361 := extend_ok (m:=361) VM333 lowM361 (by decide +kernel)
def mo488Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x303303303303303303303303303303,0x115115115115115115115115115115),(0x0,0x0),(0xfc0fc0fc0fc0fc0fc0fc0fc0fc0fc,0x24d64d64d64d64d64d64d64d64d64d),(0x3c03c03c03c03c03c03c03c03c03,0x2a42a42a42a42a42a42a42a42a42a),(0xfc0fc0fc0fc0fc0fc0fc0fc0fc0fc,0x1b29b29b29b29b29b29b29b29b29b2),(0x300f00f00f00f00f00f00f00f00f00,0x2c0ac0ac0ac0ac0ac0ac0ac0ac0ac0)]
def mo488C : List ColumnInfo := [(0,32,328,128,5)]
def mo488A : List (List Nat) := [[],[134],[117],[117,134],[99],[99,131],[99,117],[99,117,131],[131,99],[131],[131,117,99],[131,117]]
def mo488D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def mo488L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo488D5)
  | _ => emptyPacking
def mo488I (_ _ : Nat) : Option (Nat × Nat) := none
def mo488 : Forest := ⟨1512,5,fun i => mo488Y[i]?.getD (0,0),mo488C,mo488A,mo488L,mo488I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488P5_0 : block mo488 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo488B5 : block mo488 5 0 1=true := mo488P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488T : checkedTables mo488 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo488 0 0 0 = true)
  · exact (rfl : block mo488 1 0 0 = true)
  · exact (rfl : block mo488 2 0 0 = true)
  · exact (rfl : block mo488 3 0 0 = true)
  · exact (rfl : block mo488 4 0 0 = true)
  · exact mo488B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo488G : graphValid mo488 (boundsBefore KM361) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM488 : Lower false (varsX 488) (graphGoal 488) 6 := lower_forest (g:=mo488) (i:=0) (hints:=14284775424) (before_sound KM361 VM361) mo488G mo488T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM488 := extendKnown KM361 6 [(488,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM488 : Known false KM488 := extend_ok (m:=488) VM361 lowM488 (by decide +kernel)
theorem lowM231 : Lower false (varsX 231) (graphGoal 231) 8 := lower_down lowS231
def KM231 := extendKnown KM488 8 [(231,[]),(237,[32,49,80,96,112]),(485,[32,129,80,49,67,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM231 : Known false KM231 := extend_ok (m:=231) VM488 lowM231 (by decide +kernel)
def mo238Y : Array (Bits × Bits) := #[(0x0,0x0),(0xe001c0038007000e001c0038007,0x1ec33d867b0cf619ec33d867b0cf61),(0x187030e061c0c38187030e061c0c38,0x2896512ca25944b2896512ca25944b),(0x7800f001e003c007800f001e003c0,0x3a96752cea59d4b3a96752cea59d4b),(0x0,0x0),(0x200fc01f803f007e00fc01f803f007,0x213cc27984f309e613cc27984f309e),(0x7f00fe01fc03f807f00fe01fc03f8,0x5698ad315a62b4c5698ad315a62b4),(0x3801f003e007c00f801f003e007c00,0x16412c825904b2096412c825904b20),(0x0,0x0)]
def mo238C : List ColumnInfo := [(0,2,204,32,5),(0,8,166,64,5),(2,0,236,0,5),(8,0,230,0,5)]
def mo238A : List (List Nat) := [[],[49,114,101]]
def mo238D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe413f
def mo238L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,mo238D6)
  | _ => emptyPacking
def mo238I (_ _ : Nat) : Option (Nat × Nat) := none
def mo238 : Forest := ⟨1262,6,fun i => mo238Y[i]?.getD (0,0),mo238C,mo238A,mo238L,mo238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238P6_0 : block mo238 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo238B6 : block mo238 6 0 1=true := mo238P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238T : checkedTables mo238 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo238 0 0 0 = true)
  · exact (rfl : block mo238 1 0 0 = true)
  · exact (rfl : block mo238 2 0 0 = true)
  · exact (rfl : block mo238 3 0 0 = true)
  · exact (rfl : block mo238 4 0 0 = true)
  · exact (rfl : block mo238 5 0 0 = true)
  · exact mo238B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo238G : graphValid mo238 (boundsBefore KM231) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM238 : Lower false (varsX 238) (graphGoal 238) 7 := lower_forest (g:=mo238) (i:=0) (hints:=571500112) (before_sound KM231 VM231) mo238G mo238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM238 := extendKnown KM231 7 [(238,[]),(249,[16,48,82,64,32,96,112]),(430,[33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM238 : Known false KM238 := extend_ok (m:=238) VM231 lowM238 (by decide +kernel)
theorem lowM243 : Lower false (varsX 243) (graphGoal 243) 7 := lower_down lowS243
def KM243 := extendKnown KM238 7 [(423,[16,50,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM243 : Known false KM243 := extend_ok (m:=243) VM238 lowM243 (by decide +kernel)
def mo250Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3060c183060c183060c183060c183,0x1dbb76eddbb76eddbb76eddbb76edd),(0x0,0x0),(0xc183060c183060c183060c183060c,0x274e9d3a74e9d3a74e9d3a74e9d3a7),(0x102040810204081020408102040810,0x3f7efdfbf7efdfbf7efdfbf7efdfbf),(0x23c78f1e3c78f1e3c78f1e3c78f1e3,0x224489122448912244891224489122),(0xc183060c183060c183060c183060c,0x18b162c58b162c58b162c58b162c58),(0x30e1c3870e1c3870e1c3870e1c3870,0x8102040810204081020408102040),(0x0,0x0)]
def mo250C : List ColumnInfo := [(0,8,178,64,5)]
def mo250A : List (List Nat) := [[],[99],[65,117],[65,99,117]]
def mo250D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo250L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,mo250D5)
  | _ => emptyPacking
def mo250I (_ _ : Nat) : Option (Nat × Nat) := none
def mo250 : Forest := ⟨1274,5,fun i => mo250Y[i]?.getD (0,0),mo250C,mo250A,mo250L,mo250I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo250P5_0 : block mo250 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo250B5 : block mo250 5 0 1=true := mo250P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo250T : checkedTables mo250 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo250 0 0 0 = true)
  · exact (rfl : block mo250 1 0 0 = true)
  · exact (rfl : block mo250 2 0 0 = true)
  · exact (rfl : block mo250 3 0 0 = true)
  · exact (rfl : block mo250 4 0 0 = true)
  · exact mo250B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo250G : graphValid mo250 (boundsBefore KM243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM250 : Lower false (varsX 250) (graphGoal 250) 6 := lower_forest (g:=mo250) (i:=0) (hints:=1125605456) (before_sound KM243 VM243) mo250G mo250T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM250 := extendKnown KM243 6 [(429,[16,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM250 : Known false KM250 := extend_ok (m:=250) VM243 lowM250 (by decide +kernel)
def mo335Y : Array (Bits × Bits) := #[(0x2030180c06030180c06030180c0603,0x2e974ba5d2e974ba5d2e974ba5d2e9),(0x6030180c06030180c06030180c060,0x3379bcde6f379bcde6f379bcde6f37),(0xc06030180c06030180c06030180c,0x2e974ba5d2e974ba5d2e974ba5d2e9),(0x90482412090482412090482412090,0x221108844221108844221108844221),(0x0,0x0),(0x0,0x0),(0x31f8fc7e3f1f8fc7e3f1f8fc7e3f1f,0x1168b45a2d168b45a2d168b45a2d16),(0x0,0x0),(0x1e0f0783c1e0f0783c1e0f0783c1e0,0xc86432190c86432190c86432190c8)]
def mo335C : List ColumnInfo := [(1,0,334,0,6)]
def mo335A : List (List Nat) := [[],[32]]
def mo335D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo335L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,mo335D6)
  | _ => emptyPacking
def mo335I (_ _ : Nat) : Option (Nat × Nat) := none
def mo335 : Forest := ⟨1359,6,fun i => mo335Y[i]?.getD (0,0),mo335C,mo335A,mo335L,mo335I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335P6_0 : block mo335 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo335B6 : block mo335 6 0 1=true := mo335P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335T : checkedTables mo335 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo335 0 0 0 = true)
  · exact (rfl : block mo335 1 0 0 = true)
  · exact (rfl : block mo335 2 0 0 = true)
  · exact (rfl : block mo335 3 0 0 = true)
  · exact (rfl : block mo335 4 0 0 = true)
  · exact (rfl : block mo335 5 0 0 = true)
  · exact mo335B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo335G : graphValid mo335 (boundsBefore KM250) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM335 : Lower false (varsX 335) (graphGoal 335) 7 := lower_forest (g:=mo335) (i:=0) (hints:=4294993542) (before_sound KM250 VM250) mo335G mo335T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM335 := extendKnown KM250 7 [(335,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM335 : Known false KM335 := extend_ok (m:=335) VM250 lowM335 (by decide +kernel)
def mo363Y : Array (Bits × Bits) := #[(0x38f0038f0038f0038f0038f0038f,0x2a2852a2852a2852a2852a2852a285),(0xe0700e0700e0700e0700e0700e070,0x69a1069a1069a1069a1069a1069a1),(0x0,0x0),(0x31c0031c0031c0031c0031c0031c00,0x124931249312493124931249312493),(0x0,0x0),(0x7f0007f0007f0007f0007f0007f,0x1145ad145ad145ad145ad145ad145a),(0x1f80c1f80c1f80c1f80c1f80c1f80,0x59604596045960459604596045960),(0x0,0x0),(0x3e000fe000fe000fe000fe000fe000,0x2820ca820ca820ca820ca820ca820c)]
def mo363C : List ColumnInfo := [(1,0,362,0,7),(2,0,361,0,7),(8,0,355,0,7),(0,32,328,3,6),(32,0,331,0,6),(64,0,299,0,5)]
def mo363A : List (List Nat) := [[],[16,134]]
def mo363D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30bb58854be58054
def mo363D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4398a16a60d45d03faa9fc54
def mo363H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a00880000000
def mo363D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def mo363H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f40000
def mo363L : Nat → Packing
  | 6 => (2,2,3,0,0,3,0,mo363D6)
  | 7 => (2,1,3,0,0,5,0,mo363D7)
  | 8 => (1,0,3,0,0,0,0,mo363D8)
  | _ => emptyPacking
def mo363I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 6 1 1 mo363H7
  | 8 => lookupWord 1 7 0 5 1 0 mo363H8
  | _ => fun _ => none
def mo363 : Forest := ⟨1387,8,fun i => mo363Y[i]?.getD (0,0),mo363C,mo363A,mo363L,mo363I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363P6_0 : block mo363 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo363B6 : block mo363 6 0 2=true := mo363P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363P7_0 : block mo363 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo363B7 : block mo363 7 0 2=true := mo363P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363P8_0 : block mo363 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo363B8 : block mo363 8 0 1=true := mo363P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363T : checkedTables mo363 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo363 0 0 0 = true)
  · exact (rfl : block mo363 1 0 0 = true)
  · exact (rfl : block mo363 2 0 0 = true)
  · exact (rfl : block mo363 3 0 0 = true)
  · exact (rfl : block mo363 4 0 0 = true)
  · exact (rfl : block mo363 5 0 0 = true)
  · exact mo363B6
  · exact mo363B7
  · exact mo363B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo363G : graphValid mo363 (boundsBefore KM335) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM363 : Lower false (varsX 363) (graphGoal 363) 9 := lower_forest (g:=mo363) (i:=0) (hints:=4294991957) (before_sound KM335 VM335) mo363G mo363T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM363 := extendKnown KM335 9 [(363,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM363 : Known false KM363 := extend_ok (m:=363) VM335 lowM363 (by decide +kernel)
def mo365Y : Array (Bits × Bits) := #[(0x1f01f01f01f01f01f01f01f01f01f,0x325325325325325325325325325325),(0x0,0x0),(0x60060060060060060060060060060,0x32fb2fb2fb2fb2fb2fb2fb2fb2fb2f),(0x380380380380380380380380380380,0x123123123123123123123123123123),(0x0,0x0),(0xf00f00f00f00f00f00f00f00f00f,0xdacdacdacdacdacdacdacdacdacda),(0xf0cf0cf0cf0cf0cf0cf0cf0cf0cf0,0xd04d04d04d04d04d04d04d04d04d0),(0x0,0x0),(0x300f00f00f00f00f00f00f00f00f00,0x20ca0ca0ca0ca0ca0ca0ca0ca0ca0c)]
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
def mo366Y : Array (Bits × Bits) := #[(0x0,0x0),(0x230f1878c3c61e30f1878c3c61e30f,0x21b50da86d436a1b50da86d436a1b5),(0x7003801c00e007003801c00e0070,0x3713b89dc4ee27713b89dc4ee27713),(0x48024012009004802401200900480,0x2113089844c226113089844c226113),(0x0,0x0),(0x200f007803c01e00f007803c01e00f,0x1e4af25792bc95e4af25792bc95e4a),(0x18f0c7863c31e18f0c7863c31e18f0,0x8ec47623b11d88ec47623b11d88ec),(0x0,0x0),(0x1f00f807c03e01f00f807c03e01f00,0x1600b005802c01600b005802c01600)]
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
def mo489Y : Array (Bits × Bits) := #[(0x1f001f001f001f001f001f001f001f,0xc290c290c290c290c290c290c290c),(0x0,0x0),(0x0,0x0),(0x203820382038203820382038203820,0x90949094909490949094909490949),(0x0,0x0),(0x707c707c707c707c707c707c707c7,0x3d4c3d4c3d4c3d4c3d4c3d4c3d4c3),(0x38c038c038c038c038c038c038c038,0x3042b042b042b042b042b042b042b0),(0x7c007c007c007c007c007c007c0,0x3c2b3c2b3c2b3c2b3c2b3c2b3c2b3c),(0xf800f800f800f800f800f800f800,0x6b406b406b406b406b406b406b406)]
def mo489C : List ColumnInfo := [(128,0,361,0,7)]
def mo489A : List (List Nat) := [[],[131]]
def mo489D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def mo489L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo489D7)
  | _ => emptyPacking
def mo489I (_ _ : Nat) : Option (Nat × Nat) := none
def mo489 : Forest := ⟨1513,7,fun i => mo489Y[i]?.getD (0,0),mo489C,mo489A,mo489L,mo489I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo489P7_0 : block mo489 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo489B7 : block mo489 7 0 1=true := mo489P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo489T : checkedTables mo489 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo489 0 0 0 = true)
  · exact (rfl : block mo489 1 0 0 = true)
  · exact (rfl : block mo489 2 0 0 = true)
  · exact (rfl : block mo489 3 0 0 = true)
  · exact (rfl : block mo489 4 0 0 = true)
  · exact (rfl : block mo489 5 0 0 = true)
  · exact (rfl : block mo489 6 0 0 = true)
  · exact mo489B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo489G : graphValid mo489 (boundsBefore KM486) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM489 : Lower false (varsX 489) (graphGoal 489) 8 := lower_forest (g:=mo489) (i:=0) (hints:=14227103749) (before_sound KM486 VM486) mo489G mo489T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM489 := extendKnown KM486 8 [(489,[]),(490,[16,134]),(492,[32,16,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM489 : Known false KM489 := extend_ok (m:=489) VM486 lowM489 (by decide +kernel)
def mo239Y : Array (Bits × Bits) := #[(0x6200c40188031006200c40188031,0x32246448c89191232246448c891912),(0x1c0038007000e001c0038007000e,0x3a6574cae995d32ba6574cae995d32),(0x31806300c6018c031806300c6018c0,0x128e251c4a38947128e251c4a38947),(0xe001c0038007000e001c003800700,0x32ae655ccab995732ae655ccab9957),(0x0,0x0),(0x1f803f007e00fc01f803f007e00f,0x59a8b35166a2cd459a8b35166a2cd),(0xfe01fc03f807f00fe01fc03f807f0,0xd519aa335466a8cd519aa335466a8),(0x3001e003c007800f001e003c007800,0x286150c2a185430a86150c2a185430),(0x0,0x0)]
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
theorem mo239G : graphValid mo239 (boundsBefore KM489) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM239 : Lower false (varsX 239) (graphGoal 239) 9 := lower_forest (g:=mo239) (i:=0) (hints:=536897109) (before_sound KM489 VM489) mo239G mo239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM239 := extendKnown KM489 9 [(239,[]),(253,[32,49,80,65,96,112]),(443,[16,66,134]),(446,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM239 : Known false KM239 := extend_ok (m:=239) VM489 lowM239 (by decide +kernel)
theorem lowM247 : Lower false (varsX 247) (graphGoal 247) 9 := lower_down lowS247
def KM247 := extendKnown KM239 9 [(247,[]),(375,[33,101,135]),(439,[16,66,134]),(471,[32,16,65,101,117,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM247 : Known false KM247 := extend_ok (m:=247) VM239 lowM247 (by decide +kernel)
def mo251Y : Array (Bits × Bits) := #[(0x30c018600c300618030c018600c3,0x18584c2c2616130b098584c2c26161),(0xf00078003c001e000f00078003c,0x3d7a5ebd2f5e97af4bd7a5ebd2f5e9),(0x0,0x0),(0x7c003e001f000f8007c003e001f00,0x18d9cc6ce636731b398d9cc6ce6367),(0x38001c000e000700038001c000e000,0xbc7e5e3f2f1f978fcbc7e5e3f2f1f),(0xfe007f003f801fc00fe007f003f,0x285a142d0a16850b4285a142d0a16),(0x7f003f801fc00fe007f003f801fc0,0x2726339319c98ce4c6726339319c98),(0x38003c001e000f00078003c001e000,0x34381a1c0d0e0687034381a1c0d0e0),(0x0,0x0)]
def mo251C : List ColumnInfo := [(2,0,249,0,7)]
def mo251A : List (List Nat) := [[]]
def mo251D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def mo251L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,mo251D7)
  | _ => emptyPacking
def mo251I (_ _ : Nat) : Option (Nat × Nat) := none
def mo251 : Forest := ⟨1275,7,fun i => mo251Y[i]?.getD (0,0),mo251C,mo251A,mo251L,mo251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251P7_0 : block mo251 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo251B7 : block mo251 7 0 1=true := mo251P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251T : checkedTables mo251 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo251 0 0 0 = true)
  · exact (rfl : block mo251 1 0 0 = true)
  · exact (rfl : block mo251 2 0 0 = true)
  · exact (rfl : block mo251 3 0 0 = true)
  · exact (rfl : block mo251 4 0 0 = true)
  · exact (rfl : block mo251 5 0 0 = true)
  · exact (rfl : block mo251 6 0 0 = true)
  · exact mo251B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo251G : graphValid mo251 (boundsBefore KM247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM251 : Lower false (varsX 251) (graphGoal 251) 8 := lower_forest (g:=mo251) (i:=0) (hints:=1074225237) (before_sound KM247 VM247) mo251G mo251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM251 := extendKnown KM247 8 [(431,[16,66,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM251 : Known false KM251 := extend_ok (m:=251) VM247 lowM251 (by decide +kernel)
def mo367Y : Array (Bits × Bits) := #[(0x8f0023c008f0023c008f0023c008f,0x10538414e10538414e10538414e105),(0x70181c06070181c06070181c06070,0x3a10ae842ba10ae842ba10ae842ba1),(0x30001c00070001c00070001c000700,0x11fb847ee11fb847ee11fb847ee11f),(0x260009800260009800260009800,0x1130844c21130844c21130844c2113),(0x0,0x0),(0x7f001fc007f001fc007f001fc007f,0x5ac516b145ac516b145ac516b145a),(0x380c7e031f80c7e031f80c7e031f80,0x2e047b811ee047b811ee047b811ee0),(0x0,0x0),(0xf8003e000f8003e000f8003e000,0xcb0032c00cb0032c00cb0032c00c)]
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
def KM367 := extendKnown KM251 10 [(367,[]),(379,[16,66,134]),(477,[32,65,117]),(478,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM367 : Known false KM367 := extend_ok (m:=367) VM251 lowM367 (by decide +kernel)
def mo381Y : Array (Bits × Bits) := #[(0x3f00fc03f00fc03f00fc03f00fc03f,0x153854e153854e153854e153854e15),(0x0,0x0),(0x3000c003000c003000c003000c0,0x1f7a7de9f7a7de9f7a7de9f7a7de9f),(0xc003000c003000c003000c00300,0x13104c413104c413104c413104c413),(0x7001c007001c007001c007001c00,0x3395ce57395ce57395ce57395ce573),(0xf003c00f003c00f003c00f003c00f,0x2ac7ab1eac7ab1eac7ab1eac7ab1ea),(0x3087c21f087c21f087c21f087c21f0,0x208582160858216085821608582160),(0x0,0x0),(0xf803e00f803e00f803e00f803e00,0xc6a31a8c6a31a8c6a31a8c6a31a8c)]
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
def KM381 := extendKnown KM367 9 [(381,[]),(382,[16,66,134]),(463,[32,65,117]),(475,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM381 : Known false KM381 := extend_ok (m:=381) VM367 lowM381 (by decide +kernel)
theorem lowM487 : Lower false (varsX 487) (graphGoal 487) 11 := lower_down lowS487
def KM487 := extendKnown KM381 11 [(487,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM487 : Known false KM487 := extend_ok (m:=487) VM381 lowM487 (by decide +kernel)
def mo491Y : Array (Bits × Bits) := #[(0x1c0063800c70018e0031c0063800c7,0x10b422168442d0885a110b42216844),(0x20301c060380c070180e0301c06038,0x14f0029e0053c00a78014f0029e0),(0x0,0x0),(0xc080181003020060400c08018100,0x24152482a49054920a924152482a49),(0x0,0x0),(0x3c0f1f81e3f03c7e078fc0f1f81e3f,0x2f4b0de961bd2c37a586f4b0de961b),(0x300e0601c0c03818070300e0601c0,0x102d8205b040b60816c102d8205b0),(0xf0001e0003c00078000f0001e00,0x10b4f2169e42d3c85a790b4f2169e4),(0x3f0007e000fc001f8003f0007e000,0x1ae8035d006ba00d7401ae8035d006)]
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
def mo493Y : Array (Bits × Bits) := #[(0x1fc000007f000001fc000007f,0x172d48c65cb5231972d48c65cb5231),(0x0,0x0),(0xfc600003f180000fc600003f180,0xd84ca2d361328b4d84ca2d361328b),(0x1f0038007c00e001f0038007c00e00,0x321ca8c0c872a30321ca8c0c872a3),(0x0,0x0),(0xf0007c03c001f00f0007c03c001f,0x28909639a24258e68909639a24258e),(0x20003f838000fe0e0003f838000fe0,0x205235108148d44205235108148d44),(0xffc00003ff00000ffc00003ff000,0x126b21c249ac870926b21c249ac870),(0x3f000003fc00000ff000003fc00000,0x1c8c00637230018dc8c00637230018)]
def mo493C : List ColumnInfo := [(1,0,492,0,8),(4,0,489,0,8),(8,0,485,0,8),(32,0,461,0,8),(128,0,365,0,8),(256,0,237,0,8),(0,32,332,129,7),(0,128,329,36,7),(33,0,460,0,7),(132,0,361,0,7),(264,0,229,0,7),(0,8,165,320,6),(0,256,165,72,6),(1,128,328,36,6),(4,32,328,129,6),(5,0,488,0,6),(32,128,329,4,6),(64,0,429,0,6),(160,0,333,0,6),(9,0,484,0,5),(64,8,165,256,5),(64,256,165,8,5),(129,0,332,0,5),(129,32,332,0,5)]
def mo493A : List (List Nat) := [[],[131],[32,117],[32,131,117]]
def mo493D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd183a307c29f32c3a2a09057c6447454120
def mo493D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x46a3000d968c00300470b00311c2c00ff6084f0f009fd811d120df87454120fe94254120ff141501108fd861d1209f5811d120
def mo493H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x103
def mo493D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9068a1c5410830e96196112825128280201001265021e945861c20e91285080c08b942870d025111600a281ca52213889ca089420c161c305080c110aa4c828215289c44116117d9d471da567d925f9634e9113a0cd2ac8912c29003fea9a85ff50d42ffa84a87fd72503fea1281ff5c540ffa82a07fd41483fea12217f1d132bfae8905fc74483f6a1241fe54120ff280905fd74442feb9221fe50110
def mo493H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa800089a030000400000000000020800000000
def mo493D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1aa248485910a883851c62e9a0a19090828e143a8725714daa92044cd2e92881aa2483c4fcd8ae8a66481e00ff54ffd43ff50bfd32ff543fd40ff483fd10
def mo493H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x95a24118000722c9017f0ea0c33653b8095d53fc0983b0af159488b211410005313137038380061a6080010cb94003478478a0a864576af4608f54411904
def mo493D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x52501ff
def mo493H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81000000000001e66c6e0000000c480000000010000a6004d8460000000000000000000000000cbd9005c800000000000002a000000088800000000000010410d1c000d00000000008
def mo493L : Nat → Packing
  | 6 => (2,4,5,0,0,4,0,mo493D6)
  | 7 => (6,3,5,0,0,7,0,mo493D7)
  | 8 => (18,2,5,0,0,10,0,mo493D8)
  | 9 => (8,1,5,0,0,8,0,mo493D9)
  | 10 => (1,0,5,0,0,0,0,mo493D10)
  | _ => emptyPacking
def mo493I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 5 1 0 mo493H7
  | 8 => lookupWord 1 23 0 7 3 0 mo493H8
  | 9 => lookupWord 9 41 5 11 5 2 mo493H9
  | 10 => lookupWord 4 67 2 9 3 2 mo493H10
  | _ => fun _ => none
def mo493 : Forest := ⟨1517,10,fun i => mo493Y[i]?.getD (0,0),mo493C,mo493A,mo493L,mo493I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P6_0 : block mo493 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B6 : block mo493 6 0 2=true := mo493P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P7_0 : block mo493 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P7_2 : block mo493 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B7 : block mo493 7 0 6=true := (@block_merge mo493 7 0 2 4 mo493P7_0 mo493P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P8_0 : block mo493 8 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P8_9 : block mo493 8 9 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B8 : block mo493 8 0 18=true := (@block_merge mo493 8 0 9 9 mo493P8_0 mo493P8_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P9_0 : block mo493 9 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B9 : block mo493 9 0 8=true := mo493P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493P10_0 : block mo493 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo493B10 : block mo493 10 0 1=true := mo493P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493T : checkedTables mo493 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo493 0 0 0 = true)
  · exact (rfl : block mo493 1 0 0 = true)
  · exact (rfl : block mo493 2 0 0 = true)
  · exact (rfl : block mo493 3 0 0 = true)
  · exact (rfl : block mo493 4 0 0 = true)
  · exact (rfl : block mo493 5 0 0 = true)
  · exact mo493B6
  · exact mo493B7
  · exact mo493B8
  · exact mo493B9
  · exact mo493B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo493G : graphValid mo493 (boundsBefore KM491) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM493 : Lower false (varsX 493) (graphGoal 493) 11 := lower_forest (g:=mo493) (i:=0) (hints:=13421798917) (before_sound KM491 VM491) mo493G mo493T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM493 := extendKnown KM491 11 [(493,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM493 : Known false KM493 := extend_ok (m:=493) VM491 lowM493 (by decide +kernel)
def mo494Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3f01e00003f01e00003f01e00003f,0x259446c6e259446c6e259446c6e259),(0x3c00001f87c00001f87c00001f87c0,0xe30aa098ce30aa098ce30aa098ce3),(0x1e00078001e00078001e0007800,0xcb06243a8cb06243a8cb06243a8cb),(0x0,0x0),(0x3f001e0003f001e0003f001e0003f,0x1a62a8291da62a8291da62a8291da6),(0x3c0e00007fc0e00007fc0e00007fc0,0x314604a45314604a45314604a45314),(0x1ff8000001ff8000001ff8000,0x218d55d66218d55d66218d55d66218),(0xffe000000ffe000000ffe000000,0x20999180420999180420999180420)]
def mo494C : List ColumnInfo := [(2,0,492,0,8),(4,0,490,0,8),(8,0,486,0,8),(32,0,462,0,8),(128,0,366,0,8),(0,32,332,130,7),(0,128,330,36,7),(34,0,460,0,7),(64,0,430,0,7),(132,0,362,0,7),(256,0,238,0,7),(0,2,204,288,6),(0,4,298,192,6),(0,8,166,320,6),(2,32,332,128,6),(2,128,328,36,6),(4,32,328,130,6),(6,0,488,0,6),(32,128,330,4,6),(128,32,332,2,6),(160,0,334,0,6),(10,0,484,0,5),(64,4,298,128,5),(64,8,166,256,5),(68,0,426,0,5),(72,0,422,0,5),(130,0,332,0,5),(256,2,204,32,5),(256,8,166,64,5),(264,0,230,0,5),(76,0,418,0,4),(266,0,228,0,4),(320,8,166,0,4)]
def mo494A : List (List Nat) := [[],[33,117,134]]
def mo494D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x21a0e2f21d6458540
def mo494D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18008000180042e083414080c2c0c3604178e5b3357909cc00ded731c964dec725c164bed8219153bf98019153fac8259140ebd64589409fc8758540ebd6458540ead6458942
def mo494H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb0
def mo494D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10900242050a020c31405420c20181434283086418241820864290014414050a0811b42800c642c2180b086e0d0868185831b1a0c660c2c30a42800c745c2028008581800454287031715086c4508584110b0b130f070108504030100420d181008042d1c50c0b06050403010020720821c0a170c100c04082c545801b0c201c6c34644071b1020100c042c50d0a04038201801b22006c285c4491c87171072081c6c4468249071b145e081c6c40c0a0403020b18302820121c2c601071b0c4c402b24203861b160dc90a08c71c5b0f085c2c2b24208d31a2b3664ec6186b025eeb916cad2586ae156a9650e9e134a5e4a693122a36456861069f63b6710d099630e5c0b095227e4a0828f21be3305a8a210e1b02e842046001ff5cd64ffae0b27fd6458ffeb22a7ff19153ffac8a1ffd6550bfeaa285ff58d42ffaa6a17fd4350bfeb22c1ff50960ffa82b07fd64543feb12a1ff50950ffac8a07fd62503fea1281ff58540ffa82a07fd61483fea0a41ff59110ffa84887ec72592feb90c97f5c064bfaeca17bd6450bf6b12857f5d940f7ac8a07f960503fca82817f5d920bfae8907ed62483f690a41fe58120ff2a0907f940482feba2217f5c910ff280885dd73192f6b90c97e5c064
def mo494H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4bb238400c9800000000760000000001c60000000000000000400000002c20000002c80000000014682a5400000000000005a0000000000000000000000000000000147000012
def mo494D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30505263a018d860a58bc9151c4122844425083901c508841c48518508884a1072038a0c141498e80f1028444241d0101c402163e49f0e39b14221090e187150879b921c6142010f928038e5a1090e44595a11769aa5cd353f8c7240600a400ff593fc64ff58ffd53ff50ffd42ff4cbfd60ff543fd40ff483fd10
def mo494H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc24006b0d5c29400381e3ae7c000000004b4d17170011ab87a928a800000670001a100002315e00000000d1016c00000637e1db2800ca0fa5603980009160018600076570b1cd43e5b6f4cfcced7ed64da7940004f791328002a1000000003d580064c001c725291aeabb15cc00035ec98000d6a15886295dcaa0001c300000237e0b000001c1520d320000000000180c0a800d35293854a7e180022a9184d000001c4c020249
def mo494D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x448e1ff
def mo494H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1650000001d60065400007245c014754c2245b900003a28bd00035400d90528d210000000a3007cc018
def mo494L : Nat → Packing
  | 6 => (1,4,6,0,0,0,0,mo494D6)
  | 7 => (9,3,6,0,0,7,0,mo494D7)
  | 8 => (49,2,6,0,0,11,0,mo494D8)
  | 9 => (12,1,6,0,0,10,0,mo494D9)
  | 10 => (1,0,6,0,0,0,0,mo494D10)
  | _ => emptyPacking
def mo494I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 mo494H7
  | 8 => lookupWord 3 71 2 9 4 1 mo494H8
  | 9 => lookupWord 18 113 5 11 6 1 mo494H9
  | 10 => lookupWord 5 37 1 9 4 1 mo494H10
  | _ => fun _ => none
def mo494 : Forest := ⟨1518,10,fun i => mo494Y[i]?.getD (0,0),mo494C,mo494A,mo494L,mo494I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P6_0 : block mo494 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B6 : block mo494 6 0 1=true := mo494P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P7_0 : block mo494 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P7_1 : block mo494 7 1 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B7 : block mo494 7 0 9=true := (@block_merge mo494 7 0 1 8 mo494P7_0 mo494P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_0 : block mo494 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_3 : block mo494 8 3 20=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P8_23 : block mo494 8 23 26=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B8 : block mo494 8 0 49=true := (@block_merge mo494 8 0 3 46 mo494P8_0 (@block_merge mo494 8 3 20 26 mo494P8_3 mo494P8_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P9_0 : block mo494 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B9 : block mo494 9 0 12=true := mo494P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494P10_0 : block mo494 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo494B10 : block mo494 10 0 1=true := mo494P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494T : checkedTables mo494 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo494 0 0 0 = true)
  · exact (rfl : block mo494 1 0 0 = true)
  · exact (rfl : block mo494 2 0 0 = true)
  · exact (rfl : block mo494 3 0 0 = true)
  · exact (rfl : block mo494 4 0 0 = true)
  · exact (rfl : block mo494 5 0 0 = true)
  · exact mo494B6
  · exact mo494B7
  · exact mo494B8
  · exact mo494B9
  · exact mo494B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo494G : graphValid mo494 (boundsBefore KM493) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem lowM494 : Lower false (varsX 494) (graphGoal 494) 11 := lower_forest (g:=mo494) (i:=0) (hints:=4866467408) (before_sound KM493 VM493) mo494G mo494T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM494 := extendKnown KM493 11 [(494,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM494 : Known false KM494 := extend_ok (m:=494) VM493 lowM494 (by decide +kernel)
def mo255Y : Array (Bits × Bits) := #[(0x630018c00630018c00630018c0063,0x22138884e22138884e22138884e221),(0x1c00070001c00070001c00070001c,0x2717d9c5f6717d9c5f6717d9c5f671),(0x180086002180086002180086002180,0x28710a1c428710a1c428710a1c4287),(0x200078001e00078001e00078001e00,0x2a738a9ce2a738a9ce2a738a9ce2a7),(0x70001c00070001c00070001c000,0x38f93e3e4f8f93e3e4f8f93e3e4f8f),(0x1f8007e001f8007e001f8007e001f,0x18e8263a098e8263a098e8263a098e),(0x3e007f801fe007f801fe007f801fe0,0x158c75631d58c75631d58c75631d58),(0xf8003e000f8003e000f8003e000,0x706c1c1b0706c1c1b0706c1c1b070),(0x0,0x0)]
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
def mo383Y : Array (Bits × Bits) := #[(0x8f0008f0008f0008f0008f0008f,0x1e1051e1051e1051e1051e1051e105),(0x20700207002070020700207002070,0x8ba108ba108ba108ba108ba108ba1),(0x7000070000700007000070000700,0x3e11fbe11fbe11fbe11fbe11fbe11f),(0x58000580005800058000580005800,0x81130811308113081130811308113),(0x380003800038000380003800038000,0x9ff349ff349ff349ff349ff349ff3),(0x7f0007f0007f0007f0007f0007f,0x2145ae145ae145ae145ae145ae145a),(0x1f80c1f80c1f80c1f80c1f80c1f80,0x1ee041ee041ee041ee041ee041ee0),(0x0,0x0),(0x3e000fe000fe000fe000fe000fe000,0x3600cb600cb600cb600cb600cb600c)]
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
def mo495Y : Array (Bits × Bits) := #[(0x7c3c0000000f8780000001f0f,0x30ad0645a2a615a0c8b454c2b41916),(0x2000003c003c0000078007800000f0,0x241f1164888c83e22c9111907c4592),(0xfc380000001f8700000003f0e000,0x2964624f51552c8c49ea2aa591893d),(0x3c00003c00078000078000f0000,0x210d404cc0c421a809981884350133),(0x0,0x0),(0x1f00003fc003e00007f8007c0000ff,0xb40e89a5551681d134aaa2d03a269),(0x3ffc03c00007ff80780000fff00,0x61299b00c08c253360181184a66c0),(0x1ffc00000003ff800000007ff00000,0x149b1520aaaa9362a41555526c5482),(0x200000003ffc00000007ff80000000,0x18e0260333331c04c066666380980c)]
def mo495C : List ColumnInfo := [(1,0,494,0,11),(2,0,493,0,11),(8,0,487,0,11),(4,0,491,0,10),(128,0,367,0,10),(32,0,463,0,9),(132,0,363,0,9),(256,0,239,0,9),(0,32,332,131,8),(0,128,331,36,8),(6,0,489,0,8),(64,0,431,0,8),(130,0,365,0,8),(258,0,237,0,8),(264,0,231,0,8),(4,32,328,131,7),(32,128,331,4,7),(65,0,430,0,7),(72,0,423,0,7),(128,32,332,3,7),(160,0,335,0,7),(36,128,331,0,6)]
def mo495A : List (List Nat) := [[]]
def mo495D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18c14bd6d8a4644855ca9ead9948c890ab953f1b02919121572
def mo495D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x640403203430518080c40588080c50586c00886c00a860b0d80130c8016101c20384070808001349415881710201881b10200000003881b082000000e2040000000c1838307060e0c1c182c30749a10b48a10b49a1080e0e1c1c3838707420a281d082280404090c1c1838307060e0c1c182070404382c46004c46004c46004c4058840098bc40b060a0c1c18383070fc40b0fc40b0fc409880a0c115e18215e18215e182a634ae92d16a21406794e39bb33a5fcb995524a3d46b8a70ee1641d81cffdfcbf37b6f31debb7750e65c9b8d70ee05bdb6c6bad5da8b4b68acd99832a648c798c3095f4bad6e2cd57ca99472764ce96124a3a456871069fe3de780e89c2366690ca9863005c4ac941252468810ea1b63305e8ae12c1f8330570900c00c000cfd69d9121576cfd6919121576ebb2999460875cfb6599460875afb6989460875cfe6599460075dbb699921d5659fd684955d974cfb6a1921d564cfb2a1921d564deb691921d564cfe6a1901d564dbe699901d564cf7619931d554cfb619921d554deb691921d554cfd619911d554cfe619901d554bd768c7559554bdb6887559554bdd6847559554bde6807559554cfd69d9121572cfd6919121572cfd2919121572cbf6598521572cef6159421572daf6599421572cf76159321572df36899321572db76599321572de76519321572dbb6599221572deb6519221572df364d9221572cfd6159121572df96899121572dbd6599121572ded6519121572df564d9121572df96499121572cfe6159021572dbe6599021572dee6519021572df664d9021572dfa6499021572dfc6459021572b3f698855d572b6f690855d572b7768c855d572b7d684855d572b7e680855d572b7b688945d572af768c8561172afd6848561172afe68085611729fb6899521172af768c8521172afd6848521172afe6808521172af768c855d172afd684855d172afe680855d172cfb68898551728ff6959815172d7b5d59215172bbb698955c952beb690955c952bf368c955c952bf9684955c952bfa680955c952afb2a1945c952cfb260845c952b7b69c545c952cf7615931d542cfb615921d542cfd615911d542cfe6a1901d542cfe615901d542dfa689901d542be768c7555142beb6887555142bed6847555142bee6807555142bf368c955c942bf9684955c942bfa680955c942e7b615755c942f6b5d5545c9429f368c955c9429f9684955c9429fa680955c942
def mo495H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe80d00000000009
def mo495D9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xc70be2e0c6171f8b8447185a8353429754a4a3b51a28b5444a1750027b53b49d74e226f53549974c025b52bc94b49e24c525c92748c243520c8f747823a51c48db46a232516c8af45022250e486342e214507c8334122024fe47e73ee1f64fa47cb3dc1ec4f3478f3c41e04eec7733b01d74eac74339e1cd4e5c72338e1c44e046fb3761ba4dbc6cf3641ad4d5c69734019b4cbc64f31e18a4c2c5ff2f41734b6c59b2c01594a9c53328e14049d44cf25812548ec45722010a48243fb1f40f447743a31c40db46a433f1940c546042ef1660ac4524277130091445c2130fc07743841a70c805e42b414309404441f40df06402c412c07b030011405c0170003feb2242aedbfd8661175bfecb108badff648845d77fb08c12ebbfc8460975dfeca3043aeff251821d7dfaecbaacb7fc955d974dfebb10aba77f5d9755d37fb24c28e9bfd985d564dfe4c2eab26ff61d755937fb0ebaaa9bfd865d554dfec30eaaa5ff64875553efaeab2aa9f7c7559554fdebaae8aa6ff649871537fb0eba8a9bfd865d454dfebab042a7bf658855cb7fb0a42ae5fbd9421572feec990ab97fb648855cbfeb2242ae5ff99021572efe42aeab977f651755cbbf928baae57fc9561172dfec2b08b96ff215845cbbfaeac22e57fd9521172dfec2908b96ff214845cbbfaea422e57fc955d172dfe42ae8b977f5d5745caff930aa2e5dfd7555172bfecc0a8b95ff65c545cbbfaea2a2e5bfd9461d52dfe4a30ea96ff61d8454b7f90ec22a57fd9721152dfec3908a96ff21c8454aff930ba2a5bfd875d152bfecc0e8a95ff6547454b7fb0eaa2a57fd9715152dfec38a8a97fb2617254bfdb2ab92a5fec955c952ff6baae4a97fb6517254bfd928b92a5fed845c952ff6422e4a97fb5d17254bfdaa8b92a5fec545c952dfecc2eaa16ff2617550b7fb0ebaa85bfd855d542dfec28eaa17ef5d55450bf78eaaa285fed955c942ff64aae4a17fb5d57250afeb2242aedbed9660875df6ca3043aefb251821d77f32cc00ebbf99460075dfcc93003adfe64087596f7b283aacb7dd931d565bf6c90eab2dfd64475596ff3203aacb3fd92215749fe4c2caba6fb655821d27fb2e42ac97dd931d564bf6c90eab25fd64475592ff3203aac97ed9221d549fe4c2ecaa5bf65875552fbb263aaa97ed921d554bfac88eaaa5fe64075552dfb2c42ae57bd9421572beec990ab95fd644855caff32042ae53fc98551729fecc0a8b957f65c545cafdb242a2e56fd961d552bdeca0eaa95f764c7554afeb223aaa57f9901d5529fe4c2e8a94ff6607454afdb243a2a57ec985c952ef6baae4a94ff65c8550afbb263aa857ed921d542bfac88eaa15fe6407550afd92ab9285bed855c942ef6baae4a17eb5517250a7eb2242aed2fd96215729deca10ab94f764c855ca7eb2242ae53f99021572 else 0x89058e898a8681906e2640b898c2a2626160a31688164041c8c207a208201e13049050907458512151092884010d0503884e2042c2289044a242414010201d0e89005090843401300210c34584246210a5221030762080a205109288362230b0c18783620f0c1c3050c1c3070c107830985830f884c3043c2c5430825a462a114211e9284545a4a1150c3c187620a1d1c403c40743081e1494310080783a14318960d0d8a8450f07090e802030c14305918583884e2042096918a805a4a0083c162043c1420020150a844030c1080542a0111c142049c127620a0c107620a1d9184387049d91803001d8428783600e1c1444140e2138810b0844a24114201d128900515084440120d0d8831508830e1d171188487c415481217100d884e261e0c69015978b87809858b6487e2e1e01b8b87808d94565e187e2116619918e1f88478466587e2e166111b8b85831a4052713e2e1e0c61b178780bb185c527e2e1e0461b178b80b7185c52711e2e1c618201c578b87819870705e2e1e0a61a15921f86438b807070508e1e2e0c61c2f1b8780b850b27e2e1e0142f8b1b80b451127e2c6e1178b87824c4e2e1e0a610149f8b8457805c4c3e12ee017110c9f8b87806c4c327e261e01b130c9f8b84446e0e2e11513803f8b8718562e0e1c61187838b18460e2e1c6102c1c171b8b87803c80825e0c6e2e1182c1c97838b871870be0e2e125461b849f8b805450f27e1e2e0c61b17871b80b85c52761e2e0c61b149f84478b1860705e2e1e0c6181c97871b8b80625e146e2e027189f878b8218507e0e186e21420142f8b87831870be1e02ec6142f8b87809d1860be2e02dc614449f8b8718510e2e1e0862b1b8b801d2218507e0e1e28614af8b87821920690c70be2e0c6182f0f8b87804060b08e2e1e0c61b1f87804b185)
def mo495H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x298000000007d500147a680000000000000000000000000572000001c45780000074900093c0000033200000000000000000007a56125200000000000343000614000000006f400000000000c5000000000c980000000000000000000000008a90540000057cace840000000002080056a000000008b00000000000000065c2fc4c000000000000000030700000000000001250db7420000000000000000000000000003ec80000000000597000000000000000000000000000193800141438000000000000000000000287c0b3650b4006250000021b800000000003060000000072b001248298000000000021a0000000018cbb600000047000002cb423b9bc6c000004000011162c00000000000001b5ac18000016d19f94a000000000000000000000000000000000000000000000000000000000000000000000000000a8000000000004b40001d41d000841c10000000000000000000110800000000000000000000058d138ce00064c000000ebf3b00000000000a91d00a280000000027000000000000000008ab288000000000059f00031800000000001c0800000000000000000000050935c00000000000000d8000000000000000000000000000000000000000000000000000000000092200000000000000588000008a48e44180400e
def mo495D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc587046202904b830a6c431317152e0c38931097263c38310c403e4c787025c4425c38136217161c09e310189878a970e0c518826262e2c382327203e2c09b090263870a3f160c24c7202c3c4490d1880b8316130587c5830a626408161ca08c38236220589c4230e08c9c80a3f161c09c98e2c3e24d870102641088921a30e202e1c580b2112188c587027223a726430e2c098820911e1c11710e3d2e0c31b10c3c3a5c18b0c61c78b8a943e0c38a31383146c23c50f831618c946c18a3611e28b0f8a361c03c717831618c9461e9d2e18d8310e3f0e2c11938c3c3c54b870628c40f8b871608c9c74f87146c03c64b871608c28b0f8a361c03c74b871608c9c68e9f1618d8078f1f0e2c11928c2c39511870628c4151623161c11939022387c58700b8c407c5870262030b0e4f161c03c71620287c587026213e1c18a31019387c587006203e2c381313203090f14288cd8b0e01650b0e17161c02531040385cd8b0e01c3e2c380a8a2d3e2c1844461c445c58700b8c3a7278b0e01e307c5870084c362c381313203270e3f161c04c70e2c805cd8b0e0205870b8b0e012988160f161c0546111c3e2c3805c623061c518410153e1c18a30e1d3e1c18830c2d3e0c5844461c3e1c58044618445c58700b8c3e2c38044615387901b062c2548161f161c054616203e6c58700e2f361c038517903e2c3806179b1601a2910f9b161142e40f8b0e02a3c071fd8fae7bf3d01e2eee7754b9adc68dfd6d1b595a4ece965931d1842be35d2adb967cb075612a654d2a40504a76534497249a23f519a8a4436a0f500c7d63cc1d68e386ec35a99dcc8e6102f01650aac51f27b12fc9104582140fe07823831a28c545ae2b513f093842e1e70d8061c29211907102e411206001b8003ff21576ffd865d7ff5d975ffd845d7ff21175ffd825d7ff21d65ffd75597ff1d565ffd765d3ff21574ffd755d3ff59574ffd75593ff1d564ffc87553ff5d954ffd75553ff1d554ffd65553ff5d454ffd855cbff21572ffd755cbff61172ffc845cbff5d172ffd545cbff15172ffd8754bff21d52ffd7554bff1d552ffd8454bff21152ffd7454bff1d152ffd5454bff15152ffd7550bff1d542bfc855daff61875bfd841d6ff60875bfd87597bf5d965dfd765d2ff21574bfd861d2ff61474bfd821d2ff61d64bfc85592ff61d54bfd86553df59554fbd74552ff61c54bfd86152ff60854bfc855cb7f5d572bfd8754bfb5c952bfd8750aff61542bfc8550bef55142fed7250abf61875bbd841d6f760c75bed821d6fd60475bf9801d6fb60874
def mo495H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x69fa49000611b84f412865b3da7c4492268a9841022c6a400bc7ae410fc7ec400000074734a90780079474633f800637000000517281d904850000001b000032d98cf0299913daa6800220bc391669efb10005b63c2715e2b80030d0004858007a8b9c80000072480032f2bbca579333f000000543734e9280028dc9780000c5b1d1dc9219e114c8964a43570a00050800000070b0002a439f00012840b81b49d0293b243e78ef03d27496c409331bb338b3aab5e9100071aa1a000019fa1a075c54835230000004be8001b6b22c210ad6c80004ac00f5b9ac2f30f8fd00c3413972a823dab5a0000000115093aba0004813a58000000c58aedaf93ca188000006183a611c2a9e1b9acc8020e73d688e2a5329c1d37c384c88007c9d06f8980000080d080418a18104820321980483c2870c3818c0a3c407022420b0208000
def mo495D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c54208a11871479a182218b9a28601c61c54228601871c52268a08474079a28601471d42228601871c52268a18072d09a28601471478228461871618a01861d5222860187fc73b4974a2451c8b4421686000ffaedff5d7fe3affd65ffae9ff1d3feb27fd54ff8a9ff5cbfea97fd42
def mo495H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x121ddc62cb3ad0f0fd01f31e23180064204d804dc2201a4ea5784b324841e000048278005c112f922e348ef2ce881580019200352e3d00191eca30cb1fa705bd1b0012cc0043a368aec00000523ab8000003340010564c000afc00000372c5698800a06002601a0e51437d38b20010f84158b652000536c5954000227cb46acbf91f05f252b5b12d1821d44401ad0853010c155d
def mo495D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc20804ff
def mo495H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb4aa00290000e1008b0800435590020627081
def mo495L : Nat → Packing
  | 7 => (3,5,5,0,0,4,0,mo495D7)
  | 8 => (92,4,5,0,0,11,0,mo495D8)
  | 9 => (150,3,5,0,0,13,0,mo495D9)
  | 10 => (77,2,5,0,0,13,0,mo495D10)
  | 11 => (12,1,5,0,0,9,0,mo495D11)
  | 12 => (1,0,5,0,0,0,0,mo495D12)
  | _ => emptyPacking
def mo495I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 11 0 6 2 0 mo495H8
  | 9 => lookupWord 23 347 2 11 7 0 mo495H9
  | 10 => lookupWord 37 191 7 12 8 0 mo495H10
  | 11 => lookupWord 19 97 6 11 7 0 mo495H11
  | 12 => lookupWord 3 17 4 8 4 0 mo495H12
  | _ => fun _ => none
def mo495 : Forest := ⟨1519,12,fun i => mo495Y[i]?.getD (0,0),mo495C,mo495A,mo495L,mo495I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P7_0 : block mo495 7 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B7 : block mo495 7 0 3=true := mo495P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P8_0 : block mo495 8 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P8_3 : block mo495 8 3 89=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B8 : block mo495 8 0 92=true := (@block_merge mo495 8 0 3 89 mo495P8_0 mo495P8_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_0 : block mo495 9 0 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_6 : block mo495 9 6 56=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P9_62 : block mo495 9 62 88=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B9 : block mo495 9 0 150=true := (@block_merge mo495 9 0 6 144 mo495P9_0 (@block_merge mo495 9 6 56 88 mo495P9_6 mo495P9_62))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_0 : block mo495 10 0 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_7 : block mo495 10 7 29=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P10_36 : block mo495 10 36 41=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B10 : block mo495 10 0 77=true := (@block_merge mo495 10 0 7 70 mo495P10_0 (@block_merge mo495 10 7 29 41 mo495P10_7 mo495P10_36))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P11_0 : block mo495 11 0 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B11 : block mo495 11 0 12=true := mo495P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495P12_0 : block mo495 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo495B12 : block mo495 12 0 1=true := mo495P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo495T : checkedTables mo495 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo495 0 0 0 = true)
  · exact (rfl : block mo495 1 0 0 = true)
  · exact (rfl : block mo495 2 0 0 = true)
  · exact (rfl : block mo495 3 0 0 = true)
  · exact (rfl : block mo495 4 0 0 = true)
  · exact (rfl : block mo495 5 0 0 = true)
  · exact (rfl : block mo495 6 0 0 = true)
  · exact mo495B7
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
theorem lowM495 : Lower false (varsX 495) (graphGoal 495) 13 := lower_forest (g:=mo495) (i:=0) (hints:=4831864405) (before_sound KM383 VM383) mo495G mo495T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def KM495 := extendKnown KM383 13 [(495,[]),(507,[16,66,134]),(509,[32,65,117]),(510,[64,33,117,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM495 : Known false KM495 := extend_ok (m:=495) VM383 lowM495 (by decide +kernel)
theorem lowM503 : Lower false (varsX 503) (graphGoal 503) 13 := lower_down lowS503
def KM503 := extendKnown KM495 13 [(503,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem VM503 : Known false KM503 := extend_ok (m:=503) VM495 lowM503 (by decide +kernel)
def mo511Y : Array (Bits × Bits) := #[(0x7c0000000001e0f80000000003c1f,0xda2ad314d48121b455a629a902436),(0x380001e0000001f00003c0000003e0,0x28880464d8d8ab511008c9b1b156a2),(0x7e1e0000000000fc3c000,0x1b519aa80b230236a335501646046d),(0x3e00001e0000007c00003c0000,0x18c00620486a0231800c4090d40463),(0x3c001f8000000078003f0000000,0x38444222382666f0888444704ccde1),(0x3fc0001e000001ff80003c000003ff,0x1255528a222744a4aaa514444e8949),(0x3c0000001ffe00780000003ffc00,0x200c4046b094edc018808d6129db80),(0x1fffe0000000003fffc00000,0x4aa2555c4d89909544aab89b13212),(0x3fffe0000000007fffc000000000,0x733b9990701100e6773320e02201c)]
def mo511C : List ColumnInfo := [(1,0,510,0,13),(2,0,509,0,13),(4,0,507,0,13),(8,0,503,0,13),(16,0,495,0,13),(32,0,479,0,11),(128,0,383,0,11),(33,0,478,0,10),(34,0,477,0,10),(64,0,447,0,10),(132,0,379,0,10),(144,0,367,0,10),(256,0,255,0,10),(36,0,475,0,9),(40,0,471,0,9),(48,0,463,0,9),(65,0,446,0,9),(68,0,443,0,9),(72,0,439,0,9),(129,0,382,0,9),(130,0,381,0,9),(136,0,375,0,9),(258,0,253,0,9),(264,0,247,0,9),(272,0,239,0,9)]
def mo511A : List (List Nat) := [[],[16,66,134],[32,65,117],[64,33,117,134]]
def mo511D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xaa479848c180a1e3790b770cb66889859687a9e42ddc02d9a226165c16b75dd4329b226176597074dd574cca6c8985d965c1e3751d3329b2261765970765d5744ca6c8985d965c1da755d0329b22617659707a9d4740ca6c8985d965
def mo511D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xcc408110408820000011040883b88191a0ee20646820000000385040000c15f2ed70b5592bd58a95328d409d4d25d28914722d1085411fcf8793b1b6ca5cacd5aa74b214e863291047635178a446120601801b45dc670cba65d9521b62f390e0174cbb2a436d1e719c02e99765486da9ce23805d32eca90db559c3700ba65d9521b6ad384e0174cbb2a436d5c705c02e99765486e3ccda366d8352430ebc7c9b36c9b06a4861d78fa366d8b60d490c3af1f86c9b16c1a921875d396e2384d4b4a430eba74dc3709a9694861d74e7388e0352d290c3ae9d670dc06a5a521875d3b4e1380d4b4a430eba771c1701a9694861d74f3388e0352d190c3ae9f2709c06a5a321875d3e8e0b80d4b46430eba799c470da9680861d74f5388e1352d010c3ae9f270dc26a5a021875d3d8e2382d4b40430eba7d1c3705a9680861d74fc384e0b52d010c3ad1eb750b72d9a226165c3e65bb865b3444c2cb87e8b7700b6688985964fd1b2e016ed1130b2e9d9715c2261a125d65ce36e3b8ad9130bb2cb85edd7329b2261765970edbaa653644c2ecb2e1eb750ca6c8985d965c3e6e9994d9130bb2cb87e5d1329b2261765970fd3a0653644c2ecb2d1eb750ca6c8985d965a3e6e9994d9130bb2cb47e5d1329b2261765968fd3a0653644c2ecb2e1dd328a96c49761565cd3ae438cd892ec2acbb83d87710a65d98559770bb0ee190cbb30ab2ee1e61dc02197661565
def mo511H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f300008802d421046b
def mo511D9 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0xa7f9c02dca961565c7f5a96c49761565c7f4a96c49761565ae7cca6d57661565f87d876d57661565c7edca6c8985d565c7ecca6c8985d565d76dc56c8985d56587fcca2e5875d565a7edc2261a65d56587fdcb6a5865d565f87d875d9855d565c7f9a66c0a766065c7f9a86c0a865c65c7f9a66c0a865c65b5f9c02e19761c65c7f9c96c0a85d865a7f9c02a1975d865b7b9c02dda865065b7b9c02e1a765065b5bdc669d8765065c7bcba6d98765065d7b9ca6c08765065d7b9c66c08765065b7b9c021d866506597bdca2e17665065b7b9c02e1766506597bdcb6a1766506597bccb6a17665065e5bcca61d7665065f1bda861d7665065b55dc32e99765486b579c02e99765486b55dc32d59765486b56dc22d59765486b579c02d59765486b74dc22dd9564c86b759c02dd9564c86b5b9c42d59764086b5d9c32d59764086b5e9c22d59764086b5f1c12d59764086b739c42dd9564086b759c32dd9564086b769c22dd9564086b771c12dd9564086d65db56cca865875d4f5b76c4a865875d675b56c4a865875d6b5b46c4a865875d6d5b36c4a865875d4f9b76c0a865875d679b56c0a865875d6b9b46c0a865875d6d9b36c0a865875d6e9b26c0a865875d6f1b16c0a865875c7b9b46c1a921875c7d9b36c1a921875c7e9b26c1a921875c7f1b16c1a921875e47da7659a521875e65d96695a321875e1f99869da021875e4f9a7659a021875e37998695a021875e67996695a021875e6b996691a021875e3d99868da021875e6d99668da021875e3e998689a021875e6e996689a021875e6f196685a021875975dc52e1a664c7597d5c12e1a664c7597d9c02e1a664c7587dccb6a1a664c75e2dda86998664c75c75dba6d48664c75d55db76d48664c75c7d9ba6c08664c75d5d9b76c08664c75d759b56c08664c75d799b46c08664c75d7c9b26c08664c75d7d1b16c08664c75c5f9ba6dc8664075c779ba6d48664075d579b76d48664075c7b9ba6d08664075d5b9b76d08664075d739b56d08664075c7d9ba6cc8664075d5d9b76cc8664075d759b56cc8664075d799b46cc8664075c7e9ba6c88664075d5e9b76c88664075d769b56c88664075d7a9b46c88664075d7c9b36c88664075c7f1ba6c48664075d5f1b76c48664075d771b56c48664075d7b1b46c48664075d7d1b36c48664075d7e1b26c48664075a6edc62dda226165a76dc52dda226165a7adc42dda226165a7cdc32dda226165a7e5c12dda226165a7e9c02dda226165a5edc72d9a226165a76dc52d9a226165a7adc42d9a226165a7cdc32d9a226165a7e5c12d9a226165a7e9c02d9a226165a7e5c2261a125d65a5f5c12e5a72196587ecca6c8985d965a75dc32dca961565a76dc22dca961565a779c02dca961565c774a96c4976156597b9c02e1a76506597b9c02e17665065 else 0xb75dc52e1a664c75b7d5c12e1a664c75b7d9c02e1a664c75e3dda86998664c75c7ddba6988664c75c7ddba6188664c75d75da66d48664c75d75d866d48664c75d75dba6d48664c75d7d9ca6c08664c75d7d9a86c08664c75d7d9a66c08664c75d7d9866c08664c75d7d9ba6c08664c75c7f9ba6188664075d5f9b76188664075d779866d48664075d7b9866d08664075d7d9866cc8664075d7e9866c88664075d7f1866c48664075a7f5c12d9a726165a7edc62dda226165a7edc52dda226165a7edc72d9a226165c7ecb72d9a226165a7edc52d9a226165c7edb76d5a226165a77dc969da526165a7edc96dda226165a7ecc96dda226165aeedc62dda226165af6dc52dda226165afadc42dda226165afcdc32dda226165afe5c12dda226165afe9c02dda226165adedc72d9a226165af6dc52d9a226165afadc42d9a226165afcdc32d9a226165afe5c12d9a226165afe9c02d9a226165af6dc86d5a226165cf6db76d5a226165d76dc56c89865d65d76db56c89865d65c7edca6c89825d65c7eda86c89825d65d76db56c89825d65a7f5c96e1a125d65a7f4c96e1a125d65a7f5cb261a125d65e775c5261a125d65e7e5c2261a125d65afe5c2261a125d65cef5b86d9a125d65e6f5986d9a125d65c7f5a96c4a661d65c7f4a96c4a661d65e5f5c12e5a721965adf5c12e5a721965cdf5a76c49721965afb5c125da421965afd5c125da321965a7ddc961da321965a7dcc961da321965afe5c125da221965a7f5c96dda121965a7f4c96dda121965aef5c66dda1219658ff5cb25da121965a7f4c961da121965aff1c125da021965a7f9c961da021965a7f8c961da0219659eddc32e8985d9659ef5c12e8985d9659ef9c02e8985d965d4fca96dc985d965dc7db76d4985d9659eecca6c8985d965d6eca96c8985d965dcedc76c8985d965de6dc56c8985d965dcedb76c8985d965de6db56c8985d965c7edca6c8985d96597ecca6c8985d965c7ecca6c8985d965d5edc76c8985d965d6edc66c8985d9658fecca6c8985d965b73dc42dca961565b75dc32dca961565b76dc22dca961565b775c12dca961565b779c02dca961565d37ca96e09761565c77ca96e097615659f74ca6c49761565cf74a96c49761565d774a96c49761565db75c86c49761565de75c66c49761565e67cb92a57661565be79c02e17661565bc7dc72617661565be6dc22617661565f87dc961d7661565f87cc961d7661565f87cb961d7661565f87ca961d7661565c77dba2a57661565c77cba2a57661565f87d876997661565f87d872997661565be3dc42997661565f87d876197661565bc7dc72197661565f87d872197661565be3dc42197661565be5dc32197661565be6dc22197661565be75c12197661565be79c02197661565a7ddc32dca961565a7edc22dca961565) else (if j<3 then 0xaf456a2b21578ab05522a61518a8053a29a1440a1450427513909a84c425f12908d846622b111886c426210106882840e1ff0f907bc3d81e40f087643981c90e086e436c1b30d806b43541a70d2068433c19b0cc065432418f0c6062430c1830c005f42f41770ba05c42dc16b0b405942c415f0ae05642ac1530a805342941470a2050427c13b099847023211607d03dc1e80f107703ac1d00e5071037c1b80d906b034c1a00cd065031c1880c105f02ec1700b505902bc1580a9053028c12207f03681940ba05a026812808e03a019009404401f00b805002200e005800c000d75dc66cca765486d779c86c0a765486d779c66c0a765486977dc72e98665486977ccb69d8665486b75dc329d8665486b76dc229d8665486b779c029d8665486c7dda66cca765486d75dc56cca765486c7eda86c8a765486c7eda66c8a765486c7f9a86c0a765486c7f9a66c0a765486d779c56c0a765486d75dc96cca765486d779c96c0a765486f47dc62e99765486f55dc32e99765486f579c02e9976548697ddc96cca76548697edc96c8a765486b5ddc32e99765486b5edc22e99765486b5f9c02e99765486b75dc32d59765486b76dc22d59765486b779c02d59765486b7d9c02dda564c86b7cdc22dd9564c86b7d9c02dd9564c86b3f9c82d5a764086b6f9c62d5a764086b7b9c42d5a764086b7d9c32d5a764086b7e9c22d5a764086b7f1c12d5a764086c7f9b869da564086b7b9c42d59764086b7d9c32d59764086b7e9c22d59764086b7f1c12d59764086b7b9c42dd9564086b7d9c32dd9564086b7e9c22dd9564086b7f1c12dd956408687fcc92e9966197587fccb6a58621975a77cc9619a521975a7dcc9619a321975a7f8c9619a021975cdf9b76d5a021975d6dda86cca865875d6f5a86c4a865875d6f9a86c0a865875c7dda86cca865875d6ddc66cca865875d75db56cca865875c7f5a86c4a865875d5f5b76c4a865875d775b56c4a865875d7b5b46c4a865875d7d5b36c4a865875c7f9a86c0a865875d5f9b76c0a865875d779b56c0a865875d7b9b46c0a865875d7d9b36c0a865875d7e9b26c0a865875d7f1b16c0a865875b6ddc32e19661875b6f5c12e19661875b6f9c02e19661875e7b9b46c1a921875e7d9b36c1a921875e7e9b26c1a921875e7f1b16c1a921875d7b9b46c1a921875d7d9b36c1a921875d7e9b26c1a921875d7f1b16c1a921875e67dc8659a521875a77dc9619a521875e67d96619a521875e75dc36a5a521875e76dc26a5a521875e779c06a5a521875e6ddc8659a321875a7ddc9619a321875e6dd96619a321875e7d9c06a5a321875e3f9c6661a021875e6f9c8659a021875a7f9c9619a021875e3f998619a021875e6f996619a021875e7b9c46a5a021875e7d9c36a5a021875e7e9c26a5a021875e7f1c16a5a021875 else 0x750763076305e006e305e105e005e104e006e004000a5040000000000000000000000000000198100000000000000000000038c178c178c138c1b8c101e304000001e3040000000030568c2c17a30b05e8c2d141d141d141d14100000078c130c1116e30a2991428a6450a29914258c110c1316630a29b14278c178c130c1316e308c5b8c28a6c50a29b1428a6c50a29b14200000690402381008e040000018e040b8c1b8c178c178c138c178c178c1004d04013410444d988300c504e2380238010362f802f83620b62f802f801f8010011f802f801f801047e00811f802045e00962040a881a8ba0080018504e33802000000f80171415841711c3708c17005024607e007e007e007e004c410cc2304c0140f801308c008c5d8423141f801036004c430cc230440140a141a141a141617e208023412341000018504001a6244262416981f801f841f841f84103e10605f84203e007e0040617e0083407e2040198101e478de2785e0140f8be00805916358961580502e3b86e00c002e3046604000000000000068ca16803000b8ae0080698169810122c8020100300801000501e305e405e20705040000006c06e3b882000d8c103e204631882030907a404000000000000000000000000000000000000000000000000000000000000003e0070e1b3e2f804000f93e2f87e0238500000000000000000000000000000000000000000003e3f804d0fe3f80110fe3d8be00f620762040047e40800011f9020441047e4080008d04000003a40408c546122fd1788b9458a2a5142899448a225102879438a1a50cc86342da1610aa852427a131092846421a10107a83a41ba0d106282e415a0a104a82240d205d028811407202d0108054011ffcff87f93fb1fccfe07e83f01f60fa07c83e29ef4f747b73da1ec4f527a63d19e80f3a79a3cb9e28efa7703b41d80eb07503a69d28e8e74439e1cd0e4e71a3869c00df06f03719b58d9c6c635f1ac4d4869734519f4ce066d335199ccbe65c32a1944c926463219900c7a63531918a8c4461a3091828c045fa2fb97bcbd85e42e9173cb8e5ba2d916bcb445952c41600af05752b41580ab054b29f14c4a5252628f1444a1c50b28193d89e64f027693a89c44da26912d89664ab251926c92648b23791b08c84572251108874437217904c8204082000fe07d63e81f00f607aa3d21e78f1c7883c11da0eb074839c1ca0e307083811bc8db06d23611ac8d5869234119c8cd865c32b1878c305fe2fc1700b745962c81628))
def mo511H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a040004140001b4001240055f3e00085c000001037222e2800082660930115400000024461c61a00000002ce0e219f84238001c070480001b200003a05123c0008dbaaaf4503404aedc000000b300012302c3213cae0010240010562434859dbfc348000104e001246a58001a02816a013aeb3302f25221f021b5881180a43f24c0d52c0000000000000b8102a000000032cad0c80011d4a0cf460c4149b2ae5a44022015c326026000a00102011218108
def mo511D10 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then 0x65d9021bbbcdbb2ac810ddde2dd95640868ffb744c12cbac7fdb66a4865d67eed9952432eb3fe6c0a921975dafb4ed290cbae7ddb968c865d73eed4b46432ebbd7695a321975cff372d010cbaedf9b7680865d73fcd4b40432ebb7e69da021975def34ad010cbaefb9a4680865d77ecd1b40432ebbfa689a021975dfe342d010cbaf67db52a1961d7b6ed9950cb0ebdbd6c4a865875edf3605432c3ad7ddb32a1961d6bfad8950cb0eb5fe6c0a865875cfbb66d490c3ae7f9b06a4861d73becb34a430eb9df6a5a521875dafb4ed290c3af67d96694861d73eedcb46430eb9f7659a321875cfbb52d190c3af6dd9668c861d77aed2b46430eb9fe6e5a021875cff330d010c3ae7f996680861d73fcd4b40430ebcfe661a021875dbf34ed010c3af6f996680861d77bcd2b40430ebbee691a021875dfb346d010c3aefe9a2680861d77f8d0b40430eb5f72e1a664c75cfbb50d33263ad7ddba619931d73ee5d30cc98ebdb76998664c75afbb74433263ae7ddba219931d7baeda90cc98ebdf66c08664c75cff374433203af5f9b7219901d7bbcda90cc80ebdee6d08664075efb366433203af7e9b2219901d7bf8d890cc80eb1ff6d9a726165cfdb6ed1130b2e7ecb7688985973f6db3444c2cb9fb2d9a226165cfdb6ad1130b2e7ed98688985977b6dab444c2cbbdb695a226165afdb644c32eb2c7fdba26097596bf6d91304bacb9fd661a125d65cfe930d092eb2eef5b6684975972fe5cb4e432cb97f661a721965cfbb30d190cb2e7dd9768c865973f6cc344432cb9fd65da121965cff330d010cb2e7f99768086596e7edb930bb2cb7bb6c8985d965afdb644c2ecb2deddb321976596f7ad890cbb2cb7be6c0865d965cefb6e54b0ab2e77cb72a5855967be5d32ec2acb9df2a59761565cef9524bb0ab2db7db825d85596fbad892ec2acb9df2a5a661565be7b685330ab2dd7db721985596faed990cc2acb7db6c88661565bef3604330ab2ee7ca95d985597cbec3aecc2acbe3f61d76615658ffb74cc2eab2c7fdba26175596bf6d9130baacb5df2e5855d565aff36053b3032d7f9b02a1971967fcd8150bb0cb1ff6e9985d8658ff974cc2ec32f1fd9861d76196bdedb350ca0cb5ef2e1a765065af7b6cd3b2832d7bdba61d941973de5d30eca0cbcef6a18765065eb7b4ec3b2832d7bdba21d94196bdedb10eca0cb5ef6e17665065af7970bb32832f5bd875d994196baed994eca90d5db6c8a765486aef36053b2a4356ddb32a1961d6b7ad8950cb0eb5be6c0a865875ccfb2cd290c3ae6dd9668c861d71fccc340430eb9be659a0218758fbb74433263ad75db5219931d6becd810cc98eb1fe6e88664075abf36e433203ad779b5219901d6bdcda10cc80eb5f66cc8664075afd364433203ad7f1b1219901d7c3ec3aecc2acb5ee6c08765065 else (if j<2 then 0xcb7fb6c8985d965eefb6e54b0ab2f77cb72a585596fbedb952c2acb7df2e99761565def974cbb0ab2ef7ca965d85597bbe54b2ec2acbbdf2a49761565eef9524bb0ab2df7db825d85597bbe54b4cc2acb7df6dca661565befb6e4330ab2fe7dba5d985597f3e5d2ecc2acbf9f2e57661565fcf952bb30ab2fe7db85d985597f3e5c2ecc2acbf9f2617661565fcfb4ebb30ab2df7dba5d985596fbe5d2ecc2acbddf2a57661565befb70bb30ab2fd7d875d985597f3ed32ecc2acbf9f2997661565fcfb0cbb30ab2fe7c865d9855973fe5bb52c2acb9ff6dca961565cff96e54b0ab2cffcba65d855973fe54b2ec2acb9ff6a49761565cff9524bb0ab2dbfdb825d85596ffad892ec2acb9ff2a5a661565bf7b685330ab2df7db561985596efedb90cc2acb7df6d48661565bfbb664330ab2dfedb221985596ffcd810cc2acbbbf6e97661565ddf974bb30ab2eefca95d985597d7ec3aecc2acbf9f6d576615659ff974bb30ab2e7fda95d985597cfec3aecc2acbbbf6997661565cff970d4aeab2e7fdb96a1755973fe5cb50baacb3ff6d8a85d565cffb74cc2eab2e7fcba66175596bfedd130baacb5ff6dc985d565bfdb644c2eab2e7fda865d755973fe5432ebaacb5ff6e5875d565aff972c3aeab2e7fd98699755973fe4c34cbaacb3ff6e9865d5659ff974c32eab2e7fda9619755967fedd10cbaacb77f6dc865d565bf7b68432eab2dfddb321975596ff6d910cbaacb7fd6c4865d565bff360432eab2eefda85d97559777e542ecbaacbddf2e5855d565defb4cc2aeab2fe7d76615755973fed314ecc0cb9ff6dda666065cff96ed333032e7fda82a1971973fed3150cb8cbdfe6c0a865c65ebf970cbb0e32e7fda9699871979fecc34cc38cbd7f65da661c65cffb30d310e32d7fcba65d86196bfedcb0ec30cbcff6618761865ebfb2ec3b0c32d7fdb921d86196ffcd8150bb0cb5ff6e9985d865aff974cc2ec32e7fcba661761973fed4330bb0cb9ff6a1975d865cff950cbaec32f5fdb961d76197afecc30ebb0cb5ff6e5875d865e7fb30c3aec32f5fd9761d76197bdedbb50ca0cbdef2dda865065ef7b6cd432832f7bdb869d94197bde5c34eca0cbdef6d9a765065ef7b74c3b2832f7bda861d94197bded3b0eca0cbdef6d98765065ef7b5043b2832f7bda861994197bdedbb0cca0cbdef2dd8665065ef7b4ec332832f7bd8761994197bde43b0cca0cbdef6e17665065ef7970bb32832f7bda85d994197bded3aecca0cbdef61d7665065aef974c332a4357ddb329d9521abf6d914eca90d5fe6c0a765486bebb6653b2a435f6db229d9521afbcd814eca90dd5f2e99765486eafb6acbb2a43757cb565d9521b3eed3b4ac990ddd76dd9564c86eeb96ecab264357f9b869d9021abfcdc34ac810d9fe69da564086ebf36acbb204375f8b5 else 0x6cd412cbacffdb56a0965d6bfedb1304b2eb3ff6e89825975aff970cb12cbae7fda8658965d73fedb152c32eb9ff6d4a961975cffb5254b0cbacffcba659865d73fe54b2cc32eb9ff6a49661975cff9524b30cbae7fca9695865d67fedb352432eb9ff6a59621975aff972c310cbae7fda9618865d77be5cb4a432ebbdf659a521975defb0cd290cbaef7da9694865d76fed3b4a432ebbf76e5a321975dfbb2cd190cbaefdd8668c865d77eedab46432ebbf76a5a321975dfbb4ad190cbaeff9b9680865d77fccc340432ebbfe6dda021975dff32cd010cbaeff986680865d77fcdab40432ebbfe6a5a021975dff34ed010cbaeff9a5680865d7b7ed4150cb0eb9ff6a0a865875eefb6a5432c3af7ddb32a1961d7bfad8950cb0ebdfe6c0a865875edf970cb30c3af7ddb36a4861d7bfcd8352430ebdbf6e19621875affb72c310c3ae7fda9618861d7b7ecb30c430ebbdf619a521875dfbb0cd190c3aeff986680861d7beedc34cc98ebdf72e1a664c75efbb74c33263af7dda6619931d7beedd10cc98ebdf76988664c75efbb0c433263af7f986219901d73fedb34e4c2cb9ff2d9a726165cffb6ad3930b2e7fd9869c985967fedb34e4c2cbbdf69da526165defb4cd2930b2efed98688985977f6dbb444c2cbbfb2dda226165dfdb6cd1130b2efecb6688985977f6dab444c2cbbfb69da226165dfdb4cd1130b2ff6db5688985977f6d2b444c2cb9ff6a0a865d65eefb6a4c32eb2f7edb226197596ff6d9130cbacb3ff6d9a825d65cffb504c12eb2f77db526097597bf6d91304bacb3ff6e89825d65bfdb644c12eb2eff5b8684975977facc3424bacbbfd261a125d65dfeb6cd092eb2eff5b5684975973fedb152c3acb9ff6d4a961d65cffb5254b0eb2e7fca9699875973fed494cc3acb9ff2a4a661d65bfeb625330eb2d7fcb9695875973fe54b4ac3acb7fb6c89861965cffb5253b0cb2e7fca929d865973fe5d32ec32cb7fd6c49761965affb72c3b0cb2d7fcb961d865976fe5cb4e432cbb7f661a721965dbfb6ad390cb2e7fd9869c865976fed3b2e432cb3ff6e89721965dbfb4e4b90cb2dff5b125c86596bfedcb0e432cb5ff2e58721965df7b30d210cb2efbdb7690865977decbb48432cbbef25da421965df7b6ad210cb2efdd9868c865977eecbb46432cbbf725da321965dfbb0ed190cb2efed98688865977f6cbb44432cbbfb25da221965dfeb30d090cb2eff5b7684865977facbb42432cbbfd25da121965dfeb0ed090cb2eff5b5684865977fccc340432cbbfe65da021965dff12ed010cb2eff98768086596f7edc152bb2cbbbf2e9985d965edf952cc2ecb2defcba26176597b7e54930bb2cb7bf6dc985d965f9fb6e4c2ecb2fe7db526176597f76d9130bb2cb7bf2e1a55d965cff974cc2ecb2e7fda866176596efedb930bb2)) else (if j<5 then (if j<4 then 0x46488bd113e220443188451072206c3fe87df0f821ed43b0870d0dde1b4434786710c8218442e7859f0b02158c2a2852709821244230843107ba0f441d0837106a60c8c17982b1052608fc107820303ee06440a780e901ba02b403e804d0015ff23fcc7f68fe4dfabbf367e3cfbf5f72bebb7d46fa09f353e5b7c50f889f00bde97ba2f6e5ecc3d777abef51de97bd0e79ecf379e5ebc9c7908f1b1e2a3c337824efe9df13bca7740edd9da1bb2b7614ebedd7abae675aeeb21d53ba627494e8c9d0d3a0273c2e725cd8b99972dee55dc96b927720ce3b9c6b38a37128e1f1c323843707ae0ddc0fb7ec6fa8def1bc9377a6ea0dd29b99372c6e16dc15b76b6cc6d68da29b34b6516c72d861afbb5cd6b58d62dab535496a50d3b1a6eb4ce697ed29da3eb44a6864cffd9f3b3b46738ce119a8b3306654cc6d98632d96582ca3993fb2436456c7bd8e731a46306c5ad8a9b13b6246c42d879b0d26162c26583c306960a2c0c1810b0095fe2bf897e9afa95efebd557a32f375e1abbb176a2ec55d6cba557432e805cbeb8f9717ae175c10b79d6e7adb75b62b6896c9ad8d5afcb5bd6b02d515a84b48568dad0359c4b34d65dac9a5916b1a96292c3a5832afe15d9ab5c562eab015422a485418a71d4c1293451cca28542e28204fc89e7d3ad27154db29a5131ea6014b78960129da4ff497491f9221240647948e391a9231f45c68a9d13a222f43d486950b0211241ac826902f20223fba7e60fa51f053d6e79c8f1b1df13b5875c0e959ce639547194e101bdb372c6d68d8a9ad03528693cd0999d7333665a0c8418cc31206150c0797d32f1c5d48b8b16da2d3c5940b0595cf2b0254f0a7294a928ec50e89ff13b026e84ce097512b724d248b48f891b522f244f488090c5210041108040fc31f0e3d0877e8eb81ce638dc6f48dad1ad034b06780cb418f030f06000bc417222d545910ad41530294c50709d2132c256848608c7111620f440087c50f121d5839606e70d44199831085dc0b1c152427d84b608e210b01f383a206ba0c601650273045c07c80db017a027c0408063008a00ae00027fedd12e4ab0dddf6d9a765486eef974c332a43777db76199521bbbe5bb0cca90dddf69d8665486eef94ec332a4367fda629d9521b3fe5d30cca90dddf6d58665486eef96ac332a435fddb329d9521aff6d914eca90d7fe6c0a765486ebf974cbb2a43777db565d9521bbbe5ab2eca90ddf76d58664c86efb96ac33264377ddb76959321bbee5bb4ac990ddf76dd9564c86efb96ecab264377f9b869d9021bbfcdab4ec810ddfe2d5a764086eff36ec33204377f8b76199021bbfcdab0cc810ddfe2d58664086eff370d2b204377f9b76959021bbfc5bb4ac810ddfe6d59764086eff16acbb204377f9b76559021bbfc5bb2ac810d9ff6d5a8259759ffb else 0x87146c3793c3e2f0438d839b0d3e4f1787c0361b0be4f1787c0361bc9e2f0f811c3793c3e2f02385c29b0d3860779347e2f0f80ac3793c5e1f01a46c3793c5e1f01a46c3617c9e2f09a46c3617c9e3f1784d23f93c7e2f0e1cd2321f0de4f1f8bc2691f0de3f17870e691b0de4f17870e691b0de4f1f870e691b0de4f1f8b0e691a180533787c9e3f0788864b1619e3f0f83c83f93c3e3f0589cc3431ccc5f2787c762f01011f1f87c1e431324708c3192e6f278ec5e1f012e6f258bc7e1f00c11f1f86c5e01459e4f1d8bc3e01819e4f1f85c5e01812a602f93c7e2f0f808f278fc3e0c2e98693793c561f1f8060a3264cc5f278fc5e0224de3f17809028258be4f1f8bc3e0231046f278bc7e1f00cc6f278a25e1f00c0cf258fc3e2f00cc6f258bc7e1f00c0c20f93c7e2f00cc6f278bc7e1b00c0cf278fc310f10c0913793c3e3f17807f238bc385f1f806c2f8499e4f1f806c3793c212c2f8bc03e1bc985f1f8bc0361bc9e1c2f8c21e21c130cf1f93c5e1f00fe4f1f8bc3e042b9870679013e3f1787c03833c9e3f0f8bc03027c9e3f1787c105b311e4f178ccde1f00de4f13846866f1f807b3793c5e3f0f8067278bc649f0f806f278bc649f0f806f2789c649f0f806f238bc649f0f806f278bc649f0b806f27860be3f17806f1f8bc1e4f08be3f0f83c9e2c28de4f1f8bc3e01498095378fc9e2f0f808c4933c7e4f0f80604f8fc9e2f0f80983e24cde4f1f8bc2871f13e4f1f8bc2871859e4f1f8bc3c5180be1f0793c7e2181206f278fc5e1f0514844f87c1e362f93c4399b0be2f0f83c63693c7e1f003fc42b36106cf1f87c185f10c09c2f8fc5e1f00d89f078fc5e1478da4f178fc28f17c7e1f123c4079b3c1e3f1784563f830ba4f1f8bc2891f0be1f0693c7e21b0be3f1787c109360fa4f0f830be384f887c6625c666f278bc3e0231989f278fc3e0350f8cc4b80cde4f1f8bc2438f0d85f278bc3e01dc386c2f93c7e2f00ee0c3617c9e3f1784722b1bc9e3f1787c03d8d8cc5f278bc3e01ec0c662f93c7e2f08f6063317c9e3f17847361a70d85f278bc3e020d869d1a170de4f1787c04e39c186c2f93c5e11f0de4f1f8bc287190de4f1f8bc3871b0de4f1f8bc28719c986f1f8bc38719c786f278bc38719c586f278fc38719c386f278fc5871bc7e4f1787c02e931ee0c499b0be3f1784996312c02578cad095832aca54d4a7994d5292651d4a2b943928124fac9ef93af26da4d3c9a1932526324ba496592bf251e493491791ed239e46c48d2918722f6452c89f910f21e2434c848908520f2416c815901f20263eb47c78f5f1df23bb47558e7b1c9638b47078df11b5e35fc6b08d311a4a33d466b8cb9195a323c6418c53186a30145f38bc9177a2e7c5c08b6316662c0c5728ac7155229e45248a1913f627744c48959125223e4) else (if j<6 then 0xa15494351a8a83401f0be00b0be00bc30c0bc285085849f007e10605e2f00562f0040cb1786c02417c0159a0be12488058ec1e10c126608126609c8e371385c02f841f1780282f8427238dc41800391c21190c662309805337842b1784284990c66212124908cce370b80400cce3080f1f87c018009428409137803b1580282a8d42a0100c09828605f00434f00563b0d803f0f00921924c6613009a1e0124324e87801e8780490f43c02487a1601243c2a9146a250a806c28305070a0b89c010b28dc013080641d890280170bc0084d0551a85402f8bc0130d84c0f27845f27842e061425228bc7e1f00be3f0f803030a0f80124a9284a1a00b42a0044421908824014920899872260c8180348a401090462210f004036184dc00c1963412004c309b801f0092170092170092170092170092130092141548a10c4d054287e126042c5128031303057184e47178c3f18305720505710585060a0d918963b108c5b258ec42316c963b1084907c60c988c44d1892622e8c322e8c2d183e2048843f107e20405228d441a9146a20e120b11121024122689121917441688121000f05c60800f05c40a3c147828f0548e37106058f481291c5e30fc608aec6123ec7090ec60a91c7e20c13e20b49620a48a4b1068fb1424333793c7e2f0f804a39d719897199bc9e2f0f809c6627c9e3f0f80d439cf19897019bc9e3f1784933793c5e1f06246f278fc3e035624633793c7e2f0e24686427c9e3f1787c03c3213e3f278bc3e01e1909f278fc5e1f0294833197c9e2f0f802e12221909d1f93c5e1f00f0cf278bc3e089398732f8bc310f1f90633793c7e288784633793c7e2f0994203c3213e3f278bc3a01e19e4f1f8bc310728f0cf1f93c5e1880d0cf278fc5e1883987060240c05f278fc5e1f0120cf278fc3e2f00c2c14b8fc9e2f0f8071678fc9e2f08c061678fc9e2f0f805238dc65e4f1787c030b05363f278bc3e01c59e4f1787c032181830f278fc5e11bc7e1b0793c4301859e3f278bc2301859e3f278bc2301859e3f278bc2301bc7e2f08e06028c859e4f17846030b3c631f278460378fc9e21b0c05c3793c7e2f0f80d83e1b0be4f1787c06c1f0d85f278fc5e0360f86c2f93c7e2f09b073bb8f0de4f1787c185230de4f1f8bc0881b0de4f1f8bc2871a8be4f1787c1461a8de4f1f8bc345198de4f1f8bc3e0228e29f278fc5e1f03187160a7c9e3f1787c145218de4f1f8bc3e0148ec6628dfc9e2f0f8064431bc963f1787c0c51fc9e2f0f8052c5198cc5f278bc3e0148e2cf278bc3e019314763793c7e2f091c663793c7e2f0d818a3b1bc9e3f1786c0c51fc9e3f178452c5198cc5f278fc5e1948e2cf278fc5e118714763317c9e3f17845238b3c9e3f178460c51fc7e2f08e061c518642cf278bc230e28e3116793c7e1187147f278fc4361 else 0x78c1713802f182e47178c3f1836304cd630812e00287e305c2e0f187e307120e241c489c252820024cc1385c1a30f460806504004994272020040cc1391c5e30fc60b8541e30fc60b84100ca0800933040024ca1384111822c030843000048362b004000e471b89c2e015400d8ac0129146a250a80502c761b00622100562b0040906c60b18183389c01c19c61318123514201c4e008c608c810052080e470843005c46009c608c01005208a41718305718429428585070a0e14182e8c294d14294d142718243048b6304a14422d8c222b8c26298c262b8c2001c0a3814702690404702e305c40b14100cce370b8041301445e013c00f80171b87c01f801f05882f058820898bc01f82c417801f0036207c00b91c6e270b805d168025168025178021601447e0100d32142d36142f00385f004c5f004e330f803f0020862f82c22782c21000391c6e270b805b258ec41b1186c260b00503c9c00a8be40ac9610b47e01606c360b003030302f17802c2e8fc019134643211048036148ba30d8be009c6e1f007c08484c360b008c258bc010240be00e8be00bc00910864220900501c6e1f0064be004e2f004c5f0054432700331b87c01b8bc01317c0139380138dc3e00cc5e0098be009c661f006c5e0584371780262f802727002a0987801b8dc3600dc560098b6009c940084c4531f80442f8fc3e012c7e2b0d814c2a14121217c4450f0a08085070a0d141f1f87c01)))
def mo511H10 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x400016b700000002781000000000000000343f30860002087d14200000000466e16000000000000000050d00002b10000052b0c3c4d41000000000000000000000000000000409e000000000000000000193e200bd92800000000e2e00000000b4f292d38180e1000018110000f2240000000000000000000000000061ce00000000000502000010398000000183f400030650000000000000000000000364370dccc52000260a80000000000301c906200002574000441e38be323f8a3304c0000000000000000000000000045284577234400000000000000000049180000000381ba0ed000000014098000000000000000286f5ea000000000000000000386f800000000002218de880000000140e70ac96a4a42087a800092b4433000008cf0000000389fb71500000000149a01d6e63c2914b080000000000108d80000001c4254998000b51701e0000000000006914000000070b231f20500000000092300000057b20d5ad0000393e00000000000000061f5d902546a80300000000000000000000000000000004b8000261100000001ca7c0001d1b0000000090b8000000000c80000000b07000007458000000000029290000d205e8ef27a000000014c3400000000001d1b80006f3c801e0003c6380000000000000000000000000000000000000000046d800000000000000000000000000000000000000000000000044f7f9a0000000000000001083c1524c780000000000000000001463000000000000c1f50c10001e06827bc8ab9a33e450000000010be000000000008028389b87f2e27c2160000000000000000001c4408e0a1c7ad258a488ff00000000000286c3a380000000000000000000000000001a06d6d21a8000c875825de2ba925000000015a6000081a6000000000005009809143a000012c60000f7800000000000000000000001ca8800000000000000146200002010a1e4000000000000000d7980000000000292ae81671500002c640000000061c0644780d000144c4000000000000000000290c00930366a7f80000000000300f8000585289040000000a42b024cc1e0000a1a4d3f6056ca18e16861b8000162380e4229d42b486a000040f537a80000001d06c00042f10000000000018f9000000000000000a06761780000000000000000007c4900000000000586f000000000000000ea93e4000000000000120000003091000000000007a2f000000000003510127000000007d1510c000000000000000013cc00000000000000000039190000000000000005193206d09b0c22280250800120801080000a000000601050002487048022040010000204200802110401004200810320c40204e6100010040110020300000000020000000011042100040000200804108001184010800038880280410800000021 else (if j<2 then 0x8ce6011d0f7d83b22500000000310f22c0a5ad88f000000024729086f45a00000000000000000000000000a1d6000000041430001e53844b00000000000370b800000000002a2c0000f2a62c40000000000002044000000000010bf00000000000000000000000fde203a5caf80000000000000050ddb9d80001c178000903c0000000000044500001180000000000000000553362a0000289e000062060000000000030b6000000000000000000000000000000a19c000000000010260000594d944e0003a468000e19400000000000000041080000000000000000000000b28e00000000000000190b80002809000000000001c4571d8000000000000000000000000000001c35403e00008241cc5400000000000000000000000000000279e80000000000000000001a9400000000000000044e478280000000ebbc00000000000000000000000000a4b0088000000000000680e4eda21c000000000000000000000000007e1200000000000fd890103026bd2000015ad4000000000014d640000000911c000000000000000000098300000000000245b00000000000000078f20000000000000000000000000000002cb098940000000e17022350150000c51000000000000f2aec2080000000c4f800000002302000061dc0000000104a00018a8d80e000000000003105e25e000000000270001229800000000000000106d306df12a00000001b460000000000000000000000248f0000000000019ae80000001286800008ae00000000000000000016c2279d00004290000000000007a4a00018948000000000013170000000000000000076fa0c000144ef8ee82c5c8640000000d6962116b2f88cbe1df42fe290b83f48380000000000000000000000000089f20000415811a0000b8880000000000000000000000000182e904480001a04e2140000000d0fda288000000070cc000000000009e060000000000089e20001d8528c5c26a00020868000000000000000000792b8baedb1800000006123cacf92e000193f94820000002be404000694f000102cc0000b31a447141f0288000000000000004c8b00000000000000052ac000000580000000000000000000000000385a800000000000000000091aea2dce2e8000000111040004126000000000004a3e000024ac000000000000000000000000000000000552a0000c150c408000000000000000000000000000000000d5f2000000048522116c248000000000000000000000064ff0d400000000000000000000000a1870ce000000009245c517867000021f60000c2548d4d5da0003948b10a24ba2572014bf060001617400014bb01541427a9880006222000000000000e32c4580007a37a408000000000000001a4dc0000000905902a6459684f8a46c1f40000863f17d00b else 0x7f500000000000000000001d23894a8000a2640000000492400000000000415b00000000000380c000122bc00000000000000000000d894436557b2cce24008fc2f4f1db45eb23f6d5c000093d70aa0001140513b208200000000000000000000000000000084a80000000b5060003a2698348a4800032450000a69000000000000000000028230000000000000000000f61200000000000f89400024985c2f00000000000000000000000000307b00006099f777ec500000000896a15e0000000000010280000000000000000001b5200000000468b451164200000000000000040648060ed70000000021d5307cc7832f280760001c7080000000000000000000000000000000000000000069680000001648400000000000000000000000001a20f89a00000001096c00038f490258004000694cf0b00000000000000000002294e2850000437ac50bef3c22be1a76870000ecacc3e0000487af1d0a49c00000001041a3dbc27600a000000000000000e13e008400028d600000000000509c0000314492f80008dda0000000000000000000000000000006a500004427000000000004117000000000000000690a000000000000000000345e00000000000000060b139e5508c00000000096000000056450000000000000000001c2640007216000034b800000000001e1ffc8ed084a520e0e80001e2f00000001435908c0000000000000000000000081880000000d3c00000000000172c7c9d0000a11400000002336e2460003e2600000000a5280000000161dc2e40000000000001d601b6305000000000002835000060180005d11000000022a80000000000000000000d281828f452c89000000000000000000000000c5d90503136aad600280000001a0b800000000000000000000000001b43c0001941154200000004154300e00000000000b4060002ca5861c0000000000000000001a953061000000000000000185a000000000000000000000000000000000030d9030c85c30898388000000091c9806400000008632944ae596c341a77c1c7889fc500239439ac79800020a7e20207e000000000000d214d0400000002c01000000000000000000051800000d5c800000000002f7962fb4134ad1c000000))
def mo511D11 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x7ffca961565fff65d85597ffc9761565fff69985597ffca661565fff61985597ffc8661565fff5d985597ffca95d565fff6a175597ffca85d565fff66175597ffc985d565fff61d75597ffda65d565fff29975597ffd865d565fff21975597ffd765d565fff69987197ffda761865fff29d86197ffd8761865fff21d86197ffda85d865fff2a176197ffd875d865dff65d9561affda725586dff65c9561b7fc9725586dff69d9521b7fca765486dff6199521bf7da765486fdf29d9521b7fd9765486bff2a1965d77fd9865975bff6a0965d77fd9825975dff260965d77fd9625975bff6a5865d77fda961975bff2a5865d77fca961975bff6a4865d77fda921975bff2a4865d6ffda521975fdf694865d7fdda321975ffe680865d77fda865875dff2a1961d77fda961875dff659861d77fda921875dff658861d7f7da521875ff768c861d7ff9a021875dff69d985977fca766165dff66098596ffda726165fdf69498597feda226165dff6a1975977fca865d65bff2a1975977fd9865d65dff26197596ffda825d65dff660975977fc9825d65dff6a5875977fca961d65dff661865977fd9761965dff66086596ffda721965dff65c86597efca95d965fbf66176597efc985d965fbf695765977fd985d965dff26176597efd865d965fbf21976597f7ca961565fdf65d85597f7c9761565fdf69985597f7ca661565fdf61985597f7c8661565fdf5d9855977fca961565bff69985597efd7661565bff6a175596ffca85d565dff661755977fc985d565dff65d75596ffda65d565fbf5d975597f7d855d565dff69d981977fca766065dff6a1971977fca865c65dff6a5871977fd9861c65dff65d87196ffda621c65dff661861977fd9761865bff6a176196ffca85d865dff661761977fd975d865f7f61d7619777da765486ddf29d9521b77d8665486d7f65d9521b7dd8664c86df76959321b7dd9564c86dfe69d9021b7f98664086dfe6959021b7f99764086dfe6559021a7fda8259759ff2a5865d67fda921975bdf694865d6fdda321975bfe680865d76fda865875dbf2a1961d67fda961875dbf659861d67fda921875dbf658861d6f7da521875bf768c861d6ff9a021875df7699931d77dd8664c75df7219931d77f98664075dfe219901d67fda726165bfb68898596ff5a125d659ff6a5875967fca961d65b7f69c86596fbda421965bf768c86596feda221965bfd68486596ff9a021965ddf2a585597e7d76615659ff6a5855967fca9615659ff6a5755967fda6660659ff6a5871973fd9861c65d7f65d871967fda921c65def6a1941977bda765065def61d941977bc8765065def619941977bd7665065d5f65d9521b75d9564c86d7e65d9021b7799564086dee6519021b7d99364086dfa6499021b7f191640869fb6889859677ca961565 else 0x9024e38f8b87809c6c52ce4e2e1e012231b14b3938f8780448c6c5610936e4e3e2e0271b14b3938f8b844080c49e2e4e3e0e11c159b938f8b878072c064985e4e2e3e1e024183027938f8b87821490c492685e4e3e1e2e02418302617938b87838c9a64945e0e3e2e1e4229927838f8b87911480649e0e3e2e1e44521249b938f8b878114866a489e2e0e3e10f219a278f8783883c70f66a48f8985e0e3e2e129b292178f8b8781988668f09a485e2e1e0e3263c259a9217878f838890c09e4e3e2e1e01c33938b87804860ce4e3e2e1101833938f8b84406e3e2e11810144833938b84406110ce4e3e1101b938f8858405c50ce4e3e1e0183027938f8b87807dbab6c4da3b670d96b63cd89b618d80b5d4d6fb598d64b57cd5bb558d54b524d45b4f8d3ab4c4d2db498d20b474d15b428d02b3eccf7b3d0ceeb38ccdbb340ccab304cb9b2b8ca8b274c97b240c88b1fcc73b1b0c62b164c4db108c3ab0d4c2db0a0c20b04cc07afe8bf0afacbe3af70bd2af2cbbfaee0bacae9cb9dae58b8cae1cb7dadd0b6ead94b5fad58b4cad14b3face0b32acacb25ac78b0eabecaedab78accaadca9faa40a7ea99ca59a928a38a894a0da7f09f0a7849cda6d89a6a65c983a5c0960a54c945a4d8926a45c905a3d08e2a3448bfa2b88a0a24c881a1b085ea144845a0d0822a04c7ff9fb87de9f2c7bd9ea07989e1c7779d887529d0c7339c887149c0c6ef9b706ca9ae46ab9a7068e99fc66b997864a98f462d987860c97e45e797585c696dc5a7965058295c4561954054094b451994204f893944d793184b2928c4939208470917c44d90f042a90644058fd03e28f443bf8eb83968e1436f8d7834c8cf432d8c7830e8bf42ed8b782ce8afc2b18a8028c89fc271897824e88f422d885820487c41df87381ba86a41998628176858c14f84f012a846410783d80e483540bf82b809a821c07781a805c813c04380d8028807400f8000fff69d9561bffca765586fff65d9561bffd9725586fff25c9561bffda561886fff2958621bffda765486fff29d9521bffda865975fff2a1965d7ffd9865975fff6a0965d7ffd9825975fff260965d7ffd9625975fff694965d7ffda961975fff2a5865d7ffd9661975fff259865d7ffda561975fff6a4865d7ffd9621975fff618865d7ffda521975fff618861d7ffda766165fff29d98597ffd9826165fff69c98597ffda626165fff69498597ffda865d65fff2a197597ffd9865d65fff26197597ffd9825d65fff26097597ffda961d65fff2a587597ffda661d65fff29987597ffda561d65fff2a586597ffc9861965fff69d86597ffca761965fff65d86597ffc9761965fff61d86597ffda561965fff66086597ffd9721965fff25c86597ffd8721965fff2a576597ffd985d965fff26176597ffd865d965fff6957659) else (if j<3 then 0xa48e3e4e2e1e0171b17938b87838c72c290605e3e4e2e1e027191b14302517938b87838cb2c29e3e4e2e1e01cb38f938b8780a472c0605e3e4e2e1e0292430241b938f8b87811492ce3e4e2e1e0291cb3938b8780c862ce3e4e2e1301a1793861b8b838c786e4e3e2e1e0851d1917938b87838c70c46e4e1e2e0e345211b938f8b878114a484645e4e3e2e1e02920b3938f8b8780a71882cc6e4e2e1e032c520b31b938f8b84c314866e4e2e3e1e01b938b8f87819866685e4e2e3e1e02c20b02598149b938b8f8780ae4e3e2e1e02c198b938f8780b06e4e3e1e2e015249917938f878b808a626e4e3e2e1e02c20b09b938f8b878070c492645e4e3e1e2e02424149b93878f8b80885e4e2e3e1e0a61d261517938f8b8782989c5e0e3e2e1e4192714301917838f8b8790a4645e4e2e1e0e31c9a143393878f8b80846e4e2e3e1e0891f14b025189b938f8b8780a0ce4e3e1e2e0891c9b9385178f8b8078526e4e2e1e3e01c9a151793878f8b80845e4e1e3e2e018b2141b93878b838c8850945e1e4e3e0e24c261a14991793878b838c98685e4e1e3e2e0092198b127938f8b878082ce4e3e2e1e01817938b8f878198766e4e2e3e1e01817938b8f87812470c660905e4e2e1e0e327938b8f87812462c660509e4e3e1e2e027938f8b83861462c26e4e2e3e1e01c9b938f8b87821474c8609e3e2e4e1e0221817909b8f8b8780b092c8906e4e2e3e1e02226178f938b87813084c49e3e4e1e2e01cb09b938f878b80726e4e3e185e2e01cb226189b938f8b87809668985e2e0e4e3e12227938f8b8782159888985e3e1e0e4e21c9a27938f8b878214849e045e3e2e1e41c3299278b838f87911490c09e3e1e0e226e445249b1783938f8b852480945e4e2e0e1e31c30249917938b87838c9e1e0e4e3e2c51b17938f8b8780b22482c060945e4e1e3e0e2249917938f8783887c5e1e0e3e4e2891d9a32278f938b878088c89e4e3e2e1e06621983027938b87838c8a50c09e4e3e2e1e021999433938b87804886665e4e217e1e01221999433938b87804886665a08ce1e4e3e21025999433938b878c40866658ce4e3e2e11021999433938f8b8440866650ce4e3e2e110231b142793878f8b80806050c09c6c5e4e3e2e1e02f14b0a78f938b8780809c6062c29e3e4e2e1e02b158cb0cb938b87808c5602c30e3e4e2e1221a17938b87838c78685e4e3e2e1e01d151b938b87838c746e4e2e1e0e3451c251b938f8b87811484645e4e3e2e1e01d17938f8b878318763c6e4e2e1e0c51d831b938f8b8714786e4e1e2e00e183a3a1a17938b878080e6c698685e4e2e1e0261b938b878e1c686e4e3e2e18718259b14338b938f878092cc562e4e3e1e01f1584d09b938f8b808a6c5e4e3e2e1e01c181430269b17938f8b8780bc52c09e4e3e2e1e0231b15 else 0x6462e1e0e3149787838c4256462a1a0e319918b8c325e30985838c345e30a241892509918d878b805e2e009928986804019184229058980201918985838c5e3068d89803a3051985838c42904a589803096308a418545630d918b8f87805e3e1e00d8d87803e00780145e009918d878b80526e2e00c998e8987805a2e00a158d878042685e00d8d898793805e4e009158d8b03905e4c009870390345e3e00c268f80b04456462c0e3151b8f00385a362e011168f82144268564a3c015158701838c56361e00d8b8022645e00d9300245e2e00c9a158e898780645a2e00985149a15158e8b00645c060e2138780262a1e00e878014363c060e11387012430963a1c08516870124362a1c00985149b802866461c0130218983266361e010b380264c0268510998b01804c0490a198f02144c049098b0026144c56362e411918b8c345e309928e24345a309918f883e20909928a2432625e4e2e1e0e31c30259897938b87838c9e1e0e4e3e2a51b938f8b87819a947668c89e4e3e2e1e02232242497938f8b878198a8666850c0925e4e2e1e0e32e338f938b87822478ce4e3e2e1e08966219a9498943027938f8b8780be3e4e2e1e02c18b0a78f938b87807290605e4e3e1e2e020b0261a178f8b83938490c8646854509e4e3e2e1e02e1a17938f878b8))
def mo511H11 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x7cb0000257600000001072baf90bc1ba4b59700003694000022d0000004f64fa6c8400005a7051600013468000f238e13956f8000e02e4660000000000000000000085972100002677398ad11b30280000000000000000000a640001e6340002e8c0000000000041c44280000177ce8b166cac17000040611ba6c42ad368000b0670bea436c5bb685dd7228ef0000521b25cc0004174c9d7169000000000001c22e49280000000103e13f4d5e0000e160000000061f4d1c800020eb73dca323c2970e20cdee75c0006063927ec4b800041360bc600004798000998e0001d3d787a0000767000069a60204c58b86d109c000000000000000009600008338000000000000006815431d2785196ae5b00000003c7e319e00000001c7be097000061fbc600000c2b7582381c4410000009cde03eeb100000002de8c8290001175227ea8d35acc00005878bc6d4660000000000100000001c9240910000c46c0002b2900000001a74f0db0000e5d8000776c4b4acb45cbf5affc4714f350e4e812bda0f73b87480000000661000007d30000000099408f00000000085b8000e1e800032de1975523c0002448300379d1274692efae0d068c0840000000a78902503a3d05b1156000087080005ce60001cd024c80dd634fecfa8000605436b00000000aa2dcfa182070724016f3dc0c1f039cba081d400055a1f9f9c43f46b0000003b86e4000584c27a49044000000055f211f184d8000000000000002b20000000000000000000181400000065b928000348800000000e6580004169705007480000000e20964f1fea0000f6053814630010698b4b26bc61713e00005309d8bf5f12230074c1759bee74bf46f447f8000c3d8a5fca8da518225a0008bc90ac9000000000f9f1a70000000089ad147131920d40000000c2ee0002b74f94d637726ac00000000000a6f80006c487110e02b40d5bacb99a0cb800021df13393bf40002117e317632a68899ce500b472082f93e9bdd1fd0800079c3a873e716861800088dc223de63106ad6570509017581f31de000000051e0409b21e1cc907ac023400000000000384b82b0494b07312cec83f807c0c9b19c0002982c9ac000007a40000000d78bd3d349c800022614ba400071e600010742c90015c7885926fd4c315fe040a8ded3000002226716c388000cfb8162800b06040102e28100240c782280c0800014300000c1801a04089020060016d059e0a10b0c00000853614200160d6800810195221c0000e00a8100008810a4400800101870214200000d0801e1018d14087024800282040c00002001000a50f800320104000000a00603000618810005c08c041818900080090c0018000145000c00200024008118342090800089100c080201c0000600301040008100000000034180000000012000042c00181 else (if j<2 then 0x6f68de6bd0872c8bad700000001120c000484a82c20023981d5e5f1c600004a882a90001a8bc46bf827a0ecd03093b0000000000010358000864c0001891283aa30105e8c5300000000a4af8548366331ff4866cd0000d10bf1f40001138e7b282480000000c3b364df17e8000000048c319bf8ba908c012400000000000c5678501185a16c00008c388f9cabf2826c17c997524d10b0c6e81522808000000049b591600000fed8000229887c552da3330000000181e800091a5047400061b200010eb88ad3a460000000186c3c807012e2580007609713c379a72f2484041a8304dcd5d0078be0003c16d0550001b1140c990790000000282995afa25547a84c30000c077820b4c8000029cc87bee1ec04701a8e36640c6fae61fcc29101e016d9a3e00028735ee7042600018d700000001c03000000005c1a000333f74cccde8000304eb16b000000000007807a0d0000000079cd1206c03554b000000000001cb94d1c8f34000382ef965e3a9675b0a47b9d2b566776a91000000000001cce899a5268000242a3471ab740000000000000000003b6b4932b1aac0c400034240001876ce40b8640000000000038a5172c00029928000000025512ed000061d400000005ae40ebf67c000048cb621d450f45c39e400007d98000683fc7620002bab40b5e10c0000854307f82b0000126f104192125d4c00044470000000227b0000f07c3ec400030cc0000e26b05680000000000000074a2a8c2000000022140000db990cff4fec754000250120cdb18800000003ec20000544b876acec7217208e8d7cba104e202300000000136c00009c90000a5fd4d18099e8ec000127b44ee022d141c00024075519aed561bc0001128202905758120fab1044b6d60e32e7118f4c144000134a000046648b6619b8363a655415f3d8000000000004f6b9a4d46a80002025e310000343e9fda00000000c0b00000001c1c6d2c3de400000002cea800042d000000000000f178cb9821c0000f39fe7d10d0a8a3000000028a52950d37ec6a4000000000000002f2fc607000000000000000c3b1662400011a50000e5837b8d1567a28000207900000001117a178f0a700000001646c99460acd0200006bf4217be79400051110370a20e77c0000000088100000000a59924ef01628dc0000615c000781c961683d800029b7b920000000048aa32e123b80000000f09116e400008e8000002e6188d921691962cc0004eec202343440000000962c858dc2d3475000000000000000000000000007cc4000000000001bb790ee0000000417d75dc0001d8e713d79fea6cf403286218de000248619c1e15fa6080004af8000042854ed0000f2f0000145f00006026000188b7a8d83759db40b250360001060688938df552983c7419694641000002cbe51b0235ae78c0000000 else 0x39830000c1f6000084250e0000154900439e0482dd67cb4a70000d3840000000396f720a0000000182600007a698d1b95ea63f872c00030c6c608000028f00008381f98249668cf229e84060a4d869000122ff04c1b94e87676cd3b8191514e03226030012fc550a22800000000000869000039cc0000c2894228000d2aa20ddc8043000000e396c7e8000b283231e10372d0a6462a959e0001ef0dcc5120026fa1008801b3235b6700001e24dc0dc47e9378aa6548f80008228a49c02f0000000066a1c384b19078666d1c91d13a42d40000440d179000141ee06800007296000000000006032804000058ae23ceb111dde219141f048ba859569bdb8400031e48000306000004bd80000001a1f000000003132000188cf04200000000d6f29450001855ecf10a78e2a60002d44800000000001e018000090d41992edfa438658441c00061c7e2e2000046280005410547505d99e800002390000059292cd89104470689713e23d7e04d9eb64d6000000029310000e68800000000001625400000000000f45c000224501bcaa99c3a5259d6640002444f502000190f1873ad3d0000f39))
def mo511D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1325c98b0e0c63e4c5870634a3264a33262c3831892532519931e2c3804931a2e3c9871601e3050d154e3c98b0e0286098d17262c3831922434558a71e4c5870151b262c3831c51e364c78b0e08a3a68b93163c380712982c559931e2c380a8a9b263c38b00f142e4c78b0e04c40c129a2e3c587260246464c242c5c987163c05c68ab3263c587009244860a9a2e4c38f160286098c982e4c78b0e0284860a9b263c5870129a4e0c78b0e48a449c98f161c09a290984e4c5870638a4261387263c18a290192851827263c58701433263c5870091c664c58701218664c78b0901a3060b17263c587009286060b931e2c38080d17262c78700e162e4c78b0e01840c4d17263c38b010193058b930e3c5809c98b1e1c02861217263c587010313061217263c587014304e4c78b0e01d18c2593161c03a01843263c58470c17263c58700e38305c98b0e01c364c78b0871920f12171e2c3808a7fa4fa0a9c598e9428fd8b187a84380c7c078974b7066b366e6225d65915535154d749944d4163e63b636a32c2f52b727923420b1cd18114a1130dc0a506e03e000ffecab0dffc9561bffb0c437ff65486ffecb2ebffc965d7ffb0cbafff21975ffec30ebffc861d7ffb30b2fff26165ffecbacbffc97597ffb0eb2fff61965ffe432cbffd76597ffb0ab2fff5d565ffec38cbffc87197ffb0c32fff5d865bfeca90df7d9521bfbb26437fe64086bfe4b2eb7fd961d6ffb30b2dff26165bfecbacbefd76597efb0ab2dff66065bfecb8cb77d9521afbb26435fe64086b7ecb0eb7dd931d6ff3203adef65065
def mo511H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c6d1863d2983526b152558ee0003c7ec08882700014c83592421326903b5dc086a906dc1511a2e694ad28c900010ec022b15ac1437d5c1958e010d8cb752c2c49a113aa80000000200f1ec63015b2dbbc87330f5165721ef1e236500e118066ce0134f252ca03e0048000d3563d6938c8ddd368b8daaee4e700005195aaa46eb3960f8dcf3c7000018b3334c93c53c208c66e2075325e02a106562c00020fbb203ac6a3377a82029c4370a34304e11a256eb000038d4457b24fcce3668afaa2bd63f95880f9e07382eeacb84dc3a9deb8a85861f05d05aa87f8d1c226cc2202db5b7634000418d3af617c000904086210514f7db99cdf0003c8f8154000face842eab87d123f8f07861d95c104d4fda22c000d970000000245996116d0d2440000002e080001439908c000e160000f3ac047f9c75f2a0b43b91218000ca36029913000012d404b00034deb9aa0380000000e2e000022b54a4b89a30c0000000a07400081d97b100000000002c32f116106debb96af20a91d0001e3c4ccdc000920841952e07c00028a3000066d63cce1dea10053e265374e904c77000247b0002e490328000000042447040000000000c3040003702007d6248a7013db2a12f075a157bc2fe9194e49063ca9000000000000001178000226c0000003431823a0db0002a7023d4000ad2730494ccc400001c1a728a8d61c94cdc83c4000fa40000530c435d81c000000095fd15000096f80006c7c0005496885e034c7d832c000aec87d000010b9f006d2a533c8c5f39b52da57400042fc00062ec00022f98bd30b0cd7f914000ebaa0ba746f8ffbee00009015c64a284f3a000050400000e223400004dd5af90000000f251e3e0003e5f902000023480006c9b048e8cf4c608a901f024b04e0871852000280c000282000024a0a49baad84e74cc5237b45a16e49cf0fc000f31186f21584fae5bcc1170966fc53f0000d25800000f3caaaaa4000d73092fb2a2e56256ec83fb15c16b2b34f6729ae59e1e70660000c4681ae4ed51b37ad2a3e834e279a04721189f91ea00fe1c40006b44c4aa177467d22000006c7037c2d1cc7a3a48ef35ca07f0003f1d3147642000245c336234c33d20b62294000e00a49dc0ac0e87463caec09a1e800008e10002c7262ad8062025c696a944b121e31b940e87d44a1948160ce4745078490d8e85bbb2600003c140216272100070000150002020b010c041c041009000104280a0627200d22260d0c34061f00029d1a180000010b0404002c03011000011101031109090f001a083a16040022020806060b041e120430003802131a0200080603060f000416030901
def mo511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1859228608c71853099238a18091858e48a18071a48e28601471859238a18072648e2860147fcc090603000ffd86ffc86ffd75ffc75ffd65ffc65
def mo511H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xad7b12000429000c2b000d21bd02dbfd839460be23000b13a4e40551b21800029000600031ed4100000061429b000a92204f98f86000708d161240009557840c420200c64bd103dc000e2288d0005034abd81f2a61c00000010f743007a6610d00081531fc19000b5c5500007580a810992631a62839c24fc2041d30a125faaa5bf27e0160e617e67a44395011593ad58c18011805929078ce680001003012003
def mo511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20c4100bff
def mo511H14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe0002a36994216a1840000143a22c8000198f18050
def mo511L : Nat → Packing
  | 7 => (8,7,5,0,0,6,0,mo511D7)
  | 8 => (47,6,5,0,0,9,0,mo511D8)
  | 9 => (356,5,5,0,0,13,0,mo511D9)
  | 10 => (502,4,5,0,0,15,0,mo511D10)
  | 11 => (256,3,5,0,0,14,0,mo511D11)
  | 12 => (44,2,5,0,0,12,0,mo511D12)
  | 13 => (6,1,5,0,0,8,0,mo511D13)
  | 14 => (1,0,5,0,0,0,0,mo511D14)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 2 11 0 7 3 0 mo511H8
  | 9 => lookupWord 19 107 7 12 6 2 mo511H9
  | 10 => lookupWord 147 1481 5 15 9 2 mo511H10
  | 11 => lookupWord 206 1223 7 15 9 2 mo511H11
  | 12 => lookupWord 99 491 8 14 8 2 mo511H12
  | 13 => lookupWord 20 97 6 12 6 2 mo511H13
  | 14 => lookupWord 3 17 5 9 3 2 mo511H14
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,14,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P7_0 : block mo511 7 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B7 : block mo511 7 0 8=true := mo511P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P8_0 : block mo511 8 0 47=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B8 : block mo511 8 0 47=true := mo511P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_0 : block mo511 9 0 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_96 : block mo511 9 96 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_97 : block mo511 9 97 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_193 : block mo511 9 193 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P9_289 : block mo511 9 289 67=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B9 : block mo511 9 0 356=true := (@block_merge mo511 9 0 97 259 (@block_merge mo511 9 0 96 1 mo511P9_0 mo511P9_96) (@block_merge mo511 9 97 96 163 mo511P9_97 (@block_merge mo511 9 193 96 67 mo511P9_193 mo511P9_289)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_0 : block mo511 10 0 22=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_22 : block mo511 10 22 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_118 : block mo511 10 118 54=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_172 : block mo511 10 172 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_268 : block mo511 10 268 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_364 : block mo511 10 364 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P10_460 : block mo511 10 460 42=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B10 : block mo511 10 0 502=true := (@block_merge mo511 10 0 172 330 (@block_merge mo511 10 0 22 150 mo511P10_0 (@block_merge mo511 10 22 96 54 mo511P10_22 mo511P10_118)) (@block_merge mo511 10 172 192 138 (@block_merge mo511 10 172 96 96 mo511P10_172 mo511P10_268) (@block_merge mo511 10 364 96 42 mo511P10_364 mo511P10_460)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_0 : block mo511 11 0 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_10 : block mo511 11 10 59=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_69 : block mo511 11 69 96=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_165 : block mo511 11 165 3=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P11_168 : block mo511 11 168 88=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B11 : block mo511 11 0 256=true := (@block_merge mo511 11 0 69 187 (@block_merge mo511 11 0 10 59 mo511P11_0 mo511P11_10) (@block_merge mo511 11 69 96 91 mo511P11_69 (@block_merge mo511 11 165 3 88 mo511P11_165 mo511P11_168)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_0 : block mo511 12 0 7=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_7 : block mo511 12 7 13=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P12_20 : block mo511 12 20 24=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B12 : block mo511 12 0 44=true := (@block_merge mo511 12 0 7 37 mo511P12_0 (@block_merge mo511 12 7 13 24 mo511P12_7 mo511P12_20))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P13_0 : block mo511 13 0 6=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B13 : block mo511 13 0 6=true := mo511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511P14_0 : block mo511 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem mo511B14 : block mo511 14 0 1=true := mo511P14_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem mo511T : checkedTables mo511 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : block mo511 0 0 0 = true)
  · exact (rfl : block mo511 1 0 0 = true)
  · exact (rfl : block mo511 2 0 0 = true)
  · exact (rfl : block mo511 3 0 0 = true)
  · exact (rfl : block mo511 4 0 0 = true)
  · exact (rfl : block mo511 5 0 0 = true)
  · exact (rfl : block mo511 6 0 0 = true)
  · exact mo511B7
  · exact mo511B8
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
  exact root_index (g:=mo511) (top:=14) (i:=0) (before_sound KM503 VM503) mo511G mo511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_11008
open PEqualNP.Outside.L_meta_11008 in
theorem PEqualNP.Outside.L_meta_11008 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 4 && x 8) || (x 6 && x 8)) t → 15 ≤ t := by
  intro t hs
  by_contra! small
  obtain ⟨C,hf,hsize,heq⟩ := hs
  exact directSplit mo511R g511R ⟨C,hf,by omega,heq⟩
