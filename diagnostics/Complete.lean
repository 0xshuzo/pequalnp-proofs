import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_11028.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_11028
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
def graph : Sig := 0xfffffffffffffffffffffffefffffffcfffffffffffffffffffefffafffefff0fffffffefffffffefffffefefffffcfcfffefffaffeeffaafefefafaeeee0000
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 6 &&& x 8)
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


abbrev Bits := BitVec 448
abbrev Signals := Bits × Bits
abbrev Decor := Sig × Signals

def ofRows {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn
theorem ofRows_bit {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (ofRows r v).getLsbD i.val = bit (r i) v := by
  simp only [ofRows,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]
def pairSig (r s : Fin 448 → Row) (a : Sig) : Signals := (ofRows r a,ofRows s a)
def properPairs (T : Sig) (r s : Fin 448 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false
theorem pair_sep {T r s} (h : properPairs T r s) : Sep T 448 r s (pairSig r s) := by
  exact ⟨h,fun a i => ⟨ofRows_bit _ _ _,ofRows_bit _ _ _⟩⟩
def faithful (r s : Fin 448 → Row) (x : Decor) := x.2 = pairSig r s x.1
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

def asRow (cols : Nat → Bits) (i : Fin 448) : Row :=
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
theorem asRow_bit (cols : Nat → Bits) (i : Fin 448) (j : Fin 9) :
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
  (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 2 &&& x 8) ||| (x 3 &&& x 8) ||| (x 6 &&& x 8)
theorem bit_vertex (m : Nat) (v : Nat → Bits) (i : Fin 448) (j : Fin 9) :
    bit (asRow v i) (vertex m j.val) =
    ((if m.testBit j.val then v j.val else 0) : Bits).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [vertex,hh] using asRow_bit v i j
  · simp [vertex,hh,bit_zero]
theorem bit_liftGoal (m : Nat) (v : Nat → Bits) (i : Fin 448) :
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
    if (rs ||| column d z.2) != BitVec.allOnes 448 then true else
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 448) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 448 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
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
theorem chart_bit (m : Nat) (v : Nat → Bits) (i : Fin 448) :
    bit (asRow v i) (chartGoal m) = (chartSamples m v).getLsbD i.val := by
  exact bit_liftGoal m v i
theorem chart_pairs {m : Nat} {p q : Nat → Bits}
    (hp : chartSamples m p = BitVec.allOnes 448) (hq : chartSamples m q = 0) :
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
  (chartSamples g.mask (fun j => (g.samples j).1) == BitVec.allOnes 448) &&
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
def lanePlace (v : Nat) (upper : Nat) := 2^449*upper+v
def combineLanes {α : Type} (f : α → Bits) : List α → Nat
  | [] => 0
  | x::xs => lanePlace (f x).toNat (combineLanes f xs)
def units : Nat → Nat
  | 0 => 0
  | n+1 => lanePlace 1 (units n)
theorem laneSmall (x : Bits) : x.toNat < 2^449 :=
  lt_trans x.isLt (by decide +kernel)
theorem place_and (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u &&& lanePlace b.toNat v = lanePlace (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<449 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]
theorem place_or (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ||| lanePlace b.toNat v = lanePlace (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<449 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]
theorem place_xor (a b : Bits) (u v : Nat) :
    lanePlace a.toNat u ^^^ lanePlace b.toNat v = lanePlace (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [lanePlace,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (laneSmall _)]
  by_cases h : i<449 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]
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
def fullMarks (r packed : Nat) := ((packed+r) >>> 448) &&& r
theorem unit_bit (n i : Nat) (hi : i<n) : (units n).testBit (449*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [units,lanePlace,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^449)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 449*(i+1)-449=449*i := by omega
      have ge : ¬449*(i+1)<449 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)
set_option maxRecDepth 8192 in
theorem guardBit (a : Bits) : (a.toNat+1).testBit 448 = (a==BitVec.allOnes 448) := by
  by_cases h : a=BitVec.allOnes 448
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^448-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^448 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm

set_option maxRecDepth 8192 in
theorem mark_at {α} (f : α → Bits) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (fullMarks (units xs.length) (combineLanes f xs)).testBit (449*i) =
      (f xs[i]==BitVec.allOnes 448) := by
  simp only [fullMarks,Nat.testBit_and,Nat.testBit_shiftRight,unit_bit _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [combineLanes,List.length_cons,units,lanePlace]
    have sum (u v x : Nat) : 2^449*u+x+(2^449*v+1)=2^449*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^449 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using guardBit (f a)
    | succ i =>
      have ge : ¬449*(i+1)+448<449 := by omega
      have di : 449*(i+1)+448-449=449*i+448 := by omega
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
    ((mask &&& 1 == 0) || f x) && onMarks f (mask >>> 449) xs
theorem marked_ok {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (449*i)=true) (ok : onMarks f mask xs=true) : f xs[i]=true := by
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
      apply ih (mask:=mask >>> 449) (i:=i) (by simpa using hi) _ ok.2
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
      if len>k then true else if combField xs[q] (!u) ka kb op i j != BitVec.allOnes 448 then true
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
    by_cases hit : combField xs[q] (!u) ka kb op i j = BitVec.allOnes 448
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

def neighbor11028 (i : Fin 9) : Nat := [4, 4, 5, 6, 0, 0, 0, 1, 2].getD i.val 0
def absentRow11028 (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< neighbor11028 i)
def presentRow11028 (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< neighbor11028 i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 9, bit (absentRow11028 i) graph ≠ bit (presentRow11028 i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (absentRow11028 i) (inputs.getD j.val zero) =
      bit (presentRow11028 i) (inputs.getD j.val zero)) := by decide +kernel


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
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow11028 i) (presentRow11028 i)
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

theorem signedTrace (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 9 C = edge) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (u:=true) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal (by simp) graph_proper
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
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow11028 i) (presentRow11028 i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

def sl7 (a0 a1 a2 a3 a4 a5 a6 : Nat) : Bits := BitVec.ofNat 448 ((a0 <<< 0) ||| (a1 <<< 64) ||| (a2 <<< 128) ||| (a3 <<< 192) ||| (a4 <<< 256) ||| (a5 <<< 320) ||| (a6 <<< 384))
def sL0 : Nat := 0x3fffffffffff
def sL1 : Nat := 0xffffffffffffff
def sL2 : Nat := 0x7ffffffffffffff
def sL3 : Nat := 0xa28504012071049
def sL4 : Nat := 0xfffffffffffffff
def sL5 : Nat := 0x2049204920492049
def sL6 : Nat := 0x4092409240924092
def sL7 : Nat := 0x4c326089204368db
def sL8 : Nat := 0x8124812481248124
def sL9 : Nat := 0x9040851240088724
def sL10 : Nat := 0xe083060384982db6
def sL11 : Nat := 0xf63ff63ff63ff63f
def sL12 : Nat := 0xf800000000000000
def sL13 : Nat := 0xfbc7fbc7fbc7fbc7
def sL14 : Nat := 0xfdf8fdf8fdf8fdf8
def sL15 : Nat := 0xff03fffff8f71fc7
def sL16 : Nat := 0xfffc07e3ff0be838
def sL17 : Nat := 0xfffff803ffeee63f
def sL18 : Nat := 0xfffffffc00000000
def sL19 : Nat := 0xfffffffc00193dc0
def sL20 : Nat := 0xffffffffc0000000
def sL21 : Nat := 0xffffffffff800000
def sL22 : Nat := 0xffffffffffc00000
def sL23 : Nat := 0xffffffffffe00000
def sL24 : Nat := 0xfffffffffffc0000
def sL25 : Nat := 0xfffffffffffe0000
def sL26 : Nat := 0xfffffffffffff800
def sL27 : Nat := 0xfffffffffffffe00
def sL28 : Nat := 0xffffffffffffffc0
def sL29 : Nat := 0xfffffffffffffff8
def sL30 : Nat := 0xfffffffffffffffe
def sL31 : Nat := 0xffffffffffffffff
def sR0 : Bits := 0x45c94e4bcb285413844750003ffffe00000
def sR1 : Bits := 0x8b9a4e4bcb285c13a44750003fff0000000
def sR2 : Bits := 0x2754920534ad14b58f8813fffff800000000
def sR3 : Bits := 0x33aa420534ad14b5cf8813fffc0000000000
def sR4 : Bits := 0x48b9a4e4bcb285e17a4455000007f0000000
def sR5 : Bits := 0x6754920534ad14b5cf8813fffc0000000000
def sR6 : Bits := 0x4ea924f70cd3e0baf803a80ffff0000000000
def sR7 : Bits := 0x915349287c9ef0209eca5cc0000ffff000000
def sR8 : Bits := 0x3265c62f04071c388415e061978650913580ffe00000000000ffffc0000
def sR9 : Bits := 0x449a8596e90f20c6b1516200501d0256e86700000007ffffff000000000
def sR10 : Bits := 0x33b481810199052c9c32a5d2849abb11c02703ffffff8000000000000000
def sR11 : Bits := 0x58c775f0c81ad0c6107fa8c30d96300d09c27ff800000000007ff00000000000
def sR12 : Bits := 0x1936a52ce9099033fc550b45031181042a831800000ffffffff80000000000000
def sR13 : Bits := 0x76018cf4912109835ab4398a38a4678927f1a00000000000000000fffffc00000
def sR14 : Bits := 0xced20222199622b270da64a1083af831e6a663fffff0000000000000000000000
def sR15 : Bits := 0x6ec9da86114d3630c40a9a8181b38a235040475fff0000000001ffffff8000000000
def sR16 : Bits := 0x8b3696e4a18d80ceb3476adc2641c090128a2d80000007fffffe0000000000000000
def sR17 : Bits := 0x3c2b42338e5486405688539d1a136ebd6387d99200000000000000000007ffc000000
def sR18 : Bits := 0x674920d3cd3744ac98374249c402836ae2930685ffffff80000000000000000000000
def sR19 : Bits := sl7 0x9b45573c000f8000 0x45e 0 sL26 sL31 sL1 0
def sR20 : Bits := 0x7fffffffffffffffffffffff00000000001ffffffffffffffffffe000000000000000508339d4022db3c4743ab501fc000fe00000
def sR21 : Bits := 0x1ffffffffffffe00000000003fffffffffffffffffff0000000000000003ffffffffffa41303ed1b46c0aa358d9e0003f80000007f
def sR22 : Bits := 0x43f00000021f80000021f80000021f8000001e000003c00001060c22a000504088411a021150600013480c582c160b0582c160b0582c
def sR23 : Bits := 0x4fc00013c00013e00009f00009f00009f0001c0004fc00027e00027e00027e0003c001e000110e8bc02a60e022248c1c3870e1c3870e
def sR24 : Bits := 0xb00b1c00016016380002c02cbc00404f001013c4010101b32220953e1081410b90054518901a90a067033819c0ce067033819c0ce067
def sR25 : Bits := 0x14580001160000c58000214001280005160000a3000052c00014500048001280005080023000604180100a21a603862060c183060c183
def sR26 : Bits := 0x303f000000607e000000c0fc000010f000043c0004a40da00014d200044029a0001928a21404003409804c026013009804c0260130098
def sR27 : Bits := 0x8030f0000401870000401870000401878000011800002300002440222880644100480885118017242009109148a45229148a45229148a
def sR28 : Bits := 0x160b800000b03800000b03800000b05e00020f000107801c04000220297440102800276051096190c800380700e01c0380700e01c03807
def sR29 : Bits := 0x1617800582e001617000b05c010b000b0bc021700160b800581c002c0e00160bc020f0083c1083215402098304743a950e1c3870e1c387
def sR30 : Bits := 0x3070000c1c000c1c00060e00060e00060e000460030700018380018380018380008c0046000044842424b2840138001491224489122448
def sR31 : Bits := 0x307c00000183e00000183e00000183e0000008e000011c0000000988496490a2002a140600050080254606026130984c26130984c26130
def sR32 : Bits := 0x3e0828c22050d00019a0090257369b02610c02802444404cd833c992534248030f030f030f030f030f030f030f030f030f030f030f030f
def sR33 : Bits := sl7 0 0xffff0000 0xffff00000000 0x4cd8b3c99a5f66c8 0x12650c02852444c1 0x2099a2090677769b 0x3e1828c33050d0
def sR34 : Bits := 0x3f80000001fc0000001fc0000001fc0000000f000001e00000222081010099012c1412a410000a131140260381c0e070381c0e070381c0
def sR35 : Bits := 0x3f80000fe0000fe00007f00007f00007f000078003f80001fc0001fc0001fc0000f0007800338a4004348514058c8013e1c3870e1c3870
def sR36 : Bits := 0x3ffffffffffff0000007fffff8000007fffff80003fffffffffffe000001ffffffffff8000140d310fe314086c85bae70000000fe03f80
def sR37 : Bits := 0x3fffffffffffffffffe000000001fffffffffffffffe00000021809336356892dc51e180acc25c05d4b922d400000000001ff00003fe00
def sR38 : Bits := sl7 0x803fe00000000000 0x2892cc00740000ff 0x4410e64b58c5bb75 0x345a76831321 0 sL27 0x3fffffffffffff
def sR39 : Bits := 0x63e00018f800063e00018f8004700031f800063f00031f8000c7e0011e004780031f8008f004e61e8ac28264402024861c3870e1c3870e
def sR40 : Bits := 0x804465a480b1620360062dc58446021386436091a62100208a09ba3b048b10b6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6cc
def sR41 : Bits := sl7 0xffffffff00000000 0 0 0x20ea59fa3b048b14 0x33865b6091a62120 0x3688fefc5844e02 0x844467a688b162
def sR42 : Bits := 0x98180026130009858004c260022c004c2c0045800984c002612001309000984c004480112048a1003a21880000c095b02850a142850a14
def sR43 : Bits := 0x984c009004c24009004c24009004c2600804480402240808902481543b0410100b02011002c4b0132008a1142284508a1142284508a114
def sR44 : Bits := 0xc0c1041851092164201266c40040004114c0500051228902014c3004082092f800f800f800f800f800f800f800f800f800f800f800f800
def sR45 : Bits := sl7 0xffff0000 0xffff00000000 0 0xae70064c52b3184a 0x50bba35706021f86 0x5a714b6860e9f43 0x120041406380747
def sR46 : Bits := 0x1448948240011488200734111a1004c01010490d050204031000980048ee010c700c700c700c700c700c700c700c700c700c700c700c700
def sR47 : Bits := sl7 0 0xffffffff00000000 0xffff 0x31080984158fe810 0xd0184d0d050355e 0x8604734111a1204d 0x1678b49240653e8
def sR48 : Bits := 0x2003691050aa20801c4041019a00024300812811d8a01108000800268a4942004f004f004f004f004f004f004f004f004f004f004f004f0
def sR49 : Bits := 0x202521181658024401800008804a0a08a5e500008864019400e02128900030520aa20aa20aa20aa20aa20aa20aa20aa20aa20aa20aa20aa
def sR50 : Bits := sl7 0 0xffffffff 0xffff000000000000 0xc091a4126eb49438 0x704812891dce8150 0x1e7441059a10034 0x20836914d0bb608
def sR51 : Bits := 0x240024c20048004984009000930c01004880401220010212200c86003810400930080b83850861080c41420a105082841420a1050828414
def sR52 : Bits := sl7 0 0 0xffffffffffff0000 0x86014c31a44820d2 0xc114c2518af92289 0x74201266e6da408e 0x2c0e10c98510921
def sR53 : Bits := 0x2cb21e243ee4890915ea094281a9381a448598d760130300a3680c70001524e00000000ffff0000ffff000000000000ffff000000000000
def sR54 : Bits := 0xa03960280a580a02960280b58202b05016580a02c405016301405960809c20270501650404a241203290b06c02224899e2c58b162c58b16
def sR55 : Bits := 0x1382c38fc02705871f804e0b0e3f002088f008223c00c2a02338e5486405688539d1a136abd638598916deb6f5b7adbd6deb6f5b7adbd6de
def sR56 : Bits := 0x14e06005381c014e0600a7038014300a70300286014e07005381c029c0e014e070028700a1c044201e8bd4a2644180042ab162c58b162c58
def sR57 : Bits := 0x14e07004e0a703804e0a703804e0a70380104870082438056010c74912108015ab4398808a0670922f122dc5b8b716e2dc5b8b716e2dc5b8
def sR58 : Bits := 0x18ff800000c7fc00000c7fc00000c7fc00008f800047c00018c665d0401890c4107da8c30d923001014201f03e07c0f81f03e07c0f81f03e
def sR59 : Bits := 0x18ff80063fe0018ff800c7fc0027c00c7fc004f8018ff80063fe0031ff0018ff8004f8013e0048b1a4e4bca205c16a4455bd7af5ebd7af5e
def sR60 : Bits := 0x1c03fc00003807f80000700ff0000041f000107c00000b1494a4018c804eb14728dc2641408010082518e0c7063831c18e0c7063831c18e0
def sR61 : Bits := 0x1f00000700f80000700f80000700f8000020f00010780000826a524c8080032fc5503010010010020811310620c4188310620c4188310620
def sR62 : Bits := 0x1f000007c00001f00000f8000038000f8000070001f000007c00003e00001f0000070001c00027541200142410a10a0002c183060c183060
def sR63 : Bits := 0x1ffc0000003ff80000007ff00000007e00001f8000023492040cd0104ac183742494402830862920681f00f807c03e01f00f807c03e01f00
def sR64 : Bits := 0x1ffffffffffffe000000ffffffc0000fffffffffffffffff8000003ffffffffffff80001ffffbe2d6552da519822172148000007f01fc07f
def sR65 : Bits := 0x2108014842005210801484200211001084005210802908400a421000844021100108400422000108e04000690b9801104142850a142850a1
def sR66 : Bits := 0x2aa5200aa9480aa9480554a40154a40254a4029140525200552900d5290095290052280b14050ec4a14026458a13808851a3468d1a3468d1
def sR67 : Bits := 0x2aa52800aa5529400aad529400aa952940055522402aac4805552c01c1c153d00b05712a642462828dac840092a351a8d46a351a8d46a351
def sR68 : Bits := 0x3306028cc1810cc1814660c02260c06360c0432204986028983014983014d83014644092204994093109c204086c81aa63264c993264c993
def sR69 : Bits := 0x3c0002caf0e000164f0e000164f0e0001657878008f0f0011e1e1452768213204410c04958c5ba7528828800741e0f0783c1e0f0783c1e0f
def sR70 : Bits := 0x420001520a10003520a10002520a100014822002c11001420029180208446a2a4400042c40290a08c085520a4148290520a4148290520a41
def sR71 : Bits := 0x4200055080005420006a1000128001a1000290002820001508001a84000942000290002c000a320c41000251982215200042850a142850a1
def sR72 : Bits := 0x482828001a905050002520a0a00029042002c10800a7041e04420012805a80284426560140080024542921490a485242921490a485242921
def sR73 : Bits := 0x4c52181314c604c53181314c60424c26298604c5308262984098a6181091042442629860848c18211b22308250658cc698b972e5cb972e5c
def sR74 : Bits := 0x501d810010100c912802f942204209584020840862409c641e61504100132008490149014901490149014901490149014901490149014901
def sR75 : Bits := 0x707c001c1f000707c001c1f0008780383e000707c00383e000e0f80021e008780383e0010f0008a9a0c4b4b005c11a4401d1a3468d1a3468
def sR76 : Bits := 0x7f80001fe00007f80001fe0000f8003fc00007f80003fc0000ff00003e000f8003fc0001f00063108005342d10a58f8011e1c3870e1c3870
def sR77 : Bits := 0x7ffffffffffffffffffffffffffffffffffff8000003ffffffffffffc0000fffffffffffffffb98ae94063697bd80511410000000fe03fff
def sR78 : Bits := 0x8000001ffffff8000001ffffff00003ffffffffffffc000000fffffffffff00003fffffe0000412e841a8114a21e6afaea01fc07f01fc000
def sR79 : Bits := 0x804522604c02292604c02293604c02291904012482009265150489202900688028848d4a6e6c2a01a440c658cb19632c658cb19632c658cb
def sR80 : Bits := 0x8045466011489804504c02291b0092c0228320124c045226011493008a4d8045232012480493000ae901c802cd5c256201162c58b162c58b
def sR81 : Bits := 0x8130012293026002453604c0048a3208022482008934e042005b200110004a3840215906852749a748230b1858c2c61630b1858c2c61630b
def sR82 : Bits := 0x982004040218060305a704b6060a1f0350a0a34706001f868e70044c5231184a185518551855185518551855185518551855185518551855
def sR83 : Bits := 0xb30600a0cc9830050cc9830050ccd83005066644044cc8808999a1801114116810cc516100acc25c0590b920d48a45229148a45229148a45
def sR84 : Bits := 0xbc000b2f0003af00039780014b80014b80016bc00ae000b2e00058e00058e0005978013c009e0c2113d80a0063f0411e800e1c3870e1c387
def sR85 : Bits := 0xc000300cff0001806ff0001806ff00018067f800817f00102fe01cc032d40542228343ac41c50ca480a00491c026130984c26130984c2613
def sR86 : Bits := 0xc0080c3002023002021801018c01018c01018c00130080c30040610040610040618002200110013048121100518006558048912244891224
def sR87 : Bits := 0xe0000000003fffffffffffffffffff8000001fffffff0c1e644a0c1a805ee8a8442656957089a064d420000000000000000ffffffc001fff
def sR88 : Bits := 0xe0000007ff0000007ff0000007ff0000003f00001f80000ce120022199420b230d824210822c821e6a243e07c0f81f03e07c0f81f03e07c0
def sR89 : Bits := 0xe0000007ffffffffffff00000000000ffffff80001ffffffffffffc000001ffffffffffe0000219ae929cd02cd5c2576030003f800003f80
def sR90 : Bits := 0xe20b2082432e4090101e8090281a9181a448180d26001030083480450001104c003300330033003300330033003300330033003300330033
def sR91 : Bits := sl7 0xffff0000ffff 0xffff 0 0x1e65596100333129 0x422084286240dc64 0x6a12fd4a29420d78 0xfc1dc1841010ac9b
def sR92 : Bits := sl7 0xffffffff 0 0xffff 0x590e021ac9008305 0x8bfe740628964a19 0x481800319804b1a0 0xfe12de11b1658035
def sR93 : Bits := sl7 0xff8000000 0x82a014bdc801ff00 0x22a353ec4bc50ca6 0x1cc232d40552 0 0 0xffc0000000000000
def sR94 : Bits := sl7 0x9001fc07f0000000 0x13d80a04e3f0791e 0x3da1 sL27 0xf80000000003ffff 0x7ffffffffff 0xffc0000000000000
def sR95 : Bits := sl7 0x99000000001fff80 0x3b3a308358678cf6 0xfc00000000001821 sL31 sL31 63 0xffffffe000000000
def sR96 : Bits := sl7 0xb0fe000000003fff 0x33a21ca4909c8d7 0xffffffffffffdae1 sL31 0x1ffffff 0 0xfffffff800000000
def sR97 : Bits := 0xfffffff8000000007fffffffffffffffffc000001ffffff220691f524e446aeae40804ac42298aa9c285400000000000007ff001ffc007ff
def sR98 : Bits := sl7 0x59000000001fc07f 0xad506645fa138089 0xffff00007fffcec5 0xfe000001ffffffff sL31 sL31 0xfffffffff000000f
def sR99 : Bits := sl7 0x3ffe000 0x4920000000003ffe 0xe1615d068d674daf 0x845b608111024a78 0xffffe0000004f142 0x7fffffffffff sL22
def sR100 : Bits := sl7 0x7fc01ff 0x8dae854094000000 0xb05712a64357282 0xffffec01cdc1d3d6 0xfffffff0000001ff 0x1fffffffffff sL25
def sR101 : Bits := 0xffffffffffffffff8000000007ffffffffffffffe000000d9584892129806c813c949d4a6e6c7e01a541c00000000003ff800000003ff800
def sR102 : Bits := sl7 0x5dc49781bff00000 0x33aa 0 0 0 0xff00000000000000 sL31
def sR103 : Bits := sl7 0xfff0000000000000 0x92a000fff8000001 0x5d0fd10d451cd11a 0x1b32220fd3f1587 0x40101 0xffff800000000000 sL31
def sR104 : Bits := sl7 0x800003f800003fff 0xc93a15435d8c06f7 0xffffffffffffc930 sL31 0x3ffff 0xfffff80000000000 sL31
def sR105 : Bits := sl7 0xffe00000000 0x90d80007ff001ffc 0x13296237e8710971 0x1e14c0022169f648 4 0xfffffffff8000000 sL31
def sR106 : Bits := sl7 0x33aa61bff8000 0xffff800000000000 sL31 0xffc0007fffffffff 0x19d530d sL22 sL31
def sR107 : Bits := sl7 0x86fe00000fe00000 0x5e8bc6aa6761a024 0x6e6 0 0 sL28 sL31
def sR108 : Bits := sl7 0xae0000000fffc000 0x5e8bd6a26643e024 0x4426 0 0xfffffffffe000000 sL31 sL31
def sR109 : Bits := sl7 0x3ffffff 0xa0c0000007ffc000 0x9332bafa39508e11 0x3201c87283c11431 0xfffffffffff81261 sL31 sL31
def sR110 : Bits := sl7 0x8efe0000001fc000 0x6e8bc2aa62e3a224 0x253 0 sL24 sL31 sL31
def sR111 : Bits := sl7 0x3fffff 0x1724000000ffe000 0x58cb030d5402e6b2 0x8b6248d743f0510 sL29 sL31 sL31
def sR112 : Bits := sl7 0x7fc000000003ffff 0x72e2029188000000 0x4c50049ca8597a45 0xffffca45032e88ae sL31 sL31 sL31
def g146Y : Array Signals := #[(0,0),((sl7 sL11 sL11 sL11 sL11 sL11 sL11 sL11),(sl7 sL5 sL5 sL5 sL5 sL5 sL5 sL5)),(0,0),(0,0),((sl7 sL13 sL13 sL13 sL13 sL13 sL13 sL13),(sl7 sL6 sL6 sL6 sL6 sL6 sL6 sL6)),(0,0),(0,0),((sl7 sL14 sL14 sL14 sL14 sL14 sL14 sL14),(sl7 sL8 sL8 sL8 sL8 sL8 sL8 sL8)),(0,0)]
def g146C : List ColumnInfo := []
def g146A : List (List Nat) := [[],[116],[65],[65,113],[113,65],[113]]
def g146D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
def g146L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g146D3)
  | _ => emptyPacking
def g146I (_ _ : Nat) : Option (Nat × Nat) := none
def g146 : Forest := ⟨146,3,fun i => g146Y[i]?.getD (0,0),g146C,g146A,g146L,g146I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g146P3_0 : block g146 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g146B3 : block g146 3 0 1=true := g146P3_0
theorem g146T : checkedTables g146 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g146B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g146G : graphValid g146 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low146 : Lower true (varsX 146) (graphGoal 146) 4 := lower_forest (g:=g146) (i:=0) (hints:=268501056) (before_sound [] baseKnown) g146G g146T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K146 := extendKnown [] 4 [(146,[]),(328,[49,33,100,84,135])]
set_option maxRecDepth 32768 in
theorem V146 : Known true K146 := extend_ok (m:=146) baseKnown low146 (by decide +kernel)
def g51Y : Array Signals := #[((sl7 sL15 sL15 sL15 sL15 sL15 sL15 sL15),(sl7 sL3 sL3 sL3 sL3 sL3 sL3 sL3)),((sl7 sL16 sL16 sL16 sL16 sL16 sL16 sL16),(sl7 sL7 sL7 sL7 sL7 sL7 sL7 sL7)),(0,0),(0,0),((sl7 sL17 sL17 sL17 sL17 sL17 sL17 sL17),(sl7 sL9 sL9 sL9 sL9 sL9 sL9 sL9)),((sl7 sL19 sL19 sL19 sL19 sL19 sL19 sL19),(sl7 sL10 sL10 sL10 sL10 sL10 sL10 sL10)),(0,0),(0,0),(0,0)]
def g51C : List ColumnInfo := []
def g51A : List (List Nat) := [[],[64,81]]
def g51D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
def g51L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g51D3)
  | _ => emptyPacking
def g51I (_ _ : Nat) : Option (Nat × Nat) := none
def g51 : Forest := ⟨51,3,fun i => g51Y[i]?.getD (0,0),g51C,g51A,g51L,g51I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51P3_0 : block g51 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g51B3 : block g51 3 0 1=true := g51P3_0
theorem g51T : checkedTables g51 3 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · exact g51B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K146) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K146 V146) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K146 4 [(51,[]),(53,[33,84]),(83,[101]),(89,[49,33,100,84]),(101,[33,84,100]),(105,[49,33,100]),(149,[112,16,33,82,101]),(165,[32,16,84,116,100]),(177,[64,81,33,50,115,99]),(180,[32,65,49,115,99]),(209,[64,97,33,50,117]),(325,[128,16,33,100,82,117]),(337,[96,65,33,50,48,133,117]),(404,[32,65,49,115,133,99,101]),(452,[32,97,49,132,117,84])]
set_option maxRecDepth 32768 in
theorem V51 : Known true K51 := extend_ok (m:=51) V146 low51 (by decide +kernel)
def g147Y : Array Signals := #[(0xffc07e3e7e3f8801ff80fc7cfc7f1003ff01f8f9f8fe2007fe03f1f3f1fc400ffc07e3e7e3f8801ff80fc7cfc7f1003ff01f8f9f8fe2007,0xdb2a5148544878adb654a290a890f15b6ca945215121e2b6d9528a42a243c56db2a5148544878adb654a290a890f15b6ca945215121e2b6d),(0xf1fff803fffc4f87e3fff007fff89f0fc7ffe00ffff13e1f8fffc01fffe27c3f1fff803fffc4f87e3fff007fff89f0fc7ffe00ffff13e1f8,0x9230619080810b892460c3210102171248c1864202042e2491830c8404085c49230619080810b892460c3210102171248c1864202042e249),(0,0),(0,0),(0x7ffffffc07ffb978fffffff80fff72f1fffffff01ffee5e3ffffffe03ffdcbc7ffffffc07ffb978fffffff80fff72f1fffffff01ffee5e3f,0x2440820101000012488104020200002491020804040000492204100808000092440820101000012488104020200002491020804040000492),(0,0),(0,0),(0x81fffffff80066ff03fffffff000cdfe07ffffffe0019bfc0fffffffc00337f81fffffff80066ff03fffffff000cdfe07ffffffe0019bfc0,0x4983040206126464930608040c24c8c9260c1008184991924c18201030932324983040206126464930608040c24c8c9260c1008184991924),(0,0)]
def g147C : List ColumnInfo := [(1,0,146,0,4)]
def g147A : List (List Nat) := [[],[113]]
def g147D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g147L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g147D4)
  | _ => emptyPacking
def g147I (_ _ : Nat) : Option (Nat × Nat) := none
def g147 : Forest := ⟨147,4,fun i => g147Y[i]?.getD (0,0),g147C,g147A,g147L,g147I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147P4_0 : block g147 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g147B4 : block g147 4 0 1=true := g147P4_0
theorem g147T : checkedTables g147 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g147B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147G : graphValid g147 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=268435524) (before_sound K51 V51) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K51 5 [(147,[]),(150,[32,116]),(329,[49,33,100,84,135])]
set_option maxRecDepth 32768 in
theorem V147 : Known true K147 := extend_ok (m:=147) V51 low147 (by decide +kernel)
def g55Y : Array Signals := #[(0xfff800ffffff001ffe03fffffff001fffffc07fe9c3590787fffc001fff001fff001fffffe003ffc07ffffffe003fffff80ffd386b20f0f,0xa0550aa0aa02a0d409468291402a0d4128148b14898251088882a81540aa1540aa1541540541a8128d052280541a82502916291304a21111),(0xffffff000fffffe00003ff80fffffe003ffff80d1bea400787fffffe000001fffffe001fffffc00007ff01fffffc007ffff01a37d4800f0,0xc4660cc8cc44c0988d8b0322644c4989b1191226c1ae242aaaa3311988cc9988cc1991988981311b160644c89893136232244d835c485555),(0xf000000000ffffffffffc0000ffffffffc0000001fa03ef8007fffffffffffe000000001ffffffffff80001ffffffff80000003f407df000,0x1782f02f01702e02e0c0bc381700e01c05e1c3819a03a99998bc05e02f01e02f05e05e02e05c05c18178702e01c0380bc38703340753333),(0,0),(0xffffffffff000000000000000fffffffffffffff331fbb007ffffffffffffffffffffffe000000000000001ffffffffffffffe663f7600ff,0x980300300980b0130102c04098090120260000032118a55554c02601300201300600601301602602058081301202404c00000642314aaaa),((sl7 0x19dd38dff00 0xffffffe000000000 sL31 0x807fffffffffffff 0xcee9c6ff 0xfffffffff0000000 sL31),0xe00400c00e00c01c00030000e00e01c0380204046498466667003801c00c01c00801801c01803800060001c01c038070040808c9308cccc),(0,0),(0,0),(0,0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[33,84]]
def g55D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
def g55L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g55D4)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,4,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : block g55 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : block g55 4 0 1=true := g55P4_0
theorem g55T : checkedTables g55 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K147 V147) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K147 5 [(55,[]),(109,[33,49,84,100]),(167,[32,16,84,116,100]),(213,[64,33,97,49,112,80]),(217,[49,114,100,84,82]),(453,[128,16,114,49,100,82,67,84])]
set_option maxRecDepth 32768 in
theorem V55 : Known true K55 := extend_ok (m:=55) V147 low55 (by decide +kernel)
def g115Y : Array Signals := #[(0xfffffe001fffffffffffe001fffffffffffc01fffd6a9bfc7fffc003ffffffffffffe001fffffffffffe001fffffffffffc01fffd6a9bfc7,0x5001401400a00200001401400a002000008040080420b249002802801400a005001401400a00200001401400a002000008040080420b249),(0x7fffffe000fff007fffffe000fff007ffffe00169f6d038ffffffc001fff0007fffffe000fff007fffffe000fff007ffffe00169f6d038,0x262498898a4c42429249891894c484252490904a140f4d6db493093249824c5262498898a4c42429249891894c484252490904a140f4d6db),(0,0),(0,0),(0x7fffffffff000007fffffffff000007fffffff2b97e603ffffffffffe0000007fffffffff000007fffffffff000007fffffff2b97e603f,0x4849211210909485249212212109284a492120902b90a09249241240921490a4849211210909485249212212109284a492120902b90a0924),((sl7 0x1369f81c0 0x7ffffffffffffff8 sL12 sL4 0x800000001369f81c sL2 0xff80000000000000),0x7071c1dc1ce0e709c71c1c41c60e308c71c2391c1329f0db6e3823831c18e0c7071c1dc1ce0e709c71c1c41c60e308c71c2391c1329f0db6),((sl7 0xcea8c5e00 0x8000000000000000 sL31 sL4 0xcea8c5e0 sL12 sL31),0x807e01e01f00f80e07e01f81f80fc0f07e03c1e04ea8c4db6fc03c03e01f00f807e01e01f00f80e07e01f81f80fc0f07e03c1e04ea8c4db6),(0,0),(0,0)]
def g115C : List ColumnInfo := [(32,0,83,0,4)]
def g115A : List (List Nat) := [[],[101]]
def g115D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g115L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g115D4)
  | _ => emptyPacking
def g115I (_ _ : Nat) : Option (Nat × Nat) := none
def g115 : Forest := ⟨115,4,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P4_0 : block g115 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B4 : block g115 4 0 1=true := g115P4_0
theorem g115T : checkedTables g115 4 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g115B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 5 := lower_forest (g:=g115) (i:=0) (hints:=68) (before_sound K55 V55) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K55 5 [(115,[]),(117,[33,84]),(121,[49,33,100,84])]
set_option maxRecDepth 32768 in
theorem V115 : Known true K115 := extend_ok (m:=115) V55 low115 (by decide +kernel)
def g151Y : Array Signals := #[(0xf001ffe001ffc07ff001ff80ffc07ff003ffffe03ff4b12b0007fff000fff001ffe001ffc07ff001ff80ffc07ff003ffffe03ff4b12b0007,0xa9551551542a9542a8d4251a148b42a9aa4a8a458a64b1235b6d8aa8aa8aa9551551542a9542a8d4251a148b42a9aa4a8a458a64b1235b6d),(0x1fffffe00007ffffe0000fffffffffc00ffffc068db9401f8ffffff000001fffffe00007ffffe0000fffffffffc00ffffc068db9401f8,0xc198198198332604c098362c191204c1306c0c891340d38412490cc0cc0cc198198198332604c098362c191204c1306c0c891340d3841249),(0xfffe00000000007fffffffff00007fffffff0000000ff00e8e00fffffffffffe00000000007fffffffff00007fffffff0000000ff00e8e00,0x1e05e05e0bc381702e0b8305e1c1701c0702f0e1c0df00cb6db2f02f02f01e05e05e0bc381702e0b8305e1c1701c0702f0e1c0df00cb6db),(0,0),((sl7 0xffffff99af6d703f 0x7fffffff sL21 0x703fffffffffffff 0xffffffffff99af6d 0x7fff 0xffffffffffffff80),0x200600600c000180300c040602018020080300000190c082492300300300200600600c000180300c040602018020080300000190c082492),(0,0),(0,0),((sl7 0x6754f2ffc0 0xffffffff80000000 sL31 0xffc0ffffffffffff 0x6754f2 0xffffffffffff8000 sL31),0xc018018010000600c0100008000600c0300c010202200724924c00c00c00c018018010000600c0100008000600c0300c010202200724924),(0,0)]
def g151C : List ColumnInfo := [(1,0,150,0,5)]
def g151A : List (List Nat) := [[],[32,116]]
def g151D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g151L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g151D5)
  | _ => emptyPacking
def g151I (_ _ : Nat) : Option (Nat × Nat) := none
def g151 : Forest := ⟨151,5,fun i => g151Y[i]?.getD (0,0),g151C,g151A,g151L,g151I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151P5_0 : block g151 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g151B5 : block g151 5 0 1=true := g151P5_0
theorem g151T : checkedTables g151 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g151B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : graphValid g151 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := lower_forest (g:=g151) (i:=0) (hints:=268437316) (before_sound K115 V115) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K115 6 [(151,[])]
set_option maxRecDepth 32768 in
theorem V151 : Known true K151 := extend_ok (m:=151) V115 low151 (by decide +kernel)
def g179Y : Array Signals := #[(0xffe00ffe00fffff001ff87fc3ff803fffffffe1e6b067b003e0ffff001ffc01ffc01ffffe003ff0ff87ff007fffffffc3cd60cf6007c1f,0xa4150a4150a0520a4140510089052290a4102044009046b4a5294a0a41482a1482a140a4148280a201120a45214820408801208d694a529),(0xff00000fffff007ffffe0007fffffffc00ff87ffe1a8bdc107c1f07ffffe00001ffffe00fffffc000ffffffff801ff0fffc3517b820f83e0,0x4c0984c0980c2604c0982620900260304c02104805201cc118c63184c09813098130184c0981304c412004c060980420900a403982318c63),(0,0),(0,0),(0xfffffff00000007ffffffff8003fffffff0007fffe56ec8ef801ffffffffffffe0000000fffffffff0007ffffffe000ffffcadd91df003ff,0x90120101205048090120480121048040101420900052a00421084209012024020240a0901202409002420900802028412000a54008421084),(0xffffffffffffff8000000000003ffffffffff800002793f4003e007fffffffffffffffff0000000000007ffffffffff000004f27e8007c00,0xe09c0609c060704e09c17045c2270482609804e088269394b5ad6b4e09c1380c1380c0e09c1382e08b844e0904c13009c1104d27296b5ad6),(0,0),(sR106,0xe0180e018080700e0180060038070380e04701108d4308c6318c700e01c0301c030100e01c03000c00700e0701c08e02211a86118c6318),(0,0)]
def g179C : List ColumnInfo := [(0,32,146,1,5),(32,0,147,0,5),(1,32,146,0,4),(2,0,177,0,4),(128,0,51,0,4)]
def g179A : List (List Nat) := [[],[113]]
def g179D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4fd5121
def g179D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x60880480e140fd41ff21fd21
def g179H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g179D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8635f
def g179H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1100000000000ba000000084000c403000
def g179L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g179D4)
  | 5 => (3,1,3,0,0,5,0,g179D5)
  | 6 => (1,0,3,65537,0,0,1028,g179D6)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g179H5
  | 6 => lookupWord 1 19 0 7 2 1 g179H6
  | _ => fun _ => none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
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
theorem g179P5_0 : block g179 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B5 : block g179 5 0 3=true := g179P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : block g179 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B6 : block g179 6 0 1=true := g179P6_0
theorem g179T : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g179B4
  · exact g179B5
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K151) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=268435524) (before_sound K151 V151) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K151 7 [(179,[]),(182,[32,116]),(211,[101]),(345,[49,33,100,84,135]),(361,[49,33,100,135]),(364,[32,49,132,100,118])]
set_option maxRecDepth 32768 in
theorem V179 : Known true K179 := extend_ok (m:=179) V151 low179 (by decide +kernel)
def g181Y : Array Signals := #[(0xffe00ffe007ffff801ff87fc3ff803ffffc3fffe6a3e2b0001fffff001ffc01ffc00fffff003ff0ff87ff007ffff87fffcd47c560003ff,0xa4150a41505029052140510089052290a40881040280e0b4a5294a0a41482a1482a0a0520a4280a201120a4521481102080501c1694a529),(0,0),(0xff00000fffff803ffffe0007fffffffc00fffc3fe1a9a9d107fe007ffffe00001fffff007ffffc000ffffffff801fff87fc35353a20ffc00,0x2c0582c058160b0160181620500160302c0500808521289118c63182c0580b0580b02c1602c0302c40a002c060580a01010a425122318c63),(0,0),(0xfffffff00000003ffffffff8003fffffff00003ffe57e88ef8000fffffffffffe00000007ffffffff0007ffffffe00007ffcafd11df0001f,0xb016030160582c0580a0580161058040301611050053a084318c630b01602c0602c0b0580b0140b002c20b0080602c220a00a741086318c6),((sl7 0x80004d2fe8007fe0 0x7fffffffffff 0xffffffff80000000 0x3ff07fffffffff 0xffffffc0002697f4 0x3fffff sL28),0xc09804098060302604c16045822604824098002608069164a5294a4c098130081300c0604c0982c08b044c09048130004c100d22c94a5294),(0,0),(sR106,0xe0180e01804038070180060038070380e02238108c5308c6318c700e01c0301c030080700e03000c00700e0701c044702118a6118c6318),(0,0)]
def g181C : List ColumnInfo := [(1,0,180,0,4),(4,0,177,0,4),(16,0,165,0,4),(32,0,149,0,4),(128,0,53,0,4)]
def g181A : List (List Nat) := [[],[114,84],[32,116],[32,64,80,112],[64,117],[64,82,112,32],[80,66],[80,114,64,66],[112,32,66,84],[112,82]]
def g181D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g181D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e4120443f
def g181H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3
def g181D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x58d11f
def g181H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x73009baace27000000d01200b5000016b1
def g181L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g181D4)
  | 5 => (2,1,3,65537,0,4,1025,g181D5)
  | 6 => (1,0,3,65537,0,0,1029,g181D6)
  | _ => emptyPacking
def g181I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g181H5
  | 6 => lookupWord 2 17 0 8 1 3 g181H6
  | _ => fun _ => none
def g181 : Forest := ⟨181,6,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P4_0 : block g181 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B4 : block g181 4 0 1=true := g181P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : block g181 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B5 : block g181 5 0 2=true := g181P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P6_0 : block g181 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B6 : block g181 6 0 1=true := g181P6_0
theorem g181T : checkedTables g181 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g181B4
  · exact g181B5
  · exact g181B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 7 := lower_forest (g:=g181) (i:=0) (hints:=536872196) (before_sound K179 V179) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K179 7 [(181,[])]
set_option maxRecDepth 32768 in
theorem V181 : Known true K181 := extend_ok (m:=181) V179 low181 (by decide +kernel)
def g218Y : Array Signals := #[(0,0),(0xf003ffc00fffffc00fff0ffffffc00fffff0fffeea3a5303f03ffff000fff003ffc00fffffc00fff0ffffffc00fffff0fffeea3a5303f03f,0xa2282288a0282284a08a210802284a0280220882200a5314514508a08a08a2282288a0282284a08a210802284a0280220882200a53145145),(0,0),(0x3fffff003fffff0000ffc3fffff003fffffc009adfd000fc0ffffff000003fffff003fffff0000ffc3fffff003fffffc009adfd000fc0,0xc8b10b02c8b10b00c42c405090b10c4b11404108092d994d34d342c42c42c8b10b02c8b10b00c42c405090b10c4b11404108092d994d34d3),(0xfffc00000003fffffffff0003fffffffc000fffd77e88afc003ffffffffffffc00000003fffffffff0003fffffffc000fffd77e88afc003f,0xc04c1302c04c090130026104c0100c0584120152a08828a28a1301301300c04c1302c04c090130026104c0100c0584120152a08828a28a),(0,0),((sl7 0x12697f4000fc0 sL0 sL18 0xfc0ffffffffffff 0xffff00012697f400 0x3fffffff sL24),0x302701c0302702e09c08b822702609026009c11269264b2cb2c9c09c09c0302701c0302702e09c08b822702609026009c11269264b2cb2c),((sl7 0x39d530dfff000 0xffffc00000000000 sL31 0xf000ffffffffffff 0x39d530dff sL20 sL31),0xc0380200c0380300e000c00380380e03808e0208d5104c30c30e00e00e00c0380200c0380300e000c00380380e03808e0208d5104c30c30),(0,0)]
def g218C : List ColumnInfo := [(0,8,146,64,5)]
def g218A : List (List Nat) := [[],[116],[99],[99,116],[65],[65,113],[65,99],[65,99,113],[113,65],[113],[113,99,65],[113,99]]
def g218D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g218L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g218D5)
  | _ => emptyPacking
def g218I (_ _ : Nat) : Option (Nat × Nat) := none
def g218 : Forest := ⟨218,5,fun i => g218Y[i]?.getD (0,0),g218C,g218A,g218L,g218I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218P5_0 : block g218 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g218B5 : block g218 5 0 1=true := g218P5_0
theorem g218T : checkedTables g218 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g218B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218G : graphValid g218 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low218 : Lower true (varsX 218) (graphGoal 218) 6 := lower_forest (g:=g218) (i:=0) (hints:=318857280) (before_sound K181 V181) g218G g218T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K218 := extendKnown K181 6 [(218,[]),(346,[49,100,135]),(410,[134]),(458,[49,100,84,117,133]),(466,[99,83,133]),(472,[49,33,66,98,82,117,133])]
set_option maxRecDepth 32768 in
theorem V218 : Known true K218 := extend_ok (m:=218) V181 low218 (by decide +kernel)
def g119Y : Array Signals := #[(0xfffffc00000fffffc00003fffff00000ffffffffffc00003ffffe0003fffffffffffffc00003fffffffffe0003fff97e43a62aa9edf07c1f,0x2a8000aa0002a8002a8000aa000aa000550000a8001a80009400680014800a0000a8001a800128000a4005800a05c00862081c0108421),(0xfffffffffff00000000003ffffffffff000007fffffffffc000000003ffffc0007fffffffffc00003ffffffffc0000b5fc47c9174a0003e0,0x452331148cc45233115331148cc450cc4546622913114131148d824b11419049322913114931149b1148c824904930b4e846c8154ab5ad6b),((sl7 0xbada15c4320f8000 0xc000000000000676 sL2 sL20 0x7ffffffffff 0xfffffc0000000000 sL31),0x160bc0582f0160bc0583c0582f0162f0161780b05c0585c0582e042c0585e085c0b05c0581c0581c0582f041e083c27692ca058432739ce7),(0,0),((sl7 0x9707c5fea40003ff 0xfffffffffffffe81 sL2 0 0xfffff80000000000 sL31 sL31),0x984c0261300984c02604026130098300981804c260261602613008b02616011604c260261202612026130089011206011701056a254a5294),((sl7 0x6978fe62520ffc00 0x645 sL12 sL31 sL31 sL31 sL31),0xe0700381c00e070038180381c00e0400e06007038038180381c010c038180218070380381c0381c0381c010e021c04016930da62018c6318),(0x33aa5b8895b2bf00000,0xff8003fe000ff8003fe003fe000ff800ff8007fc003fe003fe001f003fe003e007fc003fe003fe003fe001f003e00322a538895a2bef7bde),(0,0),(0,0)]
def g119C : List ColumnInfo := [(2,0,117,0,5),(4,0,115,0,5),(64,0,55,0,5),(16,2,101,0,4),(32,4,83,0,4)]
def g119A : List (List Nat) := [[],[33,84]]
def g119D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x17e50
def g119D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa888ff
def g119H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g119L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g119D5)
  | 6 => (1,0,3,65537,0,0,1029,g119D6)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g119H6
  | _ => fun _ => none
def g119 : Forest := ⟨119,6,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : block g119 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : block g119 5 0 1=true := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : block g119 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : block g119 6 0 1=true := g119P6_0
theorem g119T : checkedTables g119 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g119B5
  · exact g119B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K218) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 7 := lower_forest (g:=g119) (i:=0) (hints:=1348) (before_sound K218 V218) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K218 7 [(123,[50,101]),(125,[33,49,84,100]),(249,[49,114,100,84]),(497,[113,130,49,101,50]),(500,[32,65,96,48,113,133,83])]
set_option maxRecDepth 32768 in
theorem V119 : Known true K119 := extend_ok (m:=119) V218 low119 (by decide +kernel)
def g183Y : Array Signals := #[(0xfffe01fffc0007ffe01fff807fff80007fff8001fffe0007ffffffe0007fff00fffffffff8001fffffff00ff1d203397a2ac000003f03f,0xaa01545480a90350094340290b2055205520552154815485520aa4054835204a1a41485101520d4825205216141d002390a2a91451451451),(0xff000001fffffff800001fffffffffffff80000001fffffff8000fffffff800000fffc03ffffffe0007fffff00637e8b807608003f000fc0,0xcc119898113022608d858232120466046604660998119806608cc0898026046c2c0190982260498136046424262336098066085145145145),(0x1ffffffffffffe000007ffffffffffffffe00000000000fffffffffffff000003ffffffffff800000009d8e48e9a5400fc0fc0000,0xf005e0e005c00b802e0600bc1c01780178017801e005e017802f002e00b801703005e0e00b800e003801783838150a48c1a54030c30c30c3),(0,0),((sl7 0x85ccf7f000000fff 0xffffffffffa049c5 0x3ffffffff 0xfffff00000000000 sL31 0x7fffff 0xfffffffe00000000),0x26000026004c01300804c02009800980098002002600180030013002c00980401601004c00900240098000008048c0050854a28a28a28a),((sl7 0x3e5b400000fff000 0x917538 sL18 sL31 sL31 0x7fffff 0),0xb8010138027005c0101700404e004e004e004c0138012004c009c013004e00009800027004e013804e0040408075102e5802cb2cb2cb2c),(0,0),((sl7 0x60389bffff000000 0x4e9376 0 0 0 sL21 sL31),0xc00001c003800600001800007000700070007001c001c007000e001c00700080e002038007001c00700080804881362010830c30c30c30),(0,0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(2,0,181,0,7),(4,0,179,0,7),(0,32,146,5,6),(32,0,151,0,6),(16,0,167,0,5),(128,0,55,0,5)]
def g183A : List (List Nat) := [[],[32,116]]
def g183D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4f77159653
def g183D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10420806284506c85b2c0bf59653fdd8553bdd8553bd58453be58053
def g183H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa0
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c0038007643a985f3c129aa629ff
def g183H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x730000000000000000000000280000000000000000000064001100000070000000000000000052000000000000000000000000
def g183D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb1a23f
def g183H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c03969000000000000000000000
def g183L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g183D5)
  | 6 => (5,2,3,0,0,6,0,g183D6)
  | 7 => (3,1,3,65537,0,5,1031,g183D7)
  | 8 => (1,0,3,65537,0,0,1029,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g183H6
  | 7 => lookupWord 1 53 0 8 3 1 g183H7
  | 8 => lookupWord 1 17 0 7 2 1 g183H8
  | _ => fun _ => none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : block g183 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B5 : block g183 5 0 1=true := g183P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : block g183 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_3 : block g183 6 3 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 5=true := (@block_merge g183 6 0 3 2 g183P6_0 g183P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 3=true := g183P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : block g183 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : block g183 8 0 1=true := g183P8_0
theorem g183T : checkedTables g183 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g183B5
  · exact g183B6
  · exact g183B7
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := lower_forest (g:=g183) (i:=0) (hints:=268436804) (before_sound K119 V119) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K119 9 [(183,[]),(365,[49,100,135])]
set_option maxRecDepth 32768 in
theorem V183 : Known true K183 := extend_ok (m:=183) V119 low183 (by decide +kernel)
def g215Y : Array Signals := #[(0x1ffff80001ffff000ffff8007ffff00007ffffffffc0001ffffffffffffffffffffffffc0001ffffffffc003ffd524a373e833c0007c1f,0x548015200d4004a01a002900b200aa405520154802a901548055200a900948052014400a900d4804a40148058051520013288339294a529),(0x1ffffffffe0000000ffffffffffffffff80001ffffffffe00007fffc0001ffff000ffffffffe0000fffffffc003ed51a38816c800f83e0,0x4980a2602898146c22c0a32112028cc0466051980a330219814660113018d808641260513014980a6c0519049049be541230016086318c63),(0x1ffffffffffffffff00000007ffffffffffffe00000000000007fffffffe0000000fffffffffffff0000000000073b22915bd881f00000,0x9e02cb80b2e059704b02cbc25c0b2f00978065e02cbc075e039780a5c052e02d782b8165c058e02c70165e09e09e063922115bd88e739ce7),(0,0),((sl7 0xe43c4e4f7e0003ff 0xffffffffffffc859 0xfffffffffff 0xfffff80000000000 sL31 0x7fffff 0xffe0000000000000),0x10030c00c30061808c030c04600c30011800860030c00460021800c600630031804c0186006100308018601101100009e00c420c48421084),(0,0),((sl7 0x9b47773c00007c00 0x456 0xfffff00000000000 sL31 sL31 0x7fffff 0),0xe013f004fc017e00f00bf007804fc009e004f8013f00278013e004f8027c013e007009f8027e013f009f801e01e000569a45770c2d6b5ad6),((sl7 0x5dc49781bfff8000 0x33aa 0 0 0 sL21 sL31),0x1c000700018000000c00000070000e00070001c00038001c000700038001c000800e00038001c000e00020020001820dc08401318c6318),(0,0)]
def g215C : List ColumnInfo := [(4,0,211,0,7)]
def g215A : List (List Nat) := [[]]
def g215D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g215L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g215D7)
  | _ => emptyPacking
def g215I (_ _ : Nat) : Option (Nat × Nat) := none
def g215 : Forest := ⟨215,7,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : block g215 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B7 : block g215 7 0 1=true := g215P7_0
theorem g215T : checkedTables g215 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g215B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 8 := lower_forest (g:=g215) (i:=0) (hints:=268437316) (before_sound K183 V183) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K183 8 [(215,[]),(407,[32,116,134])]
set_option maxRecDepth 32768 in
theorem V215 : Known true K215 := extend_ok (m:=215) V183 low215 (by decide +kernel)
def g219Y : Array Signals := #[(0xe007fff80007fff801ffff80001ffff80007fffe0001ffffffff80007fffc00ffffffffffe0001ffffffff003ff1d10d5daa29900003f03f,0x49510153035202922ca05528154a055285528154a154a0aa50152835281291a50524514054a0d4a094a052459141d0015da2288451451451),(0x7ffffffffffffffffffffffe000000007fffffffe0000ffffffff8000000ffff003fffffffe0001ffffffc006fd62ae3438003f000fc0,0x8260226022602320480466011980466026601198019808cc02260026011b02c00640980898049804d804640902627122ac30180145145145),(0,0),(0x7fffffff8000001fffffffffffffffff8000000000000fffffffffffffff0000003fffffffffffe0000000009dae8e542564000fc0000,0x13820b820b830bc470c178305e0c1783078305e0c5e0c2f060b830b8305c23061788e182e0c0e0c0e0c1788e2381dac8e5021644d34d34d3),((sl7 0x4e1393ffc0000fff 0xfffffffffffa0659 0x3ffffffffff 0 sL31 0x1ffffffffffffff 0xfff8000000000000),0x4c004c004c008009800260009800080026000600030004c002c00260040058010013000900090009800000080448020103728a28a28a),(0,0),((sl7 0x91ddcf0000fff000 0x915a6 0xfffffc0000000000 sL31 sL31 0x1ffffffffffffff 0),0x404700470047001010e00438010e0043004380108010c0087004300438000086000021c010e010e010e001004080526005dc10b2cb2cb2c),((sl7 0x7125e06fff000000 0x4ea97 0 0 0 0xfe00000000000000 sL31),0x180780078007800601f0007c001f0007c007c001f001f000f8007c007c00380f800e03e001f001f001f000e038048a955104e00c30c30c30),(0,0)]
def g219C : List ColumnInfo := [(8,0,211,0,7)]
def g219A : List (List Nat) := [[],[113]]
def g219D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g219L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g219D7)
  | _ => emptyPacking
def g219I (_ _ : Nat) : Option (Nat × Nat) := none
def g219 : Forest := ⟨219,7,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 1=true := g219P7_0
theorem g219T : checkedTables g219 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g219B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 8 := lower_forest (g:=g219) (i:=0) (hints:=268460100) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 8 [(219,[]),(347,[49,100,135]),(467,[131,83]),(470,[32,99,116,83,133]),(473,[49,33,114,100,82,133])]
set_option maxRecDepth 32768 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array Signals := #[(0x7ffff00001ffffc000fffff80000fffff80000fffffffffffffff00001ffffe0007fffffffffffffffffffffffff9961a4fab95940003ff,0x51002a600d48014901650055280aa50055280aa500aa500aa5002a500d4a009480d28052405140152804a500a480a1921244a9119094a529),(0,0),((sl7 0x6f136450a0f8000 0x80000ffffe0005df 0x7ffff0003ffff 0xfffffffffe00000 0xfffff0000 0xfffffffffffff000 sL2),0x60554c0aa98155904a405566012cc05566036cc02acc06acc0554c04a980aad8156025640a9814a602b6c054c81335c70671364408739ce7),(0x7ffffffffe00000000ffffffffffffffffffff0000000000ffffffffffffffffff800000003fffffffff00000000053e3e4d5a478007c00,0x82067040ce0c19e213860678304f060678304f060cf060cf06067060ce0c0ce10983067884e1813830270606f105c013a2e491a478b5ad6b),((sl7 0x8e2545fea5f0001f 0xfffffffffffffaa5 0x3ffff 0xf000000000000000 sL31 0xfffffffffffff sL12),0x67800cf0019e009c00678002700067800270004f0004f000678006f000cf002e003780170019c003380067002600250c2144e6246318c6),(0,0),((sl7 0x795afe6252007fe0 0x245 sL24 sL31 sL31 0xfffffffffffff 0),0x478008f0011e000e0087800438008780043800870008700087800870010f0003004380018021e0043c0087800380244491a4642034a5294),((sl7 0xa5b8895b2bff8000 0x73a 0 0 0 0xfff0000000000000 sL31),0x78000f0001e0003000f80007c000f80007c000f8000f8000f8000f8001f0001c007c000e003e0007c000f8001c00218a1888919038c6318),(0,0)]
def g221C : List ColumnInfo := [(0,4,89,128,5),(0,8,149,64,5),(4,0,217,0,5),(8,0,213,0,5)]
def g221A : List (List Nat) := [[],[64,50,118]]
def g221D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe413f
def g221L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g221D6)
  | _ => emptyPacking
def g221I (_ _ : Nat) : Option (Nat × Nat) := none
def g221 : Forest := ⟨221,6,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 1=true := g221P6_0
theorem g221T : checkedTables g221 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g221B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 7 := lower_forest (g:=g221) (i:=0) (hints:=536897284) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 7 [(221,[]),(237,[80,50,114,64,98]),(343,[96,49,33,64,132,116]),(455,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array Signals := #[(0,0),(0x3ffffc00007fffffffff0007fffffffe00003ffffe00003fffffffffffffe00003ffff8003fffffffffffffffff99c559a751938003f03f,0xa8140a828350504a0505220b105014154142a814154142a81055040aa020540c1a81025086814150284a050a421498055087411305145145),(0x3fffffffff80000ffffffff8003fffffffffc0000000003ffff80000fffffffffc00000003ffff80000ffffe00036ad462289af40fc0000,0x3059530b2a61656c1656445222985959818b305959839b3025660eacc14a98295305ab612b058a60b36c164c846632ad4622898f0f3cf3cf),((sl7 0x74def58a00000fc0 0xffff00000000067a sL31 0xfffffff 0xfffffffffffffffc 0x3ffff 0x3ffffffffffffff),0xc1019c00338006704067809c04e1019e0813c1019e0813c1067820cf040ce0819c1033804c1013820270406f00b806727484358a134d34d3),((sl7 0xcca8bed4bf00003f 0xffffffffffff58b1 0x3fffff 0xfffffffff0000000 sL31 0x3ffff 0xfc00000000000000),0x61e00c3c018780187808e0470061e0021c0061e0021c00478008f0018f0031e0063c0270061c00c380187008c000b00c289ec48a28a28a),(0,0),((sl7 0x2b5fcc4a40000fc0 0x48af sL22 sL31 sL31 0x3ffff 0),0x27e002fc005f8009f800f0078027e0013e0027e0013e00278004f0009f0013e0027c0038027e004fc009f800f00488d0b5bc8406cb2cb2c),((sl7 0xb7112b657ffff000 0xe754 0 0 0 sL24 sL31),0x380003000060000e0000000000380001c000380001c0003800070000e0001c000380004003800070000e00010004540a110202070c30c30),(0,0)]
def g222C : List ColumnInfo := [(0,8,150,64,6)]
def g222A : List (List Nat) := [[],[99],[65],[65,99]]
def g222D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g222L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g222D6)
  | _ => emptyPacking
def g222I (_ _ : Nat) : Option (Nat × Nat) := none
def g222 : Forest := ⟨222,6,fun i => g222Y[i]?.getD (0,0),g222C,g222A,g222L,g222I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222P6_0 : block g222 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g222B6 : block g222 6 0 1=true := g222P6_0
theorem g222T : checkedTables g222 6 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g222B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 7 := lower_forest (g:=g222) (i:=0) (hints:=318859072) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 7 [(222,[]),(411,[32,116,134]),(459,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g235Y : Array Signals := #[((sl7 0x7f4aa09de8000fff 0xfffffffffffff36d sL31 0x7fffff0000f sL30 0xffffff000003f 0xfffc0003fffffc00),0x14840582802a8280aa0a00aa0a02a8280550500aa0a00541403505004a101a0a014840502802a0a01282805210143646c0a809880249249),(0xfffffffffffffffffff000000000003fffff800000fffffffffff8000000000fffffc0003fffff000003fffff0000fbe04ebf62231fc0000,0x5590129002ab30012cc00aacc00db3001566006acc00aa98012a600556c02ac0095900a980294c00adb002a640266f8e0463e400311c71c7),(0,0),((sl7 0xc4359bd0f703f000 0xfffc0000000000a7 0x3fffffff 0xfffffffffffffff0 0xffffff sL28 0x3ffffffff),0x19e084e0b033c0b04f02c0cf02c13c0b0678160cf02c0ce05833816067021302c19e084e0b02702c09c0b037820b802744119ad0f36db6db),(0,0),((sl7 0x1674157ff000003f 0xfffffffffffff54b 0x3fffffff 0 0xffffffffff000000 sL31 0x3ffffffff),0x9e012702c33c02c2700b0cf00b09c02c2780584f00b0cf0161bc058678045c0b0de011702c3380b0ce02c338044c040b1274156770db6db6),((sl7 0xfbb7e9c20e03ffc0 0x48a sL20 sL31 sL31 sL31 0x3ffffffff),0xe002380303c00303800c0f000c0e00303800607000c0f00181c006078008600c0e002180303c00c0f00303c00870048893a461020c924924),((sl7 0x4a985f269dfc0000 0xe75 0 0 0 0 sL18),0x3c003fc0003fc000ff0000ff0003fc0007f8000ff0001fe0007f8000f800ff0003e003fc000ff0003fc000f8000714a981b268ce38e38),(0,0)]
def g235C : List ColumnInfo := [(0,2,105,128,5)]
def g235A : List (List Nat) := [[],[113],[96,83],[96,113,83]]
def g235D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g235L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g235D5)
  | _ => emptyPacking
def g235I (_ _ : Nat) : Option (Nat × Nat) := none
def g235 : Forest := ⟨235,5,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 1=true := g235P5_0
theorem g235T : checkedTables g235 5 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g235B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 6 := lower_forest (g:=g235) (i:=0) (hints:=268460149) (before_sound K222 V222) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K222 6 [(235,[]),(238,[32,49,118]),(252,[32,49,65,118])]
set_option maxRecDepth 32768 in
theorem V235 : Known true K235 := extend_ok (m:=235) V222 low235 (by decide +kernel)
def g243Y : Array Signals := #[(0x7fffe001ffff000ffffe0000ffffffffffffffffff80003ffffffffffffffff00007fffffffffffffffc003ffd76f2131c876400ffc1f,0x500014004000200210014200a10028400a10028400508028400a10010000800a100508014200200010008008001128002088721294a529),(0xfff80000001ffffffffffffffff00003ffff00003ffffffffc0000ffff8007ffffffff80001ffff000fffffffc003891d26fa15c81f003e0,0x92602498128092409002498024c04930024c029300926011300a4c02120290124c024601298048404a0249012012b8110263015486318c63),(0,0),(0,0),((sl7 0x8eba768b7e0003ff 0xffffffffffcc30 sL23 0xffffff00000007ff 0x3fffffff 0xfffffffffffffc sL23),0x24804920240124812404920049001240149005240124802240109004a4052024900488024200928094049202402404008c18648848421084),((sl7 0x64166f4d80007c00 0xff00000000000353 sL31 0x7ff sL20 sL1 0),0xc70571c0c715c70638a71c148e0a638298e0a63829c7053b829ce0a73829c538e0a710538c14e30518a71c14714702536416670dad6b5ad6),(sR19,0xf8067e017819f80bc0c7e018f00c7c031f00c7c031f8063c031f00c7c04e063f00c7e063f018fc09e0c7e027827804569b45570c2d6b5ad6),(sR102,0x78001801e000c00f8001f000f8003e000f8003e0007c003e000f8007007c000f8007c001f000e00f80038038003aa51849201318c6318),(0,0)]
def g243C : List ColumnInfo := [(32,0,211,0,7)]
def g243A : List (List Nat) := [[],[101],[113],[113,101]]
def g243D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g243L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g243D7)
  | _ => emptyPacking
def g243I (_ _ : Nat) : Option (Nat × Nat) := none
def g243 : Forest := ⟨243,7,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 1=true := g243P7_0
theorem g243T : checkedTables g243 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g243B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 8 := lower_forest (g:=g243) (i:=0) (hints:=268435524) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 8 [(243,[])]
set_option maxRecDepth 32768 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g245Y : Array Signals := #[(0x7fffe001ffff000ffffe0000fffffffff80003fffffffffffffffffffffffff00007ffffffff8007fffffffffde2d8339c932c00f83ff,0x500014004000200210014200a10028400508028400a10028400a10010000800a100508014200100100008008001a29002080321294a529),(0,0),(0xfff80000001ffffffffffffffff00003ffffffffc0000ffffc0000ffff8007ffffffff80001fffffff8007fffc0039d3724fa05c01f07c00,0x28601458118051408801458022c028b00516010b00a2c008b0062c010a02500a2c014600a58028a02402500a1011b953224b001006318c63),(0,0),((sl7 0xe9a768b7e00001f 0x7ffffffcd32 sL23 0xffffff00000007ff 0xfff 0xfffffffffffffc sL23),0xb2805960250165812c0596004b0032c0165803ac01cb0052c014b005ac05602cb0058802c600b2c04e04e02ca02505120e1a64884c6318c6),((sl7 0xe4366f4d80007fe0 0xfffff80000000251 sL31 0x7ff 0xfffffffffffff000 sL1 0),0xc3056180c615860630a618148c0a430298605230290c0a630298c0a630298530c0a610530814c30288288530c1460000c4146f4da94a5294),(sR19,0xfc067e017819f80bc0c7e018f00c7c031f8063c031f00c7c031f00c7c04e063f00c7e063f018fc04f04f063f027804569b45570c2d6b5ad6),(sR102,0x78001801e000c00f8001f000f8003e0007c003e000f8003e000f8007007c000f8007c001f0007007007c0038002a851849301b18c6318),(0,0)]
def g245C : List ColumnInfo := [(64,0,181,0,7)]
def g245A : List (List Nat) := [[],[114,84]]
def g245D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
def g245L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g245D7)
  | _ => emptyPacking
def g245I (_ _ : Nat) : Option (Nat × Nat) := none
def g245 : Forest := ⟨245,7,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P7_0 : block g245 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B7 : block g245 7 0 1=true := g245P7_0
theorem g245T : checkedTables g245 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g245B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 8 := lower_forest (g:=g245) (i:=0) (hints:=536872196) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 8 [(245,[]),(373,[100,135]),(437,[32,116,134]),(485,[32,132,118])]
set_option maxRecDepth 32768 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g469Y : Array Signals := #[(0xfffc0003fffffffc007fffe0000ffffc0003ffff0000ffffffffc0001ffff001fffe003fffffffffffffffffffffcc65acb88be2400003ff,0x202a902a202a10098149015240a9202a502a480a940a900a9202a4815200a5052004a0a4815240a92025012404a00c04aca083a22318c631),(0,0),(0xfffffffc0003fffffffffffffff000000003ffffffff0000ffffffffe0000001ffffffffffe0000ffff001fffe003b843a5ae0e501f07c00,0xab005300ab00550140055800ac00ab006b002ac012c02ac00ab0029802ac05802a80a0015801ac0094034014805a980225a806506318c63),(0,0),((sl7 0x3d9111a400f801f 0x1ffffffef3b 0x3ffffffff0 sL30 0xfffc000000000000 0x7fffffffffffff sL24),0xcc006400cc086602610660413020cc084c0833021b0233020cc08320433009043301308260413020d805841900923390358101054a5294a),(0,0),((sl7 0xe5744e4dbe0003e0 0xfffffe0000002059 0x3fffffffff 0 sL31 0x7fffffffffffff 0),0x4f0027804f002780380278009c004f00070013c001c003c004f0013c00bc00e00bc01c0138009c004e006009e00e20590054484d8c6318c6),((sl7 0x9a07773c000ffc00 0x2456 0xffffffc000000000 sL31 sL31 0x7fffffffffffff 0),0x7003380370033802c0638018e00c700318031c00c600c400c70031c018c009018c012031c018e00c7009818e0130044698056708294a5294),((sl7 0x5dc49781bff00000 0x13aa 0 0 0 0xff80000000000000 sL31),0x8003c0038003c003007c001f000f8003e003e000f800f800f8003e001f000e01f001c03e001f000f800e01f001c012225d801780318c6318)]
def g469C : List ColumnInfo := [(16,0,453,0,5),(17,0,452,0,4),(65,0,404,0,4),(132,0,337,0,4),(144,0,325,0,4),(260,0,209,0,4),(320,0,149,0,4)]
def g469A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118],[64,130,118],[64,130,112,96,98],[96,114,64,132,66],[96,114,132],[112,98,66,128],[112,98],[128,66],[128,66,98,112]]
def g469D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xbbd8940
def g469D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40c3fa81fd10
def g469H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa0
def g469D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6b1667f
def g469H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c81000312a10053001e35280001e70000362002
def g469L : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,g469D5)
  | 6 => (2,1,3,0,0,3,0,g469D6)
  | 7 => (1,0,3,65537,0,0,1030,g469D7)
  | _ => emptyPacking
def g469I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g469H6
  | 7 => lookupWord 2 17 2 9 1 4 g469H7
  | _ => fun _ => none
def g469 : Forest := ⟨469,7,fun i => g469Y[i]?.getD (0,0),g469C,g469A,g469L,g469I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P5_0 : block g469 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469B5 : block g469 5 0 1=true := g469P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P6_0 : block g469 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469B6 : block g469 6 0 2=true := g469P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469P7_0 : block g469 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g469B7 : block g469 7 0 1=true := g469P7_0
theorem g469T : checkedTables g469 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g469B5
  · exact g469B6
  · exact g469B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469G : graphValid g469 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low469 : Lower true (varsX 469) (graphGoal 469) 8 := lower_forest (g:=g469) (i:=0) (hints:=9126807300) (before_sound K245 V245) g469G g469T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K469 := extendKnown K245 8 [(469,[])]
set_option maxRecDepth 32768 in
theorem V469 : Known true K469 := extend_ok (m:=469) V245 low469 (by decide +kernel)
def g474Y : Array Signals := #[(0,0),(0x3fff07fff8001ffffffe0ffff0000ffff0003fffc000fffffffc000ffff07ffffffff0003ffffffc1ffffc92d389940f740000007fc01ff,0x2800a11045209404500842208a208a208a2228822888a2028822884a208a110840208a212880a2008441100829308000f708a45229148a45),(0,0),(0xfc00007ffffffe0007ffffffffffff00000003fffffff0003fffffff000007ffe0fffffffc000ffffffff81a52a0abb8d8801ff00003fe00,0xb022c20216041821604280042c042c042c08b010b002c08b010b000c042c200282042c043012c0450008209a50a02b1090026130984c2613),(0x7ffffffffff80000fffffffffffffffc00000000003ffffffffffff80000fffffffffff00001ffffefe1835e2102c0000ff80001ff,0xc10b04209801200982130441304130413040c104c113042c104c10904130021304413040410304160882402700815a2100d148a45229148a),(0,0),((sl7 0x4d3fe0000003fe00 0xfe0000209965726e sL1 0xc000000000000000 sL31 0xffffffffff 0xffffff8000000000),0x4c0004e009c04e009c0809c009c009c0030027001c0030027002e009c0405c0809c00980240098001381208141106c4d0582c160b0582c),((sl7 0x3c00000ffffc0000 0x24d69a0557 0xff00000000000000 sL31 sL31 0xffffffffff 0),0x2700847004e017004e0108e008e008e008c0238022008c0238023008e000460008e008e023808e0111c0200d60a05560826130984c26130),((sl7 0x81bffff000000000 0x132a5dc497 0 0 0 0xffffff0000000000 sL31),0x380007800700180070000f000f000f000f003c003c00f003c003c00f000878010f000f003c00f0021e004012a1cc48300b81c0e070381c0)]
def g474C : List ColumnInfo := [(0,2,328,144,6),(0,8,146,320,6),(0,16,328,130,6),(0,64,146,264,6),(0,128,328,18,6),(2,0,472,0,6),(8,0,466,0,6),(16,0,458,0,6),(64,0,410,0,6),(128,0,346,0,6)]
def g474A : List (List Nat) := [[],[134],[116],[116,134],[99],[99,131],[99,116],[99,116,131],[131,99],[131],[131,116,99],[131,116],[49,100,135],[49,100,116,132],[49,132,100,118],[49,132,118],[49,65,97,135],[49,65,97,113,129],[49,65,129,97,118],[49,65,129,118],[49,113,100,65,132],[49,113,100,129],[49,113,132,97],[49,113,132,100,97],[65],[65,134],[65,113],[65,113,134],[65,99],[65,99,131],[65,99,113],[65,99,113,131],[65,131,99],[65,131],[65,131,113,99],[65,131,113],[97,49,67,135],[97,49,67,116,132],[97,49,132,67,115],[97,49,132,115],[97,67,135],[97,67,113,129],[97,67,131,115],[97,67,131,113,49],[97,115,67,132],[97,115,67,65,129],[97,115,132],[97,115,132,65],[113,65],[113,65,134],[113],[113,134],[113,99,65],[113,99,65,131],[113,99],[113,99,131],[113,131,65,99],[113,131,65],[113,131,99],[113,131],[129,49,67,100,118],[129,49,67,118],[129,49,100,115],[129,49,100,116,67],[129,67,97,118],[129,67,118],[129,67,99,49,115],[129,67,99,115],[129,115,67,97,100],[129,115,67,100],[129,115,100,65],[129,115,100]]
def g474D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x94837261502bf
def g474L : Nat → Packing
  | 8 => (1,0,4,0,0,0,0,g474D8)
  | _ => emptyPacking
def g474I (_ _ : Nat) : Option (Nat × Nat) := none
def g474 : Forest := ⟨474,8,fun i => g474Y[i]?.getD (0,0),g474C,g474A,g474L,g474I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g474P8_0 : block g474 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g474B8 : block g474 8 0 1=true := g474P8_0
theorem g474T : checkedTables g474 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g474B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g474G : graphValid g474 (boundsBefore K469) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low474 : Lower true (varsX 474) (graphGoal 474) 9 := lower_forest (g:=g474) (i:=0) (hints:=13203759168) (before_sound K469 V469) g474G g474T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K474 := extendKnown K469 9 [(474,[])]
set_option maxRecDepth 32768 in
theorem V474 : Known true K474 := extend_ok (m:=474) V469 low474 (by decide +kernel)
def g127Y : Array Signals := #[((sl7 0x1e4500ff00ff00ff 0x4e9d22197ea01eb8 0x3fffffee484 sL29 0xffffff800000003f 0x3ffffffffff sL26),0x955400002955000015aa80000a95400002a950000155a80000aa9400002aa90005558002aa840044a8502181c800e981a00010101010101),(0x1ffffffffffffffffc00000001ffffffffffffffffc00000001ffffffffffffffc000000ab697b034497848c7c13b9ab00000000ff00,0xd9988a283266228a193311450cd988a283326228a199311450ccd88a2833320889990444cccab696a030493048c7c12b889555555555555),((sl7 0x461a0000ff000000 0xba158933917d287a 0x1527e 0xffffffe000000000 sL31 0x1ff 0xffffe00000000000),0x2e1e02c02bc780b00de3c05806f1e02c02bc380b009e1c05804f0e02c02bc3c101e1e080f0f0507cba15801391352878461a333333333333),((sl7 0x4cb4ff0000000000 0xf8e218d25092a39d 0x13b9d 0 0 sL27 sL31),0x4fe0000b33f80002c9fc000164fe0000b33fc0002cdfe000166ff0000b33fc0012fe00097f01239d58c218d25090229d4c340f0f0f0f0f0f),((sl7 0xe57e00000000ffff 0x9308e7c496e3c0b5 0xffffffffffff40c9 sL31 sL31 sL31 sL31),0x7000130c3c0004c30e00026187000130c3c0004c30e00026187000130c3c000223000111800100809108e144826380254576aaaaaaaaaaaa),(0x122a64d6ea9e0695f7e4321910000ffff0000,0x80001c0fc0000703f0000381f80001c0fc0000703f0000381f80001c0fc000043c00021e00012282056a29e0604a50032181cccccccccccc),(0x9d52a4f3b55f8326d10e5b80ffff00000000,0x1ff0000007fc000003fe000001ff0000007fc000003fe000001ff0000007c00003e000009c42a430a5058326d1020180f0f0f0f0f0f0),(0,0),(0,0)]
def g127C : List ColumnInfo := [(2,0,125,0,7)]
def g127A : List (List Nat) := [[],[50,101],[33,84],[33,49,84,100],[49,33,100,84],[49,100]]
def g127D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g127L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g127D7)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,7,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 1=true := g127P7_0
theorem g127T : checkedTables g127 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g127B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K474) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 8 := lower_forest (g:=g127) (i:=0) (hints:=25924) (before_sound K474 V474) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K474 8 [(127,[])]
set_option maxRecDepth 32768 in
theorem V127 : Known true K127 := extend_ok (m:=127) V474 low127 (by decide +kernel)
def g223Y : Array Signals := #[((sl7 0x6d8bc0000003f03f 0x8241494599e356c9 0xfff800000fffffee sL0 sL26 0xfffffff80000003f 0xf80000003fffffff),0x52801aaa94009554a00295528015aa9400a954a002a95280155a9400aa94a002aa9201556402aa8e8041490518e156c9040b411451451451),(0xffffffffc0000001ffffffffffffffc0000001ffffffffffffffc0000001fffffffffffff000000afa9ffc3060045308544d6c003f000fc0,0x600a13330050d998028326600a19330050cd98028332600a19930050ccd80283332022664044ccc2a29dd82020045108544d685145145145),((sl7 0x3a196c0fc0000000 0x2be74a28b1790895 21 sL25 0x1ffffffffff 0 sL30),0x802c5c3c0162e1e00b2bc7802cde3c0166f1e00b2bc3802c9e1c0164f0e00b2bc3c04787808f0f142be74828a13900953a196cf3cf3cf3cf),((sl7 0x9212d00000fc0000 0xb5ff181f8265b242 19 0 0xfffffe0000000000 sL31 sL31),0x3009fc01804fe00c033f803009fc01804fe00c033fc0300dfe01806ff00c033fc040bf80817f00395f71817826592421212c134d34d34d3),((sl7 0xa936eff000000fff 0xcb260d0ce115566 0xfffffffffffffff4 sL31 sL31 sL31 sL31),0x30e000018700000c3c000030e000018700000c3c000030e000018700000c3c00008c00011800100c2220d0c6100004a91084a28a28a28a),(0,0),(0x122a49a54f279ea821f695300000fff000,0x43f000021f800010fc000043f000021f800010fc000043f000021f800010fc00000f00001e000102a08a448251a2820e08432cb2cb2cb2c),(0x9d5249ea134f8aebe00ea03ffff000000,0x7c000003e000001f0000007c000003e000001f0000007c000003e000001f000000700000e0000095000060110c0ae2200a2030c30c30c30),(0,0)]
def g223C : List ColumnInfo := [(4,0,219,0,8)]
def g223A : List (List Nat) := [[]]
def g223D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g223L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g223D8)
  | _ => emptyPacking
def g223I (_ _ : Nat) : Option (Nat × Nat) := none
def g223 : Forest := ⟨223,8,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : block g223 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B8 : block g223 8 0 1=true := g223P8_0
theorem g223T : checkedTables g223 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g223B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 9 := lower_forest (g:=g223) (i:=0) (hints:=268461892) (before_sound K127 V127) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K127 9 [(223,[]),(463,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
theorem V223 : Known true K223 := extend_ok (m:=223) V127 low223 (by decide +kernel)
def g239Y : Array Signals := #[(0x7fffffffc00000003fffffffffffffffffffffffe00000001ffffffff0000007fffffffffffffd504a283598ceac015ff2f19400001fc07f,0x50012aa828016aa828014aa8280152a82800aa541400aad41400554a100aad05002aa90805551500a2814884e28005fe270008912244891),(0x80000000000000003fffffffc00000003fffffffffffffffe000000000000007fffffff80000035f57ea93407101929443e4ec07f0000000,0x555b33002adb33002a5933002ad9b3002aacc980154cc980155666c01333600553332009999a5557ea91407101029442c4ec78f1e3c78f),((sl7 0xe8182bf800003f80 0xf8fdd464cc534485 0xa5 sL29 0x3fffffffffffffff 0xc000000000000000 sL31),0x181c3c000c1c3c000c1e3c000c1e3c000c0f0e00060f0e000607870021c3800183c3c010e1e00478ac9460c0134085e818202850a14285),((sl7 0x7532d0000fe00000 0x3bf208a34b426aaa 0x276 0 0xc000000000000000 sL31 sL31),0x16019fc00b009fc00b009fc00b009fc00b00cff005806ff0058067f80205fc01601bfc0102fe00723af208834b42628a7130d19b366cd9b3),(0,0),((sl7 0xd795f80000003fff 0x925c231f125b8f02 0xfffffffffffffe81 sL31 sL31 sL31 sL31),0x5861e0002c30e0002c30e0002c30e0002c30f000161870001618780004460005861c0002230002818050231710408f001585db56ad5ab56a),(0x2454d25baa781a57df90c8644000fffc000,0x607e0000303f0000303f0000303f0000303f0000181f8000181f80000878000607e000043c0002054505a22480851d200c860664c993264c),(0x13aa493ced57e0c9b44396e03fff0000000,0x7f8000003fc000003fc000003fc000003fc000001fe000001fe000000f800007f8000007c000012a80114a950e0c9940112203870e1c3870),(0,0)]
def g239C : List ColumnInfo := [(2,0,237,0,7)]
def g239A : List (List Nat) := [[],[32,49,118]]
def g239D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g239L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g239D7)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,7,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_0 : block g239 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B7 : block g239 7 0 1=true := g239P7_0
theorem g239T : checkedTables g239 7 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g239B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 8 := lower_forest (g:=g239) (i:=0) (hints:=268461429) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 8 [(239,[])]
set_option maxRecDepth 32768 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array Signals := #[(sR64,sR71),(sR89,sR80),(sR20,sR29),(0,0),(sR96,sR42),(sR108,sR56),(sR4,sR59),(sR2,sR62),(0,0)]
def g247C : List ColumnInfo := [(64,0,183,0,9)]
def g247A : List (List Nat) := [[]]
def g247D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g247L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,g247D9)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,9,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 1=true := g247P9_0
theorem g247T : checkedTables g247 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g247B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 10 := lower_forest (g:=g247) (i:=0) (hints:=268436804) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 10 [(247,[]),(439,[32,116,134]),(493,[32,49,132,118])]
set_option maxRecDepth 32768 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array Signals := #[((sl7 0xe0000000ffff00ff 0xaaaa2a40d5b2c2c0 0xf00000fffff785cb 0x1fffffffffffff sL25 sL31 0x7ffffffffffff),0x55050002a828000a82800128280014840050280005414000d41400094140005210016100147008a2a22220014b2c0004021212121212121),(0xfff80000003ffffffc0000003ffffffc00003fffffffffffffe0000001ffffffffffff000005217c25ccb4a338e639105b00ff000000ff00,0x8660024a330012113001231b00122190044980122898009149800914d8009146401124011261015c248c208318c609105a0b0b0b0b0b0b0b),(0,0),((sl7 0xf0000ff00000000 0x77636101c5a51f25 0xb5a46 0xfffffffffe000000 sL0 sL20 0x3fffff),0xd781601cbc0b00a5c0b00a5c0b00b5e080ae0b00b2e058058e058058e05805978202782027834a4267636001c5a41f250367676767676767),((sl7 0x13ff00000000ffff 0x6834129cb24837ce 0xfffffffffffa5e21 sL31 sL0 0 sL22),0x18000490c00024c600024c600024c60009300024c300012610001261000126180024400244081e2100101008a00836cc0114141414141414),((sl7 0x3800000000ff0000 0xd4c86db6ed18390d 0x886cb 0 0xffffc00000000000 sL31 sL31),0xe005871f002c38f802c38f802c38f80111c02c38fc0161c7e0161c7e0161c7e00447804478088641d4c84db6e908390d38dedededededede),(sR7,0x607e000303f000303f000303f00021e00303f000181f800181f800181f8000878008780081534908489ee020920808c98989898989898),(sR6,0x7f800003fc00003fc00003fc00003e0003fc00001fe00001fe00001fe00000f8000f80004e0824b60cd340321802280e0e0e0e0e0e0e0),(0,0)]
def g251C : List ColumnInfo := [(8,0,243,0,8),(32,0,219,0,8),(0,32,218,1,7),(2,0,249,0,7),(64,8,179,0,7),(128,0,123,0,7),(0,2,105,144,6),(0,128,105,18,6),(1,0,218,0,6),(1,32,218,0,6),(16,0,235,0,6),(2,128,105,16,5),(16,2,105,128,5),(16,128,105,2,5),(130,0,121,0,5),(18,128,105,0,4)]
def g251A : List (List Nat) := [[],[113]]
def g251D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x309bd87cc640abf864c640
def g251D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf116a0a0328230220205354cc31202d3bbe564b025c2d617cc5d314dd85737df7fb7cff3190131
def g251H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1e00
def g251D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2fa104ce66304d652130f96043b003be6018ee018ef02384f3994b6cd10286a38b1349a8068503c271300ac3cc698f30a61440a1a40ffef
def g251H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x15590004401efe800008c03c3c9
def g251D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x12a62837f
def g251H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2a8017800000000ca180000000000000000000000000002cc00009c00000002440000000154f750038000000000000001
def g251L : Nat → Packing
  | 6 => (2,3,4,0,0,3,0,g251D6)
  | 7 => (6,2,4,262147,34,6,1033,g251D7)
  | 8 => (8,1,4,131073,16,8,1043,g251D8)
  | 9 => (1,0,4,0,0,0,0,g251D9)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 3 0 5 1 0 g251H7
  | 8 => lookupWord 2 13 1 8 3 1 g251H8
  | 9 => lookupWord 2 59 1 8 3 1 g251H9
  | _ => fun _ => none
def g251 : Forest := ⟨251,9,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 2=true := g251P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_2 : block g251 7 2 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 6=true := (@block_merge g251 7 0 2 4 g251P7_0 g251P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_2 : block g251 8 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 8=true := (@block_merge g251 8 0 2 6 g251P8_0 g251P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 1=true := g251P9_0
theorem g251T : checkedTables g251 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 10 := lower_forest (g:=g251) (i:=0) (hints:=268460100) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 10 [(251,[]),(379,[49,100,135]),(494,[32,49,132,118]),(499,[131]),(502,[32,99,116,131]),(508,[32,49,65,129,118])]
set_option maxRecDepth 32768 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array Signals := #[(0x7fffffffffffffe0000001ffffffffffffff00000fffffffffffffffffffffffffffffff705c92e8e16429de2c2c0c3000000ff00ffff,0x55050002a8280005414000d41400094140005210016100140a0002a0a0004a0a0005210014500c80a0a020019e2c2004121212121212121),(0,0),(0xfff80000003fffffffffffffe0000001ffffffffffff00000fffffff0000000fffffff000005b95e9144b8a160f633117200ff0000ff0000,0x26600142b3000a0a980050a980050ad80050564010a4010a6002814c002836c0028264010661995c8004188140d60311520b0b0b0b0b0b0b),((sl7 0xe0000ff00000000 0xc76b6101d5a51f24 0xbd2e4 0xffffffffffffff0 0 sL30 0x3fffff),0xb781601b3c0b00ace05804ce05804ce0580567820338203382c02a702c02a702c02b78202b83d2e0476b6001d5a41b240267676767676767),((sl7 0x12ff0000000000ff 0xc8341a9cb24837ce 0xfffffffffffadea1 sL4 0 0 sL22),0x38000593c0002ccf000166f000166f000166780025c0025c000b338000b338000b3380024c0ade2180141888a00835cc121e1e1e1e1e1e1e),((sl7 0x3900000000ffff00 0x74c865b6ed18390d 0x8064b 0xf000000000000000 sL31 sL31 sL31),0xc005861c002c30f0016187001618700161878004460044600b0c3c00b0c3c00b0c3c00447008060374c06536a408380c28d4d4d4d4d4d4d4),(sR7,0x607e000303f000181f800181f800181f80008780087800c0fc000c0fc000c0fc0008780080514908489ee020924818c98989898989898),(sR6,0x7f800003fc00001fe00001fe00001fe00000f8000f8000ff00000ff00000ff00000f8000420824f60c5360b21802280e0e0e0e0e0e0e0),(0,0)]
def g253C : List ColumnInfo := [(0,8,181,64,8),(8,0,245,0,8),(4,0,249,0,7),(16,0,237,0,7),(32,0,221,0,7),(64,8,181,0,7),(128,0,125,0,7),(0,4,89,160,6),(1,0,252,0,6),(4,128,105,16,5),(16,128,105,4,5),(32,4,89,128,5),(36,0,217,0,5),(132,0,121,0,5),(20,128,105,0,4)]
def g253A : List (List Nat) := [[],[114,84]]
def g253D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x400e040000c0400000200802582231c2f569305cae4c78a0a016e0e5d2e98db7432e8750ccb9cb7306ec85da3ba0fbdfedf3f8c21050d314c110
def g253D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x779004dec09297025bd01288a8250404ac9039801126b1d609d22520c458e358e79634e3926120050d61505318c13084110ff
def g253H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8803210060004988003500000020073a280b80a70
def g253D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2c864a37f
def g253H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd00001c80000000004ac00000000000002d40022f00000000000000000000f1a7401246800000000000001c000000000019c2
def g253L : Nat → Packing
  | 7 => (11,2,4,262150,35,7,1029,g253D7)
  | 8 => (8,1,4,65537,0,8,1041,g253D8)
  | 9 => (1,0,4,0,0,0,0,g253D9)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 3 17 4 9 4 1 g253H8
  | 9 => lookupWord 3 53 2 8 3 1 g253H9
  | _ => fun _ => none
def g253 : Forest := ⟨253,9,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_0 : block g253 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_3 : block g253 7 3 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B7 : block g253 7 0 11=true := (@block_merge g253 7 0 3 8 g253P7_0 g253P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 8=true := g253P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 1=true := g253P9_0
theorem g253T : checkedTables g253 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g253B7
  · exact g253B8
  · exact g253B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 10 := lower_forest (g:=g253) (i:=0) (hints:=536896772) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 10 [(253,[]),(375,[49,100,135]),(445,[32,116,134]),(487,[32,49,132,118])]
set_option maxRecDepth 32768 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array Signals := #[(0,0),(0x80000000fffffffffffffffc00000007fffffff000007ffffffffffffffffffffffffffff606845947e807eb553a18e5c00000ffc00003ff,0x8a50aa01148154022840a80451835008a20520110b008a282a011450940228a148044280020450432805eb503a18e14154551545515455),((sl7 0xf003ff00000ffc00 0x9581dd19d0eb8a9a 0xfffc000000f031b0 0xffff00000001ffff sL31 sL31 0xffffffff00000001),0x2c04cc0058159800b0153001602a6002c056402052002c014c005806d800b00990080cc030119095818419c0ea8888a0cc330cc330cc33),((sl7 0x900000003ff00000 0x481b2fce82f63582 0xcbe5a8c sL25 0x7fff sL29 1),0x1400e6f02801d9e0500299c0a0053381400b6782029c1400b270280164e05002cde0809704b45a0848092bce80762582943d0f43d0f43d0f),((sl7 0x9ffc0000000003ff 0x24a5a2c12a43cd4d 0xffffffffff61cf82 sL31 0x7fff 0 sL30),0x130870002611e0004c31e0009863c00130c780044e00130c3800261870004c30e0011181e61c1820485a2000241c50c92a8aa2a8aa2a8aa),((sl7 0x70000000000ffc00 0x8a5ccbae3c495753 0x184c9930 0 0xffffffffffff8000 sL31 sL31),0x59c0f800b381e0016703e002ce07c0059c0f8004870059c0fc00b381f8016703f00121e0184c88200a5c4ba63c0157535f33ccf33ccf33cc),(0x1a6a64d6ea9e8415f7a43319000000003ff00000,0x61ff0000c3fe000187fc00030ff800061ff00008f80061ff0000c3fe000187fc00023e001a4a24d6a2968411778012190bc2f0bc2f0bc2f0),(0x1952a4f3b5578326d10e4b80fffffffc0000000,0x7e000000fc000001f8000003f0000007e000000f00007e000000fc000001f8000003c00001842a0d285058002d0020100c0300c0300c0300),(0,0)]
def g254C : List ColumnInfo := [(0,8,182,64,8)]
def g254A : List (List Nat) := [[],[99],[65],[65,99]]
def g254D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
def g254L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g254D8)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,8,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P8_0 : block g254 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B8 : block g254 8 0 1=true := g254P8_0
theorem g254T : checkedTables g254 8 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g254B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 9 := lower_forest (g:=g254) (i:=0) (hints:=320955712) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 9 [(254,[]),(382,[49,100,135]),(443,[32,116,134])]
set_option maxRecDepth 32768 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g471Y : Array Signals := #[(sR98,sR66),(sR36,sR68),(sR94,sR84),(0,0),(sR104,sR86),(0,0),(sR110,sR23),(sR0,sR30),(sR3,sR35)]
def g471C : List ColumnInfo := [(1,0,470,0,8),(2,0,469,0,8),(4,0,467,0,8),(64,0,407,0,8),(256,0,215,0,8),(16,0,455,0,7),(128,0,343,0,7),(144,0,325,0,4)]
def g471A : List (List Nat) := [[],[32,116,134]]
def g471D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x17ddc553
def g471D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x76cba85923fd53
def g471H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40
def g471D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7d63447f
def g471H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x60
def g471L : Nat → Packing
  | 7 => (1,2,3,0,0,0,0,g471D7)
  | 8 => (1,1,3,0,0,0,0,g471D8)
  | 9 => (1,0,3,65537,0,0,1031,g471D9)
  | _ => emptyPacking
def g471I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 4 0 0 g471H8
  | 9 => lookupWord 1 2 0 4 0 0 g471H9
  | _ => fun _ => none
def g471 : Forest := ⟨471,9,fun i => g471Y[i]?.getD (0,0),g471C,g471A,g471L,g471I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_0 : block g471 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B7 : block g471 7 0 1=true := g471P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_0 : block g471 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B8 : block g471 8 0 1=true := g471P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P9_0 : block g471 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B9 : block g471 9 0 1=true := g471P9_0
theorem g471T : checkedTables g471 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g471B7
  · exact g471B8
  · exact g471B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471G : graphValid g471 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low471 : Lower true (varsX 471) (graphGoal 471) 10 := lower_forest (g:=g471) (i:=0) (hints:=8858371908) (before_sound K254 V254) g471G g471T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K471 := extendKnown K254 10 [(471,[]),(477,[49,100,135])]
set_option maxRecDepth 32768 in
theorem V471 : Known true K471 := extend_ok (m:=471) V254 low471 (by decide +kernel)
def g475Y : Array Signals := #[(0x1fffffffffffe000003fffffc000fffffffffffffff800000fffffffffffe0007ffe56e1be36cec4440a35203000000000007fc01ff,0x94a1552941552940552941aa52812891a94a0a448a4a50154a506a94a0952940a448b122856e1ba240ec4440a35002a8d46a351a8d46a351),(0xfffffe000001fffffffffffc000000000fffffe0007fffffffffff000001fffffffff8000806bdacc591e606033dc40000001ff00003fe00,0x1801983011983008983001306011b102c1800c88130c02260c024c1804d83008c8812204c802b5a8450144060319c4229148a45229148a45),(0,0),((sl7 0x7fc0000ff8000000 0x20515076f1e800 0x1cf8ccb5 sL25 0xf0000000007fffff sL31 0x1ffff),0xc5e00185e00182e00185c00305c023000c2f011c0060b800607000c0e00182f011c0470438c8b50020411062e1e00984c26130984c2613),((sl7 0x3fe0000003ffff 0xb35424ab01a0bb00 0xffffffffe6b040cb sL31 0x7fffff 0 sL25),0x200600400600401300401600802600040200b000201004c010048020090040130000000002904041a210208800a01945229148a45229148a),(0,0),((sl7 0x8000000ffffc0000 0xac2a998d9a8a1cff 0x1099718 0 sL21 sL31 sL31),0x10800021800021c00021800043800000010c00000008700008700010e00021c0002000800000408ac029009180a1c160b0582c160b0582c),(0x22e6a165acbca6174053400003ffff000000000,0xc1f00183e00183e00183e00307c002380c1f0011c060f80060f800c1f00183e0011c0470002c0a1618ca8a61740420984c26130984c26130),(0x19d52160534a2adc6d5842ffffc0000000000000,0xfe0001fc0001fc0001fc0003f80003c00fe0001e007f00007f0000fe0001fc0001e0078019c5214053482ac4051002e070381c0e070381c0)]
def g475C : List ColumnInfo := [(1,0,474,0,9),(2,0,473,0,8),(128,0,347,0,8),(256,0,219,0,8),(0,2,329,144,7),(0,8,147,320,7),(0,16,328,131,7),(0,64,146,265,7),(0,128,329,18,7),(0,256,147,72,7),(16,0,459,0,7),(64,0,411,0,7),(130,0,345,0,7),(264,0,211,0,7),(1,16,328,130,6),(2,16,328,129,6),(8,64,146,257,6),(16,2,329,128,6),(16,128,329,2,6),(64,256,147,8,6),(18,0,329,0,5)]
def g475A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def g475D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x61fe1b7550931
def g475D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a390dd7bab5fd093150931
def g475H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40
def g475D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x78408805841044708a041290fc7b080e18406db8208b3af6b25201ffd0b31ffe8498ffd424c6fdb82875fdd531
def g475H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x38bb00000180001e12
def g475D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f80c70fe077080e001ce8067e0410f81043dc01a23ca18d4d20d01c5b492cc4608f766354422b150090d4310f41507314c521ff
def g475H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x233a0513c0800000007004490f0c42c0ac0
def g475D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xdac07f
def g475H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x224000000000000254000000000000000000c6003007c988000000000000085000000000000000a0c0048bd80000051c00c840000000001410000000000000000000000292003c40000000000002b1000003a000000c200000ed0000000000000003a30000000000000000000000000f5c00000001cc000000000000003d10000000000000000000000000000000000000000000000000000253
def g475L : Nat → Packing
  | 6 => (1,4,5,0,0,0,0,g475D6)
  | 7 => (2,3,5,65538,1,4,1025,g475D7)
  | 8 => (5,2,5,0,0,8,0,g475D8)
  | 9 => (8,1,5,65537,0,8,1041,g475D9)
  | 10 => (1,0,5,65537,0,0,1027,g475D10)
  | _ => emptyPacking
def g475I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g475H7
  | 8 => lookupWord 1 11 0 7 1 2 g475H8
  | 9 => lookupWord 2 17 4 10 3 3 g475H9
  | 10 => lookupWord 6 127 0 10 3 3 g475H10
  | _ => fun _ => none
def g475 : Forest := ⟨475,10,fun i => g475Y[i]?.getD (0,0),g475C,g475A,g475L,g475I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P6_0 : block g475 6 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475B6 : block g475 6 0 1=true := g475P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P7_0 : block g475 7 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475B7 : block g475 7 0 2=true := g475P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P8_0 : block g475 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P8_2 : block g475 8 2 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475B8 : block g475 8 0 5=true := (@block_merge g475 8 0 2 3 g475P8_0 g475P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P9_0 : block g475 9 0 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475B9 : block g475 9 0 8=true := g475P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P10_0 : block g475 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475B10 : block g475 10 0 1=true := g475P10_0
theorem g475T : checkedTables g475 10 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g475B6
  · exact g475B7
  · exact g475B8
  · exact g475B9
  · exact g475B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475G : graphValid g475 (boundsBefore K471) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low475 : Lower true (varsX 475) (graphGoal 475) 11 := lower_forest (g:=g475) (i:=0) (hints:=13153361988) (before_sound K471 V471) g475G g475T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K475 := extendKnown K471 11 [(475,[]),(478,[32,116,134])]
set_option maxRecDepth 32768 in
theorem V475 : Known true K475 := extend_ok (m:=475) V471 low475 (by decide +kernel)
def g501Y : Array Signals := #[(sR77,sR65),(0,0),(sR78,sR25),(0,0),(sR21,sR54),(sR95,sR73),(sR107,sR39),(sR1,sR75),(sR5,sR76)]
def g501C : List ColumnInfo := [(16,0,485,0,8),(32,0,469,0,8),(64,0,437,0,8),(128,0,373,0,8),(256,0,245,0,8),(1,0,500,0,7),(4,0,497,0,7)]
def g501A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118]]
def g501D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x800603b9b73fbddd10
def g501D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6cba8591ffd10
def g501H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4060
def g501D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7d63447f
def g501H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6
def g501L : Nat → Packing
  | 7 => (2,2,3,131073,16,4,1025,g501D7)
  | 8 => (1,1,3,0,0,0,0,g501D8)
  | 9 => (1,0,3,65537,0,0,1031,g501D9)
  | _ => emptyPacking
def g501I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 3 0 5 1 0 g501H8
  | 9 => lookupWord 1 2 0 4 0 0 g501H9
  | _ => fun _ => none
def g501 : Forest := ⟨501,9,fun i => g501Y[i]?.getD (0,0),g501C,g501A,g501L,g501I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P7_0 : block g501 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P7_1 : block g501 7 1 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B7 : block g501 7 0 2=true := (@block_merge g501 7 0 1 1 g501P7_0 g501P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P8_0 : block g501 8 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B8 : block g501 8 0 1=true := g501P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P9_0 : block g501 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B9 : block g501 9 0 1=true := g501P9_0
theorem g501T : checkedTables g501 9 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g501B7
  · exact g501B8
  · exact g501B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501G : graphValid g501 (boundsBefore K475) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low501 : Lower true (varsX 501) (graphGoal 501) 10 := lower_forest (g:=g501) (i:=0) (hints:=9126806788) (before_sound K475 V475) g501G g501T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K501 := extendKnown K475 10 [(501,[])]
set_option maxRecDepth 32768 in
theorem V501 : Known true K501 := extend_ok (m:=501) V475 low501 (by decide +kernel)
def g255Y : Array Signals := #[(0xf80000000003ffffffffffffffffffff80000001fffffff9d0800168592d242c871992f42c5013fd0121dec000000000007ff001ffc007ff,0x5050000155a8280000aa941400002aa908002aac2000aaa1d000002800250428051190d4244003e001215ec1012024048090120240480901),((sl7 0x3ff800 0xeb470cf000001ffc 0x38068264b80fb782 0x210982324f1cecc 0xfffffffe00000006 0x1ffffffffff sL24),0x600228a19930011450ccd8008a28333200444cc8011133320200882300518ccc28048260380eb382e3070cf0550aa1542a8550aa1542a855),((sl7 0xffe00000000 0x24accbe000ffe000 0x4913e10b26a4090b 0xb0e6fc9a005297cc 0 0xfffffe0000000000 sL31),0x8000b009e1c0005804f0e0002c02bc3c0080f0f00203c3c0b086dc9a0042978c411381032484010b202c88e0330660cc198330660cc19833),(0x3ec2ad28c088ba4397da1243541b6c440e755ec9800000003ff80000000000000,0x16002cdfe00b00166ff005800b33fc010097f004025fc03e42a928c088ba4381d01243540b60440c755ec9b0f61ec3d87b0f61ec3d87b0f),((sl7 0x3fffff 0x981084bfff000000 0x9562784376142409 0x2f115712de065a12 0xfffffffffffffff9 sL31 sL31),0x4c30e000002618700000130c3c000011180000446000029105510de025212902260034210040908108008aa1542a8550aa1542a8550aa),(0x4265ab452698787388b96e2302f99cb6c20909480000000000000fffffc00000,0x58703f00002c381f8000161c0fc0000221e000088780000026123452698685388a86e2002399c14c200010eccd99b33666ccd99b33666cc),(0x8b9a49756713118d62aecc90c902f84832ac312800000003fffff00000000000,0x607fc00000303fe00000181ff00000043e000010f8000000b9049516710118562ae48008900f80830880124f09e13c2784f09e13c2784f0),(0x67549069da2e88593064c198c8069435055d24307fffffffc0000000000000000,0x7f800000003fc00000001fe000000007c000001f00000044449020420a800010648188c8061405014c0430700e01c0380700e01c0380700),(0,0)]
def g255C : List ColumnInfo := [(0,8,183,64,10),(2,0,253,0,10),(4,0,251,0,10),(8,0,247,0,10),(0,64,182,9,9),(1,0,254,0,9),(32,0,223,0,9),(64,0,183,0,9),(64,8,183,0,9),(0,32,218,5,8),(16,0,239,0,8),(128,0,127,0,8),(0,2,109,144,7),(0,128,105,22,7),(1,32,218,4,7),(4,32,218,1,7),(18,0,237,0,7),(33,0,222,0,7),(132,0,123,0,7),(2,128,105,20,6),(16,128,105,6,6),(17,0,238,0,6),(144,2,109,0,5)]
def g255A : List (List Nat) := [[]]
def g255D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x12836426420000010020040c161b158bc7c1f3a6cc972a4878c14202c28056541f22fb7467c8aa6491b22919042ca19e509f224f9111c8c0e4647225dbf7f5febfb7eef7cfd61f4061e745d1549d1505d1501d150a1d4061d405d14060074
def g255D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa591ef1900518b8622e18b2e28601f2df9942e3a68802f43a591899a1be30083ca012fbd30055f4f804cfaf2005df4f804cebf3404bdeb0016794025d38043710051b3bc0274e400b5d80393f1c00529c8016d4c014d4c014f7320145e5590a1deb20140674e38056b00127d3ac414de9c68052deb201579ac4272d204464e8d1204c3251324400a9963d2114b94aa12d9830e1b17394c81c20b14270e3c583d8edfa5e4f7ed633eca718c12edb5ab8a6a7c97a4088a0b7d1dc6f5a56416e5593e4990a3acce298921c04e0c815002774395d0e774299d0a574291d0a6871961c6774195d05184c4e119180b461e118087e05538054600118774e1cd184a65d2938446dd119744461e53871461c617011e09977482e05418501608098103600058270616bffffbfddff6fbfefebf6fbb7f75dd370d0274951755d1705515050074
def g255H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xcb0000000000620000000000c000fa000000000000000099000000e84c0000d600d10063000000005dc400650000b70000000000
def g255D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x100097a00143400586800c7c340069e04e062001280048000b7e8002defc00e80029e8002d612851154d8e52451a638b2a79208a1893edcace58a5506712f1105618006eabaee93a2e83a4a8aa6e0b82a1a0281ff
def g255H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd82e5b605e00022002427778e00010104540039f4840093fa4b5ed2968cc32a0084403a7000a13061345595800002c7000c514d8936d9928f0802c102c06e700000
def g255D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x66290e20808ff
def g255H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x15145600000000348000003f34ee800580000000000029c00000003e40116000000026c8
def g255L : Nat → Packing
  | 8 => (14,3,5,458762,52,7,1031,g255D8)
  | 9 => (38,2,5,655373,68,10,1063,g255D9)
  | 10 => (13,1,5,65537,0,9,1045,g255D10)
  | 11 => (1,0,5,0,0,0,0,g255D11)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 3 53 0 8 4 0 g255H9
  | 10 => lookupWord 9 47 6 10 6 0 g255H10
  | 11 => lookupWord 3 37 2 8 4 0 g255H11
  | _ => fun _ => none
def g255 : Forest := ⟨255,11,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 3=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_3 : block g255 8 3 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 14=true := (@block_merge g255 8 0 3 11 g255P8_0 g255P8_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_9 : block g255 9 9 19=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_28 : block g255 9 28 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 38=true := (@block_merge g255 9 0 9 29 g255P9_0 (@block_merge g255 9 9 19 10 g255P9_9 g255P9_28))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 13=true := g255P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 1=true := g255P11_0
theorem g255T : checkedTables g255 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K501) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low255 : Lower true (varsX 255) (graphGoal 255) 12 := lower_forest (g:=g255) (i:=0) (hints:=268461380) (before_sound K501 V501) g255G g255T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K255 := extendKnown K501 12 [(255,[]),(383,[49,100,135]),(447,[32,116,134]),(495,[32,49,132,118])]
set_option maxRecDepth 32768 in
theorem V255 : Known true K255 := extend_ok (m:=255) V501 low255 (by decide +kernel)
def g479Y : Array Signals := #[(sR100,sR67),(sR37,sR83),(sR38,sR69),(sR93,sR85),(sR112,sR27),(0,0),(sR8,sR22),(sR9,sR31),(sR10,sR34)]
def g479C : List ColumnInfo := [(1,0,478,0,11)]
def g479A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
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
theorem g479T : checkedTables g479 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g479B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479G : graphValid g479 (boundsBefore K255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low479 : Lower true (varsX 479) (graphGoal 479) 12 := lower_forest (g:=g479) (i:=0) (hints:=8858396484) (before_sound K255 V255) g479G g479T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K479 := extendKnown K255 12 [(479,[])]
set_option maxRecDepth 32768 in
theorem V479 : Known true K479 := extend_ok (m:=479) V255 low479 (by decide +kernel)
def g503Y : Array Signals := #[(sR97,sR70),(sR101,sR79),(sR105,sR28),(0,0),(sR111,sR43),(sR13,sR57),(sR11,sR58),(sR12,sR61),(sR14,sR88)]
def g503C : List ColumnInfo := [(1,0,502,0,10),(2,0,501,0,10),(4,0,499,0,10),(16,0,487,0,10),(32,0,471,0,10),(64,0,439,0,10),(128,0,375,0,10)]
def g503A : List (List Nat) := [[],[32,116,134]]
def g503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xfac688ff
def g503L : Nat → Packing
  | 11 => (1,0,3,65537,0,0,1031,g503D11)
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
theorem g503T : checkedTables g503 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g503B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : graphValid g503 (boundsBefore K479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low503 : Lower true (varsX 503) (graphGoal 503) 12 := lower_forest (g:=g503) (i:=0) (hints:=8858371396) (before_sound K479 V479) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K503 := extendKnown K479 12 [(503,[]),(509,[49,100,135])]
set_option maxRecDepth 32768 in
theorem V503 : Known true K503 := extend_ok (m:=503) V479 low503 (by decide +kernel)
def g507Y : Array Signals := #[(sR87,sR72),(sR99,sR81),(0,0),(sR103,sR24),(sR109,sR51),(sR17,sR55),(sR15,sR26),(sR16,sR60),(sR18,sR63)]
def g507C : List ColumnInfo := [(32,0,475,0,11)]
def g507A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def g507D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def g507L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g507D11)
  | _ => emptyPacking
def g507I (_ _ : Nat) : Option (Nat × Nat) := none
def g507 : Forest := ⟨507,11,fun i => g507Y[i]?.getD (0,0),g507C,g507A,g507L,g507I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P11_0 : block g507 11 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B11 : block g507 11 0 1=true := g507P11_0
theorem g507T : checkedTables g507 11 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g507B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507G : graphValid g507 (boundsBefore K503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low507 : Lower true (varsX 507) (graphGoal 507) 12 := lower_forest (g:=g507) (i:=0) (hints:=13153361988) (before_sound K503 V503) g507G g507T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K507 := extendKnown K503 12 [(507,[]),(510,[32,116,134])]
set_option maxRecDepth 32768 in
theorem V507 : Known true K507 := extend_ok (m:=507) V503 low507 (by decide +kernel)
def g511Y : Array Signals := #[(sR91,sR74),(sR45,sR82),(sR53,sR90),(sR33,sR32),(sR92,sR49),(sR41,sR40),(sR50,sR48),(sR47,sR46),(sR52,sR44)]
def g511C : List ColumnInfo := [(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(16,0,495,0,12),(32,0,479,0,12),(64,0,447,0,12),(128,0,383,0,12),(256,0,255,0,12),(0,2,365,144,11),(0,8,183,320,11),(0,32,474,5,11),(33,0,478,0,11),(36,0,475,0,11),(0,16,364,131,10),(0,64,182,265,10),(0,128,361,22,10),(0,256,179,76,10),(1,32,474,4,10),(3,0,508,0,10),(10,0,501,0,10),(12,0,499,0,10),(16,2,365,128,10),(17,0,494,0,10),(18,0,493,0,10),(34,0,477,0,10),(40,0,471,0,10),(64,8,183,256,10),(66,0,445,0,10),(72,0,439,0,10),(128,2,365,16,10),(132,0,379,0,10),(136,0,375,0,10),(256,8,183,64,10),(260,0,251,0,10),(264,0,247,0,10),(1,16,364,130,9),(1,64,182,264,9),(4,128,361,18,9),(4,256,179,72,9),(5,0,474,0,9),(5,32,474,0,9),(16,128,361,6,9),(48,0,463,0,9),(64,256,179,12,9),(68,0,443,0,9),(128,16,364,3,9),(129,0,382,0,9),(144,0,365,0,9),(144,2,365,0,9),(256,64,182,9,9),(320,0,183,0,9),(320,8,183,0,9),(20,128,361,2,8),(68,256,179,8,8),(129,16,364,2,8),(257,64,182,8,8)]
def g511A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def g511D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x59d5f4d86e57a15d120
def g511D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc598a82f0a0bc3040a17180a77dcbad4a961d64afd7c361ba15d120e77586e57a15d120b75fc361b9550520
def g511H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb0
def g511D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x37f00226fe00443f0090fc024033ab07d962000ff4b8cc011e186ca6dd941827f436402f0c605e18c6ff03a5109240bc33580cf3fc01b10724ab8720c00013fa66006fea90ca9427c013941c9601c33640bffcbb8a521595ac8015e29940ffbc0d9417f0bc8a5234999a0ae0a734ed9b4b8c2b0a4b9ae646f1af1bab6978063d936498160980e20c2b4da4e5cc5306d9152c67139ae53e6f0fe6791e345dc2b8d61cb1cdf82c4c95a43039562e12195a3f05c03871661dcb719a359184f09e1e8963492c58171538b8d5ff74da75c54f404b921447063eae2b38b72aa97a0068166440d82684c00576b2a6d655dab29b566f40d4ecd38c31ad863a7662c61879ca873950356ac66d58fcbac7b381766e1ecdeecba8fb34432c796c087d9943b38af2a7eff777f7fb9ffcff67f73ef9dfceedfdefed777afbd7d4a95d98461b915d186e517061b925c1865d17068392590a961d64e8d86553a36194061972501865c140e8574483955d12061970483a959120e5541481865052060d414816350520
def g511H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5cd40000a06275000001330000
def g511D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6f6f5da5da6c66b4f2fed2a2d0159a80bc23c7e5042719b03b00fb49238cd45fc13f2240a59a43f827e44814b348dd6c727680260dd71a13b4013334e1d05a00348017c7f998b2d4cc4f00cfff20cde20646c004fffa662db58913c0138f93a512d201decc9d3d4d39ffdb610c6672fe7a83a4d3b19ac33ec3d38cc1d066f95a71a40bc71b4b660e8607c2b4b690bff0b00051fc7c5b2228806191f42c823501e352ffe0f11282ffcf138c6aee250005440df1af85210a5813e35ec298296bb9383f9c90a7ce0f9f23c5bce6ff91d7ff67f85c28b96c313d3ff41c17a11a2be8382f42340df179e7ea1c9451d32c33300378f0ccc15e15f4f004006a8d89b9e459a01bc13a6996800d407ae3427680266e311c9b680264797e112d001a175af9b0482557fcb1b3012340704f4b353397c032d8001a33f97f01332103537d7fc880019c03ffe08c0440d25ff0886094000d41fffacf09502c5f843e0556d9404e08ff5b141164d21fbe70c100b0fffeec900502dd8dd7110c02587ff2823041340dfae12a923bff282306338017f4f738200d51ffa5980919cbe502e9c260a34edcd20ae954785f0319d1460ace2e200a2c296676a2ee165c6d8ad4d72a82d138a7269753acc5783c0904974ca6b5954804f40a214b59325900b1bccb9a32a5460b04f523124d0480d8d1285aec3182e36eca5c2f4629a599cccc61e4b2728f1ab02521a3a928141b2f0d8b122a46aa55345f13429763683479b22ac24992616bd9e84e6e890ee436e8784c160095c7ab31a913545d6e8d9661e3387c1c86c48c04bcbb90b55b21aecab9a72a2e9e89b397f94e9108e78b488a8568017c979073c7056cf6a36796506045d05a156b54551f4e24b447744140d3d83a93753493182dd2ac2732372021c218b15c1260f50c109806902f000d6195ab1ab58636b0c2d60c5ab18a3a0b43416a696cbd3523979af5125e99ebd43a186e4b0d88e5332ba66394bcae97861b70c1ee163dc32ec865d70cba31864e3069c58d30cb1a1981432c2c618b8c19716328153f761bc054d59a5b034161696c5d1ccba3897470068ba5d1e83a269746c0ea4edca9db9531f4260ea48dca913a02372a36e544dca86d62297460fffffeffafdff7fdffdfdddfbffbfebfdbf7bdf9ff5d984e4574e5970e5170e49706197060d705d17058d70e496461d6461d54619545d95461951619416154159541659406194060d405c9405c14058d40611205d1205c1205912058520505204c52061910
def g511H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x157e88d4c00003fc40000000018c000000000000006580018f00000048800c6000386800000000000147160000008600000000000000000000000000000000000000273000000000000000000014c000000001d1000000000000000000000000000180c00000000000000000000000019700000000000a000018266f00000000485a02001048240000000000011400000000d04000000003e00c40028e0000000021300000000000000aa171264000000000000000000000000124000000000000005e80000000000052b6480b50
def g511D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1b15cf4840254ffe258a500959c7802e883105af62be9b5009436d7e8154b71e029de684687200026cf8e7e847312400014379a19b9800013636d79046213350fcffc7b4000125889bc2c548bf0764b14df830f0c53b893f8051e7127e82a387f69514219d7ec6c729104b99f03ea048256af81f4844128bff5404000d06a7b00ba7fe60cc82adff8c20841267df83804124bfed440040d0befc1502093bf5e6225200026cfffafd160004abf3e18e0015ce79e49a11012cffbc0bcaff83beb0319e7916169004c13f1b13a8f18945e20de5004d007fb9e57a51246f8ac42246e7fc004479cff41088f3f03f9a1009280fc7001123bdbc000119e7e6b14201277fb07394024cfbde4f90093b8e7ad4d3a012fb18d20a900699cff2840d6c804d2ff2dfc05033f37d00012a2ff4ff95002c19f67aa00012e7ef96f1000947f81cefc2015de7b200a271fa1674004aa7f4601409ff4ab42004a2ff7ff5100a872fefa000250d46fb385800136ffeee00140ebfc75001200ffff096402497ec7be6300b37e04ff4940491e157c2549007fd57e4a024d8a7ce4cad16b02f9841ae2c542a2a8284600b8614e24040b9a23150c3020f008b15daa542c5208384b1aee28803088513a3af54ba49a11be166e605c5cc1507c3c11b46871216132b26cda62412991c4ba5a363971ac26321e430cf2dcb4661e0e3861f601deb5db5cadae589d6dd52534520d0e4fb4e7cd44bdca4c8c473c5b44cc36c1fc09bf13db3be3a2b8c371b4cb32b172ff2e5ad22beaab291a7da67a51a3a2232079ee9d09bd1a598c97395b1421319189080ee8d78c00a389007986004782e81900065dab72b59869cc3bee55f724f9875cc32e5d9730ad9864cc31e614f2ca79833cb19e54cf30d19838cb1c658a330e59862cbb1660cb2e659632cc1165c8b2c459841cba0e59072c239411c988e618330619630cc10658832640b96a5c852e5dd32ef18475c93ae41d730ab9755cb2ae6213310b9686bb42e521ae90b9284cc1265c932c51642ab8126506ae0279191ca8fffffdfbfbfdffbfb77d845d17059161551515054048110
def g511H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x109000539000000711e520000000000000000000003ddce465e14e0008db000c23000605f2400000000000000000000000000024cc3a000000fce00000001d000000000a0ed5b000000000a6c000000000000000000000462e190000000003ba7cc00063b00000050600000063400000000020000000051a7355867155ac00000000000063081b518dc4000f2f000d25b1c09e000000000000000000000000b01000f04000000000000b0b000464000000000000000426344dea2b072735d000000000b08e8400000000000000000000072874000000050260d000000000713000000000000b1eadc000000dde000000000000000000d12e2a00012c00091f000000000000000000ed2000000000000dec716000d10f0c000c36000000000000000000000000020000000000321a2900000000000034300000000000000000000000036e000000000337aa420363812b42d000550a32fc0000ac3000f83000de3000d57000d499da000aefb33000d31c7870f0000000008f200014aa0a051cd0000f1700000092e314000407000d5c000e59000000622b680000000003f8000078202013001000441010011002
def g511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xfcd220b05a7f980580a8f12380d7e1a00bbf4391829bf7e000517fe5404e7e0e44941ffe661031fef6d0050ffdb4814f7ff00204366270c982809a9713114930ce06a18404d876f1c58415366413c32316910ee74c97449dccb55a24c8410f801845d16455161545414c57050120443ff
def g511H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3823e095528e7c41ec41000000102abbc2db88f40000009d34c08276bb3405000047c09dd1f80000004260007a14c49825814b2200006a4b13907400181b0000001e43e34edeea540013b161b04f5345f95105d0ec001a83000100000120da8760af04762ed5c0001179f9b000727d83d01841918d40000000002c58000000d5dccb0000fb200070535522827140000438404e09ac1e07830cecc20b3b57639146625cf5572288570047713baa50a2c3432000997381c00022000000000016add0322b0000000000383000000000000000019ad4c1d089606433ed0904a481630d91ee7000042db2128bd41c18895148e1c3581f221a67b80662a2593841c2d037702aebb4740000007ad9705c96f1882e4001817259a008410000ccc8001842000000000002c0006cc351000514114210e002142284080002040003105
def g511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1038c20609a611ff
def g511H14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x56003f27a0c6d6ba9c428462023c0000f976000000425b7001cb94d9520b970037341c000c10300041816b8c2a62661f5e49db002a70662403859a3
def g511L : Nat → Packing
  | 8 => (1,6,6,0,0,0,0,g511D8)
  | 9 => (4,5,6,0,0,6,0,g511D9)
  | 10 => (25,4,6,917523,69,10,1102,g511D10)
  | 11 => (60,3,6,917536,69,12,1170,g511D11)
  | 12 => (68,2,6,458763,52,12,1121,g511D12)
  | 13 => (12,1,6,65537,0,9,1060,g511D13)
  | 14 => (1,0,6,0,0,0,0,g511D14)
  | _ => emptyPacking
def g511I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 g511H9
  | 10 => lookupWord 1 19 0 8 2 2 g511H10
  | 11 => lookupWord 9 149 2 11 5 2 g511H11
  | 12 => lookupWord 27 277 4 12 6 2 g511H12
  | 13 => lookupWord 33 181 6 13 7 2 g511H13
  | 14 => lookupWord 8 43 6 10 4 2 g511H14
  | _ => fun _ => none
def g511 : Forest := ⟨511,14,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P8_0 : block g511 8 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B8 : block g511 8 0 1=true := g511P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P9_0 : block g511 9 0 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B9 : block g511 9 0 4=true := g511P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_0 : block g511 10 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_2 : block g511 10 2 11=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_13 : block g511 10 13 12=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B10 : block g511 10 0 25=true := (@block_merge g511 10 0 2 23 g511P10_0 (@block_merge g511 10 2 11 12 g511P10_2 g511P10_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_0 : block g511 11 0 25=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_25 : block g511 11 25 29=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_54 : block g511 11 54 6=true := by
  apply cellsBlock (ar:=12) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B11 : block g511 11 0 60=true := (@block_merge g511 11 0 25 35 g511P11_0 (@block_merge g511 11 25 29 6 g511P11_25 g511P11_54))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_0 : block g511 12 0 2=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_2 : block g511 12 2 24=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_26 : block g511 12 26 42=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B12 : block g511 12 0 68=true := (@block_merge g511 12 0 2 66 g511P12_0 (@block_merge g511 12 2 24 42 g511P12_2 g511P12_26))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P13_0 : block g511 13 0 12=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B13 : block g511 13 0 12=true := g511P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P14_0 : block g511 14 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B14 : block g511 14 0 1=true := g511P14_0
theorem g511T : checkedTables g511 14 := by
  intro k hk
  interval_cases k
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact g511B8
  · exact g511B9
  · exact g511B10
  · exact g511B11
  · exact g511B12
  · exact g511B13
  · exact g511B14
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511G : graphValid g511 (boundsBefore K507) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511R : Impossible true graph 14 inputs.toFinset := by
  rw [show graph = targetOf g511 by decide +kernel]
  exact root_index (g:=g511) (top:=14) (i:=0) (before_sound K507 V507) g511G g511T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_11028

namespace PEqualNP.Outside.L_meta_11028
theorem binaryLower (C : PEqualNP.CircuitLowerBounds.Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (correct : PEqualNP.MetaComplexity.circuitFun 9 C = edge) :
    15 ≤ C.gates.countP (fun g => !isNot g) := by
  obtain ⟨k,hk,h⟩ := signedTrace C legal correct
  by_contra! bad
  exact g511R k (by omega) h

theorem totalLower : ∀ t : Nat, PEqualNP.MetaComplexity.HasCircuitSize 9 edge t → 15 ≤ t := by
  rintro t ⟨C,legal,sz,h⟩
  have lo := binaryLower C legal (funext h)
  have length := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
  change C.gates.length ≤ t at sz
  omega

theorem finishWhenMonotone (mono : Impossible false graph 15 inputs.toFinset) :
    ∀ t : Nat, PEqualNP.MetaComplexity.HasCircuitSize 9 edge t → 16 ≤ t := by
  rintro t ⟨C,legal,sz,h⟩
  by_contra! bad
  exact directSplit mono g511R ⟨C,legal,by omega,h⟩
namespace CrossCheck
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

def positiveAt (p n : Row) (w : Sig) := bit p w && !(bit n w)
def onlyAt (ws : List Sig) (p n : Row) : Option Sig :=
  match ws.filter (positiveAt p n) with
  | [v] => some v
  | _ => none

theorem onlyAt_sound (ws : List Sig) (T : Sig) (p n : Row) (v : Sig)
    (hp : bit p T=true) (hn : bit n T=false) (hv : onlyAt ws p n=some v) :
    onlyWire ws.toFinset T v p n := by
  refine ⟨hp,hn,?_⟩
  intro w hw wp wn
  have mem : w ∈ ws.filter (positiveAt p n) := List.mem_filter.mpr
    ⟨List.mem_toFinset.mp hw,by simp [positiveAt,wp,wn]⟩
  unfold onlyAt at hv
  split at hv
  next z eq =>
    have hE : z=v := Option.some.inj hv
    subst v
    simpa [eq] using mem
  next => contradiction

abbrev Corners := Row × Row × Row × Row × Row × Row

def cross (ws : List Sig) (T : Sig) (k : Nat) (f : Corners) : Bool :=
  let (p,n,pa,pb,na,nb) := f
  (ws.length==k+1) && bit p T && bit pa T && bit pb T &&
    !(bit n T) && !(bit na T) && !(bit nb T) &&
    match onlyAt ws p na, onlyAt ws p nb with
    | some a,some b => a != b && onlyAt ws pa n==some a && onlyAt ws pb n==some b
    | _,_ => false

theorem cross_sound {ws : List Sig} (nd : ws.Nodup) (T : Sig) (k : Nat) (c : Corners)
    (h : cross ws T k c=true) : Impossible false T k ws.toFinset := by
  obtain ⟨p,n,pa,pb,na,nb⟩ := c
  simp only [cross,Bool.and_eq_true,beq_iff_eq,Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨size,hp⟩,hpa⟩,hpb⟩,hn⟩,hna⟩,hnb⟩,hh⟩ := h
  cases ha : onlyAt ws p na with
  | none => simp [ha] at hh
  | some a =>
    cases hb : onlyAt ws p nb with
    | none => simp [ha,hb] at hh
    | some b =>
      simp only [ha,hb,Bool.and_eq_true,bne_iff_ne,beq_iff_eq] at hh
      exact kwCross (by rw [List.toFinset_card_of_nodup nd,size]) hh.1.1
        (onlyAt_sound ws T p na a hp hna ha) (onlyAt_sound ws T p nb b hp hnb hb)
        (onlyAt_sound ws T pa n a hpa hn hh.1.2) (onlyAt_sound ws T pb n b hpb hn hh.2)

end CrossCheck
namespace ImprovedCofactor

def Virtual {R S} (D : Wire R → Wire S → Prop) (a : Wire R) := ∃ w, D a w ∧ Constant w
noncomputable def virtualCost {R S} (D : Wire R → Wire S → Prop) (a : Wire R) : Nat := by
  classical exact if Virtual D a then 1 else 0
noncomputable def virtualMass {R S} (D : Wire R → Wire S → Prop) (ws : List (Wire R)) : Nat :=
  (ws.map (virtualCost D)).sum

def supplied {R S} (D : Wire R → Wire S → Prop) (bank : List (Wire S)) (a : Wire R) : Prop :=
  ∃ w, D a w ∧ Available false bank w

theorem originalCost {R S} {D : Wire R → Wire S → Prop} {a w} (h : D a w) :
    cost w ≤ virtualCost D a := by
  classical
  by_cases c : Constant w
  · have v : Virtual D a := ⟨w,h,c⟩
    simp [cost,virtualCost,c,v]
  · simp [cost,c]

theorem pick {R S} {D : Wire R → Wire S → Prop} {bank a} (h : supplied D bank a) :
    ∃ w, D a w ∧ Available false bank w ∧ cost w = virtualCost D a := by
  classical
  by_cases v : Virtual D a
  · obtain ⟨w,hw,c⟩ := v
    have hv : Virtual D a := ⟨w,hw,c⟩
    exact ⟨w,hw,Or.inr (Or.inl c),by simp [cost,virtualCost,c,hv]⟩
  · obtain ⟨w,hw,ha⟩ := h
    have c : ¬Constant w := fun e => v ⟨w,hw,e⟩
    exact ⟨w,hw,ha,by simp [cost,virtualCost,c,v]⟩

theorem extend {R S} {D : Wire R → Wire S → Prop}
    (compatible : ∀ op a x b y, D a x → D b y → D (combine op a b) (combine op x y))
    (roots : List (Wire S)) {p bank a b} (op) (hp : Reach false roots p bank)
    (ha : supplied D bank a) (hb : supplied D bank b) :
    ∃ q next, Reach false roots q next ∧ supplied D next (combine op a b) ∧
      (∀ v, supplied D bank v → supplied D next v) ∧
      q + virtualCost D a + virtualCost D b ≤ p+1+virtualCost D (combine op a b) := by
  obtain ⟨x,hx,sx,ex⟩ := pick ha
  obtain ⟨y,hy,sy,ey⟩ := pick hb
  obtain ⟨q,next,hq,hz,inc,le⟩ := extend_two roots op hp sx sy
  have hz' := compatible op a x b y hx hy
  refine ⟨q,next,hq,⟨_,hz',hz⟩,?_,?_⟩
  · rintro v ⟨w,h,hs⟩
    exact ⟨w,h,inc w hs⟩
  · have il := originalCost hz'
    omega

theorem extendComb {R S} {D : Wire R → Wire S → Prop}
    (compatible : ∀ op a x b y, D a x → D b y → D (combine op a b) (combine op x y))
    (roots : List (Wire S)) {p bank a b} (d) (hd : allowed false d) (hp : Reach false roots p bank)
    (ha : supplied D bank a) (hb : supplied D bank b) :
    ∃ q next, Reach false roots q next ∧ supplied D next (comb d a b) ∧
      (∀ v, supplied D bank v → supplied D next v) ∧
      q + virtualCost D a + virtualCost D b ≤ p+1+virtualCost D (comb d a b) := by
  rcases allowed_four hd with rfl | rfl | ⟨bad,_⟩ | ⟨bad,_⟩
  · exact extend compatible roots false hp ha hb
  · exact extend compatible roots true hp ha hb
  · cases bad
  · cases bad

theorem massCons {R S} (D : Wire R → Wire S → Prop) (a) (ws) :
    virtualMass D (a::ws) = virtualCost D a + virtualMass D ws := by
  simp [virtualMass]
theorem massKept {R S} (D : Wire R → Wire S → Prop) (a ws) (k : Bool) :
    virtualMass D ws ≤ virtualMass D (kept k a ws) := by
  cases k <;> simp [kept,massCons]

theorem dominatedContraction {R S} {goal : Wire R} {wanted : Wire S} (nc : ¬Constant wanted)
    (D : Wire R → Wire S → Prop)
    (compatible : ∀ op a x b y, D a x → D b y → D (combine op a b) (combine op x y))
    (closed : ∀ w, D goal w → w=wanted)
    {s ws} (h : Run false goal s ws) (roots : List (Wire S)) {p bank}
    (hp : Reach false roots p bank) (hs : ∀ v ∈ ws, supplied D bank v) :
    ∃ q next, Reach false roots q next ∧ Available false next wanted ∧ q+virtualMass D ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    obtain ⟨w,hw,ha⟩ := hs goal (by simp)
    have v : ¬Virtual D goal := by
      rintro ⟨w',hw',hc⟩
      exact nc (closed w' hw' ▸ hc)
    exact ⟨p,bank,hp,closed w hw ▸ ha,by simp [virtualMass,virtualCost,v]⟩
  | perm eq _ ih =>
    have hsub := fun v (hv : v ∈ _) => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [virtualMass,←(eq.map (virtualCost D)).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extendComb compatible roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : ∀ v ∈ comb op a b :: kept ka a (kept kb b rest), supplied D T v := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hh := massKept D a (kept kb b rest) ka
    have hj := massKept D b rest kb
    rw [massCons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [massCons,massCons]
    omega

def better {R : Type} (p n : R → Prop) (le : R → R → Prop) (a b : Wire R) : Prop :=
  (∀ r, p r → a r=true → b r=true) ∧
  (∀ r, n r → a r=false → b r=false) ∧
  (∀ r s, le r s → b r=true → b s=true)

private theorem boolCombine (op a b x y c : Bool) (h : a=c → x=c) (j : b=c → y=c) :
    (if op then a || b else a && b)=c → (if op then x || y else x && y)=c := by
  cases c <;> cases op <;> cases a <;> cases b <;> cases x <;> cases y <;> simp_all

theorem betterCompatible {R : Type} (p n : R → Prop) (le : R → R → Prop)
    (op : Bool) (a x b y : Wire R) (hx : better p n le a x) (hy : better p n le b y) :
    better p n le (combine op a b) (combine op x y) := by
  refine ⟨?_,?_,?_⟩
  · intro r pr
    have hb := boolCombine op (a r) (b r) (x r) (y r) true (hx.1 r pr) (hy.1 r pr)
    cases op <;> exact hb
  · intro r nr
    have hb := boolCombine op (a r) (b r) (x r) (y r) false (hx.2.1 r nr) (hy.2.1 r nr)
    cases op <;> exact hb
  · intro r s hrs
    have hb := boolCombine op (x r) (y r) (x s) (y s) true (hx.2.2 r s hrs) (hy.2.2 r s hrs)
    cases op <;> exact hb

theorem betterClosed {R : Type} {p n : R → Prop} {le : R → R → Prop} {g : Wire R}
    (hp : ∀ r, g r=true → ∃ x, p x ∧ g x=true ∧ le x r)
    (hn : ∀ r, g r=false → ∃ x, n x ∧ g x=false ∧ le r x)
    (w : Wire R) (h : better p n le g w) : w=g := by
  funext r
  cases e : g r with
  | false =>
    obtain ⟨x,xn,xe,xr⟩ := hn r e
    have no := h.2.1 x xn xe
    cases j : w r with
    | false => rfl
    | true => have bad := h.2.2 r x xr j; simp_all
  | true =>
    obtain ⟨x,xp,xe,xr⟩ := hp r e
    exact h.2.2 x r xr (h.1 x xp xe)


def projected {R S} (rows : S → R) (p n : R → Prop) (le : R → R → Prop)
    (a : Wire R) (b : Wire S) : Prop :=
  ∃ v, better p n le a v ∧ b = restrictRows rows v

theorem projectedCompatible {R S} (rows : S → R) (p n : R → Prop) (le : R → R → Prop)
    (op : Bool) (a : Wire R) (x : Wire S) (b : Wire R) (y : Wire S)
    (hx : projected rows p n le a x) (hy : projected rows p n le b y) :
    projected rows p n le (combine op a b) (combine op x y) := by
  obtain ⟨v,hv,rfl⟩ := hx
  obtain ⟨w,hw,rfl⟩ := hy
  refine ⟨combine op v w,betterCompatible p n le op a v b w hv hw,?_⟩
  cases op <;> rfl

theorem projectedClosed {R S} (rows : S → R) {p n : R → Prop} {le : R → R → Prop}
    {g : Wire R}
    (hp : ∀ r, g (rows r)=true → ∃ x, p x ∧ g x=true ∧ le x (rows r))
    (hn : ∀ r, g (rows r)=false → ∃ x, n x ∧ g x=false ∧ le (rows r) x)
    (w : Wire S) (h : projected rows p n le g w) : w=restrictRows rows g := by
  obtain ⟨v,hv,rfl⟩ := h
  funext r
  change v (rows r) = g (rows r)
  cases e : g (rows r) with
  | false =>
    obtain ⟨x,xn,xe,xr⟩ := hn r e
    have no := hv.2.1 x xn xe
    cases j : v (rows r) with
    | false => rfl
    | true => have bad := hv.2.2 (rows r) x xr j; simp_all
  | true =>
    obtain ⟨x,xp,xe,xr⟩ := hp r e
    exact hv.2.2 x (rows r) xr (hv.1 x xp xe)

theorem chargedBound {R S} (rows : S → R) {p n : R → Prop} {le : R → R → Prop}
    {g : Wire R} (hp : ∀ r, g (rows r)=true → ∃ x, p x ∧ g x=true ∧ le x (rows r))
    (hn : ∀ r, g (rows r)=false → ∃ x, n x ∧ g x=false ∧ le (rows r) x)
    (nc : ¬Constant (restrictRows rows g)) {s ws} (h : Run false g s ws)
    (roots : List (Wire S)) {base bank L}
    (hr : Reach false roots base bank)
    (cover : ∀ v ∈ ws, supplied (projected rows p n le) bank v)
    (lo : ∀ q out, Reach false roots q out → Available false out (restrictRows rows g) → L≤q) :
    L + virtualMass (projected rows p n le) ws ≤ base + s := by
  obtain ⟨q,out,hq,hv,ineq⟩ := dominatedContraction nc (projected rows p n le)
    (projectedCompatible rows p n le) (projectedClosed rows hp hn) h roots hr cover
  have b := lo q out hq hv
  omega

end ImprovedCofactor

namespace TestedCube
def rowLe (m : Nat) (r s : Row) : Bool :=
  (r.val &&& s.val &&& m) == (r.val &&& m)
def cover (m : Nat) (g domain : Sig) (pos negs : List Row) (r : Row) : Bool :=
  !bit r domain || (if bit r g then pos.any (fun p => bit p g && rowLe m p r)
                    else negs.any (fun n => !bit n g && rowLe m r n))

theorem witnesses (m : Nat) (g domain : Sig) (pos negs : List Row)
    (ok : ∀ r, cover m g domain pos negs r=true)
    (f : Row → Row) (dom : ∀ r, bit (f r) domain=true) :
    (∀ r, observe g (f r)=true → ∃ x ∈ pos, observe g x=true ∧ rowLe m x (f r)=true) ∧
    (∀ r, observe g (f r)=false → ∃ x ∈ negs, observe g x=false ∧ rowLe m (f r) x=true) := by
  constructor
  · intro r h
    change bit (f r) g=true at h
    have q := ok (f r)
    simpa [cover,dom r,h,List.any_eq_true,observe] using q
  · intro r h
    change bit (f r) g=false at h
    have q := ok (f r)
    simpa [cover,dom r,h,List.any_eq_true,observe] using q

def geometry (m : Nat) (g d : Sig) (p n : List Row) := ∀ r, cover m g d p n r=true

abbrev Dom (m : Nat) (p n : List Row) (f : Row → Row) :=
  ImprovedCofactor.projected f (fun r => r ∈ p) (fun r => r ∈ n) (fun r s => rowLe m r s=true)

def monotoneSig (m : Nat) (w : Sig) := ∀ r s, rowLe m r s=true → bit r w=true → bit s w=true

def constTest (p n : List Row) (a : Sig) :=
  p.all (fun r => !(bit r a)) || n.all (fun r => bit r a)

theorem constTest_sound {m : Nat} {p n : List Row} (f : Row → Row) {a : Sig}
    (h : constTest p n a=true) : ImprovedCofactor.Virtual (Dom m p n f) (observe a) := by
  simp only [constTest,Bool.or_eq_true,List.all_eq_true,Bool.not_eq_true'] at h
  rcases h with z | o
  · refine ⟨fun _ => false,⟨fun _ => false,⟨?_,?_,?_⟩,rfl⟩,⟨false,rfl⟩⟩
    · intro r hr on
      exact False.elim (by simpa [observe,z r hr] using on)
    · intros; rfl
    · intro _ _ _ h; exact h
  · refine ⟨fun _ => true,⟨fun _ => true,⟨?_,?_,?_⟩,rfl⟩,⟨true,rfl⟩⟩
    · intros; rfl
    · intro r hr off
      exact False.elim (by simpa [observe,o r hr] using off)
    · intros; rfl

theorem costCount {m : Nat} (p n : List Row) (f : Row → Row) (ws : List Sig) :
    ws.countP (constTest p n) ≤ ImprovedCofactor.virtualMass (Dom m p n f) (ws.map observe) := by
  classical
  induction ws with
  | nil => simp [ImprovedCofactor.virtualMass]
  | cons w ws ih =>
    simp only [List.countP_cons,List.map_cons,ImprovedCofactor.massCons]
    cases h : constTest p n w
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc := constTest_sound (m:=m) f h
      simpa [ImprovedCofactor.virtualCost,hc,Nat.add_comm] using Nat.succ_le_succ ih

theorem suppliedOf {m : Nat} {p n : List Row} (f : Row → Row) {a : Sig} {bank : List (Wire Row)}
    (mon : monotoneSig m a)
    (ready : constTest p n a=true ∨ Available false bank (restrictRows f (observe a))) :
    ImprovedCofactor.supplied (Dom m p n f) bank (observe a) := by
  rcases ready with con | av
  · obtain ⟨w,hw,c⟩ := constTest_sound (m:=m) f con
    exact ⟨w,hw,Or.inr (Or.inl c)⟩
  · exact ⟨_,⟨observe a,⟨fun _ _ h => h,fun _ _ h => h,mon⟩,rfl⟩,av⟩

theorem constantPoolCut {raw : List Sig} {T : Sig} {c : BoundPool}
    (valid : ValidPool false raw T c) (m : Nat) (pos negs : List Row)
    (geom : geometry m T c.domain pos negs) (k : Nat) (rest : List Sig)
    (choice : Choice) (paid : Bool)
    (mon : ∀ w ∈ choiceVal choice :: rest, monotoneSig m w)
    (known : ∀ a ∈ rest, constTest pos negs a=true ∨ availableB false c.domain c.wires a=true)
    (buy : if paid then choiceOK false c.domain c.wires choice=true
       else constTest pos negs (choiceVal choice)=true ∨ availableB false c.domain c.wires (choiceVal choice)=true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(choiceVal choice :: rest).countP (constTest pos negs))
    (nd : (choiceVal choice :: rest).Nodup) :
    Impossible false T k (choiceVal choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  obtain ⟨geoP,geoN⟩ := witnesses m T c.domain pos negs geom f dom
  let ws := choiceVal choice :: rest
  have done (b : Nat) (out : List (Wire Row)) (reach : Reach false (roots.map observe) b out)
      (supply : ∀ a ∈ ws, constTest pos negs a=true ∨ Available false out (restrictRows f (observe a)))
      (ex : b = c.paid+paid.toNat) : False := by
    have cover : ∀ v ∈ ws.map observe, ImprovedCofactor.supplied (Dom m pos negs f) out v := by
      intro v hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hv
      exact suppliedOf f (mon a ha) (supply a ha)
    have bnd := ImprovedCofactor.chargedBound f geoP geoN nc
      (list_run run ws nd rfl) (roots.map observe) reach cover lo
    have cnt := costCount (m:=m) pos negs f ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (constTest pos negs) at bound
    change c.bound + ImprovedCofactor.virtualMass (Dom m pos negs f) (ws.map observe) ≤ b+t at bnd
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hm
    · exact buy.imp_right (availableB_sound dom hs)
    · exact (known a hm).imp_right (availableB_sound dom hs)
  | true =>
    obtain ⟨out,hr,used⟩ := pay_choice dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a ha
    rcases List.mem_cons.mp ha with rfl | hm
    · exact Or.inr (used _ (by simp))
    · exact (known a hm).imp_right (availableB_sound dom (fun v h => used v (List.mem_cons_of_mem _ h)))

def rowsOf (s : Sig) : List Row := (List.finRange 512).filter fun r => bit r s
def inRows {s : Sig} {r : Row} (h : r ∈ rowsOf s) : bit r s=true :=
  (List.mem_filter.mp h).2

def virtualWord (ps ns w : Sig) := (ps &&& w == zero) || (ns &&& neg w == zero)

theorem virtualWord_sound {ps ns w : Sig} (h : virtualWord ps ns w = true) :
    constTest (rowsOf ps) (rowsOf ns) w = true := by
  simp only [virtualWord,Bool.or_eq_true,beq_iff_eq] at h
  simp only [constTest,Bool.or_eq_true,List.all_eq_true,Bool.not_eq_true']
  rcases h with v | v
  · left
    intro r hr
    have hp := inRows hr
    have eq := congrArg (bit r) v
    rw [bit_zero] at eq
    have eb : bit r (ps &&& w) = (bit r ps && bit r w) := by simp [bit]
    simpa only [eb,hp,Bool.true_and] using eq
  · right
    intro r hr
    have hn := inRows hr
    have eq := congrArg (bit r) v
    rw [bit_zero] at eq
    have hrw : bit r (ns &&& neg w) = (bit r ns && !(bit r w)) := by
      rw [show bit r (ns &&& neg w) = (bit r ns && bit r (neg w)) by simp [bit],bit_neg]
    rw [hrw,hn,Bool.true_and] at eq
    simpa using eq

theorem countUnder {α : Type} (p q : α → Bool) (sub : ∀ a, p a=true → q a=true) (xs : List α) :
    xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases e : p a <;> cases f : q a <;> simp_all [List.countP_cons] <;> omega

def gateCut (ps ns : Sig) (c : BoundPool) (k : Nat) (rest : List Sig) (g : Choice) :=
  let vir := virtualWord ps ns
  let supply := fun a => vir a || availableB false c.domain c.wires a
  let paid := !(supply (choiceVal g))
  ((k+c.paid+paid.toNat < c.bound+(choiceVal g::rest).countP vir) && rest.all supply) &&
    (!paid || choiceOK false c.domain c.wires g)

theorem gateCut_sound {raw T c} (valid : ValidPool false raw T c) (m) (ps ns : Sig)
    (geom : geometry m T c.domain (rowsOf ps) (rowsOf ns)) {k rest g}
    (mon : ∀ w ∈ choiceVal g :: rest, monotoneSig m w)
    (nd : (choiceVal g::rest).Nodup) (cut : gateCut ps ns c k rest g = true) :
    Impossible false T k (choiceVal g :: rest).toFinset := by
  let supply := fun a => virtualWord ps ns a || availableB false c.domain c.wires a
  let paid := !(supply (choiceVal g))
  change (((k+c.paid+paid.toNat < c.bound+(choiceVal g::rest).countP (virtualWord ps ns)) &&
    rest.all supply) && (!paid || choiceOK false c.domain c.wires g))=true at cut
  simp only [Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,Bool.or_eq_true] at cut
  have okay {a : Sig} (h : supply a = true) :
      constTest (rowsOf ps) (rowsOf ns) a=true ∨ availableB false c.domain c.wires a=true := by
    have h2 : virtualWord ps ns a=true ∨ availableB false c.domain c.wires a=true := by simpa [supply] using h
    exact h2.imp virtualWord_sound id
  apply constantPoolCut valid m _ _ geom k rest g paid mon (fun a ha => okay (cut.1.2 a ha)) _ _ nd
  · cases eq : supply (choiceVal g)
    · simpa [paid,eq] using cut.2
    · simpa [paid,eq] using okay eq
  · have ct := countUnder (virtualWord ps ns) (constTest (rowsOf ps) (rowsOf ns))
      (fun _ => virtualWord_sound) (choiceVal g :: rest)
    omega
end TestedCube
namespace CheckedNode
abbrev Rule := Nat → List Sig → Choice → Bool
def WellFoundedCut (u : Bool) (T : Sig) (cap : Nat) (good : Sig → Prop) (rules : Rule) :=
  ∀ (rest : List Sig) (op : Choice), (choiceVal op :: rest).Nodup →
    (∀ x ∈ choiceVal op :: rest, good x) → rules cap rest op=true → Impossible u T cap (choiceVal op :: rest).toFinset
def evalMove (rule : Rule) (c : NodeContext) (op : Nat) (a b z : Decor) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := restCov cov.1 (column d a.2) (column d b.2) ka kb
    if (rs ||| column d z.2) != BitVec.allOnes 448 then true else
    if !properB z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      rule (cap-1) rest (movedChoice op a b)

theorem evalMove_sound {good : Sig → Prop} {rule : Rule} {u T r s ws pools links cap a b op ka kb}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (allGood : ∀ v ∈ ws, good v.1) (opGood : good (dbin op a b).1)
    (valid : WellFoundedCut u T (cap-1) good rule)
    (pro : proper (dbin op a b).1) (fresh : (dbin op a b).1 ∉ ws.map Prod.fst)
    (test : evalMove rule (cap,ws.length,ws,preCov u ws,pools,links) op a b (dbin op a b) ka kb = true) :
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
  have be : ((restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 448) = false := by
    simpa using sep
  change (if (restCov (coverage (!u) ws) (column (!u) a.2) (column (!u) b.2) ka kb ||| column (!u) z.2) != BitVec.allOnes 448 then true else if !properB z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact valid (rest.map Prod.fst) (movedChoice op a b) ndc (by
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hm
    · exact opGood
    · obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
      exact allGood w (sub.subset hw)) test k hk h

def testPair (rule : Rule) (ctx : NodeContext) (a b : Decor) (op : Nat) :=
  let z := dbin op a b
  let attempt := evalMove rule ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true
def testRow (rule : Rule) (ctx : NodeContext) (a : Decor) (bs : List Decor) :=
    bs.all (fun b => (opsOf ctx.2.2.2.1.2).all (testPair rule ctx a b))
def testAll (rule : Rule) (ctx : NodeContext) : List Decor → Bool
  | [] => true
  | a::bs => testRow rule ctx a bs && testAll rule ctx bs

theorem all_binary {rule : Rule} {ctx ws} (h : testAll rule ctx ws=true) {a b : Decor} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, allowed ctx.2.2.2.1.2 d → testPair rule ctx a b d=true) ∨
      (∀ d, allowed ctx.2.2.2.1.2 d → testPair rule ctx b a d=true) := by
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

theorem testPair_at {rule : Rule} {ctx a b d} (h : testPair rule ctx a b d = true) (ka kb : Bool) :
    evalMove rule ctx d a b (dbin d a b) ka kb = true := by
  simp only [testPair,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2

theorem node_sound {good : Sig → Prop} {rule : Rule} {u T r s ws pools links cap}
    (pairs : properPairs T r s) (faith : ∀ w ∈ ws, faithful r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (allGood : ∀ v ∈ ws, good v.1)
    (stable : ∀ d a b, allowed u d → good a → good b → good (bin d a b))
    (valid : WellFoundedCut u T (cap-1) good rule)
    (checks : testAll rule (cap,ws.length,ws,preCov u ws,pools,links) ws = true) :
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
  have one (a b : Decor) (d : Nat) (legalOp : allowed u d) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : testPair rule (cap,ws.length,ws,preCov u ws,pools,links) a b d = true) :
      Impossible u T (cap-1) (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←binary_front nd aa bb ne']
    exact evalMove_sound pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' allGood (stable d a.1 b.1 legalOp (allGood _ aa) (allGood _ bb)) valid
      pr fr (testPair_at test ka kb)
  rcases all_binary checks haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb pro fresh (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    exact one b a (flipOp d) (flip_flip hd).1 hbW haW (Ne.symm ne) kb ka (bin_flip hd a.1 b.1 ▸ pro)
      (bin_flip hd a.1 b.1 ▸ fresh) (hh _ (flip_flip hd).1)



end CheckedNode
namespace SearchRule
abbrev Regions := List (Sig × Sig × Sig)
def extrema (regions : Regions) (domain : Sig) : Sig × Sig :=
    ((regions.find? fun it => it.1 == domain).map Prod.snd).getD (one,one)

theorem rowLe_self (m : Nat) (r : Row) : TestedCube.rowLe m r r = true := by
  simp [TestedCube.rowLe]

theorem domain_default (m : Nat) (T d : Sig) :
    TestedCube.geometry m T d (TestedCube.rowsOf one) (TestedCube.rowsOf one) := by
  intro r
  have hm : r ∈ TestedCube.rowsOf one := List.mem_filter.mpr ⟨by simp,bit_one r⟩
  cases hd : bit r d
  · simp [TestedCube.cover,hd]
  · cases ht : bit r T
    · simp only [TestedCube.cover,hd,ht,Bool.not_true,Bool.false_or,Bool.false_eq_true,ite_false,List.any_eq_true,Bool.and_eq_true]
      exact ⟨r,hm,by simp [ht],rowLe_self m r⟩
    · simp only [TestedCube.cover,hd,ht,Bool.not_true,Bool.false_or,ite_true,List.any_eq_true,Bool.and_eq_true]
      exact ⟨r,hm,ht,rowLe_self m r⟩

theorem extrema_sound {m T regions} (ok : ∀ c ∈ regions,
    TestedCube.geometry m T c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2)) (d) :
    TestedCube.geometry m T d (TestedCube.rowsOf (extrema regions d).1)
      (TestedCube.rowsOf (extrema regions d).2) := by
  unfold extrema
  cases found : regions.find? (fun it => it.1==d) with
  | none => exact domain_default m T d
  | some c =>
    have eq : c.1=d := beq_iff_eq.mp (List.find?_some (p:=fun z : Sig × Sig × Sig => z.1==d) (a:=c) found)
    subst d
    exact ok c (List.mem_of_find?_eq_some found)

def step (T : Sig) (rs : Regions) (po : List BoundPool) (links : Nat → List (List Sig))
    (crosses : Nat → Option CrossCheck.Corners) : CheckedNode.Rule := fun k rest op =>
  let ws := choiceVal op::rest
  let tag := keySet ws
  (links tag).any (sameWords ws) ||
    po.any (fun c => let en := extrema rs c.domain
                     TestedCube.gateCut en.1 en.2 c k rest op) ||
    ((crosses tag).map (CrossCheck.cross ws T k)).getD false

theorem step_sound {raw T} (m : Nat) (rs : Regions) (po : List BoundPool) (ls crosses k)
    (geometry : ∀ c ∈ rs, TestedCube.geometry m T c.1 (TestedCube.rowsOf c.2.1)
      (TestedCube.rowsOf c.2.2))
    (pv : ∀ p∈po, ValidPool false raw T p)
    (link : ∀ tag xs, xs∈ls tag → Impossible false T k (List.toFinset xs)) :
    CheckedNode.WellFoundedCut false T k (TestedCube.monotoneSig m) (step T rs po ls crosses) := by
  intro rest op nd mon ok
  simp only [step,Bool.or_eq_true,List.any_eq_true] at ok
  rcases ok with (⟨ws,hl,eq⟩ | ⟨c,hc,cut⟩) | kw
  · rw [sameWords_sound eq]
    exact link _ _ hl
  · exact TestedCube.gateCut_sound (pv c hc) m _ _ (extrema_sound geometry _) mon nd cut
  · cases atKey : crosses (keySet (choiceVal op::rest)) with
    | none => simp [atKey] at kw
    | some witness =>
      apply CrossCheck.cross_sound nd T k witness
      simpa [atKey] using kw
end SearchRule
namespace MonotoneForest
open TestedCube

def legalProgram : Nat → Nat → Bool
  | 0,_ => true
  | n+1,ops => decide (((ops >>> 8) &&& 3)<2) && legalProgram n (ops >>> 10)

theorem stable (m d : Nat) (a b : Sig) (ok : allowed false d)
    (ha : monotoneSig m a) (hb : monotoneSig m b) : monotoneSig m (bin d a b) := by
  rcases allowed_four ok with rfl | rfl | ⟨bad,_⟩ | ⟨bad,_⟩
  · intro r s le h
    have pair : bit r a=true ∧ bit r b=true := by simpa [bit_bin] using h
    simpa [bit_bin] using And.intro (ha r s le pair.1) (hb r s le pair.2)
  · intro r s le h
    have either : bit r a=true ∨ bit r b=true := by simpa [bit_bin] using h
    simpa [bit_bin] using either.imp (ha r s le) (hb r s le)
  · cases bad
  · cases bad

theorem getMono (m : Nat) (ws : List Decor) (all : ∀ v ∈ ws, monotoneSig m v.1) (j : Nat) :
    monotoneSig m (ws.getD j defaultDecor).1 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : ws[j]? with
  | none =>
    intro r s le h
    change bit r zero=true at h
    rw [bit_zero] at h
    contradiction
  | some v => exact all v (List.mem_of_getElem? eq)

theorem decMono (m d ops : Nat) (ws : List Decor) (ok : legalProgram d ops=true)
    (all : ∀ v ∈ ws, monotoneSig m v.1) : ∀ v ∈ decodeBank d ops ws, monotoneSig m v.1 := by
  induction d generalizing ops ws with
  | zero => exact all
  | succ d ih =>
    simp only [legalProgram,Bool.and_eq_true,decide_eq_true_eq] at ok
    apply ih _ _ ok.2
    intro v hv
    rcases List.mem_append.mp hv with hm | hm
    · exact all v hm
    · obtain rfl := List.mem_singleton.mp hm
      exact stable _ _ _ _ (Or.inl ok.1) (getMono m ws all _) (getMono m ws all _)

theorem wireMono (g : Forest) : ∀ v ∈ wiresOf g, monotoneSig g.mask v.1 := by
  intro v hv
  obtain ⟨⟨j,a⟩,ha,rfl⟩ := List.mem_map.mp hv
  obtain ⟨lt,rfl⟩ := selected_entry ha
  have edge : g.mask.testBit j=true := by
    obtain ⟨u,hu,h⟩ := List.mem_filterMap.mp ha
    split at h
    next on => cases h; exact on
    next => contradiction
  intro r s le h
  rw [input_coords ⟨j,lt⟩] at h ⊢
  have he := congrArg (fun x : Nat => x.testBit j) (beq_iff_eq.mp le)
  simpa [Nat.testBit_and,edge,h] using he

def programOK (g : Forest) (k i : Nat) :=
  legalProgram (g.levels k).2.1 (readNode g k i).1

theorem stateMono (g : Forest) (k i : Nat) (ok : programOK g k i=true) :
    ∀ v∈(readNode g k i).2.2, monotoneSig g.mask v.1 := by
  intro v hv
  exact decMono g.mask (g.levels k).2.1 (readNode g k i).1 (wiresOf g) ok
    (wireMono g) v ((selectLive_sub _ _).subset hv)

def verify (rs : SearchRule.Regions) (crosses : Nat → Option CrossCheck.Corners) (g : Forest) (k i : Nat) :=
  let ws := (readNode g k i).2.2
  let context := contextOf g k i
  let rule := SearchRule.step (targetOf g) rs context.2.2.2.2.1 context.2.2.2.2.2 crosses
  (programOK g k i && decide ((ws.map Prod.fst).Nodup) && !(ws.map Prod.fst).contains (targetOf g)) &&
    (if k=0 then true else CheckedNode.testAll rule context ws)

theorem verify_sound {g : Forest} (rs : SearchRule.Regions) (crosses : Nat → Option CrossCheck.Corners) (k i : Nat)
    (hu : g.mode=false)
    (samples : properPairs (targetOf g) (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (subcube ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, autoOK (targetOf g) (x.map swapRows) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, Impossible g.mode (targetOf g) (k-1) (stateSet g (k-1) j).toFinset)
    (geo : ∀ c ∈ rs, geometry g.mask (targetOf g) c.1 (rowsOf c.2.1) (rowsOf c.2.2))
    (checked : verify rs crosses g k i = true) :
    Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [verify,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have pr := checked.1.1.1
  have nd := checked.1.1.2
  have out : targetOf g ∉ stateSet g k i := by simpa [stateSet] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    obtain rfl : t=0 := by omega
    exact out (List.mem_toFinset.mp (by rw [h.1]; exact Finset.mem_singleton_self _))
  let ctx := contextOf g k i
  let rule := SearchRule.step (targetOf g) rs ctx.2.2.2.2.1 ctx.2.2.2.2.2 crosses
  have tests : CheckedNode.testAll rule ctx (readNode g k i).2.2=true := by
    simpa only [h0,if_false] using checked.2
  have pv : ∀ c∈ctx.2.2.2.2.1, ValidPool false (vars g.mask) (targetOf g) c := by
    intro c hc
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hc
    simpa only [hu] using buildRule_sound g cols h
  have lv : ∀ tag xs, xs∈ctx.2.2.2.2.2 tag → Impossible false (targetOf g) (k-1) xs.toFinset := by
    intro tag xs hx
    have e : ((g.index k tag).bind (linkedSet g (k-1)))=some xs := by simpa [ctx,contextOf] using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    simpa only [hu] using linkedSet_sound g _ names (prior (by omega)) h
  have wsFaith : ∀ v∈(readNode g k i).2.2, faithful (asRow fun j => (g.samples j).1) (asRow fun j => (g.samples j).2) v := by
    intro v hv
    exact decode_faithful _ _ _ _ _ (wires_faithful g) v ((selectLive_sub _ _).subset hv)
  have testFalse : CheckedNode.testAll rule
      (k,(readNode g k i).2.2.length,(readNode g k i).2.2,preCov false (readNode g k i).2.2,
        ctx.2.2.2.2.1,ctx.2.2.2.2.2) (readNode g k i).2.2=true := by
    rw [←hu]
    exact tests
  rw [hu]
  exact CheckedNode.node_sound samples wsFaith nd out (stateMono g k i pr) (stable g.mask)
    (SearchRule.step_sound g.mask rs _ _ crosses _ geo pv lv) testFalse

def pieces (pred : Nat → Bool) (start n : Nat) : Nat → Prop
  | 0 => (List.range n).all (fun j => pred (start+j)) = true
  | d+1 => pieces pred start (n/2) d ∧ pieces pred (start+n/2) (n-n/2) d

theorem pieces_ok {pred start n d} (ok : pieces pred start n d) (j : Nat) (hj : j<n) :
    pred (start+j) = true := by
  induction d generalizing start n j with
  | zero => exact List.all_eq_true.mp ok j (List.mem_range.mpr hj)
  | succ d ih =>
    by_cases e : j<n/2
    · exact ih ok.1 j e
    · have t := ih ok.2 (j-n/2) (by omega)
      have splitAt : start+n/2+(j-n/2) = start+j := by omega
      rwa [splitAt] at t

abbrev Checked (r : SearchRule.Regions) (crosses : Nat → Option CrossCheck.Corners) (g : Forest) :=
  ∀ k ≤ g.cap, ∀ i < (g.levels k).1, verify r crosses g k i = true

theorem allImpossible {rs crosses} (g : Forest) (hu : g.mode=false)
    (prior : Nat → Nat) (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true)
    (geo : ∀ c ∈ rs, TestedCube.geometry g.mask (targetOf g) c.1 (rowsOf c.2.1) (rowsOf c.2.2))
    (rows : Checked rs crosses g) :
    ∀ k ≤ g.cap, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    exact verify_sound rs crosses 0 i hu (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega) geo (rows 0 hk i hi)
  | succ k ih =>
    intro hk i hi
    exact verify_sound rs crosses _ i hu (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega)) geo (rows _ hk i hi)

theorem fromRoot {g : Forest} (all : ∀ i<(g.levels g.cap).1,
    Impossible g.mode (targetOf g) g.cap (stateSet g g.cap i).toFinset)
    {idx l} (row : indexedRoot g g.cap idx l=true) : Impossible g.mode (targetOf g) g.cap l.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at row
  rw [←sameWords_sound row.2]
  exact all idx row.1

theorem fromImpossible {g : Forest} {hints} (ok : Impossible g.mode (targetOf g) g.cap (vars g.mask).toFinset)
    (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints)=true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ ok
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha

def regionGrid (m : Nat) (T : Sig) (c : Sig × Sig × Sig) : Bool :=
  (List.finRange 512).all (TestedCube.cover m T c.1 (rowsOf c.2.1) (rowsOf c.2.2))

theorem regions_ok {m : Nat} {T : Sig} {rs : SearchRule.Regions} (h : rs.all (regionGrid m T)=true) : ∀ c∈rs,
    TestedCube.geometry m T c.1 (rowsOf c.2.1) (rowsOf c.2.2) := by
  intro c hc r
  exact List.all_eq_true.mp (List.all_eq_true.mp h c hc) r (by simp)

def corners (p n : List Row) (bits : Nat) : CrossCheck.Corners :=
  (p.getD (bits &&& 15) 0,n.getD ((bits >>> 4) &&& 15) 0,p.getD ((bits >>> 8) &&& 15) 0,
   p.getD ((bits >>> 12) &&& 15) 0,n.getD ((bits >>> 16) &&& 15) 0,n.getD ((bits >>> 20) &&& 15) 0)
end MonotoneForest

def rowMask (xs : List Nat) : Sig := BitVec.ofNat 512 (xs.foldl (fun w r => w ||| (1 <<< r)) 0)
def mK51 := extendKnown K507 4 [(390,[32,116,133,100,101]),(356,[128,81,32,49,66,99,116]),(353,[96,81,33,50,64,131,67,116])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV51 : Known false mK51 := extend_ok (m:=51) (known_down V507) (lower_down low51) (by decide +kernel)
def mK55 := extendKnown mK51 5 [(468,[32,65,96,48,113,133,49]),(465,[113,130,49,101,82])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV55 : Known false mK55 := extend_ok (m:=55) mV51 (lower_down low55) (by decide +kernel)
def mK115 := extendKnown mK55 5 [(241,[113,33,50]),(421,[32,16,84,116,134])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV115 : Known false mK115 := extend_ok (m:=115) mV55 (lower_down low115) (by decide +kernel)
def mK119 := extendKnown mK115 7 [(119,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV119 : Known false mK119 := extend_ok (m:=119) mV115 (lower_down low119) (by decide +kernel)
def mK147 := extendKnown mK119 5 [(332,[32,49,132,84,101,118])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV147 : Known false mK147 := extend_ok (m:=147) mV119 (lower_down low147) (by decide +kernel)
def mK151 := extendKnown mK147 6 [(333,[49,100,84,135])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV151 : Known false mK151 := extend_ok (m:=151) mV147 (lower_down low151) (by decide +kernel)
def mK179 := extendKnown mK151 7 [(406,[32,116,133,101])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV179 : Known false mK179 := extend_ok (m:=179) mV151 (lower_down low179) (by decide +kernel)
def mK181 := extendKnown mK179 7 [(357,[130,84,100,114])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV181 : Known false mK181 := extend_ok (m:=181) mV179 (lower_down low181) (by decide +kernel)
def mK219 := extendKnown mK181 8 [(476,[32,49,65,129,81,118]),(462,[32,49,132,84,118])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV219 : Known false mK219 := extend_ok (m:=219) mV181 (lower_down low219) (by decide +kernel)
def mK221 := extendKnown mK219 7 [(231,[80,49,33,98,66,64])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV221 : Known false mK221 := extend_ok (m:=221) mV219 (lower_down low221) (by decide +kernel)
def mK223 := extendKnown mK221 9 [(415,[32,116,134]),(351,[49,100,135])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV223 : Known false mK223 := extend_ok (m:=223) mV221 (lower_down low223) (by decide +kernel)
def mK243 := extendKnown mK223 8 [(377,[49,33,100,84,135])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV243 : Known false mK243 := extend_ok (m:=243) mV223 (lower_down low243) (by decide +kernel)
def mK251 := extendKnown mK243 10 [(505,[49,33,114,100,130]),(446,[32,116,134])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV251 : Known false mK251 := extend_ok (m:=251) mV243 (lower_down low251) (by decide +kernel)
def mK254 := extendKnown mK251 9 [(491,[32,49,132,118])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mV254 : Known false mK254 := extend_ok (m:=254) mV251 (lower_down low254) (by decide +kernel)
def mo247Y : Array Signals := #[(sR64,sR71),(sR89,sR80),(sR20,sR29),(0,0),(sR96,sR42),(sR108,sR56),(sR4,sR59),(sR2,sR62),(0,0)]
def mo247C : List ColumnInfo := [(64,0,183,0,9),(0,64,182,1,8),(2,0,245,0,8),(4,0,243,0,8),(32,0,215,0,8),(1,0,182,0,7),(16,0,231,0,7),(36,0,211,0,7),(128,0,119,0,7),(0,2,101,144,6),(0,4,83,160,6),(0,32,146,5,6),(96,0,151,0,6),(1,32,146,4,5),(2,64,180,1,5),(4,32,146,1,5),(6,0,241,0,5),(16,2,101,128,5),(100,0,147,0,5),(128,2,101,16,5),(128,4,83,32,5),(3,64,180,0,4),(38,0,209,0,4),(82,0,165,0,4)]
def mo247A : List (List Nat) := [[]]
def mo247D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x291210a031146ca1c471b287104bc61e8b4f0f00edd634c960ef96358120d6d545c863d75545c463d79545c063
def mo247D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1318439b108827ec18465aea20a3436c43031442f912139122003ef2ca217f82458d719157d44145309921e623d5c6322d38c24db8f1045c6f18c2eb4896c23ad8492bcc225e68934e6448ec9e4bbe0e44995d28b23f244bbe089958065006880e8628c8532b86b180f1d90bcc2a2c6a3804239350293c84414389858e2884a4700629705935450f3acb923c6711c16fa3acdc346c82e6aca789321a7e1d26797452112380aa1e044080018994e24338b193aa97438dbaa808b9022e208b803ac6f0b1b3aa6ceaa53aa8aea9abaa672991d2c26ab1cdac0929914a4256b01526234908dac036980b2c900ba00ae404b881ae01ffff7f7f7f7eff3f7f7fbf5f6f76f58d615815454d324c5304852044063
def mo247H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6b00024a400480000000040
def mo247D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ca4915eca04baacf045be704b7d84027afa0263ba125a995261722137e4809ada1217582bbed9022c48cec053945d10568558d025228c2e2348805087906a74ce2efd70321609840998a63f1104801592b1c63a874cab0d41a63486b0530a41440aa153ffdf
def mo247H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x11e80b240000000015800002fc00bc1c5946d11fde48015d000000000000000000000000000d750001af00418000000240006a00520000036800aaa3000001662fb8d001b9000000000000000093006e800c70000001a4c10030
def mo247D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8218402ff
def mo247H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9e000000008c009b008100001a6400a000f7995d00a695e8b302
def mo247L : Nat → Packing
  | 7 => (5,3,5,0,0,7,0,mo247D7)
  | 8 => (32,2,5,851980,68,10,1065,mo247D8)
  | 9 => (15,1,5,131073,16,9,1048,mo247D9)
  | 10 => (1,0,5,0,0,0,0,mo247D10)
  | _ => emptyPacking
def mo247I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 13 0 7 3 0 mo247H8
  | 9 => lookupWord 8 83 3 9 5 0 mo247H9
  | 10 => lookupWord 3 29 0 8 4 0 mo247H10
  | _ => fun _ => none
def mo247 : Forest := ⟨1271,10,fun i => mo247Y[i]?.getD (0,0),mo247C,mo247A,mo247L,mo247I⟩
def mo247Q : SearchRule.Regions := [
(subcube 64 0,rowMask [17,18,33,36,130,132,144],rowMask [7,20,34,48,129,160]),
(subcube 0 64,rowMask [65,82,100,194,196,208],rowMask [70,84,98,112,224]),
(subcube 2 0,rowMask [17,33,36,65,132,144],rowMask [5,84,112,129,224]),
(subcube 4 0,rowMask [17,18,33,65,130,144],rowMask [3,98,112,129,224]),
(subcube 32 0,rowMask [17,18,65,130,132,144],rowMask [7,70,84,129,192]),
(subcube 1 0,rowMask [18,36,130,132,144],rowMask [70,84,98,112,224]),
(subcube 16 0,rowMask [33,36,65,130,132],rowMask [7,70,98,129,224]),
(subcube 36 0,rowMask [17,18,65,130,144],rowMask [3,66,80,129,192]),
(subcube 128 0,rowMask [17,18,33,36,65],rowMask [7,70,84,98,112]),
(subcube 0 2,rowMask [18,35,38,67,130],rowMask [7,70,98]),
(subcube 0 4,rowMask [21,22,36,69,132],rowMask [7,70,84]),
(subcube 0 32,rowMask [33,36,50,162,176],rowMask [98,112,224]),
(subcube 96 0,rowMask [17,18,130,132,144],rowMask [7,20,129]),
(subcube 1 32,rowMask [36,50,162,176],rowMask [98,112,224]),
(subcube 2 64,rowMask [65,100,196,208],rowMask [84,112,224]),
(subcube 4 32,rowMask [33,50,162,176],rowMask [98,112,224]),
(subcube 6 0,rowMask [17,33,65,144],rowMask [112,129,224]),
(subcube 16 2,rowMask [35,38,67,130],rowMask [7,70,98]),
(subcube 100 0,rowMask [17,18,130,144],rowMask [3,16,129]),
(subcube 128 2,rowMask [18,35,38,67],rowMask [7,70,98]),
(subcube 128 4,rowMask [21,22,36,69],rowMask [7,70,84]),
(subcube 3 64,rowMask [100,196,208],rowMask [84,112,224]),
(subcube 38 0,rowMask [17,65,144],rowMask [80,129,192]),
(subcube 82 0,rowMask [33,36,132],rowMask [5,129,160])]
def mo247X (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd800191e00d45946c9ada6c901020
def mo247Z : Array Nat := #[2500179,2511670,5379088,5452818,5510160,5518370,5649426]
def mo247F (h : Nat) := ((lookupWord 3 17 2 7 3 0 mo247X h).map fun a => MonotoneForest.corners [17,18,33,36,65,130,132,144] [7,70,84,98,112,129,224] (mo247Z[a.1]?.getD 0))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247G : graphValid mo247 (boundsBefore mK254) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247E : ∀ c ∈ mo247Q, TestedCube.geometry mo247.mask (targetOf mo247) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := MonotoneForest.regions_ok (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247T : MonotoneForest.Checked mo247Q mo247F mo247 := by
  intro k hk
  change k ≤ 10 at hk
  interval_cases k
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo247Q mo247F mo247 7) 0 5 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo247Q mo247F mo247 8) 0 32 3 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo247Q mo247F mo247 9) 0 15 2 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo247Q mo247F mo247 10) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
theorem mo247All : ∀ k ≤ mo247.cap, ∀ i < (mo247.levels k).1, Impossible mo247.mode (targetOf mo247) k (stateSet mo247 k i).toFinset := MonotoneForest.allImpossible mo247 (by decide) (boundsBefore mK254) (before_sound mK254 mV254) mo247G mo247E mo247T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247R : Impossible false (targetOf mo247) 10 (vars 247).toFinset := MonotoneForest.fromRoot (g:=mo247) (mo247All 10 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247Low : Lower false (varsX 247) (graphGoal 247) 11 := MonotoneForest.fromImpossible (g:=mo247) (hints:=268436804) mo247R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo247K := extendKnown mK254 11 [(439,[32,116,134]),(247,[]),(493,[32,49,132,118]),(381,[49,100,135])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo247V : Known false mo247K := extend_ok (m:=247) mV254 mo247Low (by decide +kernel)
def mo471Y : Array Signals := #[(sR98,sR66),(sR36,sR68),(sR94,sR84),(0,0),(sR104,sR86),(0,0),(sR110,sR23),(sR0,sR30),(sR3,sR35)]
def mo471C : List ColumnInfo := [(1,0,470,0,8),(2,0,469,0,8),(4,0,467,0,8),(64,0,407,0,8),(256,0,215,0,8),(0,64,150,257,7),(0,256,147,68,7),(16,0,455,0,7),(65,0,406,0,7),(128,0,343,0,7),(260,0,211,0,7),(0,1,390,80,6),(0,2,325,144,6),(0,4,83,384,6),(1,64,150,256,6),(1,256,146,68,6),(4,64,146,257,6),(64,256,147,4,6),(256,64,150,1,6),(320,0,151,0,6),(3,0,468,0,5),(6,0,465,0,5),(16,1,390,64,5),(16,2,325,128,5),(128,2,325,16,5),(128,4,83,256,5),(67,0,404,0,4),(144,2,325,0,4),(262,0,209,0,4)]
def mo471A : List (List Nat) := [[],[32,116,134]]
def mo471D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x378c401d88e910f5087660937a0862780885cbc92cbc129c909281e6257a60311418a8c42001405320bc1024880ec0995184064a62122c4072df7d1b387613706d8aa7a4c22014718d710d7011537960795055313521396039502174057109701fefef7eff7ebedbd535412044053
def mo471D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x12ec257fd51882df8670448cc0450fe418ee181272e6c4a7f220270227447bf100971031608052284a6d369114d80690f2c98c1207f4d2b79c866851341c0058d5314d43505315815048110ff
def mo471H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2ca00d1ea4d98283eadcc37226e4014ad8368918060800007201a8
def mo471D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x408862ff
def mo471H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1d4860071000000003c0001c900000000000000240000002a60020ed80000007d000009300001f900010000084416e0004
def mo471L : Nat → Packing
  | 8 => (13,2,5,458757,51,8,1051,mo471D8)
  | 9 => (10,1,5,65537,0,8,1050,mo471D9)
  | 10 => (1,0,5,0,0,0,0,mo471D10)
  | _ => emptyPacking
def mo471I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 4 23 4 9 4 1 mo471H9
  | 10 => lookupWord 4 43 1 9 4 1 mo471H10
  | _ => fun _ => none
def mo471 : Forest := ⟨1495,10,fun i => mo471Y[i]?.getD (0,0),mo471C,mo471A,mo471L,mo471I⟩
def mo471Q : SearchRule.Regions := [
(subcube 1 0,rowMask [18,130,132,144,260,320],rowMask [70,84,192,258,272,384]),
(subcube 2 0,rowMask [17,65,132,144,260,320],rowMask [5,84,192,272,385]),
(subcube 4 0,rowMask [17,18,65,130,144,320],rowMask [66,80,192,259,272,385]),
(subcube 64 0,rowMask [17,18,130,132,144,260],rowMask [7,20,259,272,385]),
(subcube 256 0,rowMask [17,18,65,130,132,144],rowMask [7,70,84,129,192]),
(subcube 0 64,rowMask [65,82,194,196,208,320],rowMask [70,84,192]),
(subcube 0 256,rowMask [260,273,274,320,386,400],rowMask [259,272,385]),
(subcube 16 0,rowMask [65,130,132,260,320],rowMask [7,70,192,259,385]),
(subcube 65 0,rowMask [18,130,132,144,260],rowMask [6,20,258,272,384]),
(subcube 128 0,rowMask [17,18,65,260,320],rowMask [7,70,84,259,272]),
(subcube 260 0,rowMask [17,18,65,130,144],rowMask [3,66,80,129,192]),
(subcube 0 1,rowMask [17,65,131,133,261],rowMask [7,259,385]),
(subcube 0 2,rowMask [18,67,130,262,322],rowMask [7,70,259]),
(subcube 0 4,rowMask [21,22,69,132,260],rowMask [7,70,84]),
(subcube 1 64,rowMask [82,194,196,208,320],rowMask [70,84,192]),
(subcube 1 256,rowMask [260,274,320,386,400],rowMask [258,272,384]),
(subcube 4 64,rowMask [65,82,194,208,320],rowMask [66,80,192]),
(subcube 64 256,rowMask [260,273,274,386,400],rowMask [259,272,385]),
(subcube 256 64,rowMask [65,82,194,196,208],rowMask [70,84,192]),
(subcube 320 0,rowMask [17,18,130,132,144],rowMask [7,20,129]),
(subcube 3 0,rowMask [132,144,260,320],rowMask [84,192,272,384]),
(subcube 6 0,rowMask [17,65,144,320],rowMask [80,192,272,385]),
(subcube 16 1,rowMask [65,131,133,261],rowMask [7,259,385]),
(subcube 16 2,rowMask [67,130,262,322],rowMask [7,70,259]),
(subcube 128 2,rowMask [18,67,262,322],rowMask [7,70,259]),
(subcube 128 4,rowMask [21,22,69,260],rowMask [7,70,84]),
(subcube 67 0,rowMask [132,144,260],rowMask [20,272,384]),
(subcube 144 2,rowMask [67,262,322],rowMask [7,70,259]),
(subcube 262 0,rowMask [17,65,144],rowMask [80,129,192])]
def mo471X (j : Nat) : Nat := if 1 ≤ j then 0 else 0x165200008c00600000000000000000000000afc0000000ca6c0000086800000000000000000602d80000000000006
def mo471Z : Array Nat := #[2504260,2512468,2520118,3564039,6516818,6640176]
def mo471F (h : Nat) := ((lookupWord 3 67 2 7 3 0 mo471X h).map fun a => MonotoneForest.corners [17,18,65,130,132,144,260,320] [7,70,84,192,259,272,385] (mo471Z[a.1]?.getD 0))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471G : graphValid mo471 (boundsBefore mo247K) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471E : ∀ c ∈ mo471Q, TestedCube.geometry mo471.mask (targetOf mo471) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := MonotoneForest.regions_ok (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471T : MonotoneForest.Checked mo471Q mo471F mo471 := by
  intro k hk
  change k ≤ 10 at hk
  interval_cases k
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo471Q mo471F mo471 8) 0 13 2 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo471Q mo471F mo471 9) 0 10 1 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo471Q mo471F mo471 10) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
theorem mo471All : ∀ k ≤ mo471.cap, ∀ i < (mo471.levels k).1, Impossible mo471.mode (targetOf mo471) k (stateSet mo471 k i).toFinset := MonotoneForest.allImpossible mo471 (by decide) (boundsBefore mo247K) (before_sound mo247K mo247V) mo471G mo471E mo471T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471R : Impossible false (targetOf mo471) 10 (vars 471).toFinset := MonotoneForest.fromRoot (g:=mo471) (mo471All 10 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471Low : Lower false (varsX 471) (graphGoal 471) 11 := MonotoneForest.fromImpossible (g:=mo471) (hints:=8858371908) mo471R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo471K := extendKnown mo247K 11 [(477,[49,100,135]),(471,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo471V : Known false mo471K := extend_ok (m:=471) mo247V mo471Low (by decide +kernel)
def mo501Y : Array Signals := #[(sR77,sR65),(0,0),(sR78,sR25),(0,0),(sR21,sR54),(sR95,sR73),(sR107,sR39),(sR1,sR75),(sR5,sR76)]
def mo501C : List ColumnInfo := [(16,0,485,0,8),(32,0,469,0,8),(64,0,437,0,8),(128,0,373,0,8),(256,0,245,0,8),(1,0,500,0,7),(4,0,497,0,7),(144,0,357,0,7),(320,0,181,0,7),(0,16,356,129,6),(0,64,180,257,6),(0,128,353,20,6),(0,256,177,68,6),(1,16,356,128,5),(1,64,180,256,5),(4,128,353,16,5),(4,256,177,64,5),(80,0,421,0,5),(176,0,325,0,4),(352,0,149,0,4)]
def mo501A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118]]
def mo501D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x381ff14154110
def mo501D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xfc624c5e3c90e07921e16485f824be04600ecb126e42301894840505c4063d1424e08e1b0134506481071f4d1ef0c49a745e381a01141a2c445084b1a1768acb15522a9c8731aa07fffdf7efdfd504c910
def mo501H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9
def mo501D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x65e099db2020e582577401ce203b89020224d28080830b8418918c61e4176547ca0a80589424c9504c110ff
def mo501H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x26464eb078c00300440008329c9036000b080078800003f400000002c7000009200000000000000000000000003c600000624000014100000000e5c80000000011470
def mo501D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20c400a0e3ff
def mo501H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1340000000016d4d8000000006490a001980000000030044000000248000000000000000000000000000002880128030000000000000000000072f9461000000000004
def mo501L : Nat → Packing
  | 7 => (1,3,5,0,0,0,0,mo501D7)
  | 8 => (10,2,5,327683,50,8,1046,mo501D8)
  | 9 => (6,1,5,65537,0,7,1042,mo501D9)
  | 10 => (1,0,5,0,0,0,0,mo501D10)
  | _ => emptyPacking
def mo501I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 4 0 0 mo501H8
  | 9 => lookupWord 5 53 2 10 4 2 mo501H9
  | 10 => lookupWord 3 59 1 9 3 2 mo501H10
  | _ => fun _ => none
def mo501 : Forest := ⟨1525,10,fun i => mo501Y[i]?.getD (0,0),mo501C,mo501A,mo501L,mo501I⟩
def mo501Q : SearchRule.Regions := [
(subcube 16 0,rowMask [33,36,65,132,260,320],rowMask [5,68,224,385,416]),
(subcube 32 0,rowMask [17,65,132,144,260,320],rowMask [5,84,192,272,385]),
(subcube 64 0,rowMask [17,33,36,132,144,260],rowMask [5,20,304,385,416]),
(subcube 128 0,rowMask [17,33,36,65,260,320],rowMask [5,84,112,257,304]),
(subcube 256 0,rowMask [17,33,36,65,132,144],rowMask [5,84,112,129,224]),
(subcube 1 0,rowMask [36,132,144,260,320],rowMask [84,112,224,304,416]),
(subcube 4 0,rowMask [17,33,65,144,320],rowMask [112,224,304,385,416]),
(subcube 144 0,rowMask [33,36,65,260,320],rowMask [5,68,96,257,288]),
(subcube 320 0,rowMask [17,33,36,132,144],rowMask [5,20,48,129,160]),
(subcube 0 16,rowMask [17,52,144,276,336],rowMask [84,112,304]),
(subcube 0 64,rowMask [65,100,196,208,320],rowMask [84,112,224]),
(subcube 0 128,rowMask [132,144,161,193,448],rowMask [224,385,416]),
(subcube 0 256,rowMask [260,273,289,320,400],rowMask [304,385,416]),
(subcube 1 16,rowMask [52,144,276,336],rowMask [84,112,304]),
(subcube 1 64,rowMask [100,196,208,320],rowMask [84,112,224]),
(subcube 4 128,rowMask [144,161,193,448],rowMask [224,385,416]),
(subcube 4 256,rowMask [273,289,320,400],rowMask [304,385,416]),
(subcube 80 0,rowMask [33,36,132,260],rowMask [5,385,416]),
(subcube 176 0,rowMask [65,260,320],rowMask [5,68,257]),
(subcube 352 0,rowMask [17,132,144],rowMask [5,20,129])]
def mo501X (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6f000380000060
def mo501Z : Array Nat := #[3564295,4603909]
def mo501F (h : Nat) := ((lookupWord 1 11 0 5 1 0 mo501X h).map fun a => MonotoneForest.corners [17,33,36,65,132,144,260,320] [5,84,112,224,304,385,416] (mo501Z[a.1]?.getD 0))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501G : graphValid mo501 (boundsBefore mo471K) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501E : ∀ c ∈ mo501Q, TestedCube.geometry mo501.mask (targetOf mo501) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := MonotoneForest.regions_ok (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501T : MonotoneForest.Checked mo501Q mo501F mo501 := by
  intro k hk
  change k ≤ 10 at hk
  interval_cases k
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo501Q mo501F mo501 7) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo501Q mo501F mo501 8) 0 10 1 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo501Q mo501F mo501 9) 0 6 1 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo501Q mo501F mo501 10) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
theorem mo501All : ∀ k ≤ mo501.cap, ∀ i < (mo501.levels k).1, Impossible mo501.mode (targetOf mo501) k (stateSet mo501 k i).toFinset := MonotoneForest.allImpossible mo501 (by decide) (boundsBefore mo471K) (before_sound mo471K mo471V) mo501G mo501E mo501T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501R : Impossible false (targetOf mo501) 10 (vars 501).toFinset := MonotoneForest.fromRoot (g:=mo501) (mo501All 10 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501Low : Lower false (varsX 501) (graphGoal 501) 11 := MonotoneForest.fromImpossible (g:=mo501) (hints:=9126806788) mo501R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo501K := extendKnown mo471K 11 [(501,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo501V : Known false mo501K := extend_ok (m:=501) mo471V mo501Low (by decide +kernel)
def mo479Y : Array Signals := #[(sR100,sR67),(sR37,sR83),(sR38,sR69),(sR93,sR85),(sR112,sR27),(0,0),(sR8,sR22),(sR9,sR31),(sR10,sR34)]
def mo479C : List ColumnInfo := [(1,0,478,0,11),(2,0,477,0,11),(4,0,475,0,11),(8,0,471,0,11),(16,0,463,0,9),(64,0,415,0,9),(128,0,351,0,9),(256,0,223,0,9),(0,2,333,144,8),(0,8,151,320,8),(0,16,332,131,8),(0,64,150,265,8),(0,128,329,22,8),(0,256,147,76,8),(3,0,476,0,8),(9,0,470,0,8),(17,0,462,0,8),(1,2,332,144,7),(16,128,329,6,7),(64,256,147,12,7),(128,16,332,3,7),(256,64,150,9,7),(320,8,151,0,6)]
def mo479A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def mo479D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc41005a38d4a68db44afaaf6af58fe1d5811907560064
def mo479D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8027e098de012a5f00e6e048c3f01c002024951210442218504a41941c1b841413838f8a09a144ec9c40002620cc057548eaa5d4c3a90987bfb7ecff595745d95460464600641d464
def mo479H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xca0000000022000001d300000085000020fd
def mo479D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5fe0c0983cbc00a1fc3f8049fd06018178b09da00cff380661033e4033c1063e404b0c60a8c252a345002901a2e2161048a932810363c18b0f8e8d94a3cb4279f150b806597cbad97530ea65d98c29574430a160c4c08d803fffbeffbfafdbdedf5d16455064
def mo479H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x38a940040d1001332b9960d8c49000000101001106
def mo479D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3e0014798077c00c00051a38260c58a79c543009147d4a900ba2c8322a9ff
def mo479H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x294d0000000ca195c971000e2000a159848f43709463d00070747e80002801
def mo479D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x620804ff
def mo479H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1d8000305cf540200010802a35d
def mo479L : Nat → Packing
  | 8 => (4,4,5,262146,33,5,1024,mo479D8)
  | 9 => (7,3,5,196613,35,8,1043,mo479D9)
  | 10 => (11,2,5,458756,50,8,1050,mo479D10)
  | 11 => (4,1,5,65537,0,6,1039,mo479D11)
  | 12 => (1,0,5,0,0,0,0,mo479D12)
  | _ => emptyPacking
def mo479I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 19 0 8 2 2 mo479H9
  | 10 => lookupWord 3 19 2 9 3 2 mo479H10
  | 11 => lookupWord 4 23 4 10 4 2 mo479H11
  | 12 => lookupWord 2 13 1 8 2 2 mo479H12
  | _ => fun _ => none
def mo479 : Forest := ⟨1503,12,fun i => mo479Y[i]?.getD (0,0),mo479C,mo479A,mo479L,mo479I⟩
def mo479Q : SearchRule.Regions := [
(subcube 1 0,rowMask [18,72,130,132,144,260,264,320],rowMask [14,28,70,84,136,192,258,272,384]),
(subcube 2 0,rowMask [17,65,72,132,144,260,264,320],rowMask [13,28,84,137,192,272,385]),
(subcube 4 0,rowMask [17,18,65,72,130,144,264,320],rowMask [11,24,66,80,137,192,259,272,385]),
(subcube 8 0,rowMask [17,18,65,130,132,144,260,320],rowMask [7,70,84,192,259,272,385]),
(subcube 16 0,rowMask [65,72,130,132,260,264,320],rowMask [15,70,137,192,259,385]),
(subcube 64 0,rowMask [17,18,130,132,144,260,264],rowMask [15,28,137,259,272,385]),
(subcube 128 0,rowMask [17,18,65,72,260,264,320],rowMask [15,28,70,84,259,272]),
(subcube 256 0,rowMask [17,18,65,72,130,132,144],rowMask [15,28,70,84,137,192]),
(subcube 0 2,rowMask [18,67,74,130,262,266,322],rowMask [15,70,259]),
(subcube 0 8,rowMask [25,26,72,138,140,152,264],rowMask [15,28,137]),
(subcube 0 16,rowMask [17,18,88,144,276,280,336],rowMask [28,84,272]),
(subcube 0 64,rowMask [65,72,82,194,196,208,320],rowMask [70,84,192]),
(subcube 0 128,rowMask [130,132,144,193,200,392,448],rowMask [137,192,385]),
(subcube 0 256,rowMask [260,264,273,274,320,386,400],rowMask [259,272,385]),
(subcube 3 0,rowMask [72,132,144,260,264,320],rowMask [28,84,136,192,272,384]),
(subcube 9 0,rowMask [18,130,132,144,260,320],rowMask [70,84,192,258,272,384]),
(subcube 17 0,rowMask [72,130,132,260,264,320],rowMask [14,70,136,192,258,384]),
(subcube 1 2,rowMask [18,74,130,262,266,322],rowMask [14,70,258]),
(subcube 16 128,rowMask [130,132,193,200,392,448],rowMask [137,192,385]),
(subcube 64 256,rowMask [260,264,273,274,386,400],rowMask [259,272,385]),
(subcube 128 16,rowMask [17,18,88,276,280,336],rowMask [28,84,272]),
(subcube 256 64,rowMask [65,72,82,194,196,208],rowMask [70,84,192]),
(subcube 320 8,rowMask [25,26,138,140,152],rowMask [15,28,137])]
def mo479X (j : Nat) : Nat := if 1 ≤ j then 0 else 0x63e0001
def mo479Z : Array Nat := #[7872800,8852000]
def mo479F (h : Nat) := ((lookupWord 1 11 0 5 1 0 mo479X h).map fun a => MonotoneForest.corners [17,18,65,72,130,132,144,260,264,320] [15,28,70,84,137,192,259,272,385] (mo479Z[a.1]?.getD 0))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479G : graphValid mo479 (boundsBefore mo501K) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479E : ∀ c ∈ mo479Q, TestedCube.geometry mo479.mask (targetOf mo479) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := MonotoneForest.regions_ok (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479T : MonotoneForest.Checked mo479Q mo479F mo479 := by
  intro k hk
  change k ≤ 12 at hk
  interval_cases k
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo479Q mo479F mo479 8) 0 4 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo479Q mo479F mo479 9) 0 7 1 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo479Q mo479F mo479 10) 0 11 2 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo479Q mo479F mo479 11) 0 4 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo479Q mo479F mo479 12) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
theorem mo479All : ∀ k ≤ mo479.cap, ∀ i < (mo479.levels k).1, Impossible mo479.mode (targetOf mo479) k (stateSet mo479 k i).toFinset := MonotoneForest.allImpossible mo479 (by decide) (boundsBefore mo501K) (before_sound mo501K mo501V) mo479G mo479E mo479T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479R : Impossible false (targetOf mo479) 12 (vars 479).toFinset := MonotoneForest.fromRoot (g:=mo479) (mo479All 12 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479Low : Lower false (varsX 479) (graphGoal 479) 13 := MonotoneForest.fromImpossible (g:=mo479) (hints:=8858396484) mo479R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo479K := extendKnown mo501K 13 [(479,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo479V : Known false mo479K := extend_ok (m:=479) mo501V mo479Low (by decide +kernel)
def mo503Y : Array Signals := #[(sR97,sR70),(sR101,sR79),(sR105,sR28),(0,0),(sR111,sR43),(sR13,sR57),(sR11,sR58),(sR12,sR61),(sR14,sR88)]
def mo503C : List ColumnInfo := [(2,0,501,0,11),(32,0,471,0,11),(64,0,439,0,11),(256,0,247,0,11),(1,0,502,0,10),(4,0,499,0,10),(16,0,487,0,10),(128,0,375,0,10),(0,2,357,144,9),(0,64,182,257,9),(0,256,179,68,9),(1,64,182,256,8),(4,256,179,64,8),(16,2,357,128,8),(18,0,485,0,8),(33,0,470,0,8),(34,0,469,0,8),(36,0,467,0,8),(64,256,179,4,8),(66,0,437,0,8),(96,0,407,0,8),(128,2,357,16,8),(130,0,373,0,8),(256,64,182,1,8),(288,0,215,0,8),(68,256,179,0,7),(97,0,406,0,7),(144,2,357,0,7),(146,0,357,0,7),(257,64,182,0,7),(292,0,211,0,7)]
def mo503A : List (List Nat) := [[],[32,116,134]]
def mo503D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xbb1590ac080bfb92f618b706446026c06bc21202740601643ba422fe2303f231342406f110d0760392ca70904b97a1811c4717c5e136246a0b8ede1b864de9bc4b81ca395e50ee1b92c6618f1703297caf4ea49067b379789436130701a0012c151a74765f2da5a865ef174b961e65849d6c269878a61215a6662a1c9b2336c4c1b42e2107cb1126d839640fd87e8b765b6ada76ad756797acaf62f715f87dbda5eca9f91ee6949050d706889050d705d09050d706888358d606848358d602859650d606909850d606549161943244906194324d63581202a5535812058d325812050d3258120
def mo503D9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0xc96e49d192b1cf74ca9d9e421fa2b19798b19702d25b40cb867cba057a528476cb8276cb817eca007eba0048cb837e520302d23940d2390e503846cab70ad3b64648b648c3b548c3352e50342e50333cc3b256d2320254323acbae3ec3b13ec33156cb2d5ecaad4ccbac56cb2c5ecaac44c3b044c33066ba3066b2306cd1b046c3af68ba2f2e502b12d3aa1ad32a28d2aa2cd12a14515a50cbd904d4d24cd3d75e42d74cca536042d64eba5670d0566242d550ba556442d452ba5452cbd82ad2d882ba5832d15822514e10d3cd18d2cd20d1cd24d0cd26d04d4acbbb40c3bf56d33f56b2bf3ecabc40ca3c4acbba54caba56ca3a44c3be5ab2be44c23e5ab23e70d03e08d03e46c3bd5cb2bd46c23d5cb23d78c3cb78c24b20d14b5ccbcc5ccacc5cca4c02d24a40d24a02d14a06d24a3cd34440d24402d1440254c73c54485c50c8404c46564c45404c458e50c120d34086b24090b1c242c3d058b2d042c25058b250564c4370d02902d22702d12702d12686b22580ba2890b1a490d3239aca239aba2326d32388b22390b1a390b1a286b2239aa1a1404c1c40521006d48d40cc0d5eca8d68420f6a420e0254110ed41e2ed21e32d11e36d09e7e42207e4c1288b29216d3932ad2932ed21332d11336d09388421990499996509908549826d31688b2169c421794b21794b1979c4214a0b994a0b194a0a19430519b7e421a88b2158cb19402d20c02d10c02d10a404c0b0c54099aba089aa18700d2391cd14b1ed0cb00d24a84b2238ab194ffaff2feefeafe6fbefbcfbafb7fb6fb5fb3fb2faefa7fa6f6ef67eeeeededeeb7e7edfddfbdfadf7df3deededdebddedddddbdcfdbddbbdb7dafd9fd7ed7dd7bd6fd3fcfecfdcfbcf7cefcdfcbfc7fbfdbfcbfbbfabf6beebebbdebcfbbebbdbbbbb7bb5bb3bafb9fb7eb7bb6fb3fafeaf7a7f9fe9ef9df8ff8ef261655cd9759170245635c09050d70650635c19218d70644635c19018d705d0635c08518d705498158093605604c9705819759160249645809158d6020d635809854d6020d525819650d6061d435817450d60591435809850d6059141581904c96058d32581434c960650835819220d60644835818420d60594835816420d602617654d95619432458650c90619432418550d855d1436156450d96201436548050d92201436448050d86201435d08050d6420143655435049050d4164863501435c130261654c0985913050d624c1535813050d604c13258130581404c1815c12058d70480635c120245634808458d2064560481815812058d60481535812054960481435812050560481325812024d604808458120659434819818d20644634819018d20210634809854d105d1434409850d1050d32441434c1105013044195610635518118d97600636498018d75600635d18018d5460063 else (if j<2 then 0xfb13183e7248cc21a29fb13266b5c6902678f321ca3367d898f35afb80033e77d31c71d29ee40ceafc6083063ce59c2f2ce82c10a0c79cb385b93712ec1a44d83489b0691066d222397cc6d4289238b2a4423f10468bf3848bd8d11923f80f0996b02d82ca1cb84c99439709932e789b45d9a6b5513b1a23257e2393fd048ab74252343afe3420652fe34464d78000848f4f202659c215f811efdf52a023ee1081e0060c6e10e1fe80d0954d98edfe8e34217c663d75985842782091eb8629010cc48f3a382e12c9efd1419be703a105ae8a42777f816446d83061b083977b20c2dbe95d708de5c6840cc2f15121214be000c85ff09e404cc20768309dce5191d2fb8d09e83df71a141db0e29a149fbac6c2081ff2810a9df5ac85dc78c92626402928f20146d14b7644e1cdb22660dd9025a65c3ad676f471930b86d64ae09fb40f11b409fcc511a76b39d46d408f0a118627d82a11854f4f8848ccdfc13e212339768761d6cd1e25e3247ac2f1965d1e21848f12f1901f2cd4427bafd020d487eeff0ad32aa6f964245f24a3ee76e325d764a3b76e59082f5700b110d9db8c7b942e69e5c4263c0a226141af3af0c86e8fe0643307323af06b1f0278790cd545ba8f5d6ea42776bd6195bedcef1963d71fa1946e7a1a7ebb33633469863360e2d2d0bcf80834796881d0b8c330308dfc23c065d7c009210a6f2b0d08df65944ccdf65944cddc198f47651357f68251e906c3ce370ee44e568b75bd3d3294681c8642208208848e020b2972d0642a893a8cb32d5a82aa689f1c8d4362ec8728bc4a834369728354b1a054280e0080d54a851ca80a8b0eb1416872c9306b8c2712a1b19b1b6d83a63132cad15908015328051a49b0544b0f868e4de641f0c9d8274a2ec331b02caa311908ccaa29f8b455271a89a056cb64fe187010cd1d32709c1c130d8381044b3754da371e8b43612a0ed881b8df8ccb6285f824965f1611c4e1cdc9b88e5b925c1edd56cab595a5ecf7668b2958c2c275f6ae9570ab39587ab0550aa294f2a6952ee931479a30d10e8353fd9ec4ef67473809aecce66292f29694ae6537275929c8ba41f1ed8ed470a35b18c8b7c54626911a876c33a161086836c102042ff67e8bee1f1af757a3bca9e0aedf75d3a85d14e7372e3915c3adfa6ed36edb40d7c6adb4e1a2acf066c32f5954c8b63d3199884c226012f7979abb95c8ae016c8b50597ac615eaade55f2aa14f6a5e521a8a54109e94e526bd3429794aba4bd2108eb45fa27d10886341e2050fe27cb3d79e4cee075339b1c64df86ce35a1a58cc264030f17c8b945a32ba952ca5a50c275133095247a22a90d48343fd1f10f0c72e37f1b70d346502fe16c8b1855a28713609344582080f2073434a18e0b3853824e10707102ec13607702980f004800072d2be34d14938d0 else 0x14e2aa0c2e15946170aca3869fb88453eca217e0b06ef543075b58b14f8203ba79a131fd81078fec08323c824aa4c342c767622a16278480fe84802146e36ea300bfc6c222180ee9e684371726840f8cc7d7c080293bc3e33201a7d137c420c91f81621066e5290c2112539c5996b8c2203c0107afc6a0e110f054852424f50042c7e19841955ecc0e8476057084ecf0b1c7b3c2c9aee02b842970958acb1f826c5659f5e5a8b8d0f62b2e6562d51844b8e12574185996ba2ecc85aeabb25745d990dca683272bba36143175c4b64138b0a8eb587900067c))
def mo503H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5801220019cbb55d0c193408c2f00244e855603e4dc100248d0198c16
def mo503D10 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then 0xe5cd43cb1a8795358f286b1e5cd2bcb1a579534af28695e50d8924c2924984ef2a691e50d226bb304d74609ae6c1e50d844cbab89945712e8ae25cd5c4a9ab8943571324ae25495c4992b259756c2c8ad858d5bca1ab897056e2869a2581322bb054586028b3001161c022bb044564088ae80d16191b84a23708446e10885160d0924c1f70843f09227c9660b92ca1770842e4b225c9640bb8421d259636e2c86de60cdb84a227084448b0689c210e38a19a858134e108662619044b22089834112c682218d044a1a089814112c282250504498a07084408b06822260f44cb9e89763d12ca7a2590f44499e89833d12e67a258cf44a99e89433d13247a2548f44c89e89813d12e27a2584f44a89e89413c8b0c79c210f30b21e61633d02647a25c0f3842187943304b246204c8c44b818896030893049c5d0930bb1561642af2e63de50c7c2a91185741d0aa43935d8b26ba164d732c8b045a1504b42989685212d132e522650a44ba1489922912a450965ca30b214897028e2864214c4844b01089741b12a435e50c6c4b80d89401ae1283204c8642a08c8531190a423225c0644b00c8930180131a8f616f1ec25e3595166aea2cd640594c3883584107aea28f550520cb8941751283282505d04a0aa09419212013130f246490484805977c132cf83655f0cc93e1d917c232988664b10ec8e22190c492e994165e686cacd11949a33253476466aa41d55891aa01314c0262804cb505164a0aac738524ed28b24f0d956c2328d86649b0ec8b621906c0130bc0261734ba28696450d2869d75955aeb22b5d6356eaa6add50d5b4a1a62d970e5b281cb618118bb0635970a6b2c14d5d8296c3013185026b08040660014c3802d8600630a00d61001cbb0439740872c810f5d819eba033d640603305c3654b88ca171d912e43205cd21113642205d653cd908797590f2eb19e7d523cfa647802609804c125d6528bac851d54c6baa18dfffffbfeffbff5fdffb7effddf9feffbff7def7dbfafeffdbf7fefedfbbef77edfd7f9feffdfebfb7eefbdefbbf6febfcff595735cd705917058d705857050d70505704c57018d706156361163551632056361d606116060960605605cd605c5605c1605916058d605856054d60549605456050d60505604c96020d605d95358d5350d51619436154360943605435d5435d1435cd43595435914358d4354d432014354d4150d4158d40581405454050d404c54018d405513154d3150d315cd305c5305c130595305913058d30589305813054d305453050d3050530501304c9304c53060d20605205cd205c12058d205812054d205452050d20505204c5204c12018d205c110589105811054d1050d1050510501104c9104c5104c110481106106360463600635506361830614306103060830604305d8305d03059030 else 0x1ba41947fc8f7d1e223a547028d8519f231745e68b3d157228d44be88d9104a1e7438c868d0bc2143423083b906920b34114818d0139ff13f8c7e58fb61f373e107b68f551e7a3c7c7860efa1dcf3b4675dcea91d2f3a1a73a0e5b9c8e38ca7110e0f9bf337a46ec8dc69b5c366a6c2cd6e9aae350e6954d1399fc33a866c0cbd1941322e63b4c63189c30f06144c1a981c2fe65ec0bbb973e2e085b5cb59968e2cce58fcb0e95f52b9656ccac995682a865470a7b14d3295e51f4a23942427ee4f5c9d7138526ca4d2499392fc25ba4a9493a9253247248548f791d2236246508b49146222243c0865109a20e040f880a8fee1f9a3e847c00f5d1e783c407750ebc1d2439907178e0d1bb836e86c68d691a9034a067f8cd31954320462e8c3718082f345cd0b6816862c785800ad815622a1852f8a381438278c4df098f12f0252848f88fa11a422a043e08551072200c3ec87b20f141d9839f87100df01b7435986830cce18dc30385e10b7016202b305370a1c138025c049108c610e420683e007700e141b50341061e0bac162829104c608cc10681dc034c05a40980103018a02b403d005b007c00840004641d28d63a51aa56a354aa4699578d953f1ae67e358cec6b1a08d322c8b0f851617038ba5f8575bd0aa97916545a2ba8b459016e2e82115d4522aa0a4597128b282515d04a2c9097973968b2b2512424a2c3c98491928b0f21161a422c345617684e30d11c616238b2c4709882e32b05c6160b8bac17193828b0d0d35da1b8b243259780e2e9009659fa2c33f65657ee2e8fdc591fbcb9bf45868ee2c91d161e338ba4625977c8b0ef89659f22c33e71747ce2c8f89649f38ba4a79737ae32ef1c655e38babc719278e120f1c5d1abcb9b47174669b2fa135db43242e84d64d29b2f9d35db3b242e74d74ce9ae79e12473b242e22594c49ae988964b112c8e22590c49b2f94965b2a6bb656485cae2c99535cf2c448654d76ccc90b9935d3326bb646485c8e2c99135cf238a1e46485c69ae98d35cf1b24add6165b8c32f59861eb30c9d66092acc32359161eb30bb566165ac4b2f35161e6b0b2cd25949a8b09358592692c94d4d87b29aed658592cb0cbd56187aac32b558652ab0c2556174aac2e754965eaa2c3d56176aac2cb558592a924c536164a6c2c74c92628224c504587a04b2d41865a830b2d07184a0e2e941c592830b1d04587b6c2cb6dc252db0b25b6163b64931498592930b1d279739cf2c739e50e744c84e4587b4c2cb691612d30b25a4582b4c2c961161ea30b2d46164a849314585928924c4f45879ec2cb3d35daba6ba576164ae9ae75d858ebc248bb25916c4b20d9c659c38b2b8716370e2a6e1c50dcb8a1b7616374e286e892617924c2e44985c9aecc8965d6bcb1aa799750f32ca1e5d9412cb28717450e2c8a1) else (if j<3 then 0x199cbffe0241d80d067c5ce1397f80b48101a0cfaf84276ff0148233399e4f82143bc9d52131c112210bf4ca8d8cc0df54e350ce05fa71a866087d38a73337cfbd432847f9610cb1fe290a4151a0bff145214ca34876fec29054688ff14b42445a17cef4008ede7e94465b6d92a103fc000119bbf0801233078e4122467efc20048cddf84009199309559225fb18e30448d4bfc6014471e3ff3c02890ee2c187e3fa949448afe240048ce9e28911669fdf057447d9f7c9a5120ba7d229919f3cc245633a612ab244bc78e30448d3def9571033f731f62066e84b0f6466cf2012f65cfa14f04cdef1f6a030a1da8bd8e93c1326357a34050c1ffdac0800cf7e8404f6f065480110e50fffdcc00cf9f2a008336fff784011c3ffb5810019c549c13470ff9225012cebf8a93d347afc32d68219cad1c48e19c7ae7140a3a7e9d28c54cf10ca908433e7af6b02133efeb148849257ff780491fbf8740c200342fcf4071fc18840242fff7c515289307c8a0e8fbe0aa02242ffff91454a24ef3a914542949ffafa4008ce1cede113356d2a462139a43fd27362022694fdb18f13101135cf8fa3718b28930bb7f4709cced4fcbc11c312135b72d31c4bff980024681f3d4a8b7fc0a26e2a47b27143e09960a0d6a6a48fa62a001f5e752b0f55c40463d437626ec31222867642602a9b14676141502212509542a046160699d1cac90e5a8a10c82531c70a4045964dcd4d88884190654b8e0c88d6c503d77292a6438941c34a9159b0d395a30d1354854129c771a90b65990ec2d2cb1521d328f091a3701126f069a389d8218998f86968b1687822e818b8c6f898712119632446178bef17322ce45808aad149e27bc4c6892d11be221c42587ff0f7e1df439d86e50d46193c2ef857d0a2212f4240843f080a0f041c0834305de0abc12f821703c6065409880eb0122016c0057fbcfefdfcf3f7a7ea0fcb1f813ee27d6efa2df33be3a7c2af7d5ee93db27b02f539e91bcf87998f265e36bc4e7860f02ddf83bcb7756ee21daf3b367614eb79d5f3a9174eae955d19b9fc73c0e6c1ccb3965726ae429c6f38b57118e179c1938116fb2dee9bca376c6ea0dc81b8036df6d66da5db3936546c4ad815af5b5bd6b18d58da9d350a69b4d2b1a3db443683acfb59e6b3a766e4cd2198c32f265a6ca95940b25b6474c86d8f7b1ca6356c5f58a8b134621cc3c9869b0ae612ec1858162ffc5fa2bed97c8af695e88bc6d77f2ecc5d48ba1972eae365c14b7856dbad935ad6b51568e2cef5996b2cd648ac5f5880b0615f9abce5774ae855bcab4f5660abf55672aa154f6a9495152a0553bca6dd4c9a9665284a47d480a8e1516ca2554332834502a9fd13e6279f4efc9d5139aa70a4dbe9ac9346a6634c8c987d2fb25d24b6096152b425444a4693f926da4a8490491612 else (if j<4 then 0x37233b796804d66cf14a648967efa7d062b3278f0c88acd9e3f134ca10ea6314ceb13fc6b235394108321b8bfc10180d05f7d41ccd7f7049bfaa22236c0ffac506c9431e2111b197d0d42184c7d51a8fbe2544447afa62bd0d92a78fc0043332cfe662d0dbdfc95143c30d32402b46d7dc7ca804922ffbd06933807f07c4cdaa51f81a86ecbd525466aff282a32e79848ac6777ec61090adfa511ccd1e1cbb892676e5e88e662fc1002cad9e88b281e6cd2373e12018286dfb9c9a284b4c710a8680f97a044391a0b0d3db277509ed9432fbd3159bb0fead040ce5ea120650b7534fc19a972b5c2773c2590067ee6ba6000ce168f5e99267cfbde2933273c6c45ecdcea9c8493fb26568f9f422aa5674ac396e668a769e596bf2c315b3307cba9913c7e82196214e1ccb1487822660c38d8aca1b6bc5a8801a5bad106566affb4ec499b4e1f908ca36fc2285d7844d31f908ad511d92aa1b8328f31fd02340badc2361cd1fe4624f82f0acd9876b64cb1fa6904cb1d271265d335e42367f6c9b1c4ce5ffaa04d668ff6b0200338a938268f36f8bf451f20fc28c3f958318923bfde9030044d35ff9590019aabf80e04678f2e4648eed48cb1edd31a666ac0348e4cd9c56980e94448d75e7e92988433497f7a9254679ffbe28a94491e6382311213ffaae2840cd0dfdd224151a3715ca41594acf19e16a226800fef42014682fe0d2f4090546af72a391216bcbc819957d6a8088e58f6e1c08cf9e3bec10cce0dec7a466af8f050cb31fa822316627f599b3c39da7a44d05f9d3d22662fced2593362631c995b3b4e44cc5f9de5a44cf9da4b265ee53d66517cd05142f7c340da889a2b00d23933057df4304cfc18663a51340070eaf412682f2a463ccd9db871e091347610c27924d09c38d50899cbd0513c998703b5e919397a40a007e692fe62c11c09135057de6244ce1a68590f33e609f892661c788d049213e5a64997306ce59334423f3244bd98fb2d23acaccb9fef1f35c0904935a9dad8f68844d53eb3eacd420a4c6a7f532dc0a09a83d2382a1cd1ee991250b09d1e926622e5d7c4cc33cff0948fa39471a3043f09cab307dbf3488cdbd2089b9a11e8bcf88450121bbd398d4cc1dbc84999923f921e661e35d208c3d1a1ec8e1e18793262b40fdafb8f95009401e9d1595b87ab64aace8f62f3098e66e81a868fead92ab30f43e422c7ff0128f5bc408c1edf7c101996b47b2377ed5d20b0a2b4f7ff8c8111338f517908c8f8141f33758142d612b51acd58170648840a1b2f16bc9923fd9ade0330c627e0469f789df622325767c9c9963fcf80665cfb75022e26868feb99159a7ff22d15ed49ac25d126b3ef6b1d6d477793aa4263ecb8005436fe008119447384a3a88e72119bfa80b6819d147d414854dbcc8e731a0bfeaa9c0662ffaaa41 else 0x131c134a15d57c5042250f1a7c1cca5ef4ed30d98bf3806c1d59f52dbd1413e3fb2166ce58fd8bc4ceae3d1532b50f1f21a56b356836a80b6690874fa2719ccc9f0c95220cebfa2422cbf4098d0aa239da8ca2399846511ccc234b9a0b7008617eae04217fd760cccc3ffc62343660941f8602d440684fe180934101a4f33c9f04294f8d2991711c908d17694a38bdbba11f2bf66d9075adc22972d82220ceae5a79091885fc74cd0eea2390adddcb213f8218e85ac3b14a5941a32e1ee42387f62c9b399eaa5832607ab7903347aa61b5664f8e88c879cb9827a4bc48485a0ffba8819ebbbf2e994a3d7adcc67d3b8aa842a07ce220ce3fdfb222090850d2fecbabd7c02a348ce11eacb341fe2422c748f60651776a8848ebe20d05834007c6aa718a6957efbd2010c99d42a9c19f3ce11ce019f3b7705d7b0345b9268250432677fa64da1f21171ec205d0bb5be1131ec27410ba77143096f98c0215ba4c697f666fd43560662e5e5b320672e7e916816707c3508457f0282014316a34b2168a30b2b710d42ca5cbce4420081a8b598590bcbfbc19519c1c1983ca3cc7046225174eb8981034278a42994676fec29054670cd21488b3978f46c8199bd7771614680f968b2326707c1114247fb2c48280035606bd265d41c3b52143fd2ca85987323514b87e560081a16a97ed141ecb05091fef06d48ce5a6dac95f7a3a4666e398593292f31d10344c35fd22cf19a889ff58f50733b7e3d428881a3a9fcd040cf3f5d031048b706d485c487cff8f5c120674ae1fada059c34faf18440d11ff9027b141cd31e83284b337e8d25ce034537bcf32c057e408ccdfbcb1a000069def8da80921bdf8400881a13cb8509664f4974c99ffe0421333b75fa6032cf640f40919f418a65a7e481083ff675420917b3cc00290fe500c994af09ca4b4472fdcee0b399c2509eb6a702a66be18827064ea9094f6e08a853395443f531f95190a505b6c7844391a51b4fee7709a03d7bc504b3ae06445cd7a0153357e6340033a7a177419bbafbac00ce3f172458cabdd39039a7bf8a50399bbf6a8648ef86)))
def mo503H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4097957159d75000000113c434d39000000087960468a8000a4008ee1320d17abd1c24d0925b87846185c91fc9545300000000008411840001b18000110400163d3b90002ab4000000000000086030f82c000000065200000018b3b41d26ac7905a71bea8400123900020878c200000022ac00000000000000016ad0000001552ab800030fff68000094cdd000000055d19cc00145944a7a3bc52eaf048b0f8d4f91200000000005a3043f0800000001928002c91bb600068eeb6a00000000000006a362a5c6de56a44012905b61dc1ce5a01794cb6a0000722841800000079ffd6c000a3c0000e2be07517c5c40001b395a80018d9a809c15828000a05896b076c27a0d557413410320443a80000007a5642b4a38efa74e4ef86a0a0a70418993ec6400028cca71450f2323ef846495e9683701acc308890001dd8000a7eb0131ec564c51c163050000000449800088a0003a749f0001d5898980ac00005c0000000000000e5b91980014530003078000000b3b410b0a5e350004a6570c000c2371626ffc9014c7a88c9c0000005159508000a13812400000000000030ce00000032a38f426a0007824c4600000042e4c6d29f000086c001a30c2d9c374db415f12243c0000bbe238000000000f45ce1390ce973be80000009411074dcd28fc43f34898b40ce6f82fa49e4c6b11625c9c70ae1267c02edc001c64316ac5c0010b100068b9c0363ae8b397481e8330000003c4d88d000000155440b44dc06584400000000030068a5e44000000000000000000001c10300000071a186440a00f80189c2af1624480000c18020003860204081120818902189061a3400f0c642020600d800238084
def mo503D11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x1a4a0c5b35c088abf9804558e202a36fd8584048df1e7008d78fd940a02fc25459fc12a2e1f171166be0a801207c0e0048f7e7f68005217e12a285f84a8b847c2a2cfdc808abf3527c447ec518c79ea04469ed764465195518890bcb222ee7900047be650014ef3c401841273cd7591b2cb40655f070e11aff0ca44f7fe856276f344c6518ff880a47343422fed589b79d2000903c2f811571d9116fe81b97201628e1f0a8d7cf7f10140f630a8a7fd30135fd9404e73ff8809ce668132fd8e54235e432c98fea604dbe3ce0118feca04d7fc307139a3a0fbfe028151c93d0734741f7f889648eb24b6067242e9d594a8206878968f4988b30d505775095db606518045c00a3231cc240553878e90b1480991c682762840c8908e362c6e14b13062c78a6c43e18b079813bf4df12f2b766ba55cb2e1b6e7b655aa6d09668b25588abff5e0ad95622ac953da8ed3ee9b54bea4ed1e68b1430a09cfda7b33b79c6cdb667d30d96fcaba50d25a919c84e3db1ce8d2c61e2c3130886c3ae1a70bc846419e0810217ff3f75f72f907b23d09e2cee8761ba81cfae5a719b861c06de26e3b67daf6d5c69b344d9dccc265232118c6c4260cafb9798b9c5bd2d55646afe5642a594dea3d509a7a937a99c4bb25092248f446aa2b9108866429a10103a7f63ec1eccf2c76c3a29c60df86df35f1a5cce86513199858bf25d12d61610acc54829514309c64cd255922c8c844a21390187b23bd1cd8de46b033718b8bbc5b22bd14c09e44ba22e10607983901aa0c605a429c12a08683c019a0b004701e00a203b0128003d65ff553fd85df5d77d84df5537d73df5d47d541f5dabd74af5cebd63af61e3d868f5da3d858f5d63d658f5ce3d638f54e3d828f6063c808f5da7d749f5927d739f50e7d757f5cdfd537f5d57d745f5517d735f54d7d435f593bd63ef18fbd43ef587bd41ef4c7bd87cf5db3d65cf6133d74cf5933c83cf5cf3d63cf54f3d43cf60b3d52cf4cb3d81cf5c73d61cf5473d41cf5c33d656f58dbc636f54dbd616f545bd316f581bd764f5953d744f5913d734f58d3d534f50d3d624f5493d324f5c53d514f5053d314f5c13d604f5013d760f5d03d640f60cfd733f58cfc633f54cfd433f604fd513f504fd313f5c0fd603f4c0fd762f594bd742f590bd732f54cbd432f588bd522f4c8bd702f580bd402f4c0bd202b5d2f481d76145d84176045d801761aa965ac5ce9d868b5d22d648a59669539d5c66d43785dba885e85d3a173e761f2565c95932563cb50db1534c50d39604761c1d86076141d84076081d810b210dd833e5c0f9603761c9d822d544b5412d4c4b5212e580b930226144d841560459801061c0586026140d840460815810ffffeff7f7fbfdfeff7fbfefebf6fbbbedfafe7f5cd7058d605515354543505404c5304811018c30 else 0x3e562261acec46deff6b2236e220b2291df1a200067afe1365e0a8ef8e486503de302164524735e1542c24c5e5622df8ee24d87c5d1186c6f8a04830bf11399ef600a0f7f7a0451619f04c6067893efd44956241cea44d29bf59c04f7ffe3a236156ff146d0491dd30b04cd375f15d11f2891859663115146de16b0a3653b0b26f0b585187c486451ce68c9e4fbf430cd09018e7326b07b31384f2f09aeec303289f88310212037d880a4bb78bf6c09604de91ccf84b0617d2709e4a2edef30d809685d818cf240426d0be7252c185b9e48b3b4f12798a6938926270dd93af88d404122c8ee228be37ec80a57fa5554900944ff62c4a2fcc2a0293cdb0671c012bff1880000926ecb099293cfc0800544efe809d78f901a35667680a67f81115197ff005008e7de6ca9e255b5a98623ddf1cc7a415cf1998a740953e20b0c4858e29c08eabda9b51d696a7023df398b3229d99c48a177435f00ea2307f84251f724894499d571a0479d64928cbc72210240f8e22046b3c9798945fdcf310415f78d18cadc2a18ca5e19a0651ef7902349f2b0a5126ff27431a150ff61a88d23f4ab1c2492b7950223d4372c619875f8a182604a3f278209499f9a931d40060bf198a5240259f89a8092b1fe870900012eff39d3a029bf4e675594e1bccc2a012ab71f405367f1ac494dfd024c5a20185ffe71951495ac67448dd4f12996ff623b314eff5ac100913c130a34c5435c80c7bfcc809efbb161b94df424051be8b281487ee2604aefa6924494bf6350a11cf3d)
def mo503H11 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then 0xd2ce08e000000084b80016908001b240000000003c0000000000000000021340000001bcef91c00000000000000000600400000000000000390b5420000000000000000000000007aa8000000000000000000000000000000000000000000000000000000000000000000000000000016ca8000000000000039560000000000000000000012b4800000000000003b74000000000000000002ea400000000000926000204a000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001a7b0000000000000000012810001a14000000000000006ea600000018168000000000000021c64d4000000000010a280000001160000400ed9e80000006844000000000000008dc8000000000134d00000001178a85914e00000000000000000000143400000000000000000000000000000000000000000000000000000000652600043020000000000000000000000000000ed10c70a088000000590a0000000eb380000003232a8f36fba918000000000038b800000000016d90000000000000079d8000000000000000000000000000000000000004a240000c1c00000000000000000000000000000001132000727600000008b6680dcb30000000000000000000000000000000055a000000070a6000000000000000000000000430000030c20000000000000000074ba9348000000000000006a20000000000000000000000000000000000000000000000000000000000000000001f6c00000000000000ee2000000056e341c80000000000000000000000000000000fcf3d1000048e4000000003b800000000000000000000000000000000007a08000000000041d600070120000000000000000000000000000000000000000000000000000000000000000000000c0bbd4a000000000000000000000000000000000000000000000084800000000006a6e59f8000000000000039a000000000000000000000000000206a50000000000000058380000000000000000000000000000000690c000000000000000000000000000000000000000000000000078c0000000000000000000000000c63bcaa000784e0000001c7200000000000000000000000000000000000326a0000000000000000050cc0000000000000000000000000000000000000000000000000000000100900000000000000012c0000000000000000000000003a30000000000000000000000000000000000000000001e1d000157f000187380000000000000000000000000000000000000000449012400c400802014082020000000015090004c04014000000002880080400480000410410000440000000880000480c3010001000200001 else (if j<2 then 0x2270000000000000000000000000000000000000000000000000000000000000000000000000000000000002f22000000000000000001081c710000000000000000000000000a6e8001aa8fd92000000000000000000001e6f80000002786000000000023615468000000000000000000000000000000000000000003eea000000000076dc000494a0000000000000000000010d28000000311a0002a188ba800000034fc31e58ae000000000000000000000000000000069e60000000000000000000000000000000000000000000000001ce122ae000000000000000000000f85800000000000000000000000000000000000000000000000000000000000d78000000051b800040fe00000000000000000091e000000000000000007346a9cf2b20000000000000000000010d2000000001db61d80000000000000000000000008b88000000000125400000007a7000000000000000000145e00000000004cbe0000000e5d800000000000000000000000148eea68e3a8001845000028a00000004ea000000000006afa00000000006d54f4e8000000000000052440000000000000000079474c98001c378000000000000018c9ccf8000a3700000002046000000000000002210000000000000000000002088000000000009c200000000000001eb6aa87ace8740000000000000000000000d1d80000000000000000000000000000001e258000000000000000000004034000000108a8001f7880018750000000719e000000000000000000000000000000000000000001ca7fdda00012c800000000000001c7c8001acb000000075960c82de6ba300000000000000000000000000003a0c000000000000000000000000000000000000000001ace19706d88000000000000052fe00000000000000000000000000000000000000000000000000000000000096400000000000000000000000000000000000000000000000000000000000000000003820000000000000000000000000000000000000000006a980000000000000000000046f20000000000000167e800000000006948000000000000000005ddf8cf8208000ab400000000000cba00000000000000050e000000061e800040271fe000000000000000000000000000000000000000000000000000000000c2000000000000000000000000000032a4000000000068672ae800000000000000000000334000000000000000000000000000000000d65892800000031208b080000000000000000000041f12b7000000031fc88fdf7ac700000000000000000000000001f9e000000000000000000000000000000009da8000000000000000012608000000422600000000000000000000000001380000000000000000000006158000000000000000000000000 else 0x70a1c0c000000000d600000000000000c648000000537a0000000000000000000010c37a60000000000000000000000000000000000000000000000000000000000003e180000001a940000000000000000000000000000000000024220000000000000000000000000001fd6800000006c200000000000000000000000000000005682000000109f00000000000000000000000000000000000087e000000000000000000000000000000078d80007a0e00000000000000000750498d2aac00028060000000000000000068f2000564602698ba0000000000229200000000000000457d68a000000000000000000000000000000000000000000874000000024120000000000000000000000000000000000000000000000000000000000000000000000c070000002800092de07c000000000000000005c940000000000000000000000000000000000000079b079d0000000000000000000000000000647e00000000004b1600000000000000000000000031e40000000000000000029b400000000000000000000000000000000000000000000000000000000000000000000019792cf6482800065f8000000000000000014c78940000000015c955e0000000000000142e00000004210000000125a8000000000000000008060000000000000000000001b6e000000000000000002a200000001bcb00000000001c040000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000026200000000000000000000000070640000000000000000000000000000000000140aea6c0004eee000000000000000000000000000101a48980000000000000000000000000000000321e0000000f4d80000000000d0580000000000000000000060a80000000000000000000000000000000000000000000000000000000000069ee000241800000000000000a17000000078daa1880000000000000000000000000007580000000000029d200000001ca00000003a2c000000000000000000000000000000000017aa38f40000001c61417c00000002467c6bec73890000000000000000004676000381600000000000000000000000000000000000000000000000000007366000000000000000006ab00000000000000000000000006b5e000000000000000000000000000000000000000000a400001e54f56c0000000000000130500006618000000000000000000005ab4000000000000000000000000000000000000000000db7c21c00000000000000000000000004d46bf000000000000000000000000000000012a75a8000000009a780000000000000000000000000000000000000000072ee0004a1200000000000000c1e0001ed580000000000000000000058360000000000)) else (if j<4 then 0x8000000000000070ec0000000000000000000000001f80000000000000018000000000000000009dc20780000000000a25000000079f400000000000000000000000000000000000000000000000000005d3d87e0000000000000078d20000000000000000000000000000000000000000000000000b4c8000000000000000000000000000000000000000000000000000000000000000000000000000078f600000000000001d77d0b0000232200000000000000000000000000017bb7a400004f7800000000000001aa80000000317a000000000076bc000000000000018b180000000000000000000000000007f7e0d50000000000184c0000000000000041ea00000000000000000000000079ac0000000c6f00000000000000114d6568000000164b6da8000000000000000000000000000000000000000218000000000000000000000000000227a000000000000000001906000000000000000006a2f4410000000000000000000000001010d1900003d740000000000000040680000000000000000000038b200000000af800000000000000000000000000008260007d0a00000000000000000000067880000000001c9d0000000635d610000000000000000001eb2e18a00000000000000000625e0000001e4a8000000000000000000003abc29900000007a8c00000000000000615000175680000000000d48000000000018c4800000045f151a0001ad68000000171c0000000000711000026da000000138980000000000000000000000000000001c99f19c00000000000000000000000000000000000000000000000000000000adf0000000013a00051a400000000000001c630000000000144f80000000000000000000000000000000000000000000000000000000000000000000b79c100000000000000006a800000000000000000000000000000000000000000052e00000000000000000000000000000000000000404c0000000000000000000000001b10000000000000000000000000000000000012570000a9f8000000240e1420001c58800189200000000000000000000000013608000c96000000000000000000000000000000000000000b49000000000000001288000000000000000000000000325b417fd2ce68f9af66580010d30000000000000078d40000000000000000072c400000000000001b7b0000a5b1ae060080000000000000000000041de00000000000000000000000000000000000000000000000000000000000000000000000005a960000000a42664003f0000000000000030b400000000006b4200000000000e4400000000000000000000132e7a83d588000000236c66a0e72000000000000000000000000403e00000000000000000000000000000000000000614400000000000000000000 else (if j<5 then 0xbcc000153400000000000ccc800000072f9a6d80000000000000000000000000002772000000000000000000000000000000000000000000000000000000002c10000000000083e0000000737e0004917b5380000000000000000000000000007a140000000000000000000000000001add80000000000000000000000000000000000000000000007e080000000000000000000000000000000000000000000000000d2adb180015c30001e0c8001a409e64000000000000000000000000000000055fa00020bc00000008aa8000c950000000000000000000000000000000000029980000000a6ccf2eee180014180000c970000000000000034c200029e800000000000001cb580000005b1a00000000000000000000000000003ab0000000000081c000000000000000001829000000070e800000005d80000e818000000000000000007b34ed9448800000000000000000000290e00000000000001aa60000000000085500000000000000000188d9b140000000000419400000000c6000000000016d3d334000000000001680000000000000000018c00000000347000000000000005ae600000000780000000000000000000000000000088c000000000048c6000096e0000000000608a000000000000000000000000000000000010c3b21b8d4c2ec20e80000000000ca38000000000000000000000000abc00000000000000465a0000000000000000000000003336000000161b8000000124c000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000004b06000000000000000000000e1a8000000311200000000000000e80800000000000000000000370000000018bd80002a100000000001e3e86f400000000000000000000000000000000000000605200000000000e4800000000000000000316600000000000001432800002f80000000000000000000000000000000000105805600000000001ecc0000000792400000000000ec000000000000000000000000072012a40358000000000000000000000c2480000000001cb000000000000000000000000000000000000000000000000000001eda000000000000000000000000000008a20000000000000000069800002ab6a0b00019a272e5eca000000000000000000000000168e0000000000000000000000000000000000000000005f7c0000000000000000000016bd0000c1b00000000000d5a800004a000000000000000000000000000000000000000000000000000000007a34157000000000000006b700000001a9e0000000000000000000000000000433c00000000000000000000000000000007632000000000000000000000000000000000000000000e3c000125 else 0x11cc8000000450c00000000000000000000144d800194a000000000000000000000000000000000000000000000000048e085d0000c72800000000000000000000000000000008c9000000000000000000000000000000000000000000000105c8000000000000000000000000000454c0000000000000000006e600000000000001d6500000000000000000000028b61cd000000000000000000000000000000000000000000000000000000004767dd180000000001e7d800000000000000000a958000000000000000000000000000000035c40e6000000000000000000001ae000000000000000000122b00000000000000000000000000000000000093c0000000000000111b60140000000000000000000000000000000599a00025b80006a2200000000000000000000000000000000000000000020a2f52000000000050aa00000000005b2f39b800032480018a6800000000000000000000609e000000000000000001af2000275400000000000000000000000000002c2b2d40005189c7328e20002cae00000006de000105231a7a9380000000001b8900010ae0000000000000000000000000000000000000000000000000000000000000002ddc000000000065564310000000000000000000000001db480)))
def mo503D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x39e8157c02de84093ac0843f85067a8021a803895e0e2b80ec283273d0380043dbc031ff580417f8c0ed201d6102195943892887436c10021478a11a08c4ae5265b19813b1b2c357a750a752e9044e14002eaaa2e6b18c6a9a86a8a8298ae0b02809806090221ff
def mo503H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x187916e76257800303c66f0007830627081a0a0001137016ac331b2c1f60b848c9a972320a0000a02cbea6b93ec953c3121ca15ac94000682000594714c95db41c908000000ea5309b4986452468929cc801bb231ac0670d354080911463a7893415180002670010003d55e660000002228000d1f50812d109f79429b56ad27fccc20bc00198ba5180000000003c000000004a07959d1c000000929c90c94576f00050c124e00019085f0000e6500000025640001b66229157a4f6ba000000064dd520000001b32f4395d54dc0002428001ea660ed0a800045a000a12000000000029f39f00018270000000000000891625001395b212800354ba50a3a00000000009398002f32a634afecf6a98c1dd830000b06c92d2480024589115258d22cb5fa0411b86400069c71a3970c0806964f5cfc000000000623000000001d7d78001b6e30be9800005098043c8e091c5700078ff00a00001500024f60000004254000000ca18000000fac058b11c000679000601f9130389208000d1c3125d6fd50b50000d5655c9cc4000e508003f4c601eb28003d2c0002bc32180356000006cc000038a13934800007450004275426c7514ca8dad20e4e0002d9c03e4ae74c48dc00067e7c3a17505c000d1ee9dc000070000796c000012dcf49c5f6000000000010640000003966662000000597a4780000a78003d2e000000714bd4e0000002e5c00032d00000022a40000000aa5d50000000000000054900020ec000000cbff2b40000000002e86935c2900000008b0000901ec3a110000447fa10720000114000087200000000000009440003eabf47e35c2b7538cf4e939c93845c45d709199157c1b8067aa9e087266400000000ac67895b36084a5457b818628039b0060c020244620004b0c024e08210458d4045140120850430801c04002430c224210318028000004b
def mo503D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x610084ff
def mo503H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc209683ecb556140000174800000014744704800000000015c17ca0001d60051101248001831058d7384ca180000000007c4828000041f40698e69c3c10000
def mo503L : Nat → Packing
  | 8 => (20,5,5,1048589,68,9,1051,mo503D8)
  | 9 => (188,4,5,5374044,119,13,1186,mo503D9)
  | 10 => (453,3,5,2359403,103,15,1165,mo503D10)
  | 11 => (179,2,5,1048592,68,13,1092,mo503D11)
  | 12 => (17,1,5,65537,0,9,1045,mo503D12)
  | 13 => (1,0,5,0,0,0,0,mo503D13)
  | _ => emptyPacking
def mo503I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 5 23 5 9 5 0 mo503H9
  | 10 => lookupWord 59 349 7 13 8 1 mo503H10
  | 11 => lookupWord 155 3167 3 14 9 1 mo503H11
  | 12 => lookupWord 65 389 6 13 8 1 mo503H12
  | 13 => lookupWord 7 47 5 10 5 1 mo503H13
  | _ => fun _ => none
def mo503 : Forest := ⟨1527,13,fun i => mo503Y[i]?.getD (0,0),mo503C,mo503A,mo503L,mo503I⟩
def mo503Q : SearchRule.Regions := [
(subcube 2 0,rowMask [17,33,36,65,132,144,260,320],rowMask [5,84,112,224,304,385,416]),
(subcube 32 0,rowMask [17,18,65,130,132,144,260,320],rowMask [7,70,84,192,259,272,385]),
(subcube 64 0,rowMask [17,18,33,36,130,132,144,260],rowMask [7,20,259,290,304,385,416]),
(subcube 256 0,rowMask [17,18,33,36,65,130,132,144],rowMask [7,70,84,98,112,129,224]),
(subcube 1 0,rowMask [18,36,130,132,144,260,320],rowMask [70,84,98,112,224,290,304,416]),
(subcube 4 0,rowMask [17,18,33,65,130,144,320],rowMask [98,112,224,259,290,304,385,416]),
(subcube 16 0,rowMask [33,36,65,130,132,260,320],rowMask [7,70,98,224,259,290,385,416]),
(subcube 128 0,rowMask [17,18,33,36,65,260,320],rowMask [7,70,84,98,112,259,290,304]),
(subcube 0 2,rowMask [18,35,38,67,130,262,322],rowMask [7,70,98,259,290]),
(subcube 0 64,rowMask [65,82,100,194,196,208,320],rowMask [70,84,98,112,224]),
(subcube 0 256,rowMask [260,273,274,289,320,386,400],rowMask [259,290,304,385,416]),
(subcube 1 64,rowMask [82,100,194,196,208,320],rowMask [70,84,98,112,224]),
(subcube 4 256,rowMask [273,274,289,320,386,400],rowMask [259,290,304,385,416]),
(subcube 16 2,rowMask [35,38,67,130,262,322],rowMask [7,70,98,259,290]),
(subcube 18 0,rowMask [33,36,65,132,260,320],rowMask [5,68,224,385,416]),
(subcube 33 0,rowMask [18,130,132,144,260,320],rowMask [70,84,192,258,272,384]),
(subcube 34 0,rowMask [17,65,132,144,260,320],rowMask [5,84,192,272,385]),
(subcube 36 0,rowMask [17,18,65,130,144,320],rowMask [66,80,192,259,272,385]),
(subcube 64 256,rowMask [260,273,274,289,386,400],rowMask [259,290,304,385,416]),
(subcube 66 0,rowMask [17,33,36,132,144,260],rowMask [5,20,304,385,416]),
(subcube 96 0,rowMask [17,18,130,132,144,260],rowMask [7,20,259,272,385]),
(subcube 128 2,rowMask [18,35,38,67,262,322],rowMask [7,70,98,259,290]),
(subcube 130 0,rowMask [17,33,36,65,260,320],rowMask [5,84,112,257,304]),
(subcube 256 64,rowMask [65,82,100,194,196,208],rowMask [70,84,98,112,224]),
(subcube 288 0,rowMask [17,18,65,130,132,144],rowMask [7,70,84,129,192]),
(subcube 68 256,rowMask [273,274,289,386,400],rowMask [259,290,304,385,416]),
(subcube 97 0,rowMask [18,130,132,144,260],rowMask [6,20,258,272,384]),
(subcube 144 2,rowMask [35,38,67,262,322],rowMask [7,70,98,259,290]),
(subcube 146 0,rowMask [33,36,65,260,320],rowMask [5,68,96,257,288]),
(subcube 257 64,rowMask [82,100,194,196,208],rowMask [70,84,98,112,224]),
(subcube 292 0,rowMask [17,18,65,130,144],rowMask [3,66,80,129,192])]
def mo503X (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x54048163c0030cf280000039f00000000627000000202da32f206a0681ac4d02a01c000129ff78c0001d0000000680000007d418390360000001100d1c01f817a0000b74b57a9f4000f804dc00000000000001640015ad518009813abdb80000000000540000000a0465d800000033d0197928f881001f0323800b81d2000000000002e06c03dd47f588000000009380056423bf1000f80000007c0000392476da961f4bd3c6f802db80045a15800346640d8076800640f81103e0241e0203a6015ad80b2873c1fe6f7032054024ed002a2e4b5b03bc66b6b8000024ac000000000000cd4003a0000a81d36995c0000000006e9000001e2b0c38000360000397aca72527001952a014014e000006c0180001c74c0001d015b80e23f102aac290804de20233a84000001c0001c7cad000000b6e2100000070000040018002e0000eab102e09ee4803014be40000003d38005d60000000000000175d40e0a100b4ac0b4eb0000000000b01f480011d70120000846833409c278eab6e015a00000000000a6ca9ae008e383a63e041c21cd0355469c800010fec000000300800d80001145cd1804680000010a0000000000000000000001969a005a680a8febc40000001aad40001c9400000480000000000005880062c3800000fd810000000038e181902e0000083f01b100081200000742080003ed000ed71900069f000294005e4cde003a10005d27aa71000000002060001d66a6a000000000177a40b81cdc00462181904006eb75a0000000000000320000652002206c600010000000001b00006c00c4700000006800000000023e003e0000180b0277cc0c91703606a60c580400000d800042d1de001a9c0055a00056b8f8da001a1f13ea70011a8004a0fe200400000001c3e2a70c929edecf800c5a0000042d381b029dc40180104005420d7103e0000001d021bb4218020620603f807a6dbdc048150171593f80000001ea8c8001e06c019100304411514a0400c10c0040042089002042041b8139000a08b29515604508304305110894119f68900b0930c0089900001001181400614002a450002530080051803830870cb08288108078101a0827053803cb5870cf1271c60c01a10051011c711e1011d60451c034b0d10860000151c61010030425800c53402c500014b21001100808008b0451012ca80f40210a0072060085c00c50101800430010c00c312694400208000100518d0400cf1c60413420412821405020800832420d808328004c25f20834218010c0501c404008d011182f012082011961810803c20046c04c00000040401021c300219b0080000011c50cb0010c10490082c208300000600008104008100808114000110c00200000008104110028d1894890c01430001814400810010400c12401d50030400c00020831c5 else 0x80000930a75b400220c0c7d52b40012c180003f17c000170205800d8008ead2e43c9301c61c22800000000000130000000a3fadc0000000000000000001d9bf5800b02002b2000b81908006a7c82b04b5ca958187c001d5e6e0039d80000116bf2000c8000176fa726e0000041fd25300000000011002380000000050000001850604e400107d4f800564100003c02d1c06cdec0880002e43644c9c3260e1db80001f8000000000005c0000d000036ab5e9027580000146771140c0296a712c113e00000000880000e0000ad26240064d9800000067100000000000480003e3800001c8cc080052e0035d000216002a07409c890b5292743fdbc118408ab191e06c112947ec71b99c290119650229101e051b83ef902ca9f881b51720370000000070e2805a5353c2481168004c1d80d683212d38070000000000f02c0d40c6e0033100061200000000464000422c00c8a9f784c02800000041400000093800000000004da8cc0000018c000a7e32000780edfd936bb800000000000189d60440a1990000000000003c7000b10000005a3d6f65305dc000000000000b8056800000581d01d3800000c3800000880000000000003000000000111ae02d298000000427b80003b78000001ac0054143e0004e80075c968204c07d4a7d73401001502e0432a803a8e07400016dc197c22d2bac00789781fa5ceba70015902034093a00000000891bbd473276800030d0000000000069b0017009b800001b02203e971c00000180428ab400640001b24004b03813000000000000000747000d1114800000000002c06b4cdc0000090a001b15c0ed390020000000b86d96c48020000000066f13113000702bbe8a58cc6b14d071c1685d00e0240e8190263f47a18000c0d3a7b5c980036e17e6b000001c81c5000124db400000740981f012000000022c00000001275a08405800026000044c00320e4078000000069b8fe7fe0241f800000000011c11882ceaf80caef15a7a53e7c004a7d81d040028cbb4e8d0e4400005beb6eadb81b008f8007812504f8004e2301f2794d80001b2000480000007296808b4b7740182303db80021709000000000000870000800000000048050000164328a99564627800031bbc0dc200000000d80002133949c3c05e03efb433036d000f80d032021fc4fa52e0ba7f4e89400000b13fb413e2992e3ac9e000ace0026d60133e000002ef77400000261980001a0c4000000160000000100002c000000156800c40000006c0000db400000e80c7dd6a1dec4b02749c0001f015842900137c00223bc8251e036b02a003ad0003c5901c0a40001472f200038f300938b78800032d000000000003c0180ae1644409c630400000001475a0000680f00e003762829cf78ef001701e00000003000000095a000002b2001390002e4000) else (if j<3 then 0xb73e00320000001b1e9b8009ada7fa354068030000000080b00172c01800010ff82b81b02ed000930002f7ac20000000029f380002d3800000000e0000000000000000000000068100000363800001100000c056448c00369485501606c00004c800000c80bac0000026e00000000000f03a000000000000295000001cf8006b4c7f4fac000143c007b7dd2000004945da07e6000004a000004478c820663ca3418f011d7ad04bfa4000003c600000000fc8000000000004b6477b77b4d00e1640d460006000068000059735000001ed50e603f02a0000001502938000000000056e5d1300001c0281bac53da6a176379372c00000000215c84ca0000003d5f9132040d5a00375bc000167e2000973a003905400380000000000155400000000308004c0a80003a0094a81ab400000f80b01e02a901903bcff6b9c80026d1bc000b6aa0000d820000064002967d2000040c0016d76f04ebbfe03c078089d6000038000000000000d240004076e0016044000000063800d4eb50000002c93039bb2c3c8003606940000037500000000000000118000ed58cc5a244f4800080e053780068096b40edb552a9a602a92cc3030fd66380aec931a328030000000580002e00422513ac006a9fd28337581f001c39a0640483300e0000000db40000032a0000000001c484003a3f3a10352000000002200000000039ba6988000054800e1fcdfcf800dc95000000011df6800000000704000c03800014eac0001f0060464001b00a0040000d000000014c000ad0000013000009f0003000074000000000000000d02a071db4a5825f0007d6b003780000000000085001c7c002013800000026ed31b000000068000000562fa911c002409d1d6ba00c03d23035b800000003ad1eb00a00280800000003f50000000014f80063e0540015a080e0500ec042c789d4800001a6c99640c815038a2da0aab000062640df920b4a70013c2e0240000000e000088031c02cc0580a8c0000000076800000d6e0029beac2c9302f6361ab400000234bd590000000000e9ef14c0f664b40000000150000000001e382480000169f2d0002bafa786000000d036ae1b608d0114f510011014f8005da0022d0002c4003e00000000000000000003000000a6e000000002b467cee0005c8c9d758001c927e60362481d0aafdc0881d516058e0003b706000e81902b4800000d7fed455a4e00000740e67b0180b40e3ee9f538b2001dac00000a80001e0000000f0013e04a28b024725a44e56b6d000ed3a528a04008400000000d6e002e0000000300000000000011180006e002e00004d739293ec7cdab0360000000acbf50000d347de06b700198b8fd4000176b20fc00000000000000170000000c5a09e207c752963000000001adce000000190000000d8000000000000001a13471 else 0x2e4000000003c0000b1c000007b400000000a81589758c6a8140520014001d02f1429c6e67fca0000012b5ca000881c9c000003b400100e4000030380fda001702206170000dc005411d20037274080367ce0000c800026680000000000714000000007c7000000001e400010000000c3e0029715b001e042d000000700000810000a514800e680006100000050206000000000006c900123020d43d6e1a8a03c0b29b914ebee281d6800127000638007e4c80fa98ffc096fd1c0010198089c00601cc8003209c000000000000fdeb02cec8113a000000005d4956b561e000d03dbeb77c8c3a13a0100000000000fbbe580026b580a7c207012d369ff4d40c848b4005c000000074cdae3f90000000680c40a0000b3f8b1606a7d4feddb5000e800034738b000003202ea0009028ff8c0002f357cae14e3a800000d02000000008b4920005c4000fbf56c6ec6e000004c0a820000fdc0001100d4ec000087c000000000031b80000096370e2d00000000000b6e7ac00340c1c000003ec00000000000001b88e0297e1da056d06a8df70000332e656280008234fe04007df06e1009b8004d4c7f20000080e7c00261000500b500066e00276deeee0f05f54420007a8003c0d6e0000012700000000000000d024f80000067e14800c3a90000000fc4b0317364dd40007200000000042e81a3b638000008800008a16aa3ee980039f000000000004a40022d0000018534a11f14f3555dcc0c03f85d6b82828000002c176e00256d971c4003a07c0000000c7000080ca000000bb417f200aa528b03ed000ac8a9d605a700000380e5af4ed0442ce7000002a00000008b56d640780702528007e0000000000d40026000008516a317b7001d68000000000000079d000ee8003c10018e80000051600120000000000000007d40039e000000000c0aebec98d7e0740cae0dd2041f5813a40011f58000313b404c87be2085a001d000066b00140ce04c0d6270084e2d0b445f605efd8400000137000002a0000000f1e471e4d3e0014bc400000000000000019000740ec8000007ae2809ac00000e8045096cb700000000000c80003325400000dee05c0000001890000000000000001c96a20800905d00002c054a0023500037c00013cac04e000003c0001d0000000881f0120127000000000000000000000068000020000b9f7000000000087c007c0000d1c7780049c300000001020b40001ff80668000002800015126))
def mo503Z : Array Nat := #[135728,136208,136214,144400,332598,529424,533905,554321,562192,594736,610608,612448,612454,620646,665699,677990,1590609,1661030,1661300,1714275,2113808,2122000,2446134,2454340,2454342,2507024,2566243,2638640,2659120,2659144,2659920,2703632,2707760,2707766,2707824,2709606,2709876,2711824,2718084,2762851,2762899,2773814,2775139,2777351,2782022,3700049,3758452,4794756,4807028,4815236,5932041,6427664,6452625,6583697,6820464,6845841,6849937,7501137,7501201,7632209,7865745,7882065,7890257,7894273,7894353,7894417,7894433,7898513,7958821,7959889,8020261,8024357,8024389,8405264,8413456,8741143,8867985,8986992,8995602,9003271,9003794,9003810,9007906,9060631,9064752,9064759,9064807,9064816,9068807,9539956,9573392,9573424,9581584,9597520,9598032,9671284,9736820,9736836,9802356,9802372,9802404,9803684,9803908,9909266,9966128,9966192,9966608,9966640,9974802,9974818,9990816,9991248,10105874,10105890]
def mo503F (h : Nat) := ((lookupWord 414 2657 6 11 7 0 mo503X h).map fun a => MonotoneForest.corners [17,18,33,36,65,130,132,144,260,320] [7,70,84,98,112,224,259,290,304,385,416] (mo503Z[a.1]?.getD 0))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503G : graphValid mo503 (boundsBefore mo479K) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503E : ∀ c ∈ mo503Q, TestedCube.geometry mo503.mask (targetOf mo503) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := MonotoneForest.regions_ok (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503T : MonotoneForest.Checked mo503Q mo503F mo503 := by
  intro k hk
  change k ≤ 13 at hk
  interval_cases k
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo503Q mo503F mo503 8) 0 20 2 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo503Q mo503F mo503 9) 0 188 6 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo503Q mo503F mo503 10) 0 453 7 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo503Q mo503F mo503 11) 0 179 6 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo503Q mo503F mo503 12) 0 17 2 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo503Q mo503F mo503 13) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
theorem mo503All : ∀ k ≤ mo503.cap, ∀ i < (mo503.levels k).1, Impossible mo503.mode (targetOf mo503) k (stateSet mo503 k i).toFinset := MonotoneForest.allImpossible mo503 (by decide) (boundsBefore mo479K) (before_sound mo479K mo479V) mo503G mo503E mo503T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503R : Impossible false (targetOf mo503) 13 (vars 503).toFinset := MonotoneForest.fromRoot (g:=mo503) (mo503All 13 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503Low : Lower false (varsX 503) (graphGoal 503) 14 := MonotoneForest.fromImpossible (g:=mo503) (hints:=8858371396) mo503R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo503K := extendKnown mo479K 14 [(509,[49,100,135]),(503,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo503V : Known false mo503K := extend_ok (m:=503) mo479V mo503Low (by decide +kernel)
def mo507Y : Array Signals := #[(sR87,sR72),(sR99,sR81),(0,0),(sR103,sR24),(sR109,sR51),(sR17,sR55),(sR15,sR26),(sR16,sR60),(sR18,sR63)]
def mo507C : List ColumnInfo := [(32,0,475,0,11),(0,32,474,1,10),(2,0,505,0,10),(8,0,499,0,10),(128,0,379,0,10),(256,0,251,0,10),(1,0,474,0,9),(16,0,491,0,9),(64,0,443,0,9),(2,128,361,16,8),(8,256,179,64,8),(16,2,361,128,8),(16,128,361,2,8),(64,8,179,256,8),(64,256,179,8,8),(130,0,377,0,8),(0,48,328,131,7),(0,96,146,265,7),(32,2,329,144,7),(32,8,147,320,7)]
def mo507A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def mo507D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xfc7c59d999b964c485ee61153
def mo507D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2e6252fd20c173904e0f031dfc80eefe00c0781e74c9b9620847823c9c4b968c1719426970b1c539aba29589804b959720309054d0aa51546aa67fffdfef58553545434c110
def mo507H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20
def mo507D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f81d8247dfa2106640e7f9903866625100cf6603029083941a67c509c8a061a4ca3401465c3b52b1e128b00553ac354690d30a2050fffef
def mo507H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x286002427035200000f1131f557554685d0400000000000054143b4c00a02
def mo507D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x290231006ff
def mo507H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1b445052a0c00b140026c00000009180000315a1000b2e00002e1baf102040000264209517c40058202
def mo507L : Nat → Packing
  | 9 => (1,3,5,65537,0,0,1031,mo507D9)
  | 10 => (7,2,5,196614,35,8,1045,mo507D10)
  | 11 => (7,1,5,131073,16,8,1046,mo507D11)
  | 12 => (1,0,5,0,0,0,0,mo507D12)
  | _ => emptyPacking
def mo507I : Nat → Nat → Option (Nat × Nat)
  | 10 => lookupWord 1 2 0 4 0 0 mo507H10
  | 11 => lookupWord 3 23 4 10 3 3 mo507H11
  | 12 => lookupWord 4 31 5 10 3 3 mo507H12
  | _ => fun _ => none
def mo507 : Forest := ⟨1531,12,fun i => mo507Y[i]?.getD (0,0),mo507C,mo507A,mo507L,mo507I⟩
def mo507Q : SearchRule.Regions := [
(subcube 32 0,rowMask [17,18,65,72,130,144,264,320],rowMask [11,24,66,80,137,192,259,272,385]),
(subcube 0 32,rowMask [33,50,104,162,176,296,352],rowMask [42,56,98,112,168,224,290,304,416]),
(subcube 2 0,rowMask [17,33,65,72,144,264,320],rowMask [56,112,137,168,224,304,385,416]),
(subcube 8 0,rowMask [17,18,33,65,130,144,320],rowMask [98,112,224,259,290,304,385,416]),
(subcube 128 0,rowMask [17,18,33,65,72,264,320],rowMask [11,42,56,98,112,259,290,304]),
(subcube 256 0,rowMask [17,18,33,65,72,130,144],rowMask [11,42,56,98,112,137,168,224]),
(subcube 1 0,rowMask [18,72,130,144,264,320],rowMask [42,56,98,112,168,224,290,304,416]),
(subcube 16 0,rowMask [33,65,72,130,264,320],rowMask [11,42,98,137,168,224,259,290,385,416]),
(subcube 64 0,rowMask [17,18,33,130,144,264],rowMask [11,42,56,137,168,259,290,304,385,416]),
(subcube 2 128,rowMask [144,161,193,200,392,448],rowMask [137,168,224,385,416]),
(subcube 8 256,rowMask [273,274,289,320,386,400],rowMask [259,290,304,385,416]),
(subcube 16 2,rowMask [35,67,74,130,266,322],rowMask [11,42,98,259,290]),
(subcube 16 128,rowMask [130,161,193,200,392,448],rowMask [137,168,224,385,416]),
(subcube 64 8,rowMask [25,26,41,138,152,264],rowMask [11,42,56,137,168]),
(subcube 64 256,rowMask [264,273,274,289,386,400],rowMask [259,290,304,385,416]),
(subcube 130 0,rowMask [17,33,65,72,264,320],rowMask [9,56,112,257,304]),
(subcube 0 48,rowMask [49,50,120,176,312,368],rowMask [56,112,304]),
(subcube 0 96,rowMask [97,104,114,226,240,352],rowMask [98,112,224]),
(subcube 32 2,rowMask [18,67,74,130,266,322],rowMask [11,66,259]),
(subcube 32 8,rowMask [25,26,72,138,152,264],rowMask [11,24,137])]
def mo507F (_ : Nat) : Option CrossCheck.Corners := none
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507G : graphValid mo507 (boundsBefore mo503K) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507E : ∀ c ∈ mo507Q, TestedCube.geometry mo507.mask (targetOf mo507) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := MonotoneForest.regions_ok (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507T : MonotoneForest.Checked mo507Q mo507F mo507 := by
  intro k hk
  change k ≤ 12 at hk
  interval_cases k
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo507Q mo507F mo507 9) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo507Q mo507F mo507 10) 0 7 1 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo507Q mo507F mo507 11) 0 7 1 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo507Q mo507F mo507 12) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
theorem mo507All : ∀ k ≤ mo507.cap, ∀ i < (mo507.levels k).1, Impossible mo507.mode (targetOf mo507) k (stateSet mo507 k i).toFinset := MonotoneForest.allImpossible mo507 (by decide) (boundsBefore mo503K) (before_sound mo503K mo503V) mo507G mo507E mo507T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507R : Impossible false (targetOf mo507) 12 (vars 507).toFinset := MonotoneForest.fromRoot (g:=mo507) (mo507All 12 (by decide)) (idx:=0) (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507Low : Lower false (varsX 507) (graphGoal 507) 13 := MonotoneForest.fromImpossible (g:=mo507) (hints:=13153361988) mo507R (by decide +kernel) (by decide +kernel) (by decide +kernel)
def mo507K := extendKnown mo503K 13 [(510,[32,116,134]),(507,[])]
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo507V : Known false mo507K := extend_ok (m:=507) mo503V mo507Low (by decide +kernel)
def mo511Y : Array Signals := #[(sR91,sR74),(sR45,sR82),(sR53,sR90),(sR33,sR32),(sR92,sR49),(sR41,sR40),(sR50,sR48),(sR47,sR46),(sR52,sR44)]
def mo511C : List ColumnInfo := [(2,0,509,0,14),(8,0,503,0,14),(1,0,510,0,13),(4,0,507,0,13),(32,0,479,0,13),(16,0,495,0,12),(64,0,447,0,12),(128,0,383,0,12),(256,0,255,0,12),(0,2,365,144,11),(0,8,183,320,11),(0,32,474,5,11),(10,0,501,0,11),(18,0,493,0,11),(33,0,478,0,11),(34,0,477,0,11),(36,0,475,0,11),(40,0,471,0,11),(72,0,439,0,11),(130,0,381,0,11),(264,0,247,0,11),(1,32,474,4,10),(3,0,508,0,10),(4,32,474,1,10),(6,0,505,0,10),(9,0,502,0,10),(12,0,499,0,10),(16,2,365,128,10),(17,0,494,0,10),(64,8,183,256,10),(65,0,446,0,10),(128,2,365,16,10),(132,0,379,0,10),(256,8,183,64,10),(260,0,251,0,10),(5,32,474,0,9),(37,0,474,0,9),(144,2,365,0,9),(320,8,183,0,9)]
def mo511A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def mo511D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c8a9a86d976611425c120
def mo511D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2b8007b28370f26400000000006e001f1963b65264009f382225f50a2829e0b2d08000272d20c827365167084df36064338245ce82219c1219c1219c125b2820db97cc6073a444fc844650fc223238b053cb0513ff122283dc14b4410f803e02301f9e12dc226f8226400ef2645f02199fc04b35c87bf4aa48d748b6e856fd124650b1de7449de5895c0800042ff0110021c210e1087085d87f84f841c218c1bb32bc8b346036796b86704786746192f05d8834be8792198a8387888cb3921cdc46097d07789e0af82795e0fc9199079238770584b91da8fa8b707780b8b38a00af8962af81a2b836f87993f06e2bb87f87b81f05e04791f83f8126a3dc738d718e2dc5386304e05bf27acf05d93aa744e11b4b58676c9d872fa5ccb495caa050e99d25237446808f71da36c668c596f2a64f8921101e0384680ba1442303c86a0c41641e833044044001ce9887ba024cda853b6a0d0da814b66054d9008ba61a4e906a3aab86e93023a2c58db32c1751b25d44b99708ae93833a2e3ae23629b3002ee3c2bb2f0eeabc4ba6f18e83d6b30fbae33f79aaf8cecba43aae94e9ba5ba4e9ae83af195260cc34d390336e30aeb8e3b8e39013b8a3ed42d212ab40d42b292aae2d426e3967c2e41f12ec8c6bb20b3a29006e1d5b506dcdb1993505a06d1483b44a6ec92aba64facaf45de0bfba5772aead5cceb97571f8e3e9c7738ed71d5de99bd2b79c6f32dc75adb35b56b4bced59ceb1cbe29fc1df837f03fdf68bec5783eeb55cbab96d6daac5f58b7aed95daabb4d765aec75d36ba5d56daad74db69b5cf4e8ed70fe974508a564970714b6661845c1c42d99861170329985d9845c1c66c8945d170701b2251745c0866c8945d170219b1251745c0c46e4865d170701b2219745c1a65d984509705d9b0688945c0b96dda421970325875d984591c2291745c120704a45d17048095291745c1205d98459170480a45d1625c12070ca458970481c1291625c1205d8a458970481a86d9425c1206d9845097048176611425c1202558450970481b65d1425c1202197450970481c26d8a45c120709b421970481c66e8951d12070dba25474480b86a1a265874319a8619901d1b36c5a9218746c9b06a4861d1b16c1a921874
def mo511H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10
def mo511D10 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then 0xbadee9fb9fce7eb9f5e77b9dde75f9afe67f97ee5f797be57f93fe3fb8efe37f8bfe1ff7eadf737dadf5b7bade7b77cddeb776ddbb76dddaf76add7b73edcf773bdcdf6ded9fb63fd7eb5eed7b75ded73f5bed6ef57ed5bf56dd5af3fccfeb3f6cfbb3ebcf773d7cefb3bbcedf3afce7f37ecdbf33fcbfb2fbcbdf2efcb7f27fc7fb1fdc7f31fbc7eb1f5c7bf1dfc77b1ddc6ff0ffbfe2ff2bfaafdcbf6afd6bf3afbabdeaf76bdbaf6dbdb2f6bbdaaf67bd7af4fbbeaecfbafaeb7b7eadf6b7baddeb6fadbbb6dedafb67ed7eb5bed3fb3becdfaff2bfaafe6bf6afd6bf3afbabedafaebdeaf76bdbaf5ebcfaefabbbaedeb9fadfab7dadeeb5facfeafeabeeaf7ab7ea7fa7fa9fda7ee9efa77e9bf9fea7de9dbe5fb96fe4ff8ffa3fb8dfe1ff6d4a466170298a4661705d0a564970508a564970661a661170661a5611702d9986117066176611706c8865d5706c8945d1706c4945d170218945d1706e4865d1706c8865d1702e5a2591702e998591705d9845917025174589706e894589706cc94589706c894589706c494589705d89458970661a6509702e5a65097069984509705d984509706997450970661745097021974509702d9a8251706dda6251706c9a625170661a6251702e1a6251705d9a525170219a5251706d9a2251706c1a2251705d9a225170219a2251705d9a125170219a12517069976251706e886251706dc86251706d486251706d086251706cc86251706c886251706c086251706a0862517069886251702d1a9219706dda4219706c9a4219702e5a4219706c1a2219705d984649642a5a461d646d4a961d646d0a961d646c0a961d645d9a5611645d995611642c195611642e587611646d1766116461d76611646c0865d5545d984591546c1a22195465da0219542a186589406dc86551406c1a7219402e976611206d8a9611202d1a85c1206a1845c1205d9845c120255845c120291745c120255745c120219745c1206c9645c1206a1645c120611645c120255645c1206d1625c120611625c1205d9625c1205d1625c120591625c120291625c120255625c1206d9425c120611425c1205d1425c120591425c120255425c120219425c1206d8a45c1206cca45c1206c8a45c1206c4a45c1205d8a45c120254a45c120218955c1206e4865c1206d0865c1202e987591205d984591202d5a91d1206c9a61d1202e1a61d120255a31d120255a11d120219a11d120255a01d120219a01d1206e8951d120698951d120658951d1206d0861d1206a4861d1202a1a5658746a1a2658742e1a2658742a1a2658746c8a8658746c0a8658746d086654746d086644742d9a864074619a2640742d5a264074219a2640746a186640746e886640746dc86640746d086640746c886640746c5a9218746c1a9218746d5a4218746c9a421874 else (if j<2 then 0x1961ca047b7001151b5550071d5151b554546a5582dc5573c71542d4ba4eb57253ad4c94eb52a53ad58753b561d49b4ba512c71542d5874fb561d61b1b44b9a6dd2a0dc74db561d3001cb910c7124550a6920b7157435c25d0e705743dc05d1e715688dc25a24705698cb95c636dd6eb8c5596f6d16625c08a1071dd045c5741270dd04dc27414701d055c7701a715c06dc3701c709c075c0700a32dc65998730a325c989b772037019941b95f5c6a19545b95e626dd7975a864656999179a863666998d7da862676998981a861686998585a86069699825998670b725b859c76e1e711b87dc36e20709b889c06e97661bc34c96d0272da835c96a1771da881c56a23711a899c36a2a701aa61986ba96d9ae85986c6f6d9b2b1766cae315b2b1756c0e725a061c76821715a091c4682770da0a5c2682b701a2659869502ea30b1c58c2d7123010cb8e9132a2c10cb8d733121a15c48589702141dcb872f7261cf9c5874070e1d09c287457021e15c889856622615c6898561a26148689856162615658973662261dc08986662221986888621a22198588865962001c783547160c01c2830171e0ed59882b26620ad58782b16620815c684aa2924080ca8fbc5d23c00c980626e9f1f1b87c7f5d9fe01767e815d9f509c281447060401c87a00719e801c47a0032dec19c27a94661e6a1a6782f325dcbdc9754070dd515c0750c329da68c947646d51d91b4478770120e9c3493b7012400ca45007251951b6210a7247c6dc31f1c7087c75c01f686e08001cb15556a45979a816666985995c6196a70c65adc1199b72462b5c218546e85e4da8179b6985e75961e0e7247091c41c2770c7279961d0372c683dc91a1971c6895c41a2870c68a9c21a9f6606e7d961b037008ed587222a70911e0c5258771c9241c2240872c9889ca263672498fdc726497109929c3264b7089931c126696a0b209c72c8c708b1f5b828826d8a021cb277e6e09e2db6276e6a0ae21762b8d254adbda82a895d8aa38952a706a0a62976298f254a584cb43a36a10a91a84119728f8c1c93e45710f919c33e47708fad1983fab6a102f495400332cf2e1763aa66a0eee5763b896dcf6e9763dba724dee9c437c05d8cca8ca39ba5d8e425cb343d720d121c634ba5d8d139c3344f704d2e97638ba618daf89536bf290dae97636ba5d8d5bcca326f6a0c8a8ca322a728b4e5c92d4d710b539c32d8e6d8babda831b66a0c641b631bf5d8c7049531a76a0c6fdb630bf658c2fd8630bf218c2bda830bf5d8c3049530ba5d8befd742f526d40d59b303536d4095db202596c409c598898470225c99888b06620905c2404370502dd7633a56a0c6ec9530ff2bf9afdabf5afd3bf4bfd2bf3afcbbf1efc6beeaf8bfd5ef2fbcaff0ffc2fefabbdaee6fb7aedbbb4fecefb2febebaeeeba else 0x3e91a54c6b85e88c12625d4c1200e2f81334412e91dc8b8b40b01402c06c0941a2403971a8cc9b8b6726a9ccd18fc34cfd0d947b0324f130b66942680c40b86de0808008b2290184314b1265247780c580f6d22043158cc45aa4b4a11a4830e60803996328d1d0e58358c39a8e54789bc8cea223684f0b612c3b2a657498c6387f1066b53836e4c03305c2b870e2dc02ca51f269a3b04017411ca58b84dea0d27a4459e44c9647195869cbc3fe4c05d45627457e175313c3206a62578ce0f43e83a2c035caf4268b91f42b82b8970bc24c5788f0d8aec3e87b12e1e0d99192311cc6c8dc1783f02f07917e19c6391e0be07c1ebefab8ea3fa62e8c79f7e71b998e5b392de4478e0e2c3876e12b833e0837dbdf077a7de4376cdd23715dbaf6bbda0763cd8635ecd6b7573d4cf504d32b49dd1f3457d09b3facf2b3a6cdb732fcb972a2c997220c8071d8c6cf183c51b100c3830a0c19b041c076ff5bf46fb0be2ef57bc92ef1bb0ee9fb9cae48b86adf3b72ed92b5aed41b46acf3b30ac8cb17ec38b04abd4aeb2b81ad3eb22abe6acfaab2a87a9aea4ba8629f1a7229a1a5ca952a4ea916a3de8c1a20e840a03e7c89e6e7709cde7039b3e6a099da64f988e5fd978a5cc96da59195ae53f945650193724b99216444907a3d68eba38c8df63458caa30e8ba22c98a8e27188ba207871219785b6144849a0fa836e0ce829e09081a60508049fe37f0dfa37e11f757d79f4f7ca1ef77af9e8f795de277805dd976e1d9275a1d2673ddcce7255c6870b1bf26ef9b926d79b4f6c75afd6b4daaa6a15a52688d9f166d197c64fd8ff631589761a983160197e05f217965d5971f5b8d6c45a2d66b591d62257dd5bb562955254c14ea52c547b51114124f653944d4d3124b9d2c44a6527b494922d480d1df46e917944f10ff43890b241d9046405cfde3ebcf913dd0f503c64efc3b2cea83a2ce5a38d4dfe373cdaa3604d5c34e4d213410cde32e0c9231b0c463080c002f58baf2e48b6d2d44b292c14adc2af8aad2a50a6428d4a06277c9ad2600968252c93324188ea232889e21c085220607f21f5479a1e1476b1d0070d1bc86cd1a5866818dc61d17ec5bd167458515a055414cc51113f44d412c047f11bc445109c4060f3c39c0de83440c8c2fa0b542b809f424b086c1f7074c19e059013404140da02c0080016802e0001d5c010767083ccdc3143470850d5c0142e71c48c5c5123271048cdc312357004a48b8133171444cdc311357004569b5039e6d40e81b3035b6d40a7db502a16c80a89b102546d40961b2025a6c40a5198019c658065198009c65801ddc20e7971435e5c20d3071c30d9c50c3771030e1c30c3970832ccc6085b7081dd1c5067a71415e9c2057b7281255a80b0f72824c1c7093671424ddc4093870c25e1b80a9f6a029e1b60a747)) else (if j<4 then 0xf6df0c0019f4fd0220002a604bf9ff0540004401fd8811004053c3e5934e8e000221df8e350d3c1102253b74875c3000690d3f90c0019c9fd4100010d9b74875c300069c747d00010d277bc02521fe01231fd10000014caf87fc4e7a0805136f1f85f4100a2000e7f8e2fa28a2178f0022821fa391460022002bbda106e44b5a908fcecd5484f5d7209219dfff1a2285002235c196800010e087a3c7c18010f4e2d16427bf461ec8080000114d87fe0b04002690ffe84d00001a43fe485821003499e2626c1014c09d3be1f800069f737b3fa44200004513fd9d5c2100002245feceac9c800011297dbec002956edf6152715bb01c0a586352613bf5fa000cc06d6ba7a4cff8e4801986c8d892938fa941948aff5f6402000408987fea0520002044dbc7d0280400122734c78c93fc5784100939d3fa7f640400d3bfe31841009337f15f020124bfa7c1604044d33fd19e820126a34b764cd31e3225fa000523bffe104000087b60d9c1cdfa1450002997e3c152377a24992de1ebe98010cbf9c08047053fff4010010f5f7a500801a17f381008fbd7f3812475deb84023c7f504065dc484427e581311f02a81481d7850033075e1400cc051c8e05237a61400cd2f3540042cbfc074217fd22144cc0fc1e50a16eb5b3476f2618285cf9e064d7fe780e85ee910c066c7f838e042e7e180c87c04dea02217e35f822133c3e4f0108286cf8d7e0884cf1afc110999dfc3ba988287478fe9aa1436e152207f2c09b2f428a1cb5e78010c5e144c96f02850837ec180014baf08bd800437dd3eb478e4c02fdf110441018fbc10aaff00835797c5b286001112fa8297c020c0f33bb00528bb307c300087a65f50697ed600a4013fd5346801108a7f09a0043631f782cc821edec283860366e139bf8d4bc3aa306a4bf380a3d0e3c257f80419e5123be010a123e1022653ca24f7f258004297fe67013eb6f0d0c0021f690aaadf0982a51b5f01143f1800cb5ffc93abf001a19ea885aa0043b43b600ca4fe2ecc560043db8098213da726d2b0d6e0b32085dcf60228037fe7586a3069cfffecd2a019e5d9fb9982a1b66e2e012366d8b0121dffd2c452010f0e4f1042ec10445bfc2bd01043570e11d7806797ee400010d87ca02a052b39be25ec043031e78010a1ff671800ce03756493043220384a178485e9ae81c65503a4d494411d139f61ac2e541a684a435921aed22e09483a765f8bc52c0aa9652b6111aa7166c62044a0a65acb50e86ce9325546c7f8ab4d63689464f46e8a04751866040149a9343ea4122e918952a24ccf593f0a05009086d244164949491c5359031c5a8026894a223c488a9c1c21c99766bcd1317348c91c2bed2d01c830ca9754df1684b8590b3461c6b08c9a4670e385839c450db04cb96621a30d068961c4e8c12816e9a914e6d4 else (if j<5 then 0x18c28633fc6f0c080029f1ffc0a10010d9da34d100344fc3eb0a9243bf07464050800894fc4064c7ff0284004307ce3285113463fe8c80a1001109fbb29500d0be610cb6b16bfffdc4b1146002257ac0445eb01117cc21ecdc5c0246cdb1602417ffc8d4a8068aedfe6a01995fcded0402184cf8bf05480088c7e0043ff81300044effc9a0236ba7918804359fa9c0c104400a847fdaaa004002226fe72500810002a03e9fb020033abfed54060105115edcad0e26797cc80421e1cc5c0a49e9e4c25810f8ede462010cdf0f889c00d07dc62e05377b5d0592480a797ff4e02002002275ffff61094a008008a57cbf6901001001151ff5da41802006ac7fffd84e0200214483e8b2845ff2b1a0238de1605292bf3e210401a25ffc110407001120fff9bdc4101c004480f5ec6189e1488aa018005400000a7fe00014ee7bd000a403efd82a4abd8f000a427d3c008437a2004249d4c00290013c9d4c00298083c882474537346a4b3f0a87006ffc000295cddab029007be2e8454b2da1b600432bfae856050c02479a0b110fd80b0a900ebfcc2000014f96a7b912926d0f1002a500438d9d8915fa140198dfd9c480810edff9eda52103467d5529801a0b6f4280336ff60c008eaffe7f7228820440027fa055273e3f700286ebfd1648002988fed889054b6ff2c28285dfeb0100122bf9200328fd602091eefa009efde0409c3eb6f4910034537f120066dffac20123b7f51200662fe9d24400cf4e5801091f04c73fe78008dbcf00119bffb714c60068a7ff476a70300221dfffa50961000044d7f7c043c019c1cffa966e9900004503fa1340021bdfb7b4004343fddab080002221fecb6460021dbfd294f1009a0df2b7a46143ce6b8ac0090bdae97011d79ce7ce01217bdd7804737cc506fd2033f480c3fe3080464ff08089993f94808019ebff20200663c6246f6b7b032efdb01047f78bd5a8080872edff76290000035ef7f60208e0f83eafaf800000115bfbf6c088fbddb1023ad03ebe683180000a7469870617351468938e8142a70f3064479c140a173ee1b7204068e68f9b900000081141c7c8101981ac06fef000020450f3fd60011207f55a010489fdac0102409e1114717f3461014bdfd001918062fee000216b8031d1fe0000a4dd79220000b7f357f80510eff2590a0a1bc7041b0f1e410a12bfa11321504de24885411dcd97e1429bdadabc1021cabf6cbbf2000d39f5fee40019c3cfafbee4001a6beddf59c099fbea13d266e87f90006627d0104277e5e840cb52cdba1033c3ffe80066d2081128f0fe051921b5ff81a630a002bfb79800088038fe000052ebfb36d3f40004400009bf6f000110efd1ee400010e4d3f730010cefe5e0800010ee0134fda880000a6afc03264a66ffe1021404b776c94a3f11e0046a2fb6f86000d1d else 0x35f838aa1200e0022b9ffe100c401c0045367fc19899980bfda1c4cf0fc9f)))
def mo511H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x614c16552254000003ad40000b4827c120accb80000020000000d0000003c888508dbb9ea0a0614c64540024b2d1040b0868a8a1209804201d0970e64bdcc003709e47840c003069c384dcd18000000002093e34002ad044586c003c74c640000000000015b0001c5908f030c5e8214d400000207d01a42a4e07155d400000203fc2f8cf9cc00004c000002c718828c94a000180604a0a5200028714c500408398e82
def mo511D11 (j : Nat) : Nat := if 8 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then 0xce0889b282246c209899883206ca0c04ba7e5f661edc1767b012e5b17d986b4d6c0b481b7302c6ccc0b5b2302e6c4c0bdb0303d2d45541b214026e838f5a90e4f698394895135325449509511036e86865b91a246dc68bdb41a316cc68cdb21a356c46951a81b656606dd1761b1b6e07099b61c316cc70cdb21c356c47115a8227425481dca420725d87df5761e8025479e5741e336d87600951d846107611741d076d42421b309096c82429b0093866000ed96000c6d02035b507106d01c4db307006e80c15b7030e6d40c45b403146cc0c59b2036961d3079b2831f6c60dc5761e765d077ff5feeff5ffabfbffdefedff6bf9ffbefdd7ebff3ff7efbd7dbfeddf6afaffd7be7ff3ef9d7cbfdfdeeff6ffaffcffe3ff17f7fbbdfddfeef76ffaffd6fe7ff3fb9dfc7fdff6ff77f7bfadfbefbf7ddbebdefef7b7bbbd7ddfeeef73fb7fdbf6df76f7b77db7ed7f67faffd7f69ff3ff9fecfee7ef3ef9efcefe6ff35f97fc7fe3beffd7fdbfe5feeff57f7bfb5fbefdd7edbf5df9efbf7debebdf3ef7f7bebbfddfaefb77bbbbddbeedb76bbafdbfedfd5ffaff57f6bf75faafbd7dabeb5efaf757b6bbf5deaeed73eb7f5beaddd6deb3f57fabf4ffe7fd3df8ffc7f9766558469176610a95d984299985c0a4661705d9925c0a564970219925c1a761170699845c1a561170661845c185611705d9845c17561170691765c1985d970219755c1985d170611745c1765d170251745c0865d17069d645c1a559170689645c1985917061d645c18559170611645c176591705d5645c17459170595645c1a458970611625c176589705d1625c16458970251625c184551705d9545c16455170219545c1a650970611425c17450970591425c086509706a0945c1a625170694945c1a325170688945c1a125170618945c185251705d8945c17525170594945c086251706a4865c1a721970690865c1a22197061d95591876496461192590a76496469187590a961d6469d84591a56116465d84591956116461d8459176611642a584591a85d16469974591985d1646117459187659546598455187611545d984551985d95461d76550865d55465d6455187591546156455184591545d964551755915469c86551a42195468c86551a22195468086551a2591406196250164589402a162500865514061142500865094069c86501a42194068886501a6611206518448176611202a584480956112025574481a85c12066170481845c1205d970481745c12059170481625c12050970480a45c12025570480865c12068964481945912061d6448184591206a474481a61d12068c74481a11d12068074481961d12061874480951d12021874481a565874689961d1a0658742a1961d08665474219911d1a864074689901d18664074219901d196618746a4861d1a421874 else 0x988f4e2ea2dad988b042ea2d85988b6b61e2d85988e6166231ad988a6166229ad878a4e2ea19e0b486256e60895b482256ca09e198837861a0de08683786160de165836b6621469b982256de08adb582306d208c9b382346ca08ddb082636621068ba7e432e9f810ba7e4e6a20410ba7d732e9e9cdb87a736a1e9cd987a736d5e9cd867a7369de9cd877a735da01cd767c735d9e5cd767767661edb9987b7869dedb9877b785d9edf1767b785d5ed85987b735d9ede184781a2e5fd39a77f735d9fc69b96d256ddb4c1b46d326cdb4d1b26d376c1b58d986f61661c1cd766e1a6e64495b791306d244c9b391346ca44d9b191376c2458d9893666624955a692755da4954a492755d24a054292736a5d1cdb4741a2e5d9cd7676046e9c471b871276d9c5cd7671326cdc4d1b271366c5c5cd767573619cde09473735d9cdcd7672042e5b10cb96c43661b068b96c1a6e5a0c1b468326cda0ddb06867661adb9986b58699ade1766b61661ade1a66a78619a9e0866a67661a9e1766a735d9a5e174694e6d4b539b42d586d4b161b22c5b6d0ad61a834256dcc0c1b430326ccc0d1b230376c0c095b731306d0c4c9b331366c4c4ddb0316c2a0cdf18632046e8b895b72e306d0b8c9b32e346c8b8ddb02e58698bc69b627432a4a810ba28666a49998952966658950db615516e45145b814512e0516db214436a44119a81051698410da90f516983c11ba0d436a434c1b40d556983999960e596584d7196125c618497086125d660457596115d61845748611042e85d989518672e459b987167c5d859fc95165b69c66049519856106574b4245d6a08cddba1a376e468ddb71a376d069e9b9217a6e085e9a8217a65885e986217a6d085e98721826a06e09871b826986e09861b822186e09761b376e07175a81c376d871e9761c822547175a8226f6a089bd87227a5d88a0895227a6a081e998207a65881e986207a21881e984205d6a081e987207a5d8820895205d6a07de9b71f7a5d87df9761f822547e19841f7a5d07e1db21f876e87a1da61e875d87a1db41e872907a1d841e875d07a1d641e876d8761d961d87618761c861d87610761d641d016c2582db5090b6c8242db0093c6a02cf1a50b3c69428f5b501416c40509b001126d02061b507606a01065ba03196d40d09a805652d41405ba03066dc0c3db503126d00c55b303176c80c65b0033d6d54805b0520f6d549a9874c012e918e9b939486d4e4f997383f65cdd59b4364265cd55db435012e908a1b440296cd00a9b0400f6d65125b7595a6c16019b987206d21c85b387226ca1c8db187246c21cf19866476dd9911a85f476997cf59865485d99511a85e4769978fd98644a5d991297564406618d2d76634b5d58d69b06341661893176624c5d588e4ba8d5e6622c19b9821d6d60881b482216) else (if j<3 then 0x203df87b24f4f1e613c667828ee79d993ad874d8e7b9cb139187148e119bf137886ea0dbe9b4936346bacd5c9a8834aa687ccff99df335e65d0c9b98f231886240c36183430125f80bd517742e7a5c3cb6a96972ce05904b0995f22b885664ab1153e2a2653a4a5a947a287c50389f493b327104d3898c92dd254449a491f920a239e46488ab112e2208434c856108f20c840d48010fd41f663e287b08f371e323c087710ec21d3c39ec72b8e221bda37086d10d721aa034e06858ce4196e322862d0c2c18022f3c5d40b8616902c585720ab814ee28f850c09f0139626604b9894f123023b045b089510d8210440e87f60f7a1e0c3ae072d0df21b4c35486850cba18e030705dd0b7816242ac052e0a1a134c24d8474087610141ec03a506e00d28193030205a60ab0143026c046e08640f001b20318057809a010501ae02a80408059005600020d8625436d6590db496436c25869b096436a6590ca997042ea6068b998642e03190a80c642e02d91a80b642a02d91a50b646c02d91a50a64688290da80b436942d0da50a436882991b202436d4050db001586d40161b200682d819a1b206686a011a1b805686d815a18605682181469b203436d5490db452436c14999b5521a6c94869b052436a548adb552432a54c10ba571a2e55cc1b74b306d52cc1b24b672e54560a951582e93d9ca94f6e6e535b8b94d6e2a535b9b64d7c6e931f0ba4c7c2a531f1a74c672e54160a9506e61d41f17650582e9399ca94e6e61d39f1764e862c1390cba4f612e535b9b44d1a2e53545ba4c512e931cd874c7c6d13010ba4c6b61d310cb94a436a1210d9849586a11d61a6472b6d55010ba561a2e558c0ba55672e5559d97556e61d55f1765567655550cba464e6c0e50db939556d4e561b238586c0e10d97385b6d0d96db0365d6dcd575b4355d6c8d468ba42636e5058da941756d504adb4406d6d511858745042e90dad8743436a0fc10ba3e646e4ed91983b7361ceded763d556a0e99d973c6e61cf1f1763c7f614f1fd753c1a6da510ca6941a6ca50adb5952b6d650ddb094432d16d0db25b4e6d56939b45a4e6c96960b959586dd6561b559586c96539b7595b6e5616db7585b6d16138ba884e6a22495b987256d21c69b987256de1cc1b487326ce1cd1b287376c21d19b667462d99d19b567466c99d45b866512e199459866516d59945b266436619939b766466a18545a661046e97069b95c466a17095b75c5169970adb55c306d170c9b35c346c970ddb05c4e6a17d8d985f4e6997d5598655561995548665466a18145a6604e6a17939a65e466a17545a65d596619165856459595916db8635b6618d6db6635b6198d6c86635b6158d6d6563436618d3976635d6c18d7198625c619897086625c61589716562612ea3584b68d432ea3518ba8d616624185 else 0x648201b4794d5f17b8641c9c32d4312a8265192c4ac035754c5d839985b3259f46e99449248541ee4895494136166552c8781c251154684dc0a1d8de5b481891330c2394958d609325ac862e192961fc9447950c723486b4dc50148531552070e3a48d2521866645d12ec534c9e552cdd19c1b514dd48a305a96b08d774cca54e83c7f1c45466d178db490dd0a8565ac6c584de1505196c465c4651d23858d4d111c335c273448a4f1574aa391d19d4fc47120d609d445a955159372245d361cf0b8468f1389623c35c3b0dc69379391a48c1f02c1595d0f23e0cc6f0cc8e0bc0f07a22f41ce7f9cf1b9c0f342e613cb0393cf240e413c72b8c47149e217c367853f07ae069bfd77e1ef96de93bc4f76e6e9edcb1b8336f1eda4daefb553685eccbd937b1b3626ec13d7d5ae935b2eb2cd5e5aaf35376a25d3e3a7134c66968d269a423467e8a3d0e9a0db40367dbcf579dd33a06716cdbd9a5732d662ecbeb97172c5e553ca2f93a72536480c8b990c3202e3d4c7478dbb19f630ec5b58ac31436261c45787670d8615ec24583ab054e06ac05f8002fe5df91be9b7c96f78deb8bce978a6efeddb5baf17512e87dcddb9557222e295c23b7df6eeadc25b56b6456baed60da97b4cf68b6cfbd9dab36565e6ca0d915b1e16352c5c586fb08d601ebdf5798ae995c0eb65d686acb358b6b02d5c1ab0d5542a8f54eba96f521aa27d41ba7bd4e869bbd351a6414c0696bd2aca52949d2924d205a3bf46ba8bed144a1f7431683bd046a02b3f3a7c4cf4d9e253b527514e7e9ccf38fa7114df89ba5368e6bb4d439a3b33fa66dccb9993731aa6204c1b97ef2f1e5d24b6896652c1656ccaae94f1292a50dc9e4939925fe4af49329215232a44bc86a908d20363f3c7c18f331df23aac72c8e171b1e350c6668c9f18b22f7c5c78b5516462aa450389b51296236c43487ef0f361c8c35486250b621554284849508520ecc1a382f1054608840df8159022a02c402a7fe8ff51fccbf767e78fc81f783eb97d1af981f15bdef7b88f651eb5bd337a04f36de5cbca3790ef139e0abbdf7760edfdda13b1a75f0eb09d51ba71746ce861cefb9c17310e559c8cb8e3715ae191c14b7fa6f6eddbdb9a37026d92da61b22b6246bf0d709ac7354169f4d2ada32b42b67eacf399d5338e66c8cc6d965b29b64b2c8918f331b26328c5cd8aab1286220c39d863309f610cc159819b0105fccbed57c92f7c5e9abc51773aeb45d00b9317122dfc5b8ab62d698ad0e59a8b28163cac4857faaedd5c02b51562aaba954eaa505400a6d94b8293f5232a38d4592868503c9fd13e2277e4e7e9b8535626734c5c97c92e125924ad094cd28224ec496a91f521ea40347ca8ea11b6a33e46108b3d1432250444488090eca1b84322856108e20e0415a81d901da0093fce7e98fae1f)) else (if j<6 then (if j<5 then 0x737fc60b600d0964ecf4a00a65fc9987df00942f07a84a400443ef08161fb34d14213f581bc0043bbfff10d94800889f8f58e61f6e025e3fd076178ac0da2281fb618a028667d3e9d0a0287c3fe9624607fe3f0d0a02878ffe88200cd4df2e4126627c3b0204002231fb7f6040c0874ff2d3c02800d04ffca8a804362aff89000101112ffe0899b8800444ffc8080478f7e504400d03fe1ea860244c6b3011b7ffd0808048cfc340080cecfff3b0420021f7ebc08119b3fe001133f7f984400cf4fecdc010010e6e3dc7ce9520a24dc7b8d58009a227c2f927f00219bfebac0cbd31a92d283953e1ff31b40486d7fb37c1b801a49fe075b06010e2ffcc0e803385112f905d5ed8002209faa0e80b00111af93e06042e132a79f69ca9fadcffef7910034b78fc30d3e0889a75f94d2a0420022700c98b8216bc06016067a7c8883000438ffba48047bfd0013f7fd22002675fafaf4000914cbf88401021cdd59b8800861eaf482317fa721819838f8e440cd56f2e3b03368c3708d86e112dc310210dba98210bc32c91943fe41232abfdda24207ff0f306481a1dff944c60810f37cc30202962f96e11b3ff88348819f7f229046d5d044a7f2c04204317fb2000668edf0982033c43f2c88019f30fb680101a32df0da00668dfe3b5540906f4ea740404387080760660cf84c1941365b9597744489af3f3b48001a3bf5d2d2000682787020408617fb7dc0300000448bc3e1f41030222579cea0474f1e5204661ff5a08233bf4651004087d7d004042e1cfe0023c3dbe10a8000883bc2c5000a5887a765d8001a629ce00ca6ff84322858bec117014b4f928010a7fff4280a25ffc05aa3001118fd44f308c00441fffd0a028cf8ec00444d12ffe62a30010e3fff2502349e84c0014b164d485485e58b600cc5cf60a066b72a605021b9ff93330190d109cf06553f323005014d2fe313014087a31a055029593e140cb52c53feb0400354bd901b365404443eacc008517f0315d6110441be81b32900111e364ecc00861fbc40eb580934c1fdb8ca80871786280a167eba5891a7f328691a1fe18944143136f42a88565bd0aa216ff442577e9f120440439bfc084defd1f424000688dfff42020123bf9004066dfff420201232bcb0040674f7e500044d03ffe50a402467f8d750019f1f05b2410b8fe3a9810b9877e5280338065ec63067a205a3135950ada375d173c8f164c0360d615306822069025615d6371d8ea389a5869f7619b878a09851f911a527e9c2241f10c26c51a10510a274440560259424e50da966a50685f30a1d385262445614e1289957b040722b1ba90124120912620676942525f20c9b18d1792b8be1d20924e626140298088168d0348b61c580821b26508249a429319220e26009796c0b670a240b09766d6a195641a9714b4089326 else 0xb2cb28001a4af606d1f5cdc4f40014c2fb4df476a102226f141a397fafe80f0204399d81b472f85b9b2b5c088ec57fc20001a1bed5bfe610000d545f3ee7841034d36b9e7e1040d29f5969e17f3f0a006b6f297fda14000d359e5cfc2119dde2bc281dc8e204573fc951acb3810204574ad6feb0a0006a4ff1ec28001a03b79e7e10000d38f0ce53dc08787f9b4bdabd718050051a7e70c027a74750000868e5fd73e8001a203e5f6c2081a0dfffef0c00840000117dd3d31ff00880001b00cfb7fde180108001461bfea0a349a81001141ea7ff0300003537fff4181040d0b1fc08011e3f9cb00a2fc3009879abaa00498ffe33fe21e0500035b7f8715fc31e87500036cb0f13dce043fb9bf0f05e07381128fff8e02040876ce5e7977ac381aa9fe1a5086121db2d7964d8c01c231d03f04e0fe005040863678251ffbf25023d7d9b0197bfb3113335be209a1feee4220218bf98423297fc084652fff018119b2f4b6004094c5a71e0596f482567fdc553090de7f382080080a7dffb0900024e3fd6c210408787fd80108048717f7721004087afefc8406697fa170485f38762cbc0014e8fa357da4000440bfd9c299c808a34600011d1e6bd91965e09a6f0d0408806427d0ee2c87104d1f14900ffd8aa4028647fef6f83788600011614fffda0c05b00035c3a367846400888bfd7740054cefff4ee2000011157fc4450a941680dffd904a60001160e937fd90309300008b2ffeffefef130200006ce79b366c1d94c00022fbffdfe5d00200006b6f681073803447b8ec04cc8abff4c520143c007cc2b4129882f053fe0de218408b07bffd806032861022fcebdcd82a5278fec55a2861780587fc11280022bbfd3ed42e4c0035774ff2f9a79e508e2ac000df4f9a6f4454087f7db9f618000440be5a7e5624c00022aa1ffb6d4d8001a4abff103401a052f4d698021cb2f6f00066e78174d4000440bd5eda14086bd19c24ffdac004400d28fe42c021001111f6f59ec004400d75b7e3b0011003519d81b476e926ed94200089aa7cfd3f00c00d3083f25d90a189fe64f04d02877702bc1d520644437a7b7146ce00889b4bf4e0ba8800694cbc0ea281a131ee31963e809b64ccb1edc0462f4c8c60cdcf860e6010808857fa3a265214088e71db61298140896e38fcb1000d0aff4735285021fb0fd4fb021003565bfdac1000d01fb05032c652ea3efce2001af9feeeb4d0a9420008bc7fd788d1d14088c14ea42a4841f995ad410fcf86e09b21aadff715f51000d5ddb2a27d0339b0ffb502161fd2b04468a044c3fa51a0ed19106c3fef54086eebd427e2001a6bf0a12edec4003595bbf86f3ac00c00da1fd60a0666f1f6a498e001aabf4f8011133e4bc73d6f40d05cadfa500672a56b649bec3492d4a3fb323ad700951f16129401a3d8a8e4d1043) else (if j<7 then 0xddf6200014b6780c4c052d383f6c06943443ff456c6440d36e317f4442043c37f89901fb6034a169f8e7ab810811006dfeaf1c6094e093f208810d5fe560065262e083af760648753bb13e032042045ad7111341209fff2b205000044dbd1f17a0310c00022f7c444d047cfea7f31fe30068606c47cb9aefc1019820453bf04b800180444b93fd06002800022a3d780c220ce2fc9db0810c2f8bb0810baff08be0c160001131ff97094c8001a6b4fcb5a000069afe3f488801a13ffe91000034079fc7e912034627fdfd80819db8fffe910103447c3cfe9102345b579551440102263aff89f784400d416fcb9a1331fcee610509ffd19900068dea0f88a16fcb9a13377f9d1860679ef0445c9f80465fcc8a4f0900ffc1f7389a2081125fe5f0032e1cd91d840a9b0e6e2722054ca8b91d0780808837f944d48360802045e3cdee200081105df0e1d387c80000036c36ba6f13021da166ff8480d01dbf710d30000001b43ffa3270fd80008d63fa7e3f132820963e96ffdf640812cbf5e3f03720006a2782976400a1f44fe0011f0dc2205bfee6c99b461e115ab4d7000672fabd801983f906b800338b9b70a182185f995a72004397d5ec00cd0f611211bf158132c7e4664cb33ede22cbf3001a1021e7cceedd04881bf0c4c2cee1b282427ffcc76103385f0d1847a7eefcc0068408837ff2898c1021c2fe0ccf014a6fc1610810c4c0ddd0a21bbff80de822069efff4664819fbfe19181833e7f23b2684006ab9c02577fa3f713098080004593e210210bac1652c19e21ee92c1989fcba74d6a0002263e20dd900034e7a79558819cbf8aac197adffac58ac40d2c5d5b80333174be00cc3c9e9f808fd8eb064f7b228810ace4f88408527c4204257fe5870580000035f7096480cd2ff828148000220bf4129dff380272fffec0dc100034b7f8cc813348cee917df8106cfef90502888089d7f10c5e2c3a00802046063f2c9019a3cbf5964040d11f4ce1c16408d21fe70e0b2020698fbe55fd99100353bf9cb5030a0d5e28aaf0001119fe907e3720006a2fc659538a48001ac3f87c47bc000690fc39558819e1e68f40852ffb7564f0001a53ff988fc000680ff2d25f64000d29ffa4add980344b87a9c6286878226c10b140f9971e946206b37f5634a004393fead8800087f7c3102111aff56d4008727570cf00a1a9f369610000883f19c02727fe6d24600011181ff009961ffd6923000088bc1f226cbf0980000a6f7dd10a9000111e80c09bef0c5c70fd000672ffe850e00034376bfddb1e80035243fe2240670b7fb22200681f7fea5023a3ffa03b842343ce78fc65a81270f9eb50239b37a8509be421edea022f3fba68042202215fdd34820081103f78f90900025cff7f78484484ffa779a1033c7fa7b7c088081a66fbbe28123bcca4a662ff else 0x1132d9134ade35cb0066990d39c3b7dbd8d45002229d533392ae320011527f88cb0860002a346eaf80e080111ae6ffc6e423d90008acffeb3fb5ec48c00d717c1b5b02402a7f3bf9b225105101ff6f9b7510401ab1feb83942608008aeff06f9b688200d48fe151f50a00044d7e940e8824d147b8b612015366b3fe10499fbffe2be1ea2c2006b478a09bd4280011347b8b612015366b3fe10499fdc9f3a5c2e1f62801164f8760408004427f969e014006827fb3c5801030223137ff016c8058008af7c5c80c9d02500428bee93c2093381666fc0842402a8df11bd50d2409a359a47a7ff9aaaa582a8004507feb8e8108480355bff3b0c004373f36a90008699a5a186001ee753100053e3c9e400215929b5638bd314008aa23763a9888001510fe2b19558008817c1bc3cb3002200cda3060000a74737fa34e3684610022cbff2044dbefe0400d6000c74b3ba94ded54d34628613e61b280882a7d3ca102a497d0297ba0287cbc2ea102a5466e2fbba0004403f100a004366bea9d300678beb4481b2a40aa335e1f02c019e3f8e0580330a10e1920043c3fd50f4c0008720c7ed2cb0068203ecf80a165f6595dce80a201764d19230c40801160eaf8e09c100222de8cfe80a191dbc84af51051058ea9fa800d0cf9c4b5c080044e5f6fe32800053dbdb972f54800445b471e23410c17f1400d7516402a40b96beca4ea87980a4f65af11a0862a6ffc200cc37b1e4d040a69392d25cc2536be217dc00021fdff7eaa20a1b506be63f82180006fa3a502980e3a91e1a5038ea4786968b9f5814915e0fc65e003483ff88ccfd2c5081001189ea9cbc266b6949bca4e3928ac002345c99d3337220227bd295d12f001aadfc7b40718b0011557f28d20808002a19ffeb22c0600447bfcb903008637f98d6c18043b63fc5be0dc00d34f07e9f8240b001139f814220cc3c63fe63680920dfe7f8c09206997fc82e2fb43800893730b1720bc1020011659fa402c0cfefe1a38a6076b0011577170fa42b000a8a51fe33380087d7faaaa1c0043d7ff9f4dc00cf4819f7622021ebc0a1065d4557fb906821f3fd68591033e7cadcd100034e28fd9b7d0021d1f47c8288408777f57d480219dfc1f00e0021fbc7f7cd100034)))
def mo511H11 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x14563162b3501803847a72d0000000005540000000000000020a980000001457400040310001a2f4c0480000001f97fe0774a600000001850241f0000f04668d0151000160440000000000000000000000000000038080000492400000000000e002000000000000000000000000000000cd280000000021400000007c170000000347980000000290000061318a9400000000000000000000007827a11a000387e80df000000000000000a0640002c85e25e00000000c1f80009128000000030c42650000000000005134000004c5c1b406fb1c341a1c12c04c7014000000010d800000005843000000000002c7a5d249c6100f30992266000231980000000e0eb42700000000000000000000000000000000e20000000002699240001c07c0007313826c000289a493f000000000000000000141900000000d1db20ecc7f11110000000000000000000000198df0f5010f102c000682222a80000000000000000000000000071de00034890c6b3c8703740000000000163e000000000000e40800000000001848c0000000d0de0002468000000000000000000000000000000725d61f33520000782e00017060c9580000000c2b0000309700000001c380000000000000000000fe55c1b40000000f0b8a415869080dd18f3238000000000000000000000000006a4c000363400000000000000000000000c4fe0fc0000000000008900001850e4a270ee648604a2e39687e000000000001b1a3e8ca4751a7eb4700017197c33c0da1155096380380000000e04800040f0fa0c00000006095000000000000000000000000000000919a436d3220000000184dc00000000000000000000000000d9000000000000184b4d8be01500006338000002f00000000000000000000000000065d00002382c88785a0000000000000000000000000000000000000000000001d0e00000003ac70001216d8429a09720882740000000914760ac0000000f02600000002c092d100001c5e3c6742ac000000002390000c0380000000d079417c000261d0000ca94000000030f5213c000680860caa3261211c74f17ecb22b2c31320001d9668021a3a41ffc0180004892d0dc0003850825b0000000000000000000000000000000001a5180005803ba500514000000030ea000000000000000000123e80000000a3e9ea4ae26000000000000000f144000000068368c50000082b0000610400000007ec2000000000000000908400003188000000182380000000121e0000000614d0000a2a349480c0783a00004a70000000000000000000b55800000000000000000000000000000410230300032023070312810e008114000101266173019200002104914111020d130102250400100411018310133110304100411000201040034421100 else (if j<2 then 0x388600000000000009100002c4a000202cbb1ee63fcd18000502a0000000160e348d0000e29800000001066000200ee8240000000000000000000e22002f008100000002b1f80000000000211b000040ee00000000000bc7200000000000000000000000000000125324748000d0c400000000000c0f8000103c787b822e00000000000000000000000000c4c0000279428285920d45c000000000000000000000000000000000000050ae0000000000041ada03000018e492b600000000000000129a40000000b24b63dc0000000000162240000000ce3400000000000000000000000000d1ca00000000000d0e4000208fb94200000000c5f0000868bdc7f0450866418278680000000da9a000000000004100206c00000000000000000000000000000141680000000000000000000000a354000182000000002875089e000110400000000fe530218000000000000000000790db138836558900000001c40140e0000000000018230000d296e34c45a095200000002a22a8cb0001826c00000000000c540b83e9010001b9b00000000d2b4013000010ad0001880400000000000000000000000000000042480000000000199208050000c05c0000000000000035648000000000000000000000000000000000c0e200036958000024c41d0000007950e600018a50000000000000000000b1520000000612c000065640000000a11800000004840000020c041198f1a439c4240001957000000000631940029249847168000f14f61a0000000000000002e5380009470610400000000000000000000000000000000008140000000000000000000000284200000000d4640005421000000000000000000000000004c15000024b80000000c82c00000000000000000000000000000000018300000764e000149d000000000001c5c00000000000000000000001e4e180580000000000000000009e8920960870000000000000000000481ff2100000000168840b1c2c0000e0bb249c000000041e400000000000000000008148000d22800000000000000000000000000e1b960d40000000d27234e0000000000000000000546e000000000000000ba980001b2f4908f19e852000000000000000128f8000f11ee069d2d713e000009b023a800000002308000000031c3c114000394100002113c5aea5f62bc00000000000000084180000000000000000000000c01f220f4718000cd19ac8c05700000000215400000000000000000028b7000000010a7f1130001549a048800051ce83200000000c0eda51c0000000d0c6000005cb0b000016d0e80500000000000000048ba000181840000000000000000000000000000000000000000022c7452000000000000000000000000000000000000000002c81800090a40000000000000000001c9d8 else 0x525ee30c00060e8b20e0001410800000000000000000000000000000086b0001214c88ac2a761d7c573c98000081a800000000000000181400000000216c397141c000011260000d3880000000000248e70f4315fac2489e0000615600000000000d0fb82c80000000b0fe0001a8ef119914a0000000000000000002531043e00008059b3480000001a35c00000000000000000000000000000000000000000083400000000000000234500000000000252080000001f1b689ae9208230000000048bb00000000000000000000003b6080000000000000000000000000000068c5000021a400000000001046e40c8000000161aa82a601871b0e3b141ee851607d04a80002a7c0000751c000000000000001025b1168117990800030fbde110329c2578f6012c0000c8d2516e0720000c0158b350900000866493d0000000000048de00000002023800000000000000000000002485f45800000000000000000031cdc912f3150d10000))
def mo511D12 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then 0x11fd868fe4347f6163facb1fd98b3ed3d9f61ecfb4d67d86b3ebb59f696cfb0b67d75b3eb2d9f6629fb0d4fc86a7ec2d3f5969fb513fd989fed3cff61e7fb0d3fd769fed2cff6167faeb3fd659fec24ff68a7fb312fd8797ec34bf21a5faed2fd8497eb24bf6630fb0f87d86c3e4361f5db0fb5337d969bebb4df6926f92937d849beba4df5926fb4d27d8693e4349f6124fac927da64bec325f6952fb0a97d654bed421f6190fb4a87d8543eb2a1f6890fb0c77c863bec223f2a0ffb0c7fda43fec21ff590ffb4c6fd8637e431bf6a4afb4c57d762beca15f6589fb0c4fd8427ecb0df6186f90c37da71fec38ff6507fb083fd741e0cbed06a7381539c195d20d40b0694583442c1a0160cb0306184810c241860a04305066218352f40a97bc5041b2a5ddb4eeed97776d33bb695ddb2aec198760cbbb261ddc2ecea9a8720cc38a699cdb08e41977e0cabfb611f8352d69a56a0c3b7065d9534e9c1974d4d226a689353409c1a9594d42d06616b30eb6976634c32ba2195832ebc9875e0cb2fa6157d2eaba9a8520cc29065d4c2eca6985534baa9b611481498a9a9894d3c4a69225345159a8aeccc57661abb34b5d9a4aecd157661ebb2ed6d998aaccb55661aab10d54198aacc3d565daab2ed429a88e0cc46a69a3b2ed1d9758d4d1470662c933164987b2cbb5965d6cb3314d986a6c435366169b2cb4d984a60cc53661e9b2ed4c1989ecd3cf65da7c2ed3d9759f6c24f65d2783312d976960cc6165db0d14b861769acba4ca69a4db0926d74914d218a688cdb5086d86436d2a1b6150daca86da2436c221b618ed90c76d843b6b21d8618fdac87a9a6376c21bb590d83305c1962e05495a254ad12a4a9a9194d30da2546d12a3ed841fad10fe6a08f3304798723cd311e6588f30c4788623cbb11e2908f3084797423cb21002a7363502b0a8158d28ac688563402b196040d480569006b0c2348611cc306e21837b5013da609ec304f21827b44100a97a2c3bb75d9d134e995a44ccd1a67689343429a5a04c0d4c4269e2234b115a488cd1c4768a24343125a0882d446369a3234b199a38ced146868635b3165094a66bb4f35da6a2e9209a7308d2985690c334661da2310d0989680c692a581a9186d30c668c64342325a0192d41155d88c92a45574238b111c5088fffffeffbffafeffdffdefbffaff7ff7ef6ff3feffeefdffdfedfdddfdbfcffbffbfebfdbfbbf7befbdfbbfb7faff9ff6598465584641845d98461174661706497061d706197061570611705d9705d5705d1705957059170589705517050970251702197065d64655646496461d64611645d1646595461d546195461554611545d9545d55459154219546114060940591405894055140509402194065120611205d1205c120591201d120658746547464474640746187421874 else 0xa196252603014ad4762b0010070db130c9a46e53884529a5eb0866ca2ca8166c162805a8fa14b29223871ac23a2b0b4715aa5124a196d6598792c294a04cd41521831c26999a71383f09a5538cc152b84c1d1a1b8d49b22a5432328c4ad48b258914d632664793e1e0b81c18d1f197a313c5ee8b53161e2a8451f89db12de240444c880b0f661cdc36586590c0e16b429584b708b20fdc1ca8323059609440ef8177022a02ec01c7fcefe79fb53f3a7e1afb79f52be8b7ce2f929f093de07b56f5bde9b3d0979b6f2b5e403c4d782cefb1dda3b8f76c6ece5d8cbaec759aea99d3c3a5c746ce805ce539a172fce555c94b8fd717ee251c353832700adf55bd237786eaadc9db7c36cc6d3cd9d5b25b6156bdad715acbb56e6a84d469a7a34cd6948d1f5a27342167dccf0d9d0337b66aecccd987b2de6562ca2d92a3231640ac7558d7319162cec4f987f30bf610ec11580eafe55f3cbde17a4af1f5df2bb4d754ae865cc6b921712ae085bcab7056d32d775aa2b471678acd6594eb20d6352c4b582aafe55d8ab57565aac0d55d2a7f54a0a8114dea97a525aa40d459a878506aa0093de279a4eda9cdd387a6eb4d6e9a2532c26294bdc96ad2bba5364a1e9391255a46b48808ffd1dc239546ce8cd118222d245508a11127221543b086710b7213a4218836504ea06b40748014fe51f9d3ed07d00f841ecd3d307980f1b1e073baa76bcec61d5f3a647420e6e1cb1391a714ce129c0037886e10da61b2235cc6b04d4c9a6a349467f4ce5199a32fc6578c9e190e31b46294c40984a30365fa0bdc97952ec05c6cb7496ce2d4e5a04b2716272bf85760adc95972ad654f8a8894e629805210a2e1433280a4f709db139626ca4cc097e92c7253c49bc923921a23d246f48cc917922b644e088e90f9219642b0846906a208c40907fc8fda1f803e9c7c58f6f1e863c6c77b0ec81d1a39a07188e001ba036746bd8d411a4433f46680ca318d230d46010bd417322d505918af715822a7053c0a41140027384d689781280241c46f08bc111c215c41207de0f541dd43a407130dbc1aa8341864e0c3817902de058d0ab614c828384d60970125c23d045c087810581f083c707260dbc1a6833206220b8c15c829604d6091011001dc034c05b809880fe01b402b0047005c005a0003ecbedf6a73f9539fda4cfebb6bf6574fb4d97d86cbecc43f6a5ef952f7da47bec3c1f2a5dfb4eefd9777ec3bbf699dfaecefda577ecabbf661cfb0ce7ca77fecbbff61dffb2affd847feba3ff699afb40d7d8767ed42df61d6fb0cb7d875fed32ff6197faecbfda25fed02ff6a14fb0ea7d8653ebb29f6894f94d8fca4c7ed35ff696ffb497fd98bbec3ddf6a2bfb315fd86afed2d7f692bfb455fd98b7ec3dbf5dadfb3157d96abec355f21aafb3147d87a3ecb51f5da8fb3) else (if j<3 then 0x66f8b620ca6c591981586495be44d4b3fa6f024810d318e6ac20929c23408c19c3f40c41977ff3b5ca91444b6fe51ac0819effd980051b7e3fe7195420961feab0f5000000d7dffe600a4000d3a867158924cff5ea7506800261aff8668a1be17ba099d34e199c28340afd2e228fcfff5e318a0024113ebff0a12000344796dc13003415be5320ef519235f9f8804e18a718b0034475e3fd021034475cbfc01081a02fa31c91fbf581c35010354c7c758c10498fe58d74a80d1df360e0081a2bfea88197bff4c8c1240d05f0fd7d206000006c9feff8c000126e864139d5dc8c22b3f73bb00a27fa35e60d0252c62f8a6483ce738948553afa4d08ebe40251a2f232047cee7c484068ecfc12150346effdd44a122795ac10124c1ea50c090bff51a5d084049967fd9990504f327670299f03d2a809267f754cc090de5e540330fdc84234ff7f5a1441247d57f890a20948f17d8400021cbfd608504206903ff1666149fffe708802a3fe24c802a2fcfdaa103397e7ea00081a2df82421021b56f9a191c77fa19147eea1455fe2d208cdf8a1927f65a411d78f52c4044a5fe8608abfd0c1177fd818234ffc018236fa58028def96801121af3d1414578504eff0a078b038a327fd8838ae1f710067df5c9240488faa2703367850c3e00cea56a33c40f801301c3c0010b4ff22108c00222ff2f2e24e4571ffe954000cf5f8c2609801a45f0522846f963785a7201a80f9caa2abf1ea0a173db83b8c4d138e23358049afe37809a2e01aabfa64032e01a0bb79184e4034f7a3e09f00cebf5af66057e012f600851fe7ad8ba49c3e7715c680496fc1aa12267af0f384b4801a571979808f9c54244cc049f4873c801a4bed0bfdf354400d6affc52004043c6fcf409e36fe3924c00d29ffbe9254280d209ffe0dc9640699fa1e34023a74c244cabeea2e34024c7b7f1c962006984e3520d200d3b0040ff42bad1e9274743d425900348443ae12c801a657e2aa0009397e67f550004a0ff0bc5500134b7e192c570034affaca10476f97c4051003497ff5000000d0dfbe0d540000d43efd46008fdfea000001a0bff8a80002681f8a8a002477f26a020674fff4c010033afac208b9d6540658eb883201f5888ab5f9a08a6ff40204287fbc1800001a77f60442fd06980000699f9380047de482211cb7641387ea181943ffa8002067cffea0011997f51482377f6aa02067d7e801010b5fc4640ca01b7e01b785a000d6b70a3f81f002527d0a4ca11813517e41d05b08c81aa785f7818e0248e339c023ccff6abf0090dd380322bd96822a010fafcb0290021c38fad4e00cf1a4db1e3d0e2a900bd04e6a10141d0a01005801342d39144e908af0621904406104c2424498da054a1331174bf420f20e830844558c6a612261c75943a02b40b0f92a2e9f5262c1a4b4 else (if j<4 then 0x69efffb644cd10069cfdbfe92000134b7fcf680819f7f98572104993e576bb4126b800aaca0d15e3fc2c4089a13ffc22402c4b4ef23aa420933e7f119d04209710e0e29489e3a57ab8489f895ed611c57e97114b4d3e4084ce9fec6825758f088241625b70500d056f94c8df0da853357ae9aa49081a55faf1600800444cf406221226fb185520a5fc22212263f3e30412364f22e799267ff60fae93c104cddf5cc8a091bbeae664240fffdd01000025efc4f1a18120fffaee9120af7f3ce4000094be4d2c544937b88120a960f1f397049dfacc4280095df0915440d1235f3348025776bd03019ca5e2342c67183cdf9581412e7f9ccd211e7f9ccd211ef9f8bf5802b3ccf9a00156fe2f06b4241f56b1ac1611fbe68c527db68d60ac717dcb60927de49a40a77f0630574248e0f89340128fff7abd46a161f7f6dd802a1fc08608e7faec0c2813ac40147bfceb14283feec0c27cf8fd00030344fafac00c1257fe8510474ffcbe000840d118f88299977f5a14412557f890044128bfdb622336fe99116dfe1ba092abff03e4014c8fb3ebe2f1388266effc780b804004dcf6cb946d420694fff22ae9800809ae7f5b024123bf978f880109a7bfe579240101000369ff36050533f3e4800c12a7fd7c010479e681f511c387656066cfe3b11819c63f998234fc5e90469bf428831fabc11af37d04c3df0bc11a7f65a411f38043217f3c92060688f82409198bfebc80a048d1ef9640022187fe503effc05809049cbeb014478f94130fac01459faffa868241285e6d60ebff25dc012688001b77ffff18b9d4025a20c0053ef9741c8198be3fa081666f7af1d98c0022c6370478f2c00d8a06b48787c8a04cedfc6f195080168000dc5ea1f9c21b090001b6742feeb80021ac2729cfc67d0002d1b00148bfe8b92066487cfcd9d01b0224005313a3ffac036b09727eb1ab7c78970137b5e3e36b41344f895dd1e7ad8bc09d851a915277d80c2401a2bc3ce035200695c618cc048ce2a122660847d21e722680fe384e8019cbcf1c27400d0bac0a1e34927bff3f114b100348ffd41ee6fbb3404dec708f0f6826891b5b342bad1e9277b71a2db851cfe0d7a48fdb705acccb226a6f872a2666da226b20c430b64cf91f944620cdb006c4e9d3544ccdb4400dade7b53195ab81fce8967dc7f383d5c0939d3a078a80d12d11328f8043e3073d4d90da8285d30a05df91e700b3487f190a7095c1a43e16a898af200d7d972ed6ac9c00d76951a35aa43ee70108fbe02517f2aa125ace5f9cb028c01a13fc8c62a80001ae7f11c21ec0496af33d501034c7fcbc034001a2bffde3b0510034f7cec1b5b19dbcbd325d464d11e581352ccbf3b5e291404999f60fe91be801a6ba7481a7400d21fd207d15400d5e9b84920436fbc735610499cff5e127a5262b08dab6 else 0xa5d7eb68049195ff274402547e99e84d20069aeb16f70a6203577e72e6b958c1401b30a3522a4cffe81a6c880d1cfb1046414878fcb3f53801a06628df578404c5cd95d6cd500992b3a8de78b095bf3bf9acd6746a013adcd90d08a19bf9aa04b681006bdbfc8bf7ed0128bffd825bc9c8d30d5d9b8267575629b424337f762250161c01b37fd20fc7c8804b0fd9b1f5a0cf9f7d687a0d6855dfd935e04387f190a7095c1a54ff17d301203e16a898af200d6be925fd7d3404bcf8c85380f0689f03c6ae2024b3f74c4602183b5be9c2299c04d69f817455800696fe7010fa1135010368f7e2e8b189258ff8e6e5082497f0d7f980ab7e3367d0124efffe39a130412b0ae744c2b9d106f96e60240ff8e6c00908260ff9ab60624949e3d2824540)))
def mo511H12 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then 0x9bc112417f0000000089c2a4ce141c0000511800005100000022230000054bf1ef08d6e97de09a510b908d8214c03f24d140eec1af71de000000006227455e11d69225913fcc3c524930f5857e910f00000015000000000000b002d1c9210591860000f1fdc964c01f820c502a00000133b8ab9097d5ef21a4a1757146d0a85c64986ff0935de1154691b1ae1fc193257b71e300000000000064a800000000d15b00000000649d59bd000000000a330000000071b75c2ddc2600000000000070fb39dd80121e530000000082410000661f0000000000000000842559164063000000000000000000001977000000000000513b000000000000000094bb000078f60000c0e9a04d00000565f8900000a5690000011ae13200000d8000000000000089eb712291370000b05ed0cf0000a05800000ddf00007189a0d540a26d5f7117915f00000000660d6004c01ea032000000000000f12b00000000000061e200000000002e0000914ea09000005d2b719fd8e28c7800000000000001842c7b000030880000a17910cbe18c92280000f1d000000000c2303131000081f00000000050f300000000f04100000000000000000000006e8253d9e90000a46f544600000000557800005054819c00000026f12af05ab01ab124015ce031311c28ecd9e50000942af195d10a3de3a558208b804e8c9b0000dcbbc22e00000000c1aa08d5000001b00000e16360b27cfaa0e178a7823dc1340000e1c2000000000000d255795f0000e8f5c13900003c6d10e680d220a4941fd61b91cc00000915c9e600008059000000005d27515e60fd518178c470de98750000004665e6e1c3887c000060ff00000000715261edad7a000091ee000000007c0694cc6de800003473863d120b40b81cfbfc80e4a0818851dc6126a0c6004c0128100ca5ffce510000855a25cc9084000000009240e11100000000491102430000a0c9b1bb000074aab00afd0900003055d05d000000000000c0170000dc2a0000000051f9e8a521130000824e08e520adf14c125000008c700000c1a2e12e75f34505206c72000000c11440ed317b701481b47c1900000000c06dda00f21184c1c02000009cab021a00002cb30000713c0000000015fa755d00000000d09898f800000000dcdf405600000000d0f04d4f816180930008100500d04670324c482f6f0ca0c20810c500e0482c500001904204440238218000c1cd04031110228b1420c30001c60040a40030423850d400608e01c04200c0430460022002060411434830190811824460411800501c008024a0ed0c70411c40023830c50010000c70000084030000812420832ad1c24c93010c11000cb0020c804234204010700200a7060010002000011130050400401811c01400a308500f0920430400021801810801c21800110822c1 else 0xd361dfa0d340f1457a000035070000809931274176e53e000062360000655c2101f1d4c158f1ea35590000000051488212ec990000a051c5e361f4c068000060e011fb45cac103e4dd00000000000029e300008d55719131ca000000000000000000002e554582c24421572159e4c00000ca1e9447b4d9710600000000e076000000000000000004b3088504a100000000000000000000d42b60641121000000000000e0da1d5211070000e016b479262c71670000000029bc08a60000a60b00008cd27564000041adb0b3000000000000000059eae043ad20fd6bc9c00000000070e50000000000002a2ab125412dd4ba00009094d12cd08ca115f408011eb560000056221187b1a5e07c0000f5e2ec98cd72000000000000f8940000102f112000000000000000000000ad1f0000806000000000e1440000fdce8052206249179dcf0000f177000080a051ecf025500f0000000074b97008142829c1c0f600003e0d0000a1d771b800000000e16e1a55d1a980c400000000c0ba7df10000b1b64cb1000000003019e1190000000021aed1a3e0671c2c02386573000000000000d03c00000000c104a4c620f4146c61cba60ad4d500000000216b5c734029c196619900500000709c782f00ebb0b100008190b210201d68dde11b00009165e02b000062035dc600000000d9e4281e1cba000000000000f0ec00004108a8c50000f61c491a21f600009cfeae04a22aa22670fe00000000000000000000000005fc1553000001c40000713d000029ec0000124b0000724630d04567c9bf0cedc02150790000e5816c1f50e85c28d027bcaf20f809e0000081710000a04a015a25f5314bb16958bfe0d98217b164c13ea5e011e9cc794815000000000000102d514200009110990b61f100000000000090350000d0340000000010b52df2000020ef00000000dcca00000000000000005410ecc7e11d0000021f0000f1b90000b205000070d8963e0000724f00000000611f3102f1ff0000e91900000000000021940000605f000072020000000000000000721b000000000e140000101b0000f0ac000020820000d0e43440f86c00000000dcaab4b00000906facf900000000000000000000bd1448320000000024492224c0f70000c8b90000f1f8e02c00000000000050cc0000000000000000c05ca621000021d9000020c0642e0000046bc612ddd02028000039be0011f0453dda718a000000000000d8f3b138a0d67077f0a60000e24c98d00145147b0000f0b7b07eee17f58580bf80c13155513a31857140000044d371a078f702158610a21960e7142d7071710c883d000000000d6a000000000000b43d00000000000010dc0000904700005013b0369061817a0000a0a930ca907b82320000fe20954d70bea19a81c80000d1fa0000701c00000000f0) else (if j<3 then 0xfc000000000000000000000000d95480db000000000000a448ca0814c500000000c198920d38271893d033118f000000009cf061b5119b04cf0000450800fa0000c1fe000052510000a1d5d085000028bd044455f44173f18d000000009001aa1d0000b6554147c1c75c710cf200000000000055cb7220000051dd022b99ded0b6b63331295239ba09c4a20000000000000000525400000000ca1b190e00005a3f620468632d0a0000117d80d438b0004b21da000041fc714af90c0000000058eb30a3000050f900004174000000000000a4c84092a130bd679201488fadfc804fc162009e0000700b0000003b8568000000008150000000000000c0810000f4830000425681a62005b5f0cc08b08a91c0000040380000000024df6dc720cd40aa000021a8000060875149b0c50000c07dc007600e000000000000000000000000000000000000805700003614000000000000019e0000388e0000a5521e0ca1e4d9780000000061bac22c8c29d18ef09500000000f1230000000000000862000000000000000015e7485f2465000000006c1bb20650c7000012330000b86700000000000000000000704002342df70000000000000000000038e680004024acd5023b000050690000fe330000d160107300000000a94c0000ecc840dfc153323c2154280901b311db00000000000061ce808600002d82e221616630ddf1ebb2290000000000000000f91200000000de0f0000e1f70000703a0000207f2516000000009406d170000072090168a6170000c0ea4c488247215d01be7178148001e6000000006237e242153f40918245a08e74e060cea12f503021e8d1d8e55f00000000a1830000e0a1000010180000680e7816314d310dc009008fe4ec60e3506608250000b00dac4538a824ab964f4c18922f7192c8a4000021ab217e0c2e0d7b00000000d603908050b4000078610000d486aa320000000000004cf1000000000000000000000000c60e0000000060d100000000f23fe90d546e957d0000b218000009f340d70000d80a00000000fd7e000000000000e20800000000ad2d0000000014c2000020c2f5c90000f01071e500000000d2070000720e0cfd0000000000005869806a000000000000000000000000fd81b1c1306b1151000000000000f089903748df0000621e60750000009d000011f5003d603edde5b1e10000284a000071f289e21cb0c0bb5818110ea20f000021bc0000197c0000f9d9a24a123ab00300004078016af0ae30a51d69dccf000000000000c0bd156be07a11d238de6a0da8d8e2575252d873cde6123110657d6645562c49a156300601e0917cd40d000091a7000081800000097e0000000041410000bcfc0000000058ad5cffd0b00000417200000000b8db554e91c6986000000000421ce14300000000d16fc1 else 0x614fd13600000000a05300000000c19df074287d90f2ad062197a049f8f4a23e0000943fa09f0000000000000000421d00000000000000000000118200000000000014cb79c40000000040a72982104440ab20e200000000603931d11cbd000038dc81cfa0704213d216118b00000000000000004df6000000000000602270bc9235f1bd0000000011cd0042a0c820c321c511a1002360b9ea540000000041f31072716d8df8f13591bfec4691b26109080c9222016c205b0000b24df116000041e7304888840000d083b5c412480000620a0000f1ac05ee3c96a0965c4000000000495700003c950000e22d0000000010af685ec0))
def mo511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1bbd3300906bc391253ba8559c8093bce4449fde3504200973ff764482447cf8e52015cf87ca1b00252a8e76404889c38322a0b851cea004a5191d11312477246282441f5a80e024dfeae3002a1fc6e04dfb5b3002abfd5cc00547f57388293fa3f88289f8ba80004939bf20520acfcc107f8c0810492ff9ee00939ff82882a5fba408995f5204733f94627df568411ef9a2105207cfa4235fcff500015cff82c1197e9719023bff6d08145f9c40503fd78288d78784139de084d3c4288378821b840e3d5608b1ff02931fb804273fb821327e280c8bff2ff1440e9ede8587484b2fe6e57e602b34e3ea080b77eb2680049de89808d23f3c008c10ae5c066b339dcee01517c2057334c76c046a71db5ca17d7020d809338c2602387e7f1e00527fdd00146fc402297fd38267f081a7d6088f00c4758808d66f0098fb30253d9bc89b7d62d04698d6004698800a241b001a046344414745148618080958401c870659561f0b0d83174294130226c4254346928407a35a968553c24815054d54198d1623529382c3c0c1a29a059d99c098d9639379078e08bc88c86283b80f7e87cb7a477d7587347086de6ca69d67c6546386145f45d25b158f56354251b4f94d94b549747d46544e43941d3ff3e03c33a53783483182ee2c42a528125c22f20b1ec1ca19d17b15112f1130f40de0c50b609507a060042020000a65bd2ede995f4c87a61b5309a98614430a65e530f299594c24a5d25325298774c33a219d2ece98474b23a662d30f6996b4c35a21ad2ed6985b4bada596d1296984b4ba5a592d2a96992b4b15a50ad30ca88654c2aa5955308a96454aa2a60952c4a94254ca1a610d2e8687434b2156582b2a15900acbc86122b30d5976acb37615baead598acbb565d6b2e9616450aa27254cae0419602ca8264c1b2211901fffff7effbfdfeffdfebfb7deefdbf611745c1645514048074
def mo511H13 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0xbd00000000c5db4abeac7c0f314bc0000000000159900b480000000e120000000030aa00000000000eee4000000000000000000000058c9ac4f62c36843e110000b1f5e9960306272000393f80000000a2ad725b60374cc8a8e0bb80000001e224000000000000000000293326b1e2142a80000000000000000000fdf0fd8880e00000000000015beeca0000817edb4800000000000000705e000000034b6b061000120ef48a80000000001e49c000091ac00000000000b50a658ae5f0000000165d7000b4af0000899da0300000000a14576a8000059200000000000444a00000000000b5d04308311980d0001984800028ea000000026b2a065000000000006409709725e40000000000000000000000159a000108080000000488c0007a04eece00024984a1570a0b246087912c000000e11ad66b800019534e7880000001a188000272f0000083c000116cb25e00000000000d21382d385e86ea00000001ea21f48b8f7a5bc03efafd72117364000000054d20001222a8cb0000204f04fd9435c48ba9ae4cb0b80001446d406000092224498000785c101681a70acb14d78f4000000048dc00008549997b2aa00009bbc0002abaf97a0002a161895fc1bc300c9bb4c8744449cc000407bd2c34dc05ae673952e82558424f12d61e0289bf82004ff1c9cd31eaa38222ac8c5103b35a7d0265334d598b0ba02f1eb16123082a0000000207c16de000025c80000000113a02be865710b46be000203b00000000c10400056f58146785c000270372940002818a0f4a11e000000010607dc600000005066c01400000000000000122c4431e0b52059bda3cc122c63138000248c2840f268000144d0000e46885099ad8000842ecadb84c8000c6da0000000591652cfca480000ec5dad8000239a00000000000300169518c3e4dbb4815098a04a030dcb30000000000006c118a29ace35e85208000d0682b080003097a2385ad77140000620a01c508d075f0000643b090fa36702400003219c30de6639a247580005e700000000534df01c254e040aa110000000290f8000d88400006794e380000d3192b992a7000000034327cf3bddbe0a5410997a00001294000500920fc5d6c0a482e3eaa701c15bf0000a24aead0faa20b3f68000038b862c8764c000346700009a160003b67eeae0001821c0007c8211de000248800000001e00da2d4103f0de003ad000400d3c0c381000e3ba0d016880a28c800400086000008c1c245959600282000c780000001f0c340810a080000e44302220000f0004001027c4000a0402f067c602020458804254010e2518010042000a0801614042010400408001010202001830400035060120010000051a08b0100442860a2c0000204581003029e2e48b810a08b820a08080040c101000c181182c7101e001001600002 else (if j<2 then 0x2ca024041b1ad7f0d181cca4d80001c1c81ea05080001453fde8e76493d4de8cae548f80004e2042ef4953122e08a0000000000008629b198832cb6f64f40d5e48391d0e5a0003e4c7927d926dc37435e816cab60000000540400012568494d4a866c72b57c6c8000aeaa000000076fec0ff26047891883bcd80000000797ea0200000000000000016b80000343a0000000000000000000000000032380000a208cb70000b19a23cf71480000001a3e4852c0c4426b12cc9960000ac4000038af8000de6a00018b98000000079b800030d0a7038cacbb0207222480000000607821c400000003aff1505fe00b5d809b00000001d74800022096174476c250a0b7431882a224e00000000000711e045a8dc4354b128a16f88780006f0c41d1ecd40ad80007e4902000000000fe500bf0baf00000000857800000000000024f47d0000a108000000012df955a000254d0000000181f187aeb6a69a4000000040437199c118b2700000001c0fc0000451000000000000000000000000000000000000000004b42000002c80000b286d9360b80000000a1b6c35c00000000001003c83a8000000000000000000000142f80001033c1497a1983568ff88f80000e0100000000000000000004226841c0000000d1edab88000000026000000d228cd60000000154d8000a4600001340f837f1d200038790c4af1cda9dc0003625828cc3f00000000ed8f204400000000001209c000713b000151a949ff81f000043b8000000000000001c9f000000000000000688c0257f31c0007806a2b80002c2d0000f60200000000000b92805fd2a58000000000000006923a416836b4547171a51e0060000000024f182340000000f2800002c29c0b641cb406d8a7960ff154902e42b081e758979b6d157a0c0000991a81c80005d0000000000000b04c0000c568000829ce5a800050b9a07c458c050448540750b90000514cb1aa000289e0000c6e9f3a7868a08b7e0a00035446e5c329742b157670190001644800008420001891c0003183cd110068c5480003d7ec94eca400bf95798259f1586a1aadff3154b59685c30190e0565540300000000a3b010cb18e0000000502fa1fbe61035f5caba1829c3f84a5e218029a0b440a9cc9009ca55048cd04cb1f698c349762653200516042cd0f7dc955d27cc28000000000000004857ac16f5e7023cacb00000000000000012ba00000005b59d22800000006a810e6c2017510c96400000003c3a0b7560daa98b00e8000000025f391380000000000000020d800000002bc1000000004b00000632225400003415809e2eef85800005cea000004ea4988000d89e000000072e600004d38000000061a6000187f18249009e0f000000000000000089b28910000000000028280000612ac10065b711000010b45155000000031 else 0x38bd8917d53944280007ce2218a95140001120bdec000082961585046f1afc26bb020001b2100007c6c0000c39d192800091ba5bdc00018ece19f3a7c80bc24800000000c6938a694211a080000c9270d9280c4a38000d8b2698c0002405693c00000000000000000000000000a2fa00000003077d64034d4000686e00006514000683d7d2e000000000a71d90000000000000000000000000000000000276618bcf1140002323ff2e0000000204900000001e3500000000e0b18020b2d0000000000035c10000e1bc00000004254e064341c4a0e84400002380000590dba46821800000003a5003c78570000011dbd458640b2e0001557fe5f9cd5c41a0002471800081be23854a85067f))
def mo511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x130077de8039fbc033e600eb801c006281090814603858810196288e11226086c381062dc96910c48c5401845d074591545c140483ff
def mo511H14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1e1c88b000253200062370de820000051000326a0000000000c6a0008d98108001623dcd8805527a1d5d91eeb02aa47b1640924055b58de010f42c0b36020002015a8b211368e07a000a95843006d4ba8494217d7e640b107adf58400000008cc0000125525c4c0000003445281b7600064c1f17036000085000045a0000001b12c220000000001e0bb4530f30f847809a0006aeec16000bd228bc001ab1714a060000f3990ba89a14a00000048e00000000000001e62000000189c000b85118781c00000000000000000002048000c1b3143dc481bc7600018d8003865da55d60001c3200c81740c400164100000000014b96108003069fc7a24800000022a0000003c1c63fc12c12b428000000000255c000200442400072f00000024100000004c1000090b0002110e0133e0000ec245139dc8bba6fc572be122aefc00000040d0002f432136c90000000c39702f72800183a0000000000000d018000001cb2c9e107f49051cb0792a820810040472053800021551b714100100e0080440800421022cf
def mo511D15 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6102009ff
def mo511H15 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x34d008df14a24d963b090025e0007000012d9c8000000cd001c2002280015030000001c7000000144d14850
def mo511L : Nat → Packing
  | 8 => (1,7,6,0,0,0,0,mo511D8)
  | 9 => (58,6,6,3342373,102,11,1090,mo511D9)
  | 10 => (351,5,6,12714131,136,14,1333,mo511D10)
  | 11 => (600,4,6,8913049,136,15,1335,mo511D11)
  | 12 => (390,3,6,2097207,86,15,1185,mo511D12)
  | 13 => (75,2,6,720904,67,12,1087,mo511D13)
  | 14 => (8,1,6,65537,0,8,1041,mo511D14)
  | 15 => (1,0,6,0,0,0,0,mo511D15)
  | _ => emptyPacking
def mo511I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 1 2 0 4 0 0 mo511H9
  | 10 => lookupWord 18 101 5 12 6 2 mo511H10
  | 11 => lookupWord 125 1259 4 15 9 2 mo511H11
  | 12 => lookupWord 244 1567 6 16 10 2 mo511H12
  | 13 => lookupWord 179 1151 7 15 9 2 mo511H13
  | 14 => lookupWord 35 223 6 13 7 2 mo511H14
  | 15 => lookupWord 5 37 3 9 3 2 mo511H15
  | _ => fun _ => none
def mo511 : Forest := ⟨1535,15,fun i => mo511Y[i]?.getD (0,0),mo511C,mo511A,mo511L,mo511I⟩
def mo511Q : SearchRule.Regions := [
(subcube 2 0,rowMask [17,33,36,65,72,132,144,260,264,320],rowMask [13,28,56,84,112,137,168,224,304,385,416]),
(subcube 8 0,rowMask [17,18,33,36,65,130,132,144,260,320],rowMask [7,70,84,98,112,224,259,290,304,385,416]),
(subcube 1 0,rowMask [18,36,72,130,132,144,260,264,320],rowMask [14,28,42,56,70,84,98,112,168,224,290,304,416]),
(subcube 4 0,rowMask [17,18,33,65,72,130,144,264,320],rowMask [11,42,56,98,112,137,168,224,259,290,304,385,416]),
(subcube 32 0,rowMask [17,18,65,72,130,132,144,260,264,320],rowMask [15,28,70,84,137,192,259,272,385]),
(subcube 16 0,rowMask [33,36,65,72,130,132,260,264,320],rowMask [15,42,70,98,137,168,224,259,290,385,416]),
(subcube 64 0,rowMask [17,18,33,36,130,132,144,260,264],rowMask [15,28,42,56,137,168,259,290,304,385,416]),
(subcube 128 0,rowMask [17,18,33,36,65,72,260,264,320],rowMask [15,28,42,56,70,84,98,112,259,290,304]),
(subcube 256 0,rowMask [17,18,33,36,65,72,130,132,144],rowMask [15,28,42,56,70,84,98,112,137,168,224]),
(subcube 0 2,rowMask [18,35,38,67,74,130,262,266,322],rowMask [15,42,70,98,259,290]),
(subcube 0 8,rowMask [25,26,41,44,72,138,140,152,264],rowMask [15,28,42,56,137,168]),
(subcube 0 32,rowMask [33,36,50,104,162,176,296,352],rowMask [42,56,98,112,168,224,290,304,416]),
(subcube 10 0,rowMask [17,33,36,65,132,144,260,320],rowMask [5,84,112,224,304,385,416]),
(subcube 18 0,rowMask [33,36,65,72,132,260,264,320],rowMask [13,68,137,168,224,385,416]),
(subcube 33 0,rowMask [18,72,130,132,144,260,264,320],rowMask [14,28,70,84,136,192,258,272,384]),
(subcube 34 0,rowMask [17,65,72,132,144,260,264,320],rowMask [13,28,84,137,192,272,385]),
(subcube 36 0,rowMask [17,18,65,72,130,144,264,320],rowMask [11,24,66,80,137,192,259,272,385]),
(subcube 40 0,rowMask [17,18,65,130,132,144,260,320],rowMask [7,70,84,192,259,272,385]),
(subcube 72 0,rowMask [17,18,33,36,130,132,144,260],rowMask [7,20,259,290,304,385,416]),
(subcube 130 0,rowMask [17,33,36,65,72,260,264,320],rowMask [13,28,56,84,112,257,304]),
(subcube 264 0,rowMask [17,18,33,36,65,130,132,144],rowMask [7,70,84,98,112,129,224]),
(subcube 1 32,rowMask [36,50,104,162,176,296,352],rowMask [42,56,98,112,168,224,290,304,416]),
(subcube 3 0,rowMask [36,72,132,144,260,264,320],rowMask [28,56,84,112,168,224,304,416]),
(subcube 4 32,rowMask [33,50,104,162,176,296,352],rowMask [42,56,98,112,168,224,290,304,416]),
(subcube 6 0,rowMask [17,33,65,72,144,264,320],rowMask [56,112,137,168,224,304,385,416]),
(subcube 9 0,rowMask [18,36,130,132,144,260,320],rowMask [70,84,98,112,224,290,304,416]),
(subcube 12 0,rowMask [17,18,33,65,130,144,320],rowMask [98,112,224,259,290,304,385,416]),
(subcube 16 2,rowMask [35,38,67,74,130,262,266,322],rowMask [15,42,70,98,259,290]),
(subcube 17 0,rowMask [36,72,130,132,260,264,320],rowMask [14,42,70,98,168,224,290,416]),
(subcube 64 8,rowMask [25,26,41,44,138,140,152,264],rowMask [15,28,42,56,137,168]),
(subcube 65 0,rowMask [18,36,130,132,144,260,264],rowMask [14,28,42,56,168,290,304,416]),
(subcube 128 2,rowMask [18,35,38,67,74,262,266,322],rowMask [15,42,70,98,259,290]),
(subcube 132 0,rowMask [17,18,33,65,72,264,320],rowMask [11,42,56,98,112,259,290,304]),
(subcube 256 8,rowMask [25,26,41,44,72,138,140,152],rowMask [15,28,42,56,137,168]),
(subcube 260 0,rowMask [17,18,33,65,72,130,144],rowMask [11,42,56,98,112,137,168,224]),
(subcube 5 32,rowMask [50,104,162,176,296,352],rowMask [42,56,98,112,168,224,290,304,416]),
(subcube 37 0,rowMask [18,72,130,144,264,320],rowMask [10,24,66,80,136,192,258,272,384]),
(subcube 144 2,rowMask [35,38,67,74,262,266,322],rowMask [15,42,70,98,259,290]),
(subcube 320 8,rowMask [25,26,41,44,138,140,152],rowMask [15,28,42,56,137,168])]
def mo511X (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then 0x8e72c000286c0170ab2c000e48499d1774fa4fb99386e4e076c4e000d65365067d7538cd7bb17c3d365a77517499a4ee4ea67086c8f46500000000000018fb2848c14ed86000e3fd2814e08fb8f78e16732c086a3df48261491457128000000d17d95e8ca86961e8173c69500191864e869920f7787736823d000e01468399448833577b3f50367767434fa1766828f000070648b9412ce68130597000767868067d4e04e000f4e00067714059ad8637db3d96793d76730c53d00002fc48658667c65d61a0142a000f68e28d4e38f4102020200170c106e30050509770043005e00050d2f1d0100033f060700017f00433c437c015c01d81f080a2500010f701b1e176c013e03010ea93115003d010b011b01234c360101260f224ed38600770437010304030c09110426060302151401010740030256164a0f00052e090813001200080034010c03213c3a270723180c070102040040431009200a4b0f040107101105070415500f3f0229031400050104081617003b0149011066280d335a5a0e0f0a0e0614001424240019010500060026070104010420000b0105021702030b07270d6215086a231001001341411b261e9a1d0000000c4a0611012c1732020010050b0d000113081d020b04000000121c25223a19002500243403081f042f0704064802014d5415020f082e1603140308001b110a17000031001101080912142f25021c4f0102051e02040d01000a07000014030c030009060b06020a00040200030e0212021d19020004010c200303000909000d160000070b0003021601260201090a0d080005110a1200290c320001150129130d000d0008494102194a1e020b030900005609010733020b0000000202b5001a0b00343b1122000d78000001021c023b6b0009112c1b16040403050701501b0204021a0a0004070801080e3d161f1c230f010b15020302092e050005250a220206011d01040c04030216090705010a1505036c3800020925020b00000101021f62011d25330b09002f010a010f0974530601050902041e0405050002260001001e1472070c004b1f080802160601060e020509010d05043700000009030b0042180600000600352206031c0788380504000200140014060705000e21000217090005000346151a0001000f0c161102081f21010408010500090d0208130813010e001001010e1c0004014c2f091b16020e0902010000000202290722000d01120102000303010a14020406010503030d37020f990100090a0206250409000600010002000f01010017000b350c2d03150a0b020300230610080d091c010008110e1302180a0500040d052e000f0300070e02081804010c00120112000103020300060a00041201040b0f03000401031405090405030104000202170a020101041d0400010a09100306 else (if j<2 then 0xd2888f66548697776749600000004ea6828e94e000b8cb4e00000034ee4e00000074de99000f67c4e348d91a5d367371857d5794ef86159b8e08f568c4d520d67286a67484e2e014f2ce01f8ff9b792d6322af3e06524e04fe7718e499b6948eb7d371a4eb7d07742077cd8e96837194e468965c2c62876704e086d48d4ed9534f98ef77c99567e6586744ee4e299428f4e265d67b34a8e04812827796052bb0134ef66a2618fe5798f84e00068f83c000a7726026813d617000d44a7f000b9400088ed5876754f65886758ed8e88e64814e000f6884043db4e000e4eb8639444e286899f6549932278e86893d09558e00060123d165b4d04fe48000f67f4e565e4000046404e68ea77648000567000e48d2300089607d82872ca2c66777600093c377c6763e00026800016500057b24ed8f000000c2c000267f60e4e24ee86e4ec86000769b6825e69467104e16194ec7709900028f000a30299e8f000000067012460868851362000697c77177000970428b86b4f291e7889959592c268a6716844ea0100036100004e14ea4817dc8f000f3da95f8694e208065848577a4e42c34e465000f0158f939624469648a94b3fc2c82c665f48000e99a4ee17b8ec2880256700000054e886b2c00000093967d54ee8e00066c41a71874eb7796748e24e79462896716d94eb66b8648668ce8f267000000000765000215c3f98665f369f6904e000e2c23f286c86377000000000a6188f34ec68586d8fb1700013100049300000064e00047000000039784804ec6d87016648f000b8fc8675dd1a83d88ec8e92c117000e9900026600008ea08000020b7f000628f9ce58c6998f57f00000074e28e89504ef18177b67968a8e768d1894ec4ef3d34847736763d000d9124e44eb9946ff3d02c000c68877d8e194f6cf4888f22c74e668000128199296a77d8684eb5f000794740f7054a986a8636676f79999414e977b93b48b2ed8eb67f04000505c4a00023f54eb86663a94467000668067e6715e000000467000c8e15b895c01b4e84e94eb62e68267372f4e022d8f000f8e48f00098f813686867b66967000496b9100024e986000e48467428066c33d4fc48a8648e693695014f32c86b68116a6608618e000000f48000e6500023d394565337c2e67762e786f6721c00082c000356777f2c000a8f26626709668f677e01b2d766000b6800003e55334820100033444ed3ea8627d966048b4ed4f00000000086000088fd4e92eb9700076400011700000032c248440577d8f28f64886648f84e000a62c97917000031b8e577b65000f3d00024e44ee9402e878799568c4ea8f228868000000d4a00083fe6720358fd6763699900000092c19928e00022cd91f2cd01c3cb6977766800094e94ed99577c8f000069a67599000d8ec77a4bc48000b48301194f68 else 0xfd3d000d2c501686b8e94a093a67286d97000a68248b34d2ce1aa9924e000f67e0128fc6708ed4e55eb40f70c3e00071c00018608ca9649189194eb65e2c667c4e528000c86000428000000e4ef4e18f00000046800000063f496a61707f86248000065000367000000f9600036700000003639486136698e92000099af81c68496595a04b99d3fc2cb62583d8f799e2cd3f48e54fa8ee4e486a81a0be6800000032c00003d18fc40000267b68e6824e465000000000f2e477000000000b8ff6700000033e44e000899739968794e8600000088ff77c69d8600043024eb01c65a9cc48000f40f80e2100000000089a86926774e30144848fc15157c4ea48f48000000000f9400084ed6874e00048cd60a69000e67000c3db48268a65a4fe86c9108f817b8f963228000b7d17797dd2454e000d4ef9179956723d00048f28f000a48d67c8f00015300063654a82cf8626888e000f4800094e301000f4ef97b7723d000a3db8ec4eb76d25000e9634824ef8e669b66e4898ef65986a9c78f13da8fd17000b2c54b84ea1a000e4e000428786e25000a79b67448867e68000f68000000000000b3c74000000023d36700000004e84e69400098e000b6852ed8f000b6739144e04b20a43957714e94800018f848e1794e04f62ca8e00034f000201e48593b99299c4e865817b67b4888f966e3b68f00019434e00088c00000026757700000024eb8ff6700079100023400040100044e08663fa9300088682c49654033968e586840f67d6e98c98f00054e00000084eb0184e36615d46744ee68d97b69c68950b4e12ee86227948a77002f68a99d28099d8bc4e477645397c4ee4e51cd7116603c14ed2c28f399977a9bb62577968a28199b8e21c78fb2ff4e62c00094ed4e000d48e7d281d60c8fb8ed77d4fb99f67366000868c4ea1c601d8f28c199c96467a94f66c8ec39868d8e38f36586584ee67000101f2836758600074803e260c8fb7704e92404618fb9824e68e00088f000f6748608f367b33499342000b8634ef48386d8f56742ce8e965a9b18738e55ee91277f78b9968f48fe86565593f4ea4e97762c48640fc2e38f29517014e000c8f93cc6738e26690300014f58e84e00078f97da1723ea7c34e94ef6500000078888e94ec4e64e000448f8c06768e33d00000088669ab2c26523de99a4e001e6034e24807126685f294000000e97577101000000c4e00083289974898e000000a91a77669e4ec65386b8e62800056058ef68000799d8f98f000c86e67c8f248000000000667994d4a181b48f96c2e26952e60194ee2c00098e894000a4ef4ed8fc4ec66677177b94991c9c000367601d4e97d14854e000491000e4e64800037dd01000d3d00003d000000000568c28e6758600000014e068f6828608f586101665099368168467e48f670005180)) else (if j<5 then (if j<4 then 0x8f940b9958f28600000054e000000000b2848fc36000d3d86800000026703d000000000000000c77000000f8e68472666296704e34898fc8e069a3d56978fa6812c048b2900084800000054e54e00069700000094e000c8674800024e000c9500094db97c3d165000000000f3d00068e22c38f867986a95768b4ad4e000778000467b8f24e44855f00038e000000000000248e01367000a4ed4e43d53d47d00068e00044e29468ed6660674e55c000c8fa67a4e08e577b2e65a98fe6574e58f68e000000000b28e8fa3dc95000795000000d7d00024f58f25f49602c601b9600088600004e12cc95d45000c6268ff0d48f982f5df6523d24e14854e00002c84859984e677f91a6668fc6785de2ed9959c42c78e868b8f69a761a8fe6188f96869798ff86e8e62e23e76943df65a5233ec2833d44e00004e81708600000076748e291e67b4856800000018f794162000000000b4883d34e00088fc6fd7768f966317665c6899300000024ad4e370a6843f000765b6100032ca01a77000254000296e4e80e16684a286e4e160000961000e4f00074e000f8ff67601017e4849984e00000073d96532c84e286894067a8fc6817700004a88c34e25779543d00084e54e00000016829912b122a8e988368281f97873a3da6374834022c177386000e62d3fd48599077a8f62868c70b000296c8f00044e917b8ea99786958f9189499783cd65f4f26746700000056792c128d8fe8623d699186b94a28599e70b01e48f8e000f3d217997f8e165767401d4860134e43dd48e6875ed77b4e440b3cd6599792e54e33d00074ea28e48267960497d4ee8f83ae99163b48000b68b4e44e29162c000791648f8e000c2c43d848181568c8fc8f03de9928f000000000000681000a68b4e68127778600048e00029c64e00039438e78f68f24100064e596000c4ee8e720000c8cd91b4e000695f96a9993f00000000044e000e8e000e2cb4ed2c96803074e59944e08e28f51731753d000000b8e00008677d88e38e077345581000048417877a6729900065259900048f00087d000c6898f58e54e74ed6784e777f6498f000d4368f52c02c768301000528e69e2c893e8ff4084e69926852ec4835187723d00082a58e995925000548e77000e7758e217584b6500057159400000046852a00036797164e000e8e000766965c4e56608e84e465569000168d7844ee66c8f84ef2c148e99667064265000a8ff8e386d3fe0184a58c000e8e38f000a4e98e65bf3376500083de4e74ec2b268000699f4e74ea6700073d865b94000a4e00000000000086578f00000044e00012c34d291d2c499d9336800014e296b8fe11e8e66618c767000e32167a65e17c4a44e96184890a086694f67294c31b8f07782776500094e98fc86401000669d86b86786a7719400034ed4ea4ef4 else 0x6749036650b82c50176233d248000899a77000b6864e852e6524dd8f84fa4ef3d066991d6912cb86686986b4f695977a67d6898fe48c68101c8fa2845854e56538642c09438ea48868b99c4e667e94d6774832ee60986f9193ee4ec8174ed6588e767f4ee99869f6961c76236816778c66823d00033d23cd8f14f98f00000000086914ec8e791f2862c19698f52cc9461700004e000f28d0104ee4803d34ab81581d48368865e1061d90114e32cd7a68ff37e4e46840377019509388f73dd01b5a03df6599920112866979673e74e58f16602c097599d8f586566000f3ca34296e3d34e12c46722e91779655ca99000468217f2869400083e401028768000f4e84e76700039992cc6803d86888f86754e067b8f28fd9388f000000000e9100009994fa4e88f44e78fe8693de6600026703d286b66d3d08e54e000191577000a01000166a9103f000e99000594d68989000000e6800052c00000000000000096884e00087700000079453f94e999c2092c00014e31e000b65691e4e000330a67d6700000000000000000000086200016300053d348b4e000466d4e967248f67000d4e000000e2c00046800000064fc4e00022c000000b1700000054e000386d6769500012ee8666724e000f4f394c13b9584e26622cc78161d1763dd8f603f67767368a5787dc8686574ef2e068f9626298e09712cf1c099b48486c8f000a8f04e05e26888fc1c000000701d7144843d93d51323db8e48e768196f6234ab94199d48000000f9906758fc3d00000000088fd96d1900000073d44f000e65c4ec69b8f22e75e74e896165000d6856844e98fd0b68e86788f00074e18613f08416788ff61f8fc4ec2759403d000512f68667000267c7047794e18fa86f77000801d67d86009000d17000b2896786570da67d8e000c76f67f2cc5804e677548f7784e38f086499186a6503d52c92107119974ea6921338fa0171d44e99521a08f768165169e8fe8ce4800078e88f26109914ff8c59456786583e960e68000028000267d65000a86a18d3d460a3dc18d6749794c24e00061074016721bb2c000b1709687700012ca2c65a000365d71190000a8f00008616500024e000894c8e86700052c99a00067684e29924e00004eb6781f73dc2c770b0100046851659954fd6d28ff7782c517e4ee9724e16600e299f48577000000c4e000269c4ec2c38e000000e7702000034ea6016892fd7ce8e477000a2036246848fe2e688162467e2ca3fa01c4814e000928a67469362617d67499101c77f8614e85747708e14d64e24ec4888f48fb4ee23c77f9963d00000034039488e977b01000665b6658ed93d55c4834de4e14eb69000867b4ee8e00000084e00087704e000000b2c48d000067699000767000d2e76128fb9100000027716b00087da99000000b4e828000000000d96) else (if j<6 then 0x8733d8f76587627708694e000048f2e386165548a67000f62c68766c6953d000d8f48e64e000894466000b6201775828e78f34e24e16766836769655919566782093dc4e206960599c3d16527783983d51a48fa67000d8f513668000000000000048877e86000f3f06800056273300064e000000c86540000586000d4f169348c8613fb2e88f23c518a8636722893dc99c6716831800024e394000967d9603fd3df8600000022af4ef67000e4ef01000000817a99000386f0164898809157748ef8e000f8f168167000071e86e44e6518f740f6858f92889a94e14e00018ea4f63df4e796000b4e00023d667e28a69e39a6844836666818fa67000886000000586e67066000000735a67995694196b68000e8444ec47c6704e000e1800000086500053f88658fd97000f4000042ff2ff7e52ca68e81000000000793e2c59666884e36543dc8fa6821708f36762cc4eb4e340f6420139312cf8658f000a96a4f000348b86a4864ea1338fa77899456b4e267a61a6664e76898104ec39c66266458494000c4ec48a8659952800055bd3ca9918685576785a000001f8f999000b6726898a000000e5200048f686000d81b9700098f00086f394f4e467686000295d4e39400029100012cc7101764a00000049600051746563da8f44e000d68e65494386140358661381f68977000881d8f86700076a568167b99b8600000004ea8f000c6644e00016716869783ca8e48f996994d9966854ec8f786b4e067000886000d4973400006800098684e48f04ea65d6752884e00000054e768b3496783d76564854e68f22c000f2c801d2c72ec9600044e000000d8fb01d9ac6300098fd4eb9900018f06700006848ea4e90289484e00084eb4ef67a4e000596d25000381c9492c999c6100038fb70d5c00039794f00068f577c8ec67965466a2c84800042a000a7100040cb48000000000d93000000000b8f43147768e00046901736259996900024e00014fc4800078600000008ee4ed4e568b6152c686986285599561f70430968076428000b8cf4f84e94d796000101000000000000c9604848642c000862e65c8ff8fe2588f86200029900088f000b7736bc4e78e73d296648d8600092cf68b4e34ed9700061a38f601000000000967000000000000000f67268f3dd48167b8e368068000a68493a19569048528000b8f000000a65a2c29934e18e34df28d3016118e74eb2c66704e00016536500ba0176786576541739646824a000193000b4e08f00023d000096c22265722599a7794e16866708ec8676546bd5785764e56683fb86f3936746588ef67e01e4e14e54fe77a6281800037718fd8eb2cc8f05b199b0114e386467f68868b4ed67a2884e994b93627000000000396586c94386000f5e986f3ef1714e63d18e986a4e00013d48fa3d74fb8674e84e717b else 0x748601c99177a70367b3dc01b86f3dd94b06a97b2ec71217794a38000e3c886a8f581e00828e62677886000000717d99a6800053f000f9984e097086d93c6893d74e24e000991000567869000d69769b4068cc3d00038f98f071967a81563000000000f99000d9795ef4e06864ed8188f00000068fe0298f000a4ea39e68d0858f14ec6212008fa4ed8643d00032c35e52a52e567a65b69b4e46616708f000797d8f000168000c2484e00000000000054e48698ff5888f69c000e4e14e786b6206244838e24ec9466578f48656767d08ed77e77297000367b1816706948674e38f76700000000049100000020100092c38629436800000000000088f000e8ee67b7818694800046842e010000e86799601f28e48c6808156552c42804ef9126249130100056756778fc67000c4ee39469a68930067c40000000e9944e00048fc99000199b62477f8e000968848f86a2c94ec3d98ff7c65a15a44e58e469086362d8634fe65962b6568e26584869647014e40134e00002c94e693e2ce5d24ec3d88ff40b65e6188e000f4e89678f000b4e065297000d0188e96768f000f4e157399e66f8689476888cf86177f8e38f799986a65c28b9919753e29176752c94e168495a65d68c3d43ca3c248e8f868e3da9644884fb8cd09000e34000777677248c65f45177968e8118fe8636703f06559934e84e28fe4e67d086f75565f8fa3dc0153dd4ed6578172cb8f24e901000d4eb4868f000b66497094d4825704269772c194494a0200000000068200044e72244e66700039a22e777965b4356703dc79e8f668d8600001772a13dc6700000056143d328000877a0c98610358f567c59f2398f000668b67000e3df62567a84c4ed7143ee6264e33cf76f99f8600032cd8e54e00024e12c586f1842c00072c000000833e8e566366a2e43ce4a217d4e08666800000068e48f000b4f06865e00068ec9748fd94000f28000548b8e000a6306)))
def mo511Z : Array Nat := #[332320,332864,333632,348180,349972,350228,353344,370708,463392,463936,660327,676388,676404,676500,676660,680480,680807,696980,701140,856608,856672,856768,856864,857152,885920,886433,893584,898208,922400,922464,922912,942880,944560,944564,944567,959872,960384,1589568,1601856,3828405,3848917,5080737,5088897,5244180,5259584,5267744,5271872,5272852,5276948,5923684,5931828,5931892,5931895,5933524,6120288,6128496,6136368,6136624,6140784,6140793,6161684,6177088,6189376,6190356,6194452,6196180,6197568,6201600,6202644,6205760,6207648,6227220,6236035,6236291,6236595,6255892,7145089,7177857,7177889,7186049,7186065,7303510,7307606,8258836,8274240,9091765,10111669,10140341,10140357,10140373,10140389,10140405,10466634,10466730,11412884,12420737,12420833,13436545,13457025,13457041,13465217,13469313,13469329,13469345,13469409,13469425,13594902,13598998,13599190,14442625,14444673,14549778,14557472,14557632,14565696,14574016,14582546,14631232,15012544,15012928,15028244,15028880,15041264,15143456,15143616,15144000,15151122,15159316,15172240,15172336,15184624,15348802,15355924,15356452,15356564,15356708,15356724,15380692,15381188,15381204,15381236,15382996,15536672,15536832,15536992,15537216,15537248,15544338,15553168,15565456,15565552,15565984,15577840,15675410,15676482,15676498,16085635]
def mo511F (h : Nat) := ((lookupWord 817 4021 8 12 8 0 mo511X h).map fun a => MonotoneForest.corners [17,18,33,36,65,72,130,132,144,260,264,320] [15,28,42,56,70,84,98,112,137,168,224,259,290,304,385,416] (mo511Z[a.1]?.getD 0))
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo511G : graphValid mo511 (boundsBefore mo507K) = true := by decide +kernel
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo511E : ∀ c ∈ mo511Q, TestedCube.geometry mo511.mask (targetOf mo511) c.1 (TestedCube.rowsOf c.2.1) (TestedCube.rowsOf c.2.2) := MonotoneForest.regions_ok (by decide +kernel)
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo511T : MonotoneForest.Checked mo511Q mo511F mo511 := by
  intro k hk
  change k ≤ 15 at hk
  interval_cases k
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · intro i hi; exact (Nat.not_lt_zero i hi).elim
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo511Q mo511F mo511 8) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo511Q mo511F mo511 9) 0 58 4 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo511Q mo511F mo511 10) 0 351 7 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo511Q mo511F mo511 11) 0 600 7 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo511Q mo511F mo511 12) 0 390 7 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo511Q mo511F mo511 13) 0 75 4 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo511Q mo511F mo511 14) 0 8 1 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
  · have q : MonotoneForest.pieces (MonotoneForest.verify mo511Q mo511F mo511 15) 0 1 0 := by
      simp only [MonotoneForest.pieces]
      repeat' apply And.intro
      all_goals decide +kernel
    intro i hi
    exact MonotoneForest.pieces_ok q i hi
theorem mo511All : ∀ k ≤ mo511.cap, ∀ i < (mo511.levels k).1, Impossible mo511.mode (targetOf mo511) k (stateSet mo511 k i).toFinset := MonotoneForest.allImpossible mo511 (by decide) (boundsBefore mo507K) (before_sound mo507K mo507V) mo511G mo511E mo511T
set_option maxHeartbeats 0 in
set_option maxRecDepth 32768 in
theorem mo511R : Impossible false (targetOf mo511) 15 (vars 511).toFinset := MonotoneForest.fromRoot (g:=mo511) (mo511All 15 (by decide)) (idx:=0) (by decide +kernel)

end PEqualNP.Outside.L_meta_11028

theorem PEqualNP.Outside.L_meta_11028 : ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) t → 16 ≤ t := by
  apply PEqualNP.Outside.L_meta_11028.finishWhenMonotone
  exact PEqualNP.Outside.L_meta_11028.mo511R
