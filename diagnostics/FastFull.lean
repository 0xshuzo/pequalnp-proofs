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

def g146Y : Array (Bits × Bits) := #[(0x0,0x0),(0xf63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x2049204920492049204920492049204920492049204920492049204920492049204920492049204920492049204920492049204920492049),(0x0,0x0),(0x0,0x0),(0xfbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0x4092409240924092409240924092409240924092409240924092409240924092409240924092409240924092409240924092409240924092),(0x0,0x0),(0x0,0x0),(0xfdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x8124812481248124812481248124812481248124812481248124812481248124812481248124812481248124812481248124812481248124),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g146T : checkedTables g146 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g146 0 0 0 = true)
  · exact (rfl : block g146 1 0 0 = true)
  · exact (rfl : block g146 2 0 0 = true)
  · exact g146B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g146G : graphValid g146 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low146 : Lower true (varsX 146) (graphGoal 146) 4 := lower_forest (g:=g146) (i:=0) (hints:=268501056) (before_sound [] baseKnown) g146G g146T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K146 := extendKnown [] 4 [(146,[]),(328,[49,33,100,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V146 : Known true K146 := extend_ok (m:=146) baseKnown low146 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[(0xff03fffff8f71fc7ff03fffff8f71fc7ff03fffff8f71fc7ff03fffff8f71fc7ff03fffff8f71fc7ff03fffff8f71fc7ff03fffff8f71fc7,0xa285040120710490a285040120710490a285040120710490a285040120710490a285040120710490a285040120710490a28504012071049),(0xfffc07e3ff0be838fffc07e3ff0be838fffc07e3ff0be838fffc07e3ff0be838fffc07e3ff0be838fffc07e3ff0be838fffc07e3ff0be838,0x4c326089204368db4c326089204368db4c326089204368db4c326089204368db4c326089204368db4c326089204368db4c326089204368db),(0x0,0x0),(0x0,0x0),(0xfffff803ffeee63ffffff803ffeee63ffffff803ffeee63ffffff803ffeee63ffffff803ffeee63ffffff803ffeee63ffffff803ffeee63f,0x9040851240088724904085124008872490408512400887249040851240088724904085124008872490408512400887249040851240088724),(0xfffffffc00193dc0fffffffc00193dc0fffffffc00193dc0fffffffc00193dc0fffffffc00193dc0fffffffc00193dc0fffffffc00193dc0,0xe083060384982db6e083060384982db6e083060384982db6e083060384982db6e083060384982db6e083060384982db6e083060384982db6),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51T : checkedTables g51 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g51 0 0 0 = true)
  · exact (rfl : block g51 1 0 0 = true)
  · exact (rfl : block g51 2 0 0 = true)
  · exact g51B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g51G : graphValid g51 (boundsBefore K146) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := lower_forest (g:=g51) (i:=0) (hints:=68) (before_sound K146 V146) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K146 4 [(51,[]),(53,[33,84]),(83,[101]),(89,[49,33,100,84]),(101,[33,84,100]),(105,[49,33,100]),(149,[112,16,33,82,101]),(165,[32,16,84,116,100]),(177,[64,81,33,50,115,99]),(180,[32,65,49,115,99]),(209,[64,97,33,50,117]),(325,[128,16,33,100,82,117]),(337,[96,65,33,50,48,133,117]),(404,[32,65,49,115,133,99,101]),(452,[32,97,49,132,117,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V146 low51 (by decide +kernel)
def g147Y : Array (Bits × Bits) := #[(0xffc07e3e7e3f8801ff80fc7cfc7f1003ff01f8f9f8fe2007fe03f1f3f1fc400ffc07e3e7e3f8801ff80fc7cfc7f1003ff01f8f9f8fe2007,0xdb2a5148544878adb654a290a890f15b6ca945215121e2b6d9528a42a243c56db2a5148544878adb654a290a890f15b6ca945215121e2b6d),(0xf1fff803fffc4f87e3fff007fff89f0fc7ffe00ffff13e1f8fffc01fffe27c3f1fff803fffc4f87e3fff007fff89f0fc7ffe00ffff13e1f8,0x9230619080810b892460c3210102171248c1864202042e2491830c8404085c49230619080810b892460c3210102171248c1864202042e249),(0x0,0x0),(0x0,0x0),(0x7ffffffc07ffb978fffffff80fff72f1fffffff01ffee5e3ffffffe03ffdcbc7ffffffc07ffb978fffffff80fff72f1fffffff01ffee5e3f,0x2440820101000012488104020200002491020804040000492204100808000092440820101000012488104020200002491020804040000492),(0x0,0x0),(0x0,0x0),(0x81fffffff80066ff03fffffff000cdfe07ffffffe0019bfc0fffffffc00337f81fffffff80066ff03fffffff000cdfe07ffffffe0019bfc0,0x4983040206126464930608040c24c8c9260c1008184991924c18201030932324983040206126464930608040c24c8c9260c1008184991924),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147T : checkedTables g147 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g147 0 0 0 = true)
  · exact (rfl : block g147 1 0 0 = true)
  · exact (rfl : block g147 2 0 0 = true)
  · exact (rfl : block g147 3 0 0 = true)
  · exact g147B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g147G : graphValid g147 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low147 : Lower true (varsX 147) (graphGoal 147) 5 := lower_forest (g:=g147) (i:=0) (hints:=268435524) (before_sound K51 V51) g147G g147T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K147 := extendKnown K51 5 [(147,[]),(150,[32,116]),(329,[49,33,100,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V147 : Known true K147 := extend_ok (m:=147) V51 low147 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[(0xfff800ffffff001ffe03fffffff001fffffc07fe9c3590787fffc001fff001fff001fffffe003ffc07ffffffe003fffff80ffd386b20f0f,0xa0550aa0aa02a0d409468291402a0d4128148b14898251088882a81540aa1540aa1541540541a8128d052280541a82502916291304a21111),(0xffffff000fffffe00003ff80fffffe003ffff80d1bea400787fffffe000001fffffe001fffffc00007ff01fffffc007ffff01a37d4800f0,0xc4660cc8cc44c0988d8b0322644c4989b1191226c1ae242aaaa3311988cc9988cc1991988981311b160644c89893136232244d835c485555),(0xf000000000ffffffffffc0000ffffffffc0000001fa03ef8007fffffffffffe000000001ffffffffff80001ffffffff80000003f407df000,0x1782f02f01702e02e0c0bc381700e01c05e1c3819a03a99998bc05e02f01e02f05e05e02e05c05c18178702e01c0380bc38703340753333),(0x0,0x0),(0xffffffffff000000000000000fffffffffffffff331fbb007ffffffffffffffffffffffe000000000000001ffffffffffffffe663f7600ff,0x980300300980b0130102c04098090120260000032118a55554c02601300201300600601301602602058081301202404c00000642314aaaa),(0xfffffffffffffffffffffffff000000000000000cee9c6ff807fffffffffffffffffffffffffffffffffffe0000000000000019dd38dff00,0xe00400c00e00c01c00030000e00e01c0380204046498466667003801c00c01c00801801c01803800060001c01c038070040808c9308cccc),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : checkedTables g55 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g55 0 0 0 = true)
  · exact (rfl : block g55 1 0 0 = true)
  · exact (rfl : block g55 2 0 0 = true)
  · exact (rfl : block g55 3 0 0 = true)
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K147) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := lower_forest (g:=g55) (i:=0) (hints:=1348) (before_sound K147 V147) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K147 5 [(55,[]),(109,[33,49,84,100]),(167,[32,16,84,116,100]),(213,[64,33,97,49,112,80]),(217,[49,114,100,84,82]),(453,[128,16,114,49,100,82,67,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V147 low55 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[(0xfffffe001fffffffffffe001fffffffffffc01fffd6a9bfc7fffc003ffffffffffffe001fffffffffffe001fffffffffffc01fffd6a9bfc7,0x5001401400a00200001401400a002000008040080420b249002802801400a005001401400a00200001401400a002000008040080420b249),(0x7fffffe000fff007fffffe000fff007ffffe00169f6d038ffffffc001fff0007fffffe000fff007fffffe000fff007ffffe00169f6d038,0x262498898a4c42429249891894c484252490904a140f4d6db493093249824c5262498898a4c42429249891894c484252490904a140f4d6db),(0x0,0x0),(0x0,0x0),(0x7fffffffff000007fffffffff000007fffffff2b97e603ffffffffffe0000007fffffffff000007fffffffff000007fffffff2b97e603f,0x4849211210909485249212212109284a492120902b90a09249241240921490a4849211210909485249212212109284a492120902b90a0924),(0xff8000000000000007ffffffffffffff800000001369f81c0ffffffffffffffff8000000000000007ffffffffffffff800000001369f81c0,0x7071c1dc1ce0e709c71c1c41c60e308c71c2391c1329f0db6e3823831c18e0c7071c1dc1ce0e709c71c1c41c60e308c71c2391c1329f0db6),(0xfffffffffffffffff80000000000000000000000cea8c5e00fffffffffffffffffffffffffffffff80000000000000000000000cea8c5e00,0x807e01e01f00f80e07e01f81f80fc0f07e03c1e04ea8c4db6fc03c03e01f00f807e01e01f00f80e07e01f81f80fc0f07e03c1e04ea8c4db6),(0x0,0x0),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact g115B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 5 := lower_forest (g:=g115) (i:=0) (hints:=68) (before_sound K55 V55) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K55 5 [(115,[]),(117,[33,84]),(121,[49,33,100,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V55 low115 (by decide +kernel)
def g151Y : Array (Bits × Bits) := #[(0xf001ffe001ffc07ff001ff80ffc07ff003ffffe03ff4b12b0007fff000fff001ffe001ffc07ff001ff80ffc07ff003ffffe03ff4b12b0007,0xa9551551542a9542a8d4251a148b42a9aa4a8a458a64b1235b6d8aa8aa8aa9551551542a9542a8d4251a148b42a9aa4a8a458a64b1235b6d),(0x1fffffe00007ffffe0000fffffffffc00ffffc068db9401f8ffffff000001fffffe00007ffffe0000fffffffffc00ffffc068db9401f8,0xc198198198332604c098362c191204c1306c0c891340d38412490cc0cc0cc198198198332604c098362c191204c1306c0c891340d3841249),(0xfffe00000000007fffffffff00007fffffff0000000ff00e8e00fffffffffffe00000000007fffffffff00007fffffff0000000ff00e8e00,0x1e05e05e0bc381702e0b8305e1c1701c0702f0e1c0df00cb6db2f02f02f01e05e05e0bc381702e0b8305e1c1701c0702f0e1c0df00cb6db),(0x0,0x0),(0xffffffffffffff800000000000007fffffffffffff99af6d703fffffffffffffffffffffff800000000000007fffffffffffff99af6d703f,0x200600600c000180300c040602018020080300000190c082492300300300200600600c000180300c040602018020080300000190c082492),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffff800000000000006754f2ffc0ffffffffffffffffffffffffffffffffffff800000000000006754f2ffc0,0xc018018010000600c0100008000600c0300c010202200724924c00c00c00c018018010000600c0100008000600c0300c010202200724924),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151T : checkedTables g151 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g151 0 0 0 = true)
  · exact (rfl : block g151 1 0 0 = true)
  · exact (rfl : block g151 2 0 0 = true)
  · exact (rfl : block g151 3 0 0 = true)
  · exact (rfl : block g151 4 0 0 = true)
  · exact g151B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g151G : graphValid g151 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low151 : Lower true (varsX 151) (graphGoal 151) 6 := lower_forest (g:=g151) (i:=0) (hints:=268437316) (before_sound K115 V115) g151G g151T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K151 := extendKnown K115 6 [(151,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V115 low151 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[(0xffe00ffe00fffff001ff87fc3ff803fffffffe1e6b067b003e0ffff001ffc01ffc01ffffe003ff0ff87ff007fffffffc3cd60cf6007c1f,0xa4150a4150a0520a4140510089052290a4102044009046b4a5294a0a41482a1482a140a4148280a201120a45214820408801208d694a529),(0xff00000fffff007ffffe0007fffffffc00ff87ffe1a8bdc107c1f07ffffe00001ffffe00fffffc000ffffffff801ff0fffc3517b820f83e0,0x4c0984c0980c2604c0982620900260304c02104805201cc118c63184c09813098130184c0981304c412004c060980420900a403982318c63),(0x0,0x0),(0x0,0x0),(0xfffffff00000007ffffffff8003fffffff0007fffe56ec8ef801ffffffffffffe0000000fffffffff0007ffffffe000ffffcadd91df003ff,0x90120101205048090120480121048040101420900052a00421084209012024020240a0901202409002420900802028412000a54008421084),(0xffffffffffffff8000000000003ffffffffff800002793f4003e007fffffffffffffffff0000000000007ffffffffff000004f27e8007c00,0xe09c0609c060704e09c17045c2270482609804e088269394b5ad6b4e09c1380c1380c0e09c1382e08b844e0904c13009c1104d27296b5ad6),(0x0,0x0),(0xffffffffffffffffffffffffffc0000000000000019d530dffc0007fffffffffffffffffffffffffffff80000000000000033aa61bff8000,0xe0180e018080700e0180060038070380e04701108d4308c6318c700e01c0301c030100e01c03000c00700e0701c08e02211a86118c6318),(0x0,0x0)]
def g179C : List ColumnInfo := [(0,32,146,1,5),(32,0,147,0,5),(1,32,146,0,4),(2,0,177,0,4),(128,0,51,0,4)]
def g179A : List (List Nat) := [[],[113]]
def g179D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4fd5121
def g179D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x60880480e140fd41ff21fd21
def g179H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g179D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18d09f
def g179H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1100000000000ba000000084000c403000
def g179L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g179D4)
  | 5 => (3,1,3,0,0,5,0,g179D5)
  | 6 => (1,0,3,0,0,0,0,g179D6)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V151 low179 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[(0xffe00ffe007ffff801ff87fc3ff803ffffc3fffe6a3e2b0001fffff001ffc01ffc00fffff003ff0ff87ff007ffff87fffcd47c560003ff,0xa4150a41505029052140510089052290a40881040280e0b4a5294a0a41482a1482a0a0520a4280a201120a4521481102080501c1694a529),(0x0,0x0),(0xff00000fffff803ffffe0007fffffffc00fffc3fe1a9a9d107fe007ffffe00001fffff007ffffc000ffffffff801fff87fc35353a20ffc00,0x2c0582c058160b0160181620500160302c0500808521289118c63182c0580b0580b02c1602c0302c40a002c060580a01010a425122318c63),(0x0,0x0),(0xfffffff00000003ffffffff8003fffffff00003ffe57e88ef8000fffffffffffe00000007ffffffff0007ffffffe00007ffcafd11df0001f,0xb016030160582c0580a0580161058040301611050053a084318c630b01602c0602c0b0580b0140b002c20b0080602c220a00a741086318c6),(0xffffffffffffffc000000000003fffffffffffc0002697f4003ff07fffffffffffffffff8000000000007fffffffffff80004d2fe8007fe0,0xc09804098060302604c16045822604824098002608069164a5294a4c098130081300c0604c0982c08b044c09048130004c100d22c94a5294),(0x0,0x0),(0xffffffffffffffffffffffffffc0000000000000019d530dffc0007fffffffffffffffffffffffffffff80000000000000033aa61bff8000,0xe0180e01804038070180060038070380e02238108c5308c6318c700e01c0301c030080700e03000c00700e0701c044702118a6118c6318),(0x0,0x0)]
def g181C : List ColumnInfo := [(1,0,180,0,4),(4,0,177,0,4),(16,0,165,0,4),(32,0,149,0,4),(128,0,53,0,4)]
def g181A : List (List Nat) := [[],[114,84],[32,116],[32,64,80,112],[64,117],[64,82,112,32],[80,66],[80,114,64,66],[112,32,66,84],[112,82]]
def g181D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g181D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g181H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3
def g181D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g181H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x73009baace27000000d01200b5000016b1
def g181L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g181D4)
  | 5 => (2,1,3,0,0,4,0,g181D5)
  | 6 => (1,0,3,0,0,0,0,g181D6)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : checkedTables g181 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g181 0 0 0 = true)
  · exact (rfl : block g181 1 0 0 = true)
  · exact (rfl : block g181 2 0 0 = true)
  · exact (rfl : block g181 3 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V179 low181 (by decide +kernel)
def g218Y : Array (Bits × Bits) := #[(0x0,0x0),(0xf003ffc00fffffc00fff0ffffffc00fffff0fffeea3a5303f03ffff000fff003ffc00fffffc00fff0ffffffc00fffff0fffeea3a5303f03f,0xa2282288a0282284a08a210802284a0280220882200a5314514508a08a08a2282288a0282284a08a210802284a0280220882200a53145145),(0x0,0x0),(0x3fffff003fffff0000ffc3fffff003fffffc009adfd000fc0ffffff000003fffff003fffff0000ffc3fffff003fffffc009adfd000fc0,0xc8b10b02c8b10b00c42c405090b10c4b11404108092d994d34d342c42c42c8b10b02c8b10b00c42c405090b10c4b11404108092d994d34d3),(0xfffc00000003fffffffff0003fffffffc000fffd77e88afc003ffffffffffffc00000003fffffffff0003fffffffc000fffd77e88afc003f,0xc04c1302c04c090130026104c0100c0584120152a08828a28a1301301300c04c1302c04c090130026104c0100c0584120152a08828a28a),(0x0,0x0),(0xfffffffffffc0000000000003fffffffffff00012697f4000fc0fffffffffffffffffffc0000000000003fffffffffff00012697f4000fc0,0x302701c0302702e09c08b822702609026009c11269264b2cb2c9c09c09c0302701c0302702e09c08b822702609026009c11269264b2cb2c),(0xffffffffffffffffffffffffc0000000000000039d530dfff000ffffffffffffffffffffffffffffffffc0000000000000039d530dfff000,0xc0380200c0380300e000c00380380e03808e0208d5104c30c30e00e00e00c0380200c0380300e000c00380380e03808e0208d5104c30c30),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218T : checkedTables g218 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g218 0 0 0 = true)
  · exact (rfl : block g218 1 0 0 = true)
  · exact (rfl : block g218 2 0 0 = true)
  · exact (rfl : block g218 3 0 0 = true)
  · exact (rfl : block g218 4 0 0 = true)
  · exact g218B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g218G : graphValid g218 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low218 : Lower true (varsX 218) (graphGoal 218) 6 := lower_forest (g:=g218) (i:=0) (hints:=318857280) (before_sound K181 V181) g218G g218T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K218 := extendKnown K181 6 [(218,[]),(346,[49,100,135]),(410,[134]),(458,[49,100,84,117,133]),(466,[99,83,133]),(472,[49,33,66,98,82,117,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V218 : Known true K218 := extend_ok (m:=218) V181 low218 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[(0xfffffc00000fffffc00003fffff00000ffffffffffc00003ffffe0003fffffffffffffc00003fffffffffe0003fff97e43a62aa9edf07c1f,0x2a8000aa0002a8002a8000aa000aa000550000a8001a80009400680014800a0000a8001a800128000a4005800a05c00862081c0108421),(0xfffffffffff00000000003ffffffffff000007fffffffffc000000003ffffc0007fffffffffc00003ffffffffc0000b5fc47c9174a0003e0,0x452331148cc45233115331148cc450cc4546622913114131148d824b11419049322913114931149b1148c824904930b4e846c8154ab5ad6b),(0xfffffffffffffffffffffc0000000000000007ffffffffffffffffffc000000007ffffffffffffffc000000000000676bada15c4320f8000,0x160bc0582f0160bc0583c0582f0162f0161780b05c0585c0582e042c0585e085c0b05c0581c0581c0582f041e083c27692ca058432739ce7),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffff80000000000000000000000000007fffffffffffffffffffffffffffe819707c5fea40003ff,0x984c0261300984c02604026130098300981804c260261602613008b02616011604c260261202612026130089011206011701056a254a5294),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000006456978fe62520ffc00,0xe0700381c00e070038180381c00e0400e06007038038180381c010c038180218070380381c0381c0381c010e021c04016930da62018c6318),(0x33aa5b8895b2bf00000,0xff8003fe000ff8003fe003fe000ff800ff8007fc003fe003fe001f003fe003e007fc003fe003fe003fe001f003e00322a538895a2bef7bde),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(2,0,117,0,5),(4,0,115,0,5),(64,0,55,0,5),(16,2,101,0,4),(32,4,83,0,4)]
def g119A : List (List Nat) := [[],[33,84]]
def g119D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x17e50
def g119D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x222317f
def g119H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g119L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g119D5)
  | 6 => (1,0,3,0,0,0,0,g119D6)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : checkedTables g119 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g119 0 0 0 = true)
  · exact (rfl : block g119 1 0 0 = true)
  · exact (rfl : block g119 2 0 0 = true)
  · exact (rfl : block g119 3 0 0 = true)
  · exact (rfl : block g119 4 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V218 low119 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[(0xfffe01fffc0007ffe01fff807fff80007fff8001fffe0007ffffffe0007fff00fffffffff8001fffffff00ff1d203397a2ac000003f03f,0xaa01545480a90350094340290b2055205520552154815485520aa4054835204a1a41485101520d4825205216141d002390a2a91451451451),(0xff000001fffffff800001fffffffffffff80000001fffffff8000fffffff800000fffc03ffffffe0007fffff00637e8b807608003f000fc0,0xcc119898113022608d858232120466046604660998119806608cc0898026046c2c0190982260498136046424262336098066085145145145),(0x1ffffffffffffe000007ffffffffffffffe00000000000fffffffffffff000003ffffffffff800000009d8e48e9a5400fc0fc0000,0xf005e0e005c00b802e0600bc1c01780178017801e005e017802f002e00b801703005e0e00b800e003801783838150a48c1a54030c30c30c3),(0x0,0x0),(0xfffffffe0000000000000000007ffffffffffffffffffffffffff0000000000000000003ffffffffffffffffffa049c585ccf7f000000fff,0x26000026004c01300804c02009800980098002002600180030013002c00980401601004c00900240098000008048c0050854a28a28a28a),(0x7ffffffffffffffffffffffffffffffffffffffffffffc0000000000000000009175383e5b400000fff000,0xb8010138027005c0101700404e004e004e004c0138012004c009c013004e00009800027004e013804e0040408075102e5802cb2cb2cb2c),(0x0,0x0),(0xffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000004e937660389bffff000000,0xc00001c003800600001800007000700070007001c001c007000e001c00700080e002038007001c00700080804881362010830c30c30c30),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(2,0,181,0,7),(4,0,179,0,7),(0,32,146,5,6),(32,0,151,0,6),(16,0,167,0,5),(128,0,55,0,5)]
def g183A : List (List Nat) := [[],[32,116]]
def g183D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4f77159653
def g183D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x10420806284506c85b2c0bf59653fdd8553bdd8553bd58453be58053
def g183H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa0
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x190e2a5474365a891d90ea6147888807f94ffaa7fc53
def g183H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x730000000000000000000000280000000000000000000064001100000070000000000000000052000000000000000000000000
def g183D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def g183H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c03969000000000000000000000
def g183L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g183D5)
  | 6 => (5,2,3,0,0,6,0,g183D6)
  | 7 => (3,1,3,0,0,7,0,g183D7)
  | 8 => (1,0,3,0,0,0,0,g183D8)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g183 0 0 0 = true)
  · exact (rfl : block g183 1 0 0 = true)
  · exact (rfl : block g183 2 0 0 = true)
  · exact (rfl : block g183 3 0 0 = true)
  · exact (rfl : block g183 4 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V119 low183 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[(0x1ffff80001ffff000ffff8007ffff00007ffffffffc0001ffffffffffffffffffffffffc0001ffffffffc003ffd524a373e833c0007c1f,0x548015200d4004a01a002900b200aa405520154802a901548055200a900948052014400a900d4804a40148058051520013288339294a529),(0x1ffffffffe0000000ffffffffffffffff80001ffffffffe00007fffc0001ffff000ffffffffe0000fffffffc003ed51a38816c800f83e0,0x4980a2602898146c22c0a32112028cc0466051980a330219814660113018d808641260513014980a6c0519049049be541230016086318c63),(0x1ffffffffffffffff00000007ffffffffffffe00000000000007fffffffe0000000fffffffffffff0000000000073b22915bd881f00000,0x9e02cb80b2e059704b02cbc25c0b2f00978065e02cbc075e039780a5c052e02d782b8165c058e02c70165e09e09e063922115bd88e739ce7),(0x0,0x0),(0xffe000000000000000000000007ffffffffffffffffffffffffff8000000000000000fffffffffffffffffffffffc859e43c4e4f7e0003ff,0x10030c00c30061808c030c04600c30011800860030c00460021800c600630031804c0186006100308018601101100009e00c420c48421084),(0x0,0x0),(0x7ffffffffffffffffffffffffffffffffffffffffff0000000000000000000000004569b47773c00007c00,0xe013f004fc017e00f00bf007804fc009e004f8013f00278013e004f8027c013e007009f8027e013f009f801e01e000569a45770c2d6b5ad6),(0xffffffffffffffffffffffffff80000000000000000000000000000000000000000000000000000000000000000033aa5dc49781bfff8000,0x1c000700018000000c00000070000e00070001c00038001c000700038001c000800e00038001c000e00020020001820dc08401318c6318),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : checkedTables g215 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g215 0 0 0 = true)
  · exact (rfl : block g215 1 0 0 = true)
  · exact (rfl : block g215 2 0 0 = true)
  · exact (rfl : block g215 3 0 0 = true)
  · exact (rfl : block g215 4 0 0 = true)
  · exact (rfl : block g215 5 0 0 = true)
  · exact (rfl : block g215 6 0 0 = true)
  · exact g215B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 8 := lower_forest (g:=g215) (i:=0) (hints:=268437316) (before_sound K183 V183) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K183 8 [(215,[]),(407,[32,116,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V183 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[(0xe007fff80007fff801ffff80001ffff80007fffe0001ffffffff80007fffc00ffffffffffe0001ffffffff003ff1d10d5daa29900003f03f,0x49510153035202922ca05528154a055285528154a154a0aa50152835281291a50524514054a0d4a094a052459141d0015da2288451451451),(0x7ffffffffffffffffffffffe000000007fffffffe0000ffffffff8000000ffff003fffffffe0001ffffffc006fd62ae3438003f000fc0,0x8260226022602320480466011980466026601198019808cc02260026011b02c00640980898049804d804640902627122ac30180145145145),(0x0,0x0),(0x7fffffff8000001fffffffffffffffff8000000000000fffffffffffffff0000003fffffffffffe0000000009dae8e542564000fc0000,0x13820b820b830bc470c178305e0c1783078305e0c5e0c2f060b830b8305c23061788e182e0c0e0c0e0c1788e2381dac8e5021644d34d34d3),(0xfff800000000000001ffffffffffffffffffffffffffffff0000000000000000000003fffffffffffffffffffffa06594e1393ffc0000fff,0x4c004c004c008009800260009800080026000600030004c002c00260040058010013000900090009800000080448020103728a28a28a),(0x0,0x0),(0x1fffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000000000000915a691ddcf0000fff000,0x404700470047001010e00438010e0043004380108010c0087004300438000086000021c010e010e010e001004080526005dc10b2cb2cb2c),(0xfffffffffffffffffe00000000000000000000000000000000000000000000000000000000000000000000000004ea977125e06fff000000,0x180780078007800601f0007c001f0007c007c001f001f000f8007c007c00380f800e03e001f001f001f000e038048a955104e00c30c30c30),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact (rfl : block g219 5 0 0 = true)
  · exact (rfl : block g219 6 0 0 = true)
  · exact g219B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 8 := lower_forest (g:=g219) (i:=0) (hints:=268460100) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 8 [(219,[]),(347,[49,100,135]),(467,[131,83]),(470,[32,99,116,83,133]),(473,[49,33,114,100,82,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[(0x7ffff00001ffffc000fffff80000fffff80000fffffffffffffff00001ffffe0007fffffffffffffffffffffffff9961a4fab95940003ff,0x51002a600d48014901650055280aa50055280aa500aa500aa5002a500d4a009480d28052405140152804a500a480a1921244a9119094a529),(0x0,0x0),(0x7fffffffffffffffffffffffffff0000000000fffff00000fffffffffe000000007ffff0003ffff80000ffffe0005df06f136450a0f8000,0x60554c0aa98155904a405566012cc05566036cc02acc06acc0554c04a980aad8156025640a9814a602b6c054c81335c70671364408739ce7),(0x7ffffffffe00000000ffffffffffffffffffff0000000000ffffffffffffffffff800000003fffffffff00000000053e3e4d5a478007c00,0x82067040ce0c19e213860678304f060678304f060cf060cf06067060ce0c0ce10983067884e1813830270606f105c013a2e491a478b5ad6b),(0xf800000000000000000ffffffffffffffffffffffffffffff000000000000000000000000003fffffffffffffffffaa58e2545fea5f0001f,0x67800cf0019e009c00678002700067800270004f0004f000678006f000cf002e003780170019c003380067002600250c2144e6246318c6),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000245795afe6252007fe0,0x478008f0011e000e0087800438008780043800870008700087800870010f0003004380018021e0043c0087800380244491a4642034a5294),(0xfffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000073aa5b8895b2bff8000,0x78000f0001e0003000f80007c000f80007c000f8000f8000f8000f8001f0001c007c000e003e0007c000f8001c00218a1888919038c6318),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact (rfl : block g221 5 0 0 = true)
  · exact g221B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 7 := lower_forest (g:=g221) (i:=0) (hints:=536897284) (before_sound K219 V219) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K219 7 [(221,[]),(237,[80,50,114,64,98]),(343,[96,49,33,64,132,116]),(455,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3ffffc00007fffffffff0007fffffffe00003ffffe00003fffffffffffffe00003ffff8003fffffffffffffffff99c559a751938003f03f,0xa8140a828350504a0505220b105014154142a814154142a81055040aa020540c1a81025086814150284a050a421498055087411305145145),(0x3fffffffff80000ffffffff8003fffffffffc0000000003ffff80000fffffffffc00000003ffff80000ffffe00036ad462289af40fc0000,0x3059530b2a61656c1656445222985959818b305959839b3025660eacc14a98295305ab612b058a60b36c164c846632ad4622898f0f3cf3cf),(0x3ffffffffffffff000000000003fffffffffffffffffffc000000000fffffffffffffffffffffffffff00000000067a74def58a00000fc0,0xc1019c00338006704067809c04e1019e0813c1019e0813c1067820cf040ce0819c1033804c1013820270406f00b806727484358a134d34d3),(0xfc00000000000000000000000003fffffffffffffffffffffffffffff000000000000000003fffffffffffffffff58b1cca8bed4bf00003f,0x61e00c3c018780187808e0470061e0021c0061e0021c00478008f0018f0031e0063c0270061c00c380187008c000b00c289ec48a28a28a),(0x0,0x0),(0x3ffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000048af2b5fcc4a40000fc0,0x27e002fc005f8009f800f0078027e0013e0027e0013e00278004f0009f0013e0027c0038027e004fc009f800f00488d0b5bc8406cb2cb2c),(0xfffffffffffffffffffffffffffc0000000000000000000000000000000000000000000000000000000000000000e754b7112b657ffff000,0x380003000060000e0000000000380001c000380001c0003800070000e0001c000380004003800070000e00010004540a110202070c30c30),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222T : checkedTables g222 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g222 0 0 0 = true)
  · exact (rfl : block g222 1 0 0 = true)
  · exact (rfl : block g222 2 0 0 = true)
  · exact (rfl : block g222 3 0 0 = true)
  · exact (rfl : block g222 4 0 0 = true)
  · exact (rfl : block g222 5 0 0 = true)
  · exact g222B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g222G : graphValid g222 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low222 : Lower true (varsX 222) (graphGoal 222) 7 := lower_forest (g:=g222) (i:=0) (hints:=318859072) (before_sound K221 V221) g222G g222T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K222 := extendKnown K221 7 [(222,[]),(411,[32,116,134]),(459,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[(0xfffc0003fffffc00000ffffff000003ffffffffffffffffe000007fffff0000ffffffffffffffffffffffffffffff36d7f4aa09de8000fff,0x14840582802a8280aa0a00aa0a02a8280550500aa0a00541403505004a101a0a014840502802a0a01282805210143646c0a809880249249),(0xfffffffffffffffffff000000000003fffff800000fffffffffff8000000000fffffc0003fffff000003fffff0000fbe04ebf62231fc0000,0x5590129002ab30012cc00aacc00db3001566006acc00aa98012a600556c02ac0095900a980294c00adb002a640266f8e0463e400311c71c7),(0x0,0x0),(0x3ffffffffffffffffffffffc00000000000fffffffffffffffffffff0000000003ffffffffffc0000000000a7c4359bd0f703f000,0x19e084e0b033c0b04f02c0cf02c13c0b0678160cf02c0ce05833816067021302c19e084e0b02702c09c0b037820b802744119ad0f36db6db),(0x0,0x0),(0x3ffffffffffffffffffffffffffffffffff0000000000000000000000000000003ffffffffffffffffffff54b1674157ff000003f,0x9e012702c33c02c2700b0cf00b09c02c2780584f00b0cf0161bc058678045c0b0de011702c3380b0ce02c338044c040b1274156770db6db6),(0x3ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000000048afbb7e9c20e03ffc0,0xe002380303c00303800c0f000c0e00303800607000c0f00181c006078008600c0e002180303c00c0f00303c00870048893a461020c924924),(0xfffffffc0000000000000000000000000000000000000000000000000000000000000000000000000000000000000e754a985f269dfc0000,0x3c003fc0003fc000ff0000ff0003fc0007f8000ff0001fe0007f8000f800ff0003e003fc000ff0003fc000f8000714a981b268ce38e38),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact g235B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K222) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 6 := lower_forest (g:=g235) (i:=0) (hints:=268460149) (before_sound K222 V222) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K222 6 [(235,[]),(238,[32,49,118]),(252,[32,49,65,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V222 low235 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[(0x7fffe001ffff000ffffe0000ffffffffffffffffff80003ffffffffffffffff00007fffffffffffffffc003ffd76f2131c876400ffc1f,0x500014004000200210014200a10028400a10028400508028400a10010000800a100508014200200010008008001128002088721294a529),(0xfff80000001ffffffffffffffff00003ffff00003ffffffffc0000ffff8007ffffffff80001ffff000fffffffc003891d26fa15c81f003e0,0x92602498128092409002498024c04930024c029300926011300a4c02120290124c024601298048404a0249012012b8110263015486318c63),(0x0,0x0),(0x0,0x0),(0xffffffffffe0000000fffffffffffffc000000003fffffffffffff00000007ffffffffffffe0000000ffffffffffcc308eba768b7e0003ff,0x24804920240124812404920049001240149005240124802240109004a4052024900488024200928094049202402404008c18648848421084),(0xffffffffffffffffffffffc000000000000000000007ffffffffffffffffffff0000000000035364166f4d80007c00,0xc70571c0c715c70638a71c148e0a638298e0a63829c7053b829ce0a73829c538e0a710538c14e30518a71c14714702536416670dad6b5ad6),(0xfffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000045e9b45573c000f8000,0xf8067e017819f80bc0c7e018f00c7c031f00c7c031f8063c031f00c7c04e063f00c7e063f018fc09e0c7e027827804569b45570c2d6b5ad6),(0xffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000033aa5dc49781bff00000,0x78001801e000c00f8001f000f8003e000f8003e0007c003e000f8007007c000f8007c001f000e00f80038038003aa51849201318c6318),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact (rfl : block g243 5 0 0 = true)
  · exact (rfl : block g243 6 0 0 = true)
  · exact g243B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 8 := lower_forest (g:=g243) (i:=0) (hints:=268435524) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 8 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[(0x7fffe001ffff000ffffe0000fffffffff80003fffffffffffffffffffffffff00007ffffffff8007fffffffffde2d8339c932c00f83ff,0x500014004000200210014200a10028400508028400a10028400a10010000800a100508014200100100008008001a29002080321294a529),(0x0,0x0),(0xfff80000001ffffffffffffffff00003ffffffffc0000ffffc0000ffff8007ffffffff80001fffffff8007fffc0039d3724fa05c01f07c00,0x28601458118051408801458022c028b00516010b00a2c008b0062c010a02500a2c014600a58028a02402500a1011b953224b001006318c63),(0x0,0x0),(0xffffffffffe0000000fffffffffffffc0000000000000fffffffff00000007ffffffffffffe00000000007ffffffcd320e9a768b7e00001f,0xb2805960250165812c0596004b0032c0165803ac01cb0052c014b005ac05602cb0058802c600b2c04e04e02ca02505120e1a64884c6318c6),(0xfffffffffffffffffffffffffff00000000000000007fffffffffffffffffffffff80000000251e4366f4d80007fe0,0xc3056180c615860630a618148c0a430298605230290c0a630298c0a630298530c0a610530814c30288288530c1460000c4146f4da94a5294),(0xfffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000000045e9b45573c000f8000,0xfc067e017819f80bc0c7e018f00c7c031f8063c031f00c7c031f00c7c04e063f00c7e063f018fc04f04f063f027804569b45570c2d6b5ad6),(0xffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000000000000033aa5dc49781bff00000,0x78001801e000c00f8001f000f8003e0007c003e000f8003e000f8007007c000f8007c001f0007007007c0038002a851849301b18c6318),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : checkedTables g245 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g245 0 0 0 = true)
  · exact (rfl : block g245 1 0 0 = true)
  · exact (rfl : block g245 2 0 0 = true)
  · exact (rfl : block g245 3 0 0 = true)
  · exact (rfl : block g245 4 0 0 = true)
  · exact (rfl : block g245 5 0 0 = true)
  · exact (rfl : block g245 6 0 0 = true)
  · exact g245B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 8 := lower_forest (g:=g245) (i:=0) (hints:=536872196) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 8 [(245,[]),(373,[100,135]),(437,[32,116,134]),(485,[32,132,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g469Y : Array (Bits × Bits) := #[(0xfffc0003fffffffc007fffe0000ffffc0003ffff0000ffffffffc0001ffff001fffe003fffffffffffffffffffffcc65acb88be2400003ff,0x202a902a202a10098149015240a9202a502a480a940a900a9202a4815200a5052004a0a4815240a92025012404a00c04aca083a22318c631),(0x0,0x0),(0xfffffffc0003fffffffffffffff000000003ffffffff0000ffffffffe0000001ffffffffffe0000ffff001fffe003b843a5ae0e501f07c00,0xab005300ab00550140055800ac00ab006b002ac012c02ac00ab0029802ac05802a80a0015801ac0094034014805a980225a806506318c63),(0x0,0x0),(0xfffffffffffc0000007ffffffffffffffffc000000000000fffffffffffffffe0000003ffffffff0000001ffffffef3b03d9111a400f801f,0xcc006400cc086602610660413020cc084c0833021b0233020cc08320433009043301308260413020d805841900923390358101054a5294a),(0x0,0x0),(0x7fffffffffffffffffffffffffffff00000000000000000000003ffffffffffffffe0000002059e5744e4dbe0003e0,0x4f0027804f002780380278009c004f00070013c001c003c004f0013c00bc00e00bc01c0138009c004e006009e00e20590054484d8c6318c6),(0x7fffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000000024569a07773c000ffc00,0x7003380370033802c0638018e00c700318031c00c600c400c70031c018c009018c012031c018e00c7009818e0130044698056708294a5294),(0xffffffffffffffffff8000000000000000000000000000000000000000000000000000000000000000000000000013aa5dc49781bff00000,0x8003c0038003c003007c001f000f8003e003e000f800f800f8003e001f000e01f001c03e001f000f800e01f001c012225d801780318c6318)]
def g469C : List ColumnInfo := [(16,0,453,0,5),(17,0,452,0,4),(65,0,404,0,4),(132,0,337,0,4),(144,0,325,0,4),(260,0,209,0,4),(320,0,149,0,4)]
def g469A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118],[64,130,118],[64,130,112,96,98],[96,114,64,132,66],[96,114,132],[112,98,66,128],[112,98],[128,66],[128,66,98,112]]
def g469D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xbbd8940
def g469D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40c3fa81fd10
def g469H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa0
def g469D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2c5991bf
def g469H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c81000312a10053001e35280001e70000362002
def g469L : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,g469D5)
  | 6 => (2,1,3,0,0,3,0,g469D6)
  | 7 => (1,0,3,0,0,0,0,g469D7)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g469T : checkedTables g469 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g469 0 0 0 = true)
  · exact (rfl : block g469 1 0 0 = true)
  · exact (rfl : block g469 2 0 0 = true)
  · exact (rfl : block g469 3 0 0 = true)
  · exact (rfl : block g469 4 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V469 : Known true K469 := extend_ok (m:=469) V245 low469 (by decide +kernel)
def g474Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fff07fff8001ffffffe0ffff0000ffff0003fffc000fffffffc000ffff07ffffffff0003ffffffc1ffffc92d389940f740000007fc01ff,0x2800a11045209404500842208a208a208a2228822888a2028822884a208a110840208a212880a2008441100829308000f708a45229148a45),(0x0,0x0),(0xfc00007ffffffe0007ffffffffffff00000003fffffff0003fffffff000007ffe0fffffffc000ffffffff81a52a0abb8d8801ff00003fe00,0xb022c20216041821604280042c042c042c08b010b002c08b010b000c042c200282042c043012c0450008209a50a02b1090026130984c2613),(0x7ffffffffff80000fffffffffffffffc00000000003ffffffffffff80000fffffffffff00001ffffefe1835e2102c0000ff80001ff,0xc10b04209801200982130441304130413040c104c113042c104c10904130021304413040410304160882402700815a2100d148a45229148a),(0x0,0x0),(0xffffff8000000000000000ffffffffffffffffffffffffffc00000000000000000fffffffffffffffe0000209965726e4d3fe0000003fe00,0x4c0004e009c04e009c0809c009c009c0030027001c0030027002e009c0405c0809c00980240098001381208141106c4d0582c160b0582c),(0xffffffffffffffffffffffffffffffffffffffffffff0000000000000000000024d69a05573c00000ffffc0000,0x2700847004e017004e0108e008e008e008c0238022008c0238023008e000460008e008e023808e0111c0200d60a05560826130984c26130),(0xffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000132a5dc49781bffff000000000,0x380007800700180070000f000f000f000f003c003c00f003c003c00f000878010f000f003c00f0021e004012a1cc48300b81c0e070381c0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g474T : checkedTables g474 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g474 0 0 0 = true)
  · exact (rfl : block g474 1 0 0 = true)
  · exact (rfl : block g474 2 0 0 = true)
  · exact (rfl : block g474 3 0 0 = true)
  · exact (rfl : block g474 4 0 0 = true)
  · exact (rfl : block g474 5 0 0 = true)
  · exact (rfl : block g474 6 0 0 = true)
  · exact (rfl : block g474 7 0 0 = true)
  · exact g474B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g474G : graphValid g474 (boundsBefore K469) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low474 : Lower true (varsX 474) (graphGoal 474) 9 := lower_forest (g:=g474) (i:=0) (hints:=13203759168) (before_sound K469 V469) g474G g474T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K474 := extendKnown K469 9 [(474,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V474 : Known true K474 := extend_ok (m:=474) V469 low474 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[(0xfffffffffffff800000003ffffffffffffffff800000003ffffffffffffffff8000003fffffee4844e9d22197ea01eb81e4500ff00ff00ff,0x955400002955000015aa80000a95400002a950000155a80000aa9400002aa90005558002aa840044a8502181c800e981a00010101010101),(0x1ffffffffffffffffc00000001ffffffffffffffffc00000001ffffffffffffffc000000ab697b034497848c7c13b9ab00000000ff00,0xd9988a283266228a193311450cd988a283326228a199311450ccd88a2833320889990444cccab696a030493048c7c12b889555555555555),(0xffffe0000000000000000000000001ffffffffffffffffffffffffe000000000000000000001527eba158933917d287a461a0000ff000000,0x2e1e02c02bc780b00de3c05806f1e02c02bc380b009e1c05804f0e02c02bc3c101e1e080f0f0507cba15801391352878461a333333333333),(0xfffffffffffffffffffffffffffffe00000000000000000000000000000000000000000000013b9df8e218d25092a39d4cb4ff0000000000,0x4fe0000b33f80002c9fc000164fe0000b33fc0002cdfe000166ff0000b33fc0012fe00097f01239d58c218d25090229d4c340f0f0f0f0f0f),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff40c99308e7c496e3c0b5e57e00000000ffff,0x7000130c3c0004c30e00026187000130c3c0004c30e00026187000130c3c000223000111800100809108e144826380254576aaaaaaaaaaaa),(0x122a64d6ea9e0695f7e4321910000ffff0000,0x80001c0fc0000703f0000381f80001c0fc0000703f0000381f80001c0fc000043c00021e00012282056a29e0604a50032181cccccccccccc),(0x9d52a4f3b55f8326d10e5b80ffff00000000,0x1ff0000007fc000003fe000001ff0000007fc000003fe000001ff0000007c00003e000009c42a430a5058326d1020180f0f0f0f0f0f0),(0x0,0x0),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g127 0 0 0 = true)
  · exact (rfl : block g127 1 0 0 = true)
  · exact (rfl : block g127 2 0 0 = true)
  · exact (rfl : block g127 3 0 0 = true)
  · exact (rfl : block g127 4 0 0 = true)
  · exact (rfl : block g127 5 0 0 = true)
  · exact (rfl : block g127 6 0 0 = true)
  · exact g127B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K474) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 8 := lower_forest (g:=g127) (i:=0) (hints:=25924) (before_sound K474 V474) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K474 8 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V474 low127 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[(0xf80000003ffffffffffffff80000003ffffffffffffff80000003ffffffffffffff800000fffffee8241494599e356c96d8bc0000003f03f,0x52801aaa94009554a00295528015aa9400a954a002a95280155a9400aa94a002aa9201556402aa8e8041490518e156c9040b411451451451),(0xffffffffc0000001ffffffffffffffc0000001ffffffffffffffc0000001fffffffffffff000000afa9ffc3060045308544d6c003f000fc0,0x600a13330050d998028326600a19330050cd98028332600a19930050ccd80283332022664044ccc2a29dd82020045108544d685145145145),(0xfffffffffffffffe0000000000000000000001fffffffffffffffffffffe000000000000000000152be74a28b17908953a196c0fc0000000,0x802c5c3c0162e1e00b2bc7802cde3c0166f1e00b2bc3802c9e1c0164f0e00b2bc3c04787808f0f142be74828a13900953a196cf3cf3cf3cf),(0xfffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000000000013b5ff181f8265b2429212d00000fc0000,0x3009fc01804fe00c033f803009fc01804fe00c033fc0300dfe01806ff00c033fc040bf80817f00395f71817826592421212c134d34d34d3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff40cb260d0ce115566a936eff000000fff,0x30e000018700000c3c000030e000018700000c3c000030e000018700000c3c00008c00011800100c2220d0c6100004a91084a28a28a28a),(0x0,0x0),(0x122a49a54f279ea821f695300000fff000,0x43f000021f800010fc000043f000021f800010fc000043f000021f800010fc00000f00001e000102a08a448251a2820e08432cb2cb2cb2c),(0x9d5249ea134f8aebe00ea03ffff000000,0x7c000003e000001f0000007c000003e000001f0000007c000003e000001f000000700000e0000095000060110c0ae2200a2030c30c30c30),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : checkedTables g223 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g223 0 0 0 = true)
  · exact (rfl : block g223 1 0 0 = true)
  · exact (rfl : block g223 2 0 0 = true)
  · exact (rfl : block g223 3 0 0 = true)
  · exact (rfl : block g223 4 0 0 = true)
  · exact (rfl : block g223 5 0 0 = true)
  · exact (rfl : block g223 6 0 0 = true)
  · exact (rfl : block g223 7 0 0 = true)
  · exact g223B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 9 := lower_forest (g:=g223) (i:=0) (hints:=268461892) (before_sound K127 V127) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K127 9 [(223,[]),(463,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V127 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[(0x7fffffffc00000003fffffffffffffffffffffffe00000001ffffffff0000007fffffffffffffd504a283598ceac015ff2f19400001fc07f,0x50012aa828016aa828014aa8280152a82800aa541400aad41400554a100aad05002aa90805551500a2814884e28005fe270008912244891),(0x80000000000000003fffffffc00000003fffffffffffffffe000000000000007fffffff80000035f57ea93407101929443e4ec07f0000000,0x555b33002adb33002a5933002ad9b3002aacc980154cc980155666c01333600553332009999a5557ea91407101029442c4ec78f1e3c78f),(0xffffffffffffffffc0000000000000003ffffffffffffffffffffffffffffff800000000000000a5f8fdd464cc534485e8182bf800003f80,0x181c3c000c1c3c000c1e3c000c1e3c000c0f0e00060f0e000607870021c3800183c3c010e1e00478ac9460c0134085e818202850a14285),(0xffffffffffffffffffffffffffffffffc000000000000000000000000000000000000000000002763bf208a34b426aaa7532d0000fe00000,0x16019fc00b009fc00b009fc00b009fc00b00cff005806ff0058067f80205fc01601bfc0102fe00723af208834b42628a7130d19b366cd9b3),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe81925c231f125b8f02d795f80000003fff,0x5861e0002c30e0002c30e0002c30e0002c30f000161870001618780004460005861c0002230002818050231710408f001585db56ad5ab56a),(0x2454d25baa781a57df90c8644000fffc000,0x607e0000303f0000303f0000303f0000303f0000181f8000181f80000878000607e000043c0002054505a22480851d200c860664c993264c),(0x13aa493ced57e0c9b44396e03fff0000000,0x7f8000003fc000003fc000003fc000003fc000001fe000001fe000000f800007f8000007c000012a80114a950e0c9940112203870e1c3870),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g239 0 0 0 = true)
  · exact (rfl : block g239 1 0 0 = true)
  · exact (rfl : block g239 2 0 0 = true)
  · exact (rfl : block g239 3 0 0 = true)
  · exact (rfl : block g239 4 0 0 = true)
  · exact (rfl : block g239 5 0 0 = true)
  · exact (rfl : block g239 6 0 0 = true)
  · exact g239B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 8 := lower_forest (g:=g239) (i:=0) (hints:=268461429) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 8 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0x1ffffffffffffe000000ffffffc0000fffffffffffffffff8000003ffffffffffff80001ffffbe2d6552da519822172148000007f01fc07f,0x4200055080005420006a1000128001a1000290002820001508001a84000942000290002c000a320c41000251982215200042850a142850a1),(0xe0000007ffffffffffff00000000000ffffff80001ffffffffffffc000001ffffffffffe0000219ae929cd02cd5c2576030003f800003f80,0x8045466011489804504c02291b0092c0228320124c045226011493008a4d8045232012480493000ae901c802cd5c256201162c58b162c58b),(0x7fffffffffffffffffffffff00000000001ffffffffffffffffffe000000000000000508339d4022db3c4743ab501fc000fe00000,0x1617800582e001617000b05c010b000b0bc021700160b800581c002c0e00160bc020f0083c1083215402098304743a950e1c3870e1c387),(0x0,0x0),(0xfffffff80000000000000000000000000000000001ffffffffffffffffffffffffffffffffffdae1033a21ca4909c8d7b0fe000000003fff,0x98180026130009858004c260022c004c2c0045800984c002612001309000984c004480112048a1003a21880000c095b02850a142850a14),(0xfffffffffffffffffffffffffffffffffffffffffe000000000000000000000000000000000044265e8bd6a26643e024ae0000000fffc000,0x14e06005381c014e0600a7038014300a70300286014e07005381c029c0e014e070028700a1c044201e8bd4a2644180042ab162c58b162c58),(0x48b9a4e4bcb285e17a4455000007f0000000,0x18ff80063fe0018ff800c7fc0027c00c7fc004f8018ff80063fe0031ff0018ff8004f8013e0048b1a4e4bca205c16a4455bd7af5ebd7af5e),(0x2754920534ad14b58f8813fffff800000000,0x1f000007c00001f00000f8000038000f8000070001f000007c00003e00001f0000070001c00027541200142410a10a0002c183060c183060),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 9 := by
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
  · exact (rfl : block g247 8 0 0 = true)
  · exact g247B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 10 := lower_forest (g:=g247) (i:=0) (hints:=268436804) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 10 [(247,[]),(439,[32,116,134]),(493,[32,49,132,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[(0x7fffffffffffffffffffffffffffffffffffffffe0000001ffffffffffffff00000fffff785cbaaaa2a40d5b2c2c0e0000000ffff00ff,0x55050002a828000a82800128280014840050280005414000d41400094140005210016100147008a2a22220014b2c0004021212121212121),(0xfff80000003ffffffc0000003ffffffc00003fffffffffffffe0000001ffffffffffff000005217c25ccb4a338e639105b00ff000000ff00,0x8660024a330012113001231b00122190044980122898009149800914d8009146401124011261015c248c208318c609105a0b0b0b0b0b0b0b),(0x0,0x0),(0x3fffffffffffffc000000000003ffffffffffffffffffffe00000000000000000b5a4677636101c5a51f250f0000ff00000000,0xd781601cbc0b00a5c0b00a5c0b00b5e080ae0b00b2e058058e058058e05805978202782027834a4267636001c5a41f250367676767676767),(0xffffffffffc00000000000000000000000003ffffffffffffffffffffffffffffffffffffffa5e216834129cb24837ce13ff00000000ffff,0x18000490c00024c600024c600024c60009300024c300012610001261000126180024400244081e2100101008a00836cc0114141414141414),(0xffffffffffffffffffffffffffffffffffffc00000000000000000000000000000000000000886cbd4c86db6ed18390d3800000000ff0000,0xe005871f002c38f802c38f802c38f80111c02c38fc0161c7e0161c7e0161c7e00447804478088641d4c84db6e908390d38dedededededede),(0x915349287c9ef0209eca5cc0000ffff000000,0x607e000303f000303f000303f00021e00303f000181f800181f800181f8000878008780081534908489ee020920808c98989898989898),(0x4ea924f70cd3e0baf803a80ffff0000000000,0x7f800003fc00003fc00003fc00003e0003fc00001fe00001fe00001fe00000f8000f80004e0824b60cd340321802280e0e0e0e0e0e0e0),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,8),(32,0,219,0,8),(0,32,218,1,7),(2,0,249,0,7),(64,8,179,0,7),(128,0,123,0,7),(0,2,105,144,6),(0,128,105,18,6),(1,0,218,0,6),(1,32,218,0,6),(16,0,235,0,6),(2,128,105,16,5),(16,2,105,128,5),(16,128,105,2,5),(130,0,121,0,5),(18,128,105,0,4)]
def g251A : List (List Nat) := [[],[113]]
def g251D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x309bd87cc640abf864c640
def g251D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20424c1081541330c74134202a921e302402feb8663ef58640f7e63207bd319027fbb2636f5ce40
def g251H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1e00
def g251D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c614730640a0ba8e3451258c0d478c731461a2544146d8b2891c2bad12c1a616b1341ab3450488375728b310f83400ff587ff31ff4c7ff30ff4c3fd10ef50fbe40
def g251H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x15590004401efe800008c03c3c9
def g251D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x12a62837f
def g251H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2a8017800000000ca180000000000000000000000000002cc00009c00000002440000000154f750038000000000000001
def g251L : Nat → Packing
  | 6 => (2,3,4,0,0,3,0,g251D6)
  | 7 => (6,2,4,0,0,7,0,g251D7)
  | 8 => (8,1,4,0,0,9,0,g251D8)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[(0x7fffffffffffffe0000001ffffffffffffff00000fffffffffffffffffffffffffffffff705c92e8e16429de2c2c0c3000000ff00ffff,0x55050002a8280005414000d41400094140005210016100140a0002a0a0004a0a0005210014500c80a0a020019e2c2004121212121212121),(0x0,0x0),(0xfff80000003fffffffffffffe0000001ffffffffffff00000fffffff0000000fffffff000005b95e9144b8a160f633117200ff0000ff0000,0x26600142b3000a0a980050a980050ad80050564010a4010a6002814c002836c0028264010661995c8004188140d60311520b0b0b0b0b0b0b),(0x3ffffffffffffffffffffe00000000000000000ffffffffffffff000000000000bd2e4c76b6101d5a51f240e0000ff00000000,0xb781601b3c0b00ace05804ce05804ce0580567820338203382c02a702c02a702c02b78202b83d2e0476b6001d5a41b240267676767676767),(0xffffffffffc00000000000000000000000000000000000000ffffffffffffffffffffffffffadea1c8341a9cb24837ce12ff0000000000ff,0x38000593c0002ccf000166f000166f000166780025c0025c000b338000b338000b3380024c0ade2180141888a00835cc121e1e1e1e1e1e1e),(0xfffffffffffffffffffffffffffffffffffffffffffffffff000000000000000000000000008064b74c865b6ed18390d3900000000ffff00,0xc005861c002c30f0016187001618700161878004460044600b0c3c00b0c3c00b0c3c00447008060374c06536a408380c28d4d4d4d4d4d4d4),(0x915349287c9ef0209eca5cc0000ffff000000,0x607e000303f000181f800181f800181f80008780087800c0fc000c0fc000c0fc0008780080514908489ee020924818c98989898989898),(0x4ea924f70cd3e0baf803a80ffff0000000000,0x7f800003fc00001fe00001fe00001fe00000f8000f8000ff00000ff00000ff00000f8000420824f60c5360b21802280e0e0e0e0e0e0e0),(0x0,0x0)]
def g253C : List ColumnInfo := [(0,8,181,64,8),(8,0,245,0,8),(4,0,249,0,7),(16,0,237,0,7),(32,0,221,0,7),(64,8,181,0,7),(128,0,125,0,7),(0,4,89,160,6),(1,0,252,0,6),(4,128,105,16,5),(16,128,105,4,5),(32,4,89,128,5),(36,0,217,0,5),(132,0,121,0,5),(20,128,105,0,4)]
def g253A : List (List Nat) := [[],[114,84]]
def g253D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30040582080008040031c02c700b1c02e5b2d549d09e36484805ff7050efeba461f74c630bfee8985fd744c3eea1a617f5ce10bfee6884ff764c67ebb4216fdd110
def g253D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8a16ab4883a931ab54226353b05346ab70a72082ab0ea824713988242aa48c2932ea81cc41c522aac88abedb8bd4515c5c00ff50ffd61ff507fd31ff8c3fd30ff843fd10
def g253H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8803210060004988003500000020073a280b80a70
def g253D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2c864a37f
def g253H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd00001c80000000004ac00000000000002d40022f00000000000000000000f1a7401246800000000000001c000000000019c2
def g253L : Nat → Packing
  | 7 => (11,2,4,0,0,7,0,g253D7)
  | 8 => (8,1,4,0,0,9,0,g253D8)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact (rfl : block g253 6 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),(0x80000000fffffffffffffffc00000007fffffff000007ffffffffffffffffffffffffffff606845947e807eb553a18e5c00000ffc00003ff,0x8a50aa01148154022840a80451835008a20520110b008a282a011450940228a148044280020450432805eb503a18e14154551545515455),(0xffffffff00000001ffffffffffffffffffffffffffffffffffff00000001fffffffc000000f031b09581dd19d0eb8a9af003ff00000ffc00,0x2c04cc0058159800b0153001602a6002c056402052002c014c005806d800b00990080cc030119095818419c0ea8888a0cc330cc330cc33),(0x1fffffffffffffff80000000000007ffffffffffffffe0000000000000cbe5a8c481b2fce82f63582900000003ff00000,0x1400e6f02801d9e0500299c0a0053381400b6782029c1400b270280164e05002cde0809704b45a0848092bce80762582943d0f43d0f43d0f),(0xfffffffffffffffe00000000000000000000000000007fffffffffffffffffffffffffffff61cf8224a5a2c12a43cd4d9ffc0000000003ff,0x130870002611e0004c31e0009863c00130c780044e00130c3800261870004c30e0011181e61c1820485a2000241c50c92a8aa2a8aa2a8aa),(0xffffffffffffffffffffffffffffffffffffffffffff8000000000000000000000000000184c99308a5ccbae3c49575370000000000ffc00,0x59c0f800b381e0016703e002ce07c0059c0f8004870059c0fc00b381f8016703f00121e0184c88200a5c4ba63c0157535f33ccf33ccf33cc),(0x1a6a64d6ea9e8415f7a43319000000003ff00000,0x61ff0000c3fe000187fc00030ff800061ff00008f80061ff0000c3fe000187fc00023e001a4a24d6a2968411778012190bc2f0bc2f0bc2f0),(0x1952a4f3b5578326d10e4b80fffffffc0000000,0x7e000000fc000001f8000003f0000007e000000f00007e000000fc000001f8000003c00001842a0d285058002d0020100c0300c0300c0300),(0x0,0x0)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : checkedTables g254 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g254 0 0 0 = true)
  · exact (rfl : block g254 1 0 0 = true)
  · exact (rfl : block g254 2 0 0 = true)
  · exact (rfl : block g254 3 0 0 = true)
  · exact (rfl : block g254 4 0 0 = true)
  · exact (rfl : block g254 5 0 0 = true)
  · exact (rfl : block g254 6 0 0 = true)
  · exact (rfl : block g254 7 0 0 = true)
  · exact g254B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 9 := lower_forest (g:=g254) (i:=0) (hints:=320955712) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 9 [(254,[]),(382,[49,100,135]),(443,[32,116,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g471Y : Array (Bits × Bits) := #[(0xfffffffff000000ffffffffffffffffffffffffffffffffffe000001ffffffffffff00007fffcec5ad506645fa13808959000000001fc07f,0x2aa5200aa9480aa9480554a40154a40254a4029140525200552900d5290095290052280b14050ec4a14026458a13808851a3468d1a3468d1),(0x3ffffffffffff0000007fffff8000007fffff80003fffffffffffe000001ffffffffff8000140d310fe314086c85bae70000000fe03f80,0x3306028cc1810cc1814660c02260c06360c0432204986028983014983014d83014644092204994093109c204086c81aa63264c993264c993),(0xffc0000000000000000007fffffffffff80000000003fffffffffffffffffe000000000000003da113d80a04e3f0791e9001fc07f0000000,0xbc000b2f0003af00039780014b80014b80016bc00ae000b2e00058e00058e0005978013c009e0c2113d80a0063f0411e800e1c3870e1c387),(0x0,0x0),(0xfffffffffffffffffffff80000000000000000000003ffffffffffffffffffffffffffffffffc930c93a15435d8c06f7800003f800003fff,0xc0080c3002023002021801018c01018c01018c00130080c30040610040610040618002200110013048121100518006558048912244891224),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffc0000000000000000000000000000000002536e8bc2aa62e3a2248efe0000001fc000,0x4fc00013c00013e00009f00009f00009f0001c0004fc00027e00027e00027e0003c001e000110e8bc02a60e022248c1c3870e1c3870e),(0x45c94e4bcb285413844750003ffffe00000,0x3070000c1c000c1c00060e00060e00060e000460030700018380018380018380008c0046000044842424b2840138001491224489122448),(0x33aa420534ad14b5cf8813fffc0000000000,0x3f80000fe0000fe00007f00007f00007f000078003f80001fc0001fc0001fc0000f0007800338a4004348514058c8013e1c3870e1c3870)]
def g471C : List ColumnInfo := [(1,0,470,0,8),(2,0,469,0,8),(4,0,467,0,8),(64,0,407,0,8),(256,0,215,0,8),(16,0,455,0,7),(128,0,343,0,7),(144,0,325,0,4)]
def g471A : List (List Nat) := [[],[32,116,134]]
def g471D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x17ddc553
def g471D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x76cba85923fd53
def g471H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40
def g471D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x358d103ff
def g471H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x60
def g471L : Nat → Packing
  | 7 => (1,2,3,0,0,0,0,g471D7)
  | 8 => (1,1,3,0,0,0,0,g471D8)
  | 9 => (1,0,3,0,0,0,0,g471D9)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471T : checkedTables g471 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g471 0 0 0 = true)
  · exact (rfl : block g471 1 0 0 = true)
  · exact (rfl : block g471 2 0 0 = true)
  · exact (rfl : block g471 3 0 0 = true)
  · exact (rfl : block g471 4 0 0 = true)
  · exact (rfl : block g471 5 0 0 = true)
  · exact (rfl : block g471 6 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V471 : Known true K471 := extend_ok (m:=471) V254 low471 (by decide +kernel)
def g475Y : Array (Bits × Bits) := #[(0x1fffffffffffe000003fffffc000fffffffffffffff800000fffffffffffe0007ffe56e1be36cec4440a35203000000000007fc01ff,0x94a1552941552940552941aa52812891a94a0a448a4a50154a506a94a0952940a448b122856e1ba240ec4440a35002a8d46a351a8d46a351),(0xfffffe000001fffffffffffc000000000fffffe0007fffffffffff000001fffffffff8000806bdacc591e606033dc40000001ff00003fe00,0x1801983011983008983001306011b102c1800c88130c02260c024c1804d83008c8812204c802b5a8450144060319c4229148a45229148a45),(0x0,0x0),(0x1fffffffffffffffffffff0000000007ffffffffffffffffe0000000000001cf8ccb50020515076f1e8007fc0000ff8000000,0xc5e00185e00182e00185c00305c023000c2f011c0060b800607000c0e00182f011c0470438c8b50020411062e1e00984c26130984c2613),(0xfffffffffffe0000000000000000000000000000007fffffffffffffffffffffffffffffe6b040cbb35424ab01a0bb00003fe0000003ffff,0x200600400600401300401600802600040200b000201004c010048020090040130000000002904041a210208800a01945229148a45229148a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffff80000000000000000000000000000001099718ac2a998d9a8a1cff8000000ffffc0000,0x10800021800021c00021800043800000010c00000008700008700010e00021c0002000800000408ac029009180a1c160b0582c160b0582c),(0x22e6a165acbca6174053400003ffff000000000,0xc1f00183e00183e00183e00307c002380c1f0011c060f80060f800c1f00183e0011c0470002c0a1618ca8a61740420984c26130984c26130),(0x19d52160534a2adc6d5842ffffc0000000000000,0xfe0001fc0001fc0001fc0003f80003c00fe0001e007f00007f0000fe0001fc0001e0078019c5214053482ac4051002e070381c0e070381c0)]
def g475C : List ColumnInfo := [(1,0,474,0,9),(2,0,473,0,8),(128,0,347,0,8),(256,0,219,0,8),(0,2,329,144,7),(0,8,147,320,7),(0,16,328,131,7),(0,64,146,265,7),(0,128,329,18,7),(0,256,147,72,7),(16,0,459,0,7),(64,0,411,0,7),(130,0,345,0,7),(264,0,211,0,7),(1,16,328,130,6),(2,16,328,129,6),(8,64,146,257,6),(16,2,329,128,6),(16,128,329,2,6),(64,256,147,8,6),(18,0,329,0,5)]
def g475A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def g475D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x61fe1b7550931
def g475D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x28c1e0d7f75d0931d7f7550931
def g475H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40
def g475D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x78408805841044708a041290fc7b080e18406db8208b3af6b25201ffd0b31ffe8498ffd424c6fdb82875fdd531
def g475H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x38bb00000180001e12
def g475D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x34d28104460d38928103c72454ad2e04472452ed80c44724380c41118b24716d80a3082c91c5b6018c20b1e030d446a8481e0c04b1805400ff90ffd43ff10fff41ff507ff31ff4c7fd21
def g475H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x233a0513c0800000007004490f0c42c0ac0
def g475D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6b001ff
def g475H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x224000000000000254000000000000000000c6003007c988000000000000085000000000000000a0c0048bd80000051c00c840000000001410000000000000000000000292003c40000000000002b1000003a000000c200000ed0000000000000003a30000000000000000000000000f5c00000001cc000000000000003d10000000000000000000000000000000000000000000000000000253
def g475L : Nat → Packing
  | 6 => (1,4,5,0,0,0,0,g475D6)
  | 7 => (2,3,5,0,0,4,0,g475D7)
  | 8 => (5,2,5,0,0,8,0,g475D8)
  | 9 => (8,1,5,0,0,9,0,g475D9)
  | 10 => (1,0,5,0,0,0,0,g475D10)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475T : checkedTables g475 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g475 0 0 0 = true)
  · exact (rfl : block g475 1 0 0 = true)
  · exact (rfl : block g475 2 0 0 = true)
  · exact (rfl : block g475 3 0 0 = true)
  · exact (rfl : block g475 4 0 0 = true)
  · exact (rfl : block g475 5 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V475 : Known true K475 := extend_ok (m:=475) V471 low475 (by decide +kernel)
def g501Y : Array (Bits × Bits) := #[(0x7ffffffffffffffffffffffffffffffffffff8000003ffffffffffffc0000fffffffffffffffb98ae94063697bd80511410000000fe03fff,0x2108014842005210801484200211001084005210802908400a421000844021100108400422000108e04000690b9801104142850a142850a1),(0x0,0x0),(0x8000001ffffff8000001ffffff00003ffffffffffffc000000fffffffffff00003fffffe0000412e841a8114a21e6afaea01fc07f01fc000,0x14580001160000c58000214001280005160000a3000052c00014500048001280005080023000604180100a21a603862060c183060c183),(0x0,0x0),(0x1ffffffffffffe00000000003fffffffffffffffffff0000000000000003ffffffffffa41303ed1b46c0aa358d9e0003f80000007f,0xa03960280a580a02960280b58202b05016580a02c405016301405960809c20270501650404a241203290b06c02224899e2c58b162c58b16),(0xffffffe000000000000000000000003ffffffffffffffffffffffffffffffffffc000000000018213b3a308358678cf699000000001fff80,0x4c52181314c604c53181314c60424c26298604c5308262984098a6181091042442629860848c18211b22308250658cc698b972e5cb972e5c),(0xffffffffffffffffffffffffffffffc00000000000000000000000000000000000000000000006e65e8bc6aa6761a02486fe00000fe00000,0x63e00018f800063e00018f8004700031f800063f00031f8000c7e0011e004780031f8008f004e61e8ac28264402024861c3870e1c3870e),(0x8b9a4e4bcb285c13a44750003fff0000000,0x707c001c1f000707c001c1f0008780383e000707c00383e000e0f80021e008780383e0010f0008a9a0c4b4b005c11a4401d1a3468d1a3468),(0x6754920534ad14b5cf8813fffc0000000000,0x7f80001fe00007f80001fe0000f8003fc00007f80003fc0000ff00003e000f8003fc0001f00063108005342d10a58f8011e1c3870e1c3870)]
def g501C : List ColumnInfo := [(16,0,485,0,8),(32,0,469,0,8),(64,0,437,0,8),(128,0,373,0,8),(256,0,245,0,8),(1,0,500,0,7),(4,0,497,0,7)]
def g501A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118]]
def g501D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1040c3efb9a2177dcd10
def g501D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6cba8591ffd10
def g501H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4060
def g501D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x358d103ff
def g501H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6
def g501L : Nat → Packing
  | 7 => (2,2,3,0,0,3,0,g501D7)
  | 8 => (1,1,3,0,0,0,0,g501D8)
  | 9 => (1,0,3,0,0,0,0,g501D9)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501T : checkedTables g501 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g501 0 0 0 = true)
  · exact (rfl : block g501 1 0 0 = true)
  · exact (rfl : block g501 2 0 0 = true)
  · exact (rfl : block g501 3 0 0 = true)
  · exact (rfl : block g501 4 0 0 = true)
  · exact (rfl : block g501 5 0 0 = true)
  · exact (rfl : block g501 6 0 0 = true)
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
set_option maxHeartbeats 0 in
theorem V501 : Known true K501 := extend_ok (m:=501) V475 low501 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0xf80000000003ffffffffffffffffffff80000001fffffff9d0800168592d242c871992f42c5013fd0121dec000000000007ff001ffc007ff,0x5050000155a8280000aa941400002aa908002aac2000aaa1d000002800250428051190d4244003e001215ec1012024048090120240480901),(0xfffffffffffc0000000001fffffffffffffffffe000000060210982324f1cecc38068264b80fb782eb470cf000001ffc00000000003ff800,0x600228a19930011450ccd8008a28333200444cc8011133320200882300518ccc28048260380eb382e3070cf0550aa1542a8550aa1542a855),(0xfffffffffffffffffffffe00000000000000000000000000b0e6fc9a005297cc4913e10b26a4090b24accbe000ffe00000000ffe00000000,0x8000b009e1c0005804f0e0002c02bc3c0080f0f00203c3c0b086dc9a0042978c411381032484010b202c88e0330660cc198330660cc19833),(0x3ec2ad28c088ba4397da1243541b6c440e755ec9800000003ff80000000000000,0x16002cdfe00b00166ff005800b33fc010097f004025fc03e42a928c088ba4381d01243540b60440c755ec9b0f61ec3d87b0f61ec3d87b0f),(0xfffffffffffffffffffffffffffffffffffffffffffffff92f115712de065a129562784376142409981084bfff00000000000000003fffff,0x4c30e000002618700000130c3c000011180000446000029105510de025212902260034210040908108008aa1542a8550aa1542a8550aa),(0x4265ab452698787388b96e2302f99cb6c20909480000000000000fffffc00000,0x58703f00002c381f8000161c0fc0000221e000088780000026123452698685388a86e2002399c14c200010eccd99b33666ccd99b33666cc),(0x8b9a49756713118d62aecc90c902f84832ac312800000003fffff00000000000,0x607fc00000303fe00000181ff00000043e000010f8000000b9049516710118562ae48008900f80830880124f09e13c2784f09e13c2784f0),(0x67549069da2e88593064c198c8069435055d24307fffffffc0000000000000000,0x7f800000003fc00000001fe000000007c000001f00000044449020420a800010648188c8061405014c0430700e01c0380700e01c0380700),(0x0,0x0)]
def g255C : List ColumnInfo := [(0,8,183,64,10),(2,0,253,0,10),(4,0,251,0,10),(8,0,247,0,10),(0,64,182,9,9),(1,0,254,0,9),(32,0,223,0,9),(64,0,183,0,9),(64,8,183,0,9),(0,32,218,5,8),(16,0,239,0,8),(128,0,127,0,8),(0,2,109,144,7),(0,128,105,22,7),(1,32,218,4,7),(4,32,218,1,7),(18,0,237,0,7),(33,0,222,0,7),(132,0,123,0,7),(2,128,105,20,6),(16,128,105,6,6),(17,0,238,0,6),(144,2,109,0,5)]
def g255A : List (List Nat) := [[]]
def g255D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1810b04341000e3e00a2b8f83144e3e00a9a826a523a21e9b1796148f058037f32ac00e97f7915d154edfba4e8a85fde4574542fdb243a2a17f5911d150bfcc80e8a85ef65287502f7f28c3a817f79161d40bfbc8ae8a04fde45879d27ef22c3e813f79161d40
def g255D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50b2818d16290898c3111211112121222434e911a24280491207262a5044258a86285940d0942c1e30e13062c22c7118c5070837161c0389121c304c78b0e04a50ac4071e01a586c6344870c1310ac381297880e3c034b0c243864a131e2c0589122f3e6c98c562c3812961c263c58700a1c3490e131e2c380714231890e18260178b0c5294a4c78b0452c38ac6243860837160c314bc78b00bc314a0e294a4c7831618a509121c304c788560c31469624386098f161c114a14243868a131e2c184a14545e3c02b2621d84a14365e4ce3f0e01c466c797267162b161c0563192b3659793393c580bc79338b1427161c04e6c797267158701227363cb933e21780812571e6c99c5e2c22b0159338f158700e1f2671627161c11488b788787385f8448067e47c97ae7937557106c46946416115cc5795344f64aa4734203e93a43513052b926d22f1e319014b1060c107503e000fff74553ff5d154fff74543ff9d150ffd74543ff1d150ffe87503ff61d40fff74503ff5d140bfd84dd6ffe1175bfd80dd2ff61e74bfd809d3fde0574bff805d2ff60074bfd87952ffe1d54bfd84dc37f5d370bff845c37fdd170dfd745c2ff61f40bff87502ff61d40ff970502fbe0975dbf749d2fde0574b7d851d2fb60874bf5811d2fe60074bed82952df61770
def g255H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xcb0000000000620000000000c000fa000000000000000099000000e84c0000d600d10063000000005dc400650000b70000000000
def g255D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x50d24e5c304471251a58d3c90c111c51319534b24f14301659319a5cd2c93c50c051919259534b24e6c3140b1a4cc2883472971434146163493950c111c49650d24f0c111c49434c74f2450c029659654c74f2450c02a85c93930c502239731d3c91422c051459530b3c87450c0a979e5f5594c908384c32948117445090007ff75ffaebffdd3ff3a7fd74ff8e9ff953feaa7ff70ffae1ff543ffa07fd40
def g255H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xd82e5b605e00022002427778e00010104540039f4840093fa4b5ed2968cc32a0084403a7000a13061345595800002c7000c514d8936d9928f0802c102c06e700000
def g255D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x66290e20808ff
def g255H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x15145600000000348000003f34ee800580000000000029c00000003e40116000000026c8
def g255L : Nat → Packing
  | 8 => (14,3,5,0,0,8,0,g255D8)
  | 9 => (38,2,5,0,0,12,0,g255D9)
  | 10 => (13,1,5,0,0,10,0,g255D10)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 11 := by
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
set_option maxHeartbeats 0 in
theorem V255 : Known true K255 := extend_ok (m:=255) V501 low255 (by decide +kernel)
def g479Y : Array (Bits × Bits) := #[(0xfffffffffffe000000001ffffffffffffffffff0000001ffffffec01cdc1d3d60b05712a643572828dae8540940000000000000007fc01ff,0x2aa52800aa5529400aad529400aa952940055522402aac4805552c01c1c153d00b05712a642462828dac840092a351a8d46a351a8d46a351),(0x3fffffffffffffffffe000000001fffffffffffffffe00000021809336356892dc51e180acc25c05d4b922d400000000001ff00003fe00,0xb30600a0cc9830050cc9830050ccd83005066644044cc8808999a1801114116810cc516100acc25c0590b920d48a45229148a45229148a45),(0x3ffffffffffffffffffffffffffe0000000000000000000000345a768313214410e64b58c5bb752892cc00740000ff803fe00000000000,0x3c0002caf0e000164f0e000164f0e0001657878008f0f0011e1e1452768213204410c04958c5ba7528828800741e0f0783c1e0f0783c1e0f),(0xffc00000000000000000000000000000000000000000000000001cc232d4055222a353ec4bc50ca682a014bdc801ff000000000ff8000000,0xc000300cff0001806ff0001806ff00018067f800817f00102fe01cc032d40542228343ac41c50ca480a00491c026130984c26130984c2613),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffca45032e88ae4c50049ca8597a4572e20291880000007fc000000003ffff,0x8030f0000401870000401870000401878000011800002300002440222880644100480885118017242009109148a45229148a45229148a),(0x0,0x0),(0x3265c62f04071c388415e061978650913580ffe00000000000ffffc0000,0x43f00000021f80000021f80000021f8000001e000003c00001060c22a000504088411a021150600013480c582c160b0582c160b0582c),(0x449a8596e90f20c6b1516200501d0256e86700000007ffffff000000000,0x307c00000183e00000183e00000183e0000008e000011c0000000988496490a2002a140600050080254606026130984c26130984c26130),(0x33b481810199052c9c32a5d2849abb11c02703ffffff8000000000000000,0x3f80000001fc0000001fc0000001fc0000000f000001e00000222081010099012c1412a410000a131140260381c0e070381c0e070381c0)]
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
theorem g479G : graphValid g479 (boundsBefore K255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low479 : Lower true (varsX 479) (graphGoal 479) 12 := lower_forest (g:=g479) (i:=0) (hints:=8858396484) (before_sound K255 V255) g479G g479T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K479 := extendKnown K255 12 [(479,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V479 : Known true K479 := extend_ok (m:=479) V255 low479 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0xfffffff8000000007fffffffffffffffffc000001ffffff220691f524e446aeae40804ac42298aa9c285400000000000007ff001ffc007ff,0x420001520a10003520a10002520a100014822002c11001420029180208446a2a4400042c40290a08c085520a4148290520a4148290520a41),(0xffffffffffffffff8000000007ffffffffffffffe000000d9584892129806c813c949d4a6e6c7e01a541c00000000003ff800000003ff800,0x804522604c02292604c02293604c02291904012482009265150489202900688028848d4a6e6c2a01a440c658cb19632c658cb19632c658cb),(0xfffffffffffffffffffffffff800000000000000000000041e14c0022169f64813296237e871097190d80007ff001ffc00000ffe00000000,0x160b800000b03800000b03800000b05e00020f000107801c04000220297440102800276051096190c800380700e01c0380700e01c03807),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffff808b6248d743f051058cb030d5402e6b21724000000ffe00000000000003fffff,0x984c009004c24009004c24009004c2600804480402240808902481543b0410100b02011002c4b0132008a1142284508a1142284508a114),(0x76018cf4912109835ab4398a38a4678927f1a00000000000000000fffffc00000,0x14e07004e0a703804e0a703804e0a70380104870082438056010c74912108015ab4398808a0670922f122dc5b8b716e2dc5b8b716e2dc5b8),(0x58c775f0c81ad0c6107fa8c30d96300d09c27ff800000000007ff00000000000,0x18ff800000c7fc00000c7fc00000c7fc00008f800047c00018c665d0401890c4107da8c30d923001014201f03e07c0f81f03e07c0f81f03e),(0x1936a52ce9099033fc550b45031181042a831800000ffffffff80000000000000,0x1f00000700f80000700f80000700f8000020f00010780000826a524c8080032fc5503010010010020811310620c4188310620c4188310620),(0xced20222199622b270da64a1083af831e6a663fffff0000000000000000000000,0xe0000007ff0000007ff0000007ff0000003f00001f80000ce120022199420b230d824210822c821e6a243e07c0f81f03e07c0f81f03e07c0)]
def g503C : List ColumnInfo := [(1,0,502,0,10),(2,0,501,0,10),(4,0,499,0,10),(16,0,487,0,10),(32,0,471,0,10),(64,0,439,0,10),(128,0,375,0,10)]
def g503A : List (List Nat) := [[],[32,116,134]]
def g503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6b1a207ff
def g503L : Nat → Packing
  | 11 => (1,0,3,0,0,0,0,g503D11)
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
theorem g503G : graphValid g503 (boundsBefore K479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low503 : Lower true (varsX 503) (graphGoal 503) 12 := lower_forest (g:=g503) (i:=0) (hints:=8858371396) (before_sound K479 V479) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K503 := extendKnown K479 12 [(503,[]),(509,[49,100,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V503 : Known true K503 := extend_ok (m:=503) V479 low503 (by decide +kernel)
def g507Y : Array (Bits × Bits) := #[(0xe0000000003fffffffffffffffffff8000001fffffff0c1e644a0c1a805ee8a8442656957089a064d420000000000000000ffffffc001fff,0x482828001a905050002520a0a00029042002c10800a7041e04420012805a80284426560140080024542921490a485242921490a485242921),(0xffffffffffc0000000007fffffffffffffffe0000004f142845b608111024a78e1615d068d674daf4920000000003ffe0000000003ffe000,0x8130012293026002453604c0048a3208022482008934e042005b200110004a3840215906852749a748230b1858c2c61630b1858c2c61630b),(0x0,0x0),(0xffffffffffffffffffff800000000000000000000004010101b32220fd3f15875d0fd10d451cd11a92a000fff8000001fff0000000000000,0xb00b1c00016016380002c02cbc00404f001013c4010101b32220953e1081410b90054518901a90a067033819c0ce067033819c0ce067),(0xfffffffffffffffffffffffffffffffffffffffffff812613201c87283c114319332bafa39508e11a0c0000007ffc0000000000003ffffff,0x240024c20048004984009000930c01004880401220010212200c86003810400930080b83850861080c41420a105082841420a1050828414),(0x3c2b42338e5486405688539d1a136ebd6387d99200000000000000000007ffc000000,0x1382c38fc02705871f804e0b0e3f002088f008223c00c2a02338e5486405688539d1a136abd638598916deb6f5b7adbd6deb6f5b7adbd6de),(0x6ec9da86114d3630c40a9a8181b38a235040475fff0000000001ffffff8000000000,0x303f000000607e000000c0fc000010f000043c0004a40da00014d200044029a0001928a21404003409804c026013009804c0260130098),(0x8b3696e4a18d80ceb3476adc2641c090128a2d80000007fffffe0000000000000000,0x1c03fc00003807f80000700ff0000041f000107c00000b1494a4018c804eb14728dc2641408010082518e0c7063831c18e0c7063831c18e0),(0x674920d3cd3744ac98374249c402836ae2930685ffffff80000000000000000000000,0x1ffc0000003ff80000007ff00000007e00001f8000023492040cd0104ac183742494402830862920681f00f807c03e01f00f807c03e01f00)]
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507T : checkedTables g507 11 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g507 0 0 0 = true)
  · exact (rfl : block g507 1 0 0 = true)
  · exact (rfl : block g507 2 0 0 = true)
  · exact (rfl : block g507 3 0 0 = true)
  · exact (rfl : block g507 4 0 0 = true)
  · exact (rfl : block g507 5 0 0 = true)
  · exact (rfl : block g507 6 0 0 = true)
  · exact (rfl : block g507 7 0 0 = true)
  · exact (rfl : block g507 8 0 0 = true)
  · exact (rfl : block g507 9 0 0 = true)
  · exact (rfl : block g507 10 0 0 = true)
  · exact g507B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507G : graphValid g507 (boundsBefore K503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low507 : Lower true (varsX 507) (graphGoal 507) 12 := lower_forest (g:=g507) (i:=0) (hints:=13153361988) (before_sound K503 V503) g507G g507T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K507 := extendKnown K503 12 [(507,[]),(510,[32,116,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V507 : Known true K507 := extend_ok (m:=507) V503 low507 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0xfc1dc1841010ac9b6a12fd4a29420d78422084286240dc641e655961003331290000000000000000000000000000ffff0000ffff0000ffff,0x501d810010100c912802f942204209584020840862409c641e61504100132008490149014901490149014901490149014901490149014901),(0x12004140638074705a714b6860e9f4350bba35706021f86ae70064c52b3184a00000000000000000000ffff0000000000000000ffff0000,0x982004040218060305a704b6060a1f0350a0a34706001f868e70044c5231184a185518551855185518551855185518551855185518551855),(0x2cb21e243ee4890915ea094281a9381a448598d760130300a3680c70001524e00000000ffff0000ffff000000000000ffff000000000000,0xe20b2082432e4090101e8090281a9181a448180d26001030083480450001104c003300330033003300330033003300330033003300330033),(0x3e1828c33050d02099a2090677769b12650c02852444c14cd8b3c99a5f66c80000ffff0000000000000000ffff00000000000000000000,0x3e0828c22050d00019a0090257369b02610c02802444404cd833c992534248030f030f030f030f030f030f030f030f030f030f030f030f),(0xfe12de11b1658035481800319804b1a08bfe740628964a19590e021ac9008305000000000000ffff000000000000000000000000ffffffff,0x202521181658024401800008804a0a08a5e500008864019400e02128900030520aa20aa20aa20aa20aa20aa20aa20aa20aa20aa20aa20aa),(0x844467a688b16203688fefc5844e0233865b6091a6212020ea59fa3b048b1400000000000000000000000000000000ffffffff00000000,0x804465a480b1620360062dc58446021386436091a62100208a09ba3b048b10b6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6cc),(0x20836914d0bb60801e7441059a10034704812891dce8150c091a4126eb49438ffff00000000000000000000ffffffff0000000000000000,0x2003691050aa20801c4041019a00024300812811d8a01108000800268a4942004f004f004f004f004f004f004f004f004f004f004f004f0),(0x1678b49240653e88604734111a1204d0d0184d0d050355e31080984158fe810000000000000ffffffffffff000000000000000000000000,0x1448948240011488200734111a1004c01010490d050204031000980048ee010c700c700c700c700c700c700c700c700c700c700c700c700),(0x2c0e10c9851092174201266e6da408ec114c2518af9228986014c31a44820d2ffffffffffff000000000000000000000000000000000000,0xc0c1041851092164201266c40040004114c0500051228902014c3004082092f800f800f800f800f800f800f800f800f800f800f800f800)]
def g511C : List ColumnInfo := [(1,0,510,0,12),(2,0,509,0,12),(4,0,507,0,12),(8,0,503,0,12),(16,0,495,0,12),(32,0,479,0,12),(64,0,447,0,12),(128,0,383,0,12),(256,0,255,0,12),(0,2,365,144,11),(0,8,183,320,11),(0,32,474,5,11),(33,0,478,0,11),(36,0,475,0,11),(0,16,364,131,10),(0,64,182,265,10),(0,128,361,22,10),(0,256,179,76,10),(1,32,474,4,10),(3,0,508,0,10),(10,0,501,0,10),(12,0,499,0,10),(16,2,365,128,10),(17,0,494,0,10),(18,0,493,0,10),(34,0,477,0,10),(40,0,471,0,10),(64,8,183,256,10),(66,0,445,0,10),(72,0,439,0,10),(128,2,365,16,10),(132,0,379,0,10),(136,0,375,0,10),(256,8,183,64,10),(260,0,251,0,10),(264,0,247,0,10),(1,16,364,130,9),(1,64,182,264,9),(4,128,361,18,9),(4,256,179,72,9),(5,0,474,0,9),(5,32,474,0,9),(16,128,361,6,9),(48,0,463,0,9),(64,256,179,12,9),(68,0,443,0,9),(128,16,364,3,9),(129,0,382,0,9),(144,0,365,0,9),(144,2,365,0,9),(256,64,182,9,9),(320,0,183,0,9),(320,8,183,0,9),(20,128,361,2,8),(68,256,179,8,8),(129,16,364,2,8),(257,64,182,8,8)]
def g511A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def g511D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x59d5f4d86e57a15d120
def g511D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc598a82f0a0bc3040a17180a77dcbad4a961d64afd7c361ba15d120e77586e57a15d120b75fc361b9550520
def g511H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb0
def g511D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8ba2a02dc5122e8a80b71448b22a02dc5122c8a80b71441a4cc0903c5f0e09c6d11c3d0570538669f8570db36945e1718c243719c35614912c3962490ec3962490c0be6f96f0fc1735cc8b22a279be5bc3f05c58de351d896058be138c92b48d1b8d2756c3b2a0f4bb1b00c7b26c906c0b0ec2704c071032ac8b1b8c298b62585e138092b48d1981e59a62f49cab17cb8462d8a60f8292747d138c6c892a58cd18241389b22c6cd72917cd32ac8c2787f32c6e108f23c6f0e49d1d8be0b44e009bad6a2bd54ca5143a664948e110a0f3fa734d39772ca510878d517c2383b85b0600019ffed4a95d984cffb6a54aecc267ffb52a5875933feda952c3ac9dfee81a0e4964bfbf66c32e4a0777d86e55744837fac3742ba2417f7ecd8650520eefb0dcaa8290777f9560d41483bbfcaac6a0a419dfad4a961d64cefb6a54b0eb267df97e8d86552befd9b0dca2e1777ecd865d170afbf66c3724b867dd97e8d86502fedd9b0cb82819fd65ba15d120cff361d4ac8905fdbb361970482bebd9b0dc8ae99dde57a15d120
def g511H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5cd40000a06275000001330000
def g511D11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x4c62f0f839bcb50a5d3292122bc49270643c090708dba46368f8c27e2cf45dcec349a0d0eb78ca463520ae30578924e0c878120d1b095bc651f1a51c59e4b2510e9ac627d33319e24964a21d328c51a6e633c4d598cc3874a94af41e96cb62b0586db8f31a89265297436b23ac6aaad8ca665d0d009e6258eb6a42686d6475755561194ccba1a013cc4aed854848bd490e84b258d046240e02c161b6f18c893295161c0a1d0982406218c71b6ca61c0a1d0982406218c6eb84a19d2d1689a35150a83a0e128681ade5a90a692a28b44a170943c02072d635356cb45a250b84a1e01039653576c25c318cc3a4cb84b177a110c61d265ce38bb6c78630e931770b765c38c1174a45512868340d06ad82c651d65243d168a41e0b195856578845a290782c6561655e2312c963305b6c3644a44b352b12c371ca5b7351b12c36eca5c3351a8c0be2f0f2dc1c456c6e352996c3e6c270fccc23d080282c6f9be1e5b83cc160d4ac34398bc8e3f0f839bcb4da6a69330d84e471f87c1cde5a85369ab30ce1e6f8396a114a652e230f84e092a9196c6d1b198b2b1799255231b46c66588e692a91cca36633c3e32b7c3cf7046435549187c260b824aa467a8db5c6155be1e5b8232c60b87e3f0b8396255231946cb9224c671f8335e1d86ac36549525a35138f35e1d87835645c9e48649e4b4aa250791c6e1f06ac8bc151e48762b0bc8e370c9347a26a49a309319c8e3f0f83369ad6eaca9324f48a271f05c3adf06ac8b9ad1a4869470b5be1d5b83c79ad1848a92eb7c345e0abd80ae5588e471b868bc1602b15e211782af56f0156aa0e2d13b19b7c3af7044a291a9593255233d46c66587aec55e2a0d4a6a27cfe270d31495ec8c237d13186d420e07cfd57ccbd09e0ceaf70836c1aa0cb16242f7d722b4c583a9e94589de4bf250920c8a642c1fe0f0c7143631998c305d32c294949c04892148edc6662dc13507bc30c138075029408a000fff61972503ffd635c940fff61974483ffd8650520fff60d41483ffd6350520dffe83925937fda0e4964fdf69792592fffa661d54dffe5d86552fffa85d954bffe9985506fffa859541dff61b945c3dfd865d170dffe51835c3dfd7460d70dffe51635c3dfd7458d70dff61b925c37fd83e4970dff58f925c37fd9761940dff65d835037fd9758d40ffe61970503ff9835c140ffe58d705037fd965d120dff661414837fd9650520ffe61970483ff9835c120ffe58d704827fca95d984dfd61b915d27fca961d64ddf697925927fda0e4964bdf69792592fdfa361954bf7e8d86546fdfa3619419ff68b965c2fdfa3619709ffe8996502fdfa3619409ffea58448377f9561120ddfe5574482ff7a15d1209ffea56448377f9559120bfee816448377f9558520ddfe554148377f954c520ffa58970482fdfa361910 else 0x5f283198742c045d2e4f87238b4ba398742c01762f0e45128a3829e4cc6c2d11874159cc14b24314e5824b1b0ac359c6212a52b0ac3c028e305845424924e1587804ec60b08a849249c366f2ccce471f87c19b4d44869319986cde5a1dc8e3f0f83369a9a)
def g511H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x157e88d4c00003fc40000000018c000000000000006580018f00000048800c6000386800000000000147160000008600000000000000000000000000000000000000273000000000000000000014c000000001d1000000000000000000000000000180c00000000000000000000000019700000000000a000018266f00000000485a02001048240000000000011400000000d04000000003e00c40028e0000000021300000000000000aa171264000000000000000000000000124000000000000005e80000000000052b6480b50
def g511D12 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x6c361c1968c488d8b2a350caca9871e13070d3d216e5a35ce322d02c2b47c8c35bc1968c468d8b2a35290e05212e7936713258a437361c399489e5b8d8c962d2d190f37326279d0848c6c3614d4b9e4c9825211b0d6d352e613278943cdcc63989e5b1d0f37317661867874b4d4c985b5a9e1e1d190e120b04967ad631d0b87438482c19e63b58c5b2a1d0e120b067ad5863174a2dc19ec35b8c3835209519870f0658ba31225cd4b4643c7c2c196258c977429290e5f065a30b8e0d4943c7c2c1968c63975b265f06598186316cb8843c7c2c1968c5d619724390b0d87065b1f18e0d6318a5cdc8c6c3c1962e8c5f972a283b0d6f065b1cd6310a5ce0b2485c361c156c7354436a92cc09c9896292a151107231b0f05591c92a5185c35bc156c8c736354624a9322a0d063320d979715aa4a8a8cc8c6c3585ea922a106095185796e315894643259e8c969374210e4e798e316e587439e8c5d9661931d1908e30d864e5a318a78a435b93968c429e38210986595632796c7c7c596c1c35b842536243e125b070e8530d8dc9c8c59bc3c196862637242c2414066f0f065898c890b0806c3c19b162e2436242e183b231f0f07026e58d8d534d9bc3c296c14c383720401d870e5b06321234b0a110f0ac8c6c384c18c96108d30402c1d6f0e5b06123630c8b0e0461c39ec1872c8c27283e1c19870e7b0520aa3098b0e5bc3c19e358c3220b01b0d6f04789a30a894ac8c6c3c1560e8c35209413231b0f047a309890a110f0ac8c6c39ec18c3528401d870e5b06109e30b0a110f0a0901c8c6c384c1968c26356f0f0a5b04ca30b8806c35bc1168c2e3823205f1b0f065830b8d49110f0b0ac8c6c356c1828c2e309d1f231b0f0578a4d49c8c6c3cd0987cc8423231f1b130f042e0a009b0d5712acd510a5d51b27fd3789854ad24ad2108e145d226d0f885d417200cfb07b53c31d6ce6870d3751b0cd18661319180cb785892af14eca284f126912cc910465223107c7f03d11d10dec68832117b0b0c52826911d085c3d81c90cf05cc290111077032c148071025009c000ffebb309fff95613ffb0cba7ff61d64fffcaac9fff92593ffb0eaa7ff61954ffebb2a9ffd85587ffb0ca8fff61941ffec2a83ffd65507ffb06a0fff58d41ffea9a83ffd865c3ffb06b87ff58d70ffeb12e1ffd87503ffb0ca07ff5d940ffec1a81ffd73503ffac6a07ff60940ffeb9281ffd62503ffb08907ff5d120ffeb2241ffd61483ffa82907ff4c520ffec3221ffd83443ffac6887ff60910ffeb1221ffd32442fff2cc25ffe4184bffcbac97fd97593f7b08b25ffe4964bffc82c97ff98552fff2eaa5ffe5954bffcc2e17fd985c2fff2cb877f5d970bffca2e1dfd745c2fff24b85ff66140bfecba817fd96503f7ac8a07fe5c140bfeca241ff970482fef22ba5dfe5520 else 0x8b4bc55bc3c196372c352a130e87065935312cb8b0a0e8b4b46844381cdcc74b12e2d2f166f0f0658dcc8d4a84c39bc1964d4b4c322e2a130e6f0658b934c8909322b47c)
def g511H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x109000539000000711e520000000000000000000003ddce465e14e0008db000c23000605f2400000000000000000000000000024cc3a000000fce00000001d000000000a0ed5b000000000a6c000000000000000000000462e190000000003ba7cc00063b00000050600000063400000000020000000051a7355867155ac00000000000063081b518dc4000f2f000d25b1c09e000000000000000000000000b01000f04000000000000b0b000464000000000000000426344dea2b072735d000000000b08e8400000000000000000000072874000000050260d000000000713000000000000b1eadc000000dde000000000000000000d12e2a00012c00091f000000000000000000ed2000000000000dec716000d10f0c000c36000000000000000000000000020000000000321a2900000000000034300000000000000000000000036e000000000337aa420363812b42d000550a32fc0000ac3000f83000de3000d57000d499da000aefb33000d31c7870f0000000008f200014aa0a051cd0000f1700000092e314000407000d5c000e59000000622b680000000003f8000078202013001000441010011002
def g511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2c4070d3424383310966ed8d1628201911a1cd98c4a702c38499221c1365a6866e68a911e3048704b0d182cb026e1b89b30f1c2c4c88d0cc9e1a30b11223439b30c1e1c0cd427a61b2c508141c202911a1c13cdda8c305488f1a1c282586172850919223c6890e0a92a446870899e18588ca2dc9ee2878da55b9303588a0f800ffd84ffd74ffd64ffd54ffd61ffd51ffd41ffd31ffd70ffd40ffd20ffd10
def g511H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3823e095528e7c41ec41000000102abbc2db88f40000009d34c08276bb3405000047c09dd1f80000004260007a14c49825814b2200006a4b13907400181b0000001e43e34edeea540013b161b04f5345f95105d0ec001a83000100000120da8760af04762ed5c0001179f9b000727d83d01841918d40000000002c58000000d5dccb0000fb200070535522827140000438404e09ac1e07830cecc20b3b57639146625cf5572288570047713baa50a2c3432000997381c00022000000000016add0322b0000000000383000000000000000019ad4c1d089606433ed0904a481630d91ee7000042db2128bd41c18895148e1c3581f221a67b80662a2593841c2d037702aebb4740000007ad9705c96f1882e4001817259a008410000ccc8001842000000000002c0006cc351000514114210e002142284080002040003105
def g511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1038c20609a611ff
def g511H14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x56003f27a0c6d6ba9c428462023c0000f976000000425b7001cb94d9520b970037341c000c10300041816b8c2a62661f5e49db002a70662403859a3
def g511L : Nat → Packing
  | 8 => (1,6,6,0,0,0,0,g511D8)
  | 9 => (4,5,6,0,0,6,0,g511D9)
  | 10 => (25,4,6,0,0,11,0,g511D10)
  | 11 => (60,3,6,0,0,13,0,g511D11)
  | 12 => (68,2,6,0,0,13,0,g511D12)
  | 13 => (12,1,6,0,0,10,0,g511D13)
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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511T : checkedTables g511 14 := by
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
end PEqualNP.Outside.L_meta_11028
