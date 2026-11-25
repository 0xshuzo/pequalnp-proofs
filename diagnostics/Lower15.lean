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

def g146Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3ff63ff63ff63ff63ff63ff63ff63ff63ff63f,0x49204920492049204920492049204920492049),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7fbc7,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff92409240924092409240924092409240924092),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8fdf8,0x24812481248124812481248124812481248124),(0x0,0x0)]
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
def g51Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff71fc7ff03fffff8f71fc7ff03fffff8f71fc7,0x710490a285040120710490a28504012071049),(0xbe838fffc07e3ff0be838fffc07e3ff0be838,0x4368db4c326089204368db4c326089204368db),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeee63ffffff803ffeee63ffffff803ffeee63f,0x8872490408512400887249040851240088724),(0x193dc0fffffffc00193dc0fffffffc00193dc0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff982db6e083060384982db6e083060384982db6),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def K51 := extendKnown K146 4 [(51,[]),(53,[33,84]),(83,[101]),(89,[49,33,100,84]),(101,[33,84,100]),(105,[49,33,100]),(149,[112,16,33,82,101]),(165,[32,16,84,116,100]),(166,[32,116,100]),(177,[64,81,33,50,115,99]),(180,[32,65,49,115,99]),(209,[64,97,33,50,117]),(325,[128,16,33,100,82,117]),(337,[96,65,33,50,48,133,117]),(353,[96,81,33,50,64,131,67,116]),(356,[128,81,32,49,66,99,116]),(390,[32,116,133,100,101]),(404,[32,65,49,115,133,99,101]),(452,[32,97,49,132,117,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V146 low51 (by decide +kernel)
def g147Y : Array (Bits × Bits) := #[(0x3f8801ff80fc7cfc7f1003ff01f8f9f8fe2007,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff878adb654a290a890f15b6ca945215121e2b6d),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc4f87e3fff007fff89f0fc7ffe00ffff13e1f8,0x10b892460c3210102171248c1864202042e249),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb978fffffff80fff72f1fffffff01ffee5e3f,0x12488104020200002491020804040000492),(0x0,0x0),(0x0,0x0),(0x66ff03fffffff000cdfe07ffffffe0019bfc0,0x26464930608040c24c8c9260c1008184991924),(0x0,0x0)]
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
def K147 := extendKnown K51 5 [(147,[]),(150,[32,116]),(329,[49,33,100,84,135]),(332,[32,49,132,84,101,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V147 : Known true K147 := extend_ok (m:=147) V51 low147 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe003ffc07ffffffe003fffff80ffd386b20f0f,0x41a8128d052280541a82502916291304a21111),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00007ff01fffffc007ffff01a37d4800f0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81311b160644c89893136232244d835c485555),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80001ffffffff80000003f407df000,0x5c05c18178702e01c0380bc38703340753333),(0x0,0x0),(0x1ffffffffffffffe663f7600ff,0x1602602058081301202404c00000642314aaaa),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000000000019dd38dff00,0x1803800060001c01c038070040808c9308cccc),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
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
def K55 := extendKnown K147 5 [(55,[]),(167,[32,16,84,116,100]),(213,[64,33,97,49,112,80]),(217,[49,114,100,84,82]),(229,[80,97,114,49,64,66]),(339,[130,50,101,83,117]),(341,[96,33,65,49,131,80,83,117]),(405,[112,16,130,49,82,99,101]),(453,[128,16,114,49,100,82,67,84]),(454,[32,96,48,116,133]),(465,[113,130,49,101,82]),(468,[32,65,96,48,113,133,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V147 low55 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe001fffffffffffc01fffd6a9bfc7,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa00200001401400a002000008040080420b249),(0xfff007fffffe000fff007ffffe00169f6d038,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc42429249891894c484252490904a140f4d6db),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000007fffffffff000007fffffff2b97e603f,0x9485249212212109284a492120902b90a0924),(0x7ffffffffffffff800000001369f81c0,0xe709c71c1c41c60e308c71c2391c1329f0db6),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000000000000cea8c5e00,0xf80e07e01f81f80fc0f07e03c1e04ea8c4db6),(0x0,0x0),(0x0,0x0)]
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
def K115 := extendKnown K55 5 [(115,[]),(117,[33,84]),(121,[49,33,100,84]),(241,[113,33,50]),(369,[129,33,50,100,84,115]),(421,[32,16,84,116,134]),(436,[32,65,49,115,134]),(484,[32,97,49,132,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V55 low115 (by decide +kernel)
def g151Y : Array (Bits × Bits) := #[(0x7ff001ff80ffc07ff003ffffe03ff4b12b0007,0x42a8d4251a148b42a9aa4a8a458a64b1235b6d),(0x7ffffe0000fffffffffc00ffffc068db9401f8,0x4c098362c191204c1306c0c891340d3841249),(0x7fffffffff00007fffffff0000000ff00e8e00,0x1702e0b8305e1c1701c0702f0e1c0df00cb6db),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000007fffffffffffff99af6d703f,0x180300c040602018020080300000190c082492),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000000000006754f2ffc0,0x600c0100008000600c0300c010202200724924),(0x0,0x0)]
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
def K151 := extendKnown K115 6 [(151,[]),(333,[49,100,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V151 : Known true K151 := extend_ok (m:=151) V115 low151 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe003ff0ff87ff007fffffffc3cd60cf6007c1f,0x48280a201120a45214820408801208d694a529),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000ffffffff801ff0fffc3517b820f83e0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff81304c412004c060980420900a403982318c63),(0x0,0x0),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0007ffffffe000ffffcadd91df003ff,0x2409002420900802028412000a54008421084),(0x7ffffffffff000004f27e8007c00,0x1382e08b844e0904c13009c1104d27296b5ad6),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000033aa61bff8000,0x1c03000c00700e0701c08e02211a86118c6318),(0x0,0x0)]
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
def K179 := extendKnown K151 7 [(179,[]),(182,[32,116]),(211,[101]),(345,[49,33,100,84,135]),(361,[49,33,100,135]),(364,[32,49,132,100,118]),(406,[32,116,133,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V151 low179 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff003ff0ff87ff007ffff87fffcd47c560003ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa4280a201120a4521481102080501c1694a529),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000ffffffff801fff87fc35353a20ffc00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0302c40a002c060580a01010a425122318c63),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0007ffffffe00007ffcafd11df0001f,0x140b002c20b0080602c220a00a741086318c6),(0x7fffffffffff80004d2fe8007fe0,0x982c08b044c09048130004c100d22c94a5294),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000000000033aa61bff8000,0xe03000c00700e0701c044702118a6118c6318),(0x0,0x0)]
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
def K181 := extendKnown K179 7 [(181,[]),(357,[130,84,100,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V179 low181 (by decide +kernel)
def g218Y : Array (Bits × Bits) := #[(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00fff0ffffffc00fffff0fffeea3a5303f03f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff84a08a210802284a0280220882200a53145145),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000ffc3fffff003fffffc009adfd000fc0,0xc42c405090b10c4b11404108092d994d34d3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0003fffffffc000fffd77e88afc003f,0x90130026104c0100c0584120152a08828a28a),(0x0,0x0),(0x3fffffffffff00012697f4000fc0,0x2e09c08b822702609026009c11269264b2cb2c),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000039d530dfff000,0x300e000c00380380e03808e0208d5104c30c30),(0x0,0x0)]
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
def g119Y : Array (Bits × Bits) := #[(0x3fffffffffe0003fff97e43a62aa9edf07c1f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa800128000a4005800a05c00862081c0108421),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00003ffffffffc0000b5fc47c9174a0003e0,0x31149b1148c824904930b4e846c8154ab5ad6b),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000000000000676bada15c4320f8000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0581c0582f041e083c27692ca058432739ce7),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe819707c5fea40003ff,0x2612026130089011206011701056a254a5294),(0x6456978fe62520ffc00,0x381c0381c010e021c04016930da62018c6318),(0x33aa5b8895b2bf00000,0x3fe003fe001f003e00322a538895a2bef7bde),(0x0,0x0),(0x0,0x0)]
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
def K119 := extendKnown K218 7 [(119,[]),(123,[50,101]),(125,[33,49,84,100]),(249,[49,114,100,84]),(371,[130,50,101,115]),(486,[32,96,48,116,133,83,67]),(497,[113,130,49,101,50]),(500,[32,65,96,48,113,133,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V218 low119 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8001fffffff00ff1d203397a2ac000003f03f,0x520d4825205216141d002390a2a91451451451),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0007fffff00637e8b807608003f000fc0,0x60498136046424262336098066085145145145),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800000009d8e48e9a5400fc0fc0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff800e003801783838150a48c1a54030c30c30c3),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa049c585ccf7f000000fff,0x900240098000008048c0050854a28a28a28a),(0x9175383e5b400000fff000,0x4e013804e0040408075102e5802cb2cb2cb2c),(0x0,0x0),(0x4e937660389bffff000000,0x7001c00700080804881362010830c30c30c30),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(2,0,181,0,7),(4,0,179,0,7),(0,32,146,5,6),(32,0,151,0,6),(16,0,167,0,5),(128,0,55,0,5)]
def g183A : List (List Nat) := [[],[32,116]]
def g183D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4f77159653
def g183D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x410826284018a1141f3185b2c0bf59653fdd8553d7d4e53bdd8553bd58453be58053
def g183H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa0
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x190e2a5474365a891d90ea6147888807f94ffaa7fc53
def g183H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x240000550000000018000000000100000000b0000000005200b30000
def g183D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def g183H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3c03969000000000000000000000
def g183L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g183D5)
  | 6 => (6,2,3,0,0,6,0,g183D6)
  | 7 => (3,1,3,0,0,7,0,g183D7)
  | 8 => (1,0,3,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g183H6
  | 7 => lookupWord 1 29 0 8 3 1 g183H7
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
theorem g183P6_0 : block g183 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_4 : block g183 6 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B6 : block g183 6 0 6=true := (@block_merge g183 6 0 4 2 g183P6_0 g183P6_4)
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
def g215Y : Array (Bits × Bits) := #[(0x1ffffffffc003ffd524a373e833c0007c1f,0xd4804a40148058051520013288339294a529),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000fffffffc003ed51a38816c800f83e0,0x14980a6c0519049049be541230016086318c63),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000073b22915bd881f00000,0x58e02c70165e09e09e063922115bd88e739ce7),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc859e43c4e4f7e0003ff,0x6100308018601101100009e00c420c48421084),(0x0,0x0),(0x4569b47773c00007c00,0x7e013f009f801e01e000569a45770c2d6b5ad6),(0x33aa5dc49781bfff8000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8001c000e00020020001820dc08401318c6318),(0x0,0x0)]
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
def K215 := extendKnown K183 8 [(215,[]),(407,[32,116,134]),(461,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V183 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[(0x1ffffffff003ff1d10d5daa29900003f03f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa0d4a094a052459141d0015da2288451451451),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0001ffffffc006fd62ae3438003f000fc0,0x49804d804640902627122ac30180145145145),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000009dae8e542564000fc0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0e0c0e0c1788e2381dac8e5021644d34d34d3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa06594e1393ffc0000fff,0x900090009800000080448020103728a28a28a),(0x0,0x0),(0x915a691ddcf0000fff000,0xe010e010e001004080526005dc10b2cb2cb2c),(0x4ea977125e06fff000000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff001f001f000e038048a955104e00c30c30c30),(0x0,0x0)]
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
def K219 := extendKnown K215 8 [(219,[]),(347,[49,100,135]),(462,[32,49,132,84,118]),(467,[131,83]),(470,[32,99,116,83,133]),(473,[49,33,114,100,82,133])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9961a4fab95940003ff,0x5140152804a500a480a1921244a9119094a529),(0x0,0x0),(0x3ffff80000ffffe0005df06f136450a0f8000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9814a602b6c054c81335c70671364408739ce7),(0x3fffffffff00000000053e3e4d5a478007c00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe1813830270606f105c013a2e491a478b5ad6b),(0x3fffffffffffffffffaa58e2545fea5f0001f,0x19c003380067002600250c2144e6246318c6),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00000000000000000245795afe6252007fe0,0x21e0043c0087800380244491a4642034a5294),(0x73aa5b8895b2bff8000,0x3e0007c000f8001c00218a1888919038c6318),(0x0,0x0)]
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
def K221 := extendKnown K219 7 [(221,[]),(231,[80,49,33,98,66,64]),(237,[80,50,114,64,98]),(343,[96,49,33,64,132,116]),(413,[32,116,134]),(455,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V219 low221 (by decide +kernel)
def g222Y : Array (Bits × Bits) := #[(0x0,0x0),(0x3fffffffffffffffff99c559a751938003f03f,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff814150284a050a421498055087411305145145),(0x3ffff80000ffffe00036ad462289af40fc0000,0x58a60b36c164c846632ad4622898f0f3cf3cf),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000067a74def58a00000fc0,0x1013820270406f00b806727484358a134d34d3),(0x3fffffffffffffffff58b1cca8bed4bf00003f,0x61c00c380187008c000b00c289ec48a28a28a),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000000000048af2b5fcc4a40000fc0,0x27e004fc009f800f00488d0b5bc8406cb2cb2c),(0xe754b7112b657ffff000,0x3800070000e00010004540a110202070c30c30),(0x0,0x0)]
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
def K222 := extendKnown K221 7 [(350,[49,100,135]),(411,[32,116,134]),(459,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V222 : Known true K222 := extend_ok (m:=222) V221 low222 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff36d7f4aa09de8000fff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff802a0a01282805210143646c0a809880249249),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff000003fffff0000fbe04ebf62231fc0000,0x294c00adb002a640266f8e0463e400311c71c7),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc0000000000a7c4359bd0f703f000,0x2702c09c0b037820b802744119ad0f36db6db),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff54b1674157ff000003f,0x3380b0ce02c338044c040b1274156770db6db6),(0x48afbb7e9c20e03ffc0,0x3c00c0f00303c00870048893a461020c924924),(0xe754a985f269dfc0000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc000ff0003fc000f8000714a981b268ce38e38),(0x0,0x0)]
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
def K235 := extendKnown K222 6 [(235,[]),(252,[32,49,65,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V222 low235 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc003ffd76f2131c876400ffc1f,0x4200200010008008001128002088721294a529),(0x1ffff000fffffffc003891d26fa15c81f003e0,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8048404a0249012012b8110263015486318c63),(0x0,0x0),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000000ffffffffffcc308eba768b7e0003ff,0x928094049202402404008c18648848421084),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000035364166f4d80007c00,0x14e30518a71c14714702536416670dad6b5ad6),(0x45e9b45573c000f8000,0x18fc09e0c7e027827804569b45570c2d6b5ad6),(0x33aa5dc49781bff00000,0x1f000e00f80038038003aa51849201318c6318),(0x0,0x0)]
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
def K243 := extendKnown K235 8 [(243,[]),(377,[49,33,100,84,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8007fffffffffde2d8339c932c00f83ff,0x4200100100008008001a29002080321294a529),(0x0,0x0),(0x1fffffff8007fffc0039d3724fa05c01f07c00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8028a02402500a1011b953224b001006318c63),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe00000000007ffffffcd320e9a768b7e00001f,0xb2c04e04e02ca02505120e1a64884c6318c6),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80000000251e4366f4d80007fe0,0x14c30288288530c1460000c4146f4da94a5294),(0x45e9b45573c000f8000,0x18fc04f04f063f027804569b45570c2d6b5ad6),(0x33aa5dc49781bff00000,0x1f0007007007c0038002a851849301b18c6318),(0x0,0x0)]
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
def g469Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcc65acb88be2400003ff,0x5240a92025012404a00c04aca083a22318c631),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000ffff001fffe003b843a5ae0e501f07c00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff801ac0094034014805a980225a806506318c63),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000001ffffffef3b03d9111a400f801f,0x413020d805841900923390358101054a5294a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000002059e5744e4dbe0003e0,0x9c004e006009e00e20590054484d8c6318c6),(0x24569a07773c000ffc00,0x18e00c7009818e0130044698056708294a5294),(0x13aa5dc49781bff00000,0x1f000f800e01f001c012225d801780318c6318)]
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
def g474Y : Array (Bits × Bits) := #[(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc1ffffc92d389940f740000007fc01ff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff80a2008441100829308000f708a45229148a45),(0x0,0x0),(0xffffffff81a52a0abb8d8801ff00003fe00,0x12c0450008209a50a02b1090026130984c2613),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00001ffffefe1835e2102c0000ff80001ff,0x304160882402700815a2100d148a45229148a),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe0000209965726e4d3fe0000003fe00,0x240098001381208141106c4d0582c160b0582c),(0x24d69a05573c00000ffffc0000,0x3808e0111c0200d60a05560826130984c26130),(0x132a5dc49781bffff000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc00f0021e004012a1cc48300b81c0e070381c0)]
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
def g223Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffee8241494599e356c96d8bc0000003f03f,0x2aa8e8041490518e156c9040b411451451451),(0xafa9ffc3060045308544d6c003f000fc0,0x44ccc2a29dd82020045108544d685145145145),(0x152be74a28b17908953a196c0fc0000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8f0f142be74828a13900953a196cf3cf3cf3cf),(0x13b5ff181f8265b2429212d00000fc0000,0x17f00395f71817826592421212c134d34d34d3),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff40cb260d0ce115566a936eff000000fff,0x1800100c2220d0c6100004a91084a28a28a28a),(0x0,0x0),(0x122a49a54f279ea821f695300000fff000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000102a08a448251a2820e08432cb2cb2cb2c),(0x9d5249ea134f8aebe00ea03ffff000000,0x95000060110c0ae2200a2030c30c30c30),(0x0,0x0)]
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
theorem g223G : graphValid g223 (boundsBefore K474) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 9 := lower_forest (g:=g223) (i:=0) (hints:=268461892) (before_sound K474 V474) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K474 9 [(223,[]),(351,[49,100,135]),(415,[32,116,134]),(463,[32,49,132,84,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V474 low223 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbe2d6552da519822172148000007f01fc07f,0xa320c41000251982215200042850a142850a1),(0x219ae929cd02cd5c2576030003f800003f80,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff93000ae901c802cd5c256201162c58b162c58b),(0x508339d4022db3c4743ab501fc000fe00000,0x3c1083215402098304743a950e1c3870e1c387),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffdae1033a21ca4909c8d7b0fe000000003fff,0x2048a1003a21880000c095b02850a142850a14),(0x44265e8bd6a26643e024ae0000000fffc000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc044201e8bd4a2644180042ab162c58b162c58),(0x48b9a4e4bcb285e17a4455000007f0000000,0x48b1a4e4bca205c16a4455bd7af5ebd7af5e),(0x2754920534ad14b58f8813fffff800000000,0x27541200142410a10a0002c183060c183060),(0x0,0x0)]
def g247C : List ColumnInfo := [(64,0,183,0,9),(0,64,182,1,8),(2,0,245,0,8),(4,0,243,0,8),(32,0,215,0,8),(1,0,182,0,7),(1,64,182,0,7),(16,0,231,0,7),(36,0,211,0,7),(128,0,119,0,7),(0,2,101,144,6),(0,4,83,160,6),(0,32,146,5,6),(32,64,150,1,6),(64,32,146,5,6),(96,0,151,0,6),(1,32,146,4,5),(2,64,180,1,5),(4,32,146,1,5),(4,64,146,1,5),(6,0,241,0,5),(16,2,101,128,5),(16,64,166,1,5),(18,0,229,0,5),(32,4,83,128,5),(33,0,150,0,5),(33,64,150,0,5),(34,0,213,0,5),(65,32,146,4,5),(68,32,146,1,5),(80,0,167,0,5),(128,2,101,16,5),(128,4,83,32,5),(130,0,117,0,5),(132,0,115,0,5),(3,64,180,0,4),(5,32,146,0,4),(17,64,166,0,4),(37,64,146,0,4),(82,0,165,0,4),(144,2,101,0,4),(146,0,101,0,4),(160,4,83,0,4)]
def g247A : List (List Nat) := [[]]
def g247D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x70c100000000000000000000002c30602040038604204282000000000000000000000000000000000e101e101b5592a94ea450a7936984aa491e8c44a1906803e9d4da6a3397ca44f261248c43200f474371a0c45c2b14094441f0e0642c130802000af3c9309b8ac75e7925937158fa6ac8aa6e2b1d5de4d54dc563af3c92e9b8ac71f7985d07158ebcf24ba0e2b1c7de61721c563a7bcb2e438ac71f6981c57058f3af0638ae0b1d5e653855c063cbbba702b1aa795f84dcd535878eaecaa6c398ed555183d8731f2aaa2c7b0e63577915d9544c787eecb22a898f9555163585318efcc2e639ac16cd921cd63582dab2239ac6b063721d634c960aaec9d0cb9ca155f9361973942aef22c32e7287175d36398e50cbaba702b1ca197573e05639432dae8c10c72865d5d18118e50cbcba30031ca13779160f629426ef22c32652865d61f61cc650d3ac36c398ca175593d8731943caac7b0e63284dde45864c650f2ab1ac298ca127f9660d21942aeb2f98a43286d5e0f3148650cebc1902bb2619b774e05634827cf22c1ec4906f1e0f3148520
def g247D7 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0xd80dc961edd634c961bef8259331d7d7655331f3d6455331f5d5458f319ff805cb31f7554d8731bf582d8731df7615c331cff7659131bef8259131d7f7655131d7d7655131f3d6455131b7f8355131f5d5498d31f5d5458d319fd80dc931f7554585319ff805d9219ff805cd21bef8058921bef804c921bf78058521bf580cc5219fd86dc1219fd83dc121ded32dc121afd869cd60ddf739cd60bf7815cd60ddd731cd60bed821cd60bf5811cd60afd8698d60ddf7398d60bf98098d60edf7358d60edc7358d60ef78158d60ef48158d60ddf7358d60bf78158d609fd83dc9609fe87cc9609fd87cc960afd86cc960edd63cc960bf980cc9609ff874c9609fc874c960edd634c960bdf835c560bdc835c5609fe87cc5609fd87cc560afd86cc560edd63cc560bf980cc560edd634c560aff8648560d7e865ce50d7d865ce50d7d825ce50d7d815ce50d7d74d8e50d7d73d8e50b7d82d8e50b7d81d8e50b7d8698e50d7d7498e50b7d8298e50b7d8198e50d7d7458e50d7d7358e50b7f8258e50b7f8158e50f778158e50f748158e50d7d7418e50b7d8218e50b7d8118e50b7d83d8a50d7d73d8a50b7d81d8a50b7f8358a50d7d7358a50b7f8158a50b7d86cca50f5d63cca50b7d81cca50b7f864ca50b7d864ca50d7d734ca50f5e634ca50f5d634ca50f6d624ca50b7f814ca50d7d74d8650b7d83d8650d7d73d8650e7d63d8650b7d82d8650d7d7458650b7f8358650d7d7358650e7f6358650e7d6358650b7f8258650b7d86cc650d7d74cc650f5d63cc650b7d82cc650f7761cc650b7f864c650b7d864c650d7d744c650d7d734c650f5e634c650f5d634c650b7f824c650f75614c650b7f8648650b7d8648650b7f8348650b7d8348650d7d7348650f6d6248650f6d3248650f756148650f773148650edf6398d40bf78158d40bed8218d40bf58118d40bf98018d40bdd839d9309ff835d930ddf835d930df7815d930df4815d930bdf835d930bf7815d9309fd87d8d30bf980d8d30bf78158d309fd87d8930bf980d8930bfb804c9309fd87d8530bf980d8530fdb8358130fd88358130efb6358130ef963581309ff835d920dbf7498d20dbf7458d20bf78158d20bed83d8920bed81d8920bef814c920dbf7458520dbf74cc520dbf744c520bef8348520fe73148520ef963581209fd83dc910ddf734c910bf582d8510bf7824c510d3d64dcd54e5d54d8e63d7554dc563d6d545c863d75545c463d7b855c063d79545c063b6f8259153b778158d539f7815cf629f7815d932d5f7354d61cf576d8731bd583d8731ed563d87319f7815d931ed563585318ff865cd21dd773cc52197d8798e50e5f6398e50b778158e5097d8718e50b6d8218e50b758118e50b798018e5097d87cca5097d87cc6509f7815db309f7815d9309df835d910cf776d8510 else (if j<2 then 0x1012860b01860814020080044301c205a182050040018290c070c0ec1083906080f06080f06080200084141a00742070981c0078407080e101a10342a0d0030308030b08240848200804080c1020e083111060f870983b118c2f0d88c60e0e1884b1846041f8709630ac16041c384f0d8825128980c30780c3041584f0310205711c00e8c0a1c2fc00f801508421743f0040af0020142b8029102b88e00614e007f10200018470c938023e044c06042066008e19270047c08849c0e008e207b02470c0148238600065088e241f81860f81860b8186083fc00ae184a8053ea9b34caa50522290547ca32510e86941ca024fb27bb3c59dfce9e71f3809b8cd8a6b935699acc7662f2ff97ccbaa5c92cc95ecaba53f27e933493a46d227910c8263e31d98e546ee35919d8cbc5fe2cf1588a944ea2330f8879438e1a90bc85b427a11f080834416609503b8164051ff8fe47eabed1f5cf847babd75eaef517a5bccde5af27790bc25e06efd7773b59d8eeaf74bb9fdce0e58724b8c5c32e136fdb7d5bbadc56d6b655afad6e6ab351da70d20688b4099d4cd265d3289926c8d63f319988ac3660f2fd17b8bbb5d1ae516f8b645aaacf564aafb571ab7559cac85612acd536a95547aa014e2a6b532a9594a0a1d50ba8454049f34f6a79d3c29db4eaa73d3929c34da26b93509994c526112ea96f4b0254529694549b24c125491b48aa43d1dc8df46ca34d19a8c7460a2ed16a8a6450224511688543b219d0c2852421a0d104a80d3fa9f74f8a7a43c61dd0eca7443919c50df86d235d1a88cf0660324189cc0c5ee2eb16f8b4c58e2b69578a7a52e28f9440a024e026d130895449224191d08dc45f21f102c7d43c01c68db06843211848b7c57c2af14709d849823410507a437e19e0ba0570276111073831814a07b02d0108054000b7f8355363d7d545c763bef8259263d7d7655263f3d64552639ff805ca63d7d545c663bef825d163bef8259163f3d6455163b7f83551639fd80dc963df584dc563df564dc563df582dc563df580dc563d7d54dc5639fd80dc563df574dc563f7554dc563df572dc563df5741c563f75541c563df5721c563df7715c163df4715c163d7d545c463df9845c063b7f8359153d7f74d8d53b7d82d8d53d7f7458d53d7d85dd943cff76d8d43cff7658d43bf78158d43d7f7654d439ff835c3629fd80dcd62bf78158d62d7f7354d629fd80dc5629fd83dc1629ff805d932fd78158d32fd48158d32cff7658d32bf78158d32d7f7654d32d7d7654d32f5d6354d32f6d5358932bef80589329fd80dc5329fd86dc132b7f8355361d7d545cf61e7d5458f61b7f8454f619ff8750f61d7d535cb619ff835c361cfd635c361bef8259161f3d6455161b7f8355161d7d54dcd61e7d54d8d61e7d5458d61b7f8454d61ddf7350d619f else 0xc43c103021381c00682041e8961c04400800200084e08244b0f041e0810080026230c26230c26182c0630400018c106d86140810a02c3040004741a00741a00403004a1010704083d08200038404180e1303800c3c010802000802000b06080010004010004010005830706082c1c1820055041309121424100020008140301060c82608302040e081008002000200080e0e08161e082c102c106040c08183e082a081020080020a8382c0e003001ec3c140448102010004000050c08100000896184001020402000a12080400100400142404100818480c20182030104010004001c0a101c0c305866105c0c305c0c30407028586040e05080e0e18183e182838200070186081402080200080200080a08009040200081402100620078186081542e06184008002050040018280a142810502420b87c2028210620416610413083118620458410047040008408341810005081a1020004204002d0e840d060a00042068608000000000001081000218247040a10205081210200181040008408005081a0c0c8408000000000042040238200043049208042048409241218380c30580c30580c30580c305804301030490420080021283860170030561b8018941e0618205008020))
def g247H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4400000000000006d60a1d00000000000032a000000039b0000000000000000000000000a380000000a7c000000000000000000000000000000000000000000a2b1900000fafc8a1400002e20000000000003cfb1800000000000000000ab0000000000000e87560710d000000000000000243530000000000098009261ab5400e6000ca3e4003c00000073000000000019729c0000000002ef0000000000000006a4ae0000000000d8e0100000002540000000000f1c0000000d2d257440000383000000000000000000000032000000000000005e00000648000000000000208408801
def g247D8 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x3078c072fa0bc92ee8ba72e20b6d2d38b372c80b052b98acf2ac0a9529c8a5b2900a2928089eb27609c526c899b2610965255894324d090d23c88d723008b1222887721a085120f882720507fd1fa87cb1ee07a11e3876b1d707411ca87131c006e51af86a71a40669191862318205e917185a716205691528533147050113a84cb12b048d11b845710d041910183e30ef03a10df83570cd03110bf82e30b302bd0aa827f09b024908c821b08101e907581b7068018905c815b04e012104280e703100a10238073017004500b80170001ff59263ffae8b1ffd6458ffeb92c7ff5c163ffec6a1ffd6350fff31ac5ff58d62ffac6997ff714cbffb8265ff50f61ffac8b0ffd43587feb12c3ff4c961ffac998ffd62cc7feb2263ff50d31ffac498ffd324c7ffb9ac1ff9cd60ffae6b07fc73583ff31ac1ff58d60ffee4b07fd72583feb12c1ffcc960ffa64b07ff71583feb8ac1ff58560ffe62b07fd31583fe90ac1ffd8d40ffcc6a07fd63503fe31a81ffd8540ffac2a07ff31503fe98a81ff58b30ffcec987fd764c3ffb1a61ff58d30ffae4987ff624c3feb1261ff4c930ffae2987ff614c3feb0a61ff4c530ffa42987fe63483feb1a41ff58520ffe62907fd31483feb1221ff4c910bfae7b25fd71d92ffb9ac97fdc564efaa9b1dfd72d8efeb8ec77f5c363bfaed31f7d5498efeb94c77f5c663bfae131f7d5458effb92c77fdc563feee2b1ff47158effb82c7df55063bfae431dfd7118efeb80c7dfd9153efac8a9f7f6354fbeb1aa77f5da43bfae321dff7650fbea9a877fdc543bfae7b177d53d8afeb8ec57f5c362bfee6b177d5358affb8ac57fdc162bfaed997dd63ccafeb8e657f5c332bfeec995fd764cbef31a65f758d32efaa6997ed624caffb8a657fdc132efaa9b0dfd73d877eb1ec3df54f61bfae5b0dfd70d87beaa2c37fdcd61dfec6b0efd63587bea9ac37fdc961bfee0b0dff76506ffb9a83df54d41bfaed98f7d54cc7eeb1e637f5cb31feec398dfd70cc6ffbb2637f5d931efaa898fde634c7eeb1a63df54d31bfee498ff5614c6ffb82637fdd921bfaec90dff73486feb9a43df54d21fdac490fed32487fab0a43fdcc521bfee090dfd73d837eb1ec17f5cb60bfae3b05ff735837fb1ac1bf58d60bfee4b05ff71583bfb1ca1df98e50efac72877c63943bfb14a1df58a50efe652877d32943bfb0ca1df58650efe632877d31943be90ca17f5db30bfae5985fd71cc2ffbb2617f5d930bfee4985ff714c3fcb02617f5d920bfae6907ef62483f699241fb48520ff2c0905ff76442febb2217fdcd10bfae6885ff72442feb9221fdd8510fea62887f521443fcb0221fe4c110bdee4b273d64552bfb9aa9b7d8e63beee2b1dbd7418ef6b90c77d5c463bf2e031d7f7454ef6b94876f5d332b7ae9b057d74942beb9ca16fdd120 else (if j<2 then 0xe042b1038288050b860e021405103830ac4c12344070c023f10382a282816044140b108c501e044108a880e05803f108c3058281144460110e8104508d10282a160440a8a140e0581108c4438382810ae044100f8110501c4600f8b88120402002b104a38502e16044100c44140a0511804038ae003c4100a3e0f8110402c48ae103a3440c3e2a120f8010403828ae0440f8a1614120581108c38643c12423448c180a08064105802a40b9060410a8a1d0907048c2a324416005910a12180e08070580408c4c4c3c123240b8d80422a20160108a882a058052203c10aa3148a160b809052286058201e023148e203650188070a8d89108c5018605828201c160038f921f13048c910e3109003e0410f8c0e0b8090402e024c38618161208060381044a4e1e00f8b898014521c4c3c124230a3f802e2a21003e0410f8b048c504e202e010240b8a14138052206058201e023148f1180285020a02e0440a8b811028502058482c10ae0440f91108c5018584e04104140d810410402a284e010440a8b808f103e20483e044230a0c181208060441803f0c490276043140a91810c164428605848201e021430a92181608065185810c412900fa7600a84c3100e9c1380510c3050381604305a40e1816080780850c2a40723a221a142a48e1c928886850a8e3872221a124a3c28e20928886850a8e3a3a124c2a40a928e850a9028824a142a4238c928e850a9028723a221a142a48e1c928e8886850a38724a221a142a38e1c928e8886850a3a4a3a124428a1816080605810c5040501604324100d810c142e20605820181601412904a181608060451810c48501604324100c1816080780850c3e412900f8a8e60048383121c140e0581110c4041207050160444310110980924c20ae003c304100d088580404c2e01013060b80504620f8605838201c160430a940380504620a86058201e0430f900f810c90402870fa4430a8a9d80930c2a2a703e00fc30a8c3f0c902a2100e04e00341140e39800d045028905c4e10e0a938418110c2a3e10783440a418c2b84120f91804630f8ae4600a2b84120e38291630ae10c0483e010402e158d9013800e4100ae103e064049290184e0c90209058ae1038e0c2b85060e3828fe104c30e8a1b840a18902e1028b64080a4185061d0c2d8f1629584960357b15d156c959b562156d558955354e152153f94eb53714bd528948751b14595119433509140d4fa93d34ef13a94e1936f4d4133d4ca930f4be12dd4b292ab4a5127d499924748b121147d91e347311b5467918f45e1159450912b44610fd43990cf42f10a1420906741210254018feb3f50fc53ec8f9f3e30f713d78f4f3cb0f093bb8ecf3b00e993a08e6b3920e2d3858df73760dc136b8d8335d0d5d34e8d1b3410cf53368cbf32a0c913208c6f3150c35 else 0x87030018542a1a115140888870418542a11114064a8480508c28483c0c006420c180e85030013083c1a0a010110b06844044205a1600483c18c841612005a3068280188904143060521a2410a42140f0482808818405818fc10904422a1a1c0c0150641050f03004417043e30b85048221860c18148280890430b852185881614870420483e043080f810c1942112e0430a380e88868413810c40483c020430a1285010c502c360219008484438168887810c41105c021c30a12888700380f0c381c0c010090d80843e21190852160430c421500850c284c0202105430d03002e3e204a140c0100a0f8e321900130c2c0200c86430a850032190c2a1a140200c86430e32188500130c30c86214005430c85008032190c3400b85430887010c441628e2212e0430a84504b810c2c012c3064a8500510c2920e05a221e0430e4a8700130c2a1c01105c30a1700070c2118b852160430c4b00850c2a2a14010c30a8b002a2f0c205a140430a8a0d090283008048403c22140c012100c421508070300403c22140a0c0201205902e150807030016391058140c00f8c0f0300462a2c40e14068510382a205010e15091084382a20643c12423448c91801644260108a861808060441803e8c40602820181106014101f1304908d0e3050382816005a40f80142e186058201810ae003a31305130e908c28582e024140a18160a080780842a46362618160140d8d89878050286058201e023140e1e190512908d0e3a403e005910a1380142e204860ae261e1601003a314910c501a10aa443070a1c88862b840f0c9240703a221a143140e))
def g247H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1828cd5cfd682c2a000041b04692bbc8a70992d22e1995e64e5ea083165ad5286bafc000658085e43f863475069c9b71b9440288723390cd13c2b9b7c000a09c3588c84a00001417b9c5ca049a34835e40a0000007a1fc28000d0ac3f00012c870eb86098eebbb08e0aa0dc4e8e3a3378d40000d62ea99114000f48493b8442d213d80c256fc6ff29f82c000c16e71a11cca94a913c8001447685a15eb0b61ce0ee8460b84ed09ea4400004ee8032758002876cfa0002b90e240f07138ab30ac6afc52525646c826b60d813d8947303f78ce85964f31ff99797c65220469c11168ad325fb395f00000006b769dc85905d10e5dd98b100018784218ea00021fea22000448a268000000d2acac285241af4230bc5e8694655aa840016000004a4d93aa0f7637353c7dcfea861982d980488256b0f1ebe51b1ab1a15daeb9678da5d1ec6464805a3d202281767b0734f0cb4a1e59f45c2c0644ca2ce9cc87cc16e979112ea317bf9eb20e6d65109bbd13e002912d36e5e4428a6cf2d61390aa15e1ba7d44a17e335b37131271265e907dc44a5c3930dcdf305d38558d3de650626c183203f8b6d12416c0d8612a0c80030bf302e7fb1868cf0c0164fa0fcc4a4ce1d504c000263881a10d1a2000a53da4948570464b4836d37ce084063ec0004da00009365a0e44e2e60f7c70e01b470000001c0701176502062492013b65001f52110000980602085b6505cd4001213f031b143b2111043709361812066e04100c59000041000e0619090b000001430001013a0c0008070036
def g247D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x39f842441c183898420e0a3901f0f1a148802491c04a898d0a4400e4821c243c28d220282500e080c1062b1a109910039a240802b083883840902003c2107070f1a128802440e2438b8d09140104201204ac68500407244878d090401038e0e80ac6900a009247090e863029101412243a8107051c2409f8d201400e48e121cbc6052202824a090f18140502080e1101f8108e481218a0f004c2392030e003421c20d0c2614038a24070c4090f0212539203102438403010424c423121e01c0521406261080c1800f0a4061484290144ca58a6f259fab53e65dc8489b03de539369cc257029b4ac860e61952ca49c748ab0cc12c11000ffd93fd64ffd8ffe63ff58ffc63ff90ffd43ffd8bfd62ffccbfd32ffd87fd61ff507ff31ff4c7fd21ffd83fd60ff503ff30ff4c3fd20ff4437d54df54f7e50
def g247H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6cc00094a1547689887bbcd500092ddd1987673f14eb5000000000f40c38981000e2bf8d5df0000000007630004cfb0a00000077c000000b5827dbabec12531ddc3b0190001d9d610000000002862b3744196000dd05adf4d39b000c1a0000005300006d6000b3c0db7842bd8668a176a00cdc0a64000192831169d32f09180000404000acb7986b76acb9100000000000042f000000000000615f0d1da220000175000000000dc67a6ebf4a3000000abc7d3000000d95179fb1000c05a4f52e4dc000676a944c200000000024130e000000e9f54612c84b0002aea3600000003f2d4d7096220b97a000acaec5000000ca70000000003c8710000000000000b85baf000389cbec1c00000053465195b516000be00009251747bab775d83a9000c7b66b36d52215700000046fd23497c8f00090700000051f25d0009b80006aa00000089d000c03145000e2aeb04654130004cd000000b52000b26a4858e000000000d5005500096e000000ab600025c000000000000000000000000000000d5abce0003a80001a00005d7660000000000000fa508300000000009a000093000000e1e000c4e00066797e000608f4c000490000000bb4ad289c9438355a2c27000b5627fe0f00100000028a2c46720000b287153a00000043ee374590000c3d3df02f8c933b1d947b5fe7800000001bfdec248180b9b8b2007c9028e9ee2100000000079976c000617000000000000c39ca4000729c5ed12000000ec7211982942000806000a49fa4200802140b27bb40630900088210868008c3200001a0001200c0680883844128020
def g247D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x30440027f
def g247H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a16a15c00f59580000000000000009d8680000000000000000000067000000000578000032000000000000280000005200000d81140000007980000000000000f600000430000285ae000000000007900039000000158000029a000000000003480000f10000000000065800000000000b300000600
def g247L : Nat → Packing
  | 6 => (48,4,6,0,0,9,0,g247D6)
  | 7 => (276,3,6,0,0,13,0,g247D7)
  | 8 => (225,2,6,0,0,14,0,g247D8)
  | 9 => (28,1,6,0,0,11,0,g247D9)
  | 10 => (1,0,6,0,0,0,0,g247D10)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 12 179 3 10 6 0 g247H7
  | 8 => lookupWord 69 307 8 13 9 0 g247H8
  | 9 => lookupWord 56 367 5 12 8 0 g247H9
  | 10 => lookupWord 7 107 2 9 5 0 g247H10
  | _ => fun _ => none
def g247 : Forest := ⟨247,10,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : block g247 6 0 48=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B6 : block g247 6 0 48=true := g247P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : block g247 7 0 32=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_32 : block g247 7 32 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_128 : block g247 7 128 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_224 : block g247 7 224 52=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B7 : block g247 7 0 276=true := (@block_merge g247 7 0 128 148 (@block_merge g247 7 0 32 96 g247P7_0 g247P7_32) (@block_merge g247 7 128 96 52 g247P7_128 g247P7_224))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : block g247 8 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_16 : block g247 8 16 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_112 : block g247 8 112 44=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_156 : block g247 8 156 69=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B8 : block g247 8 0 225=true := (@block_merge g247 8 0 112 113 (@block_merge g247 8 0 16 96 g247P8_0 g247P8_16) (@block_merge g247 8 112 44 69 g247P8_112 g247P8_156))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : block g247 9 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_3 : block g247 9 3 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : block g247 9 0 28=true := (@block_merge g247 9 0 3 25 g247P9_0 g247P9_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : block g247 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : block g247 10 0 1=true := g247P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : checkedTables g247 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g247 0 0 0 = true)
  · exact (rfl : block g247 1 0 0 = true)
  · exact (rfl : block g247 2 0 0 = true)
  · exact (rfl : block g247 3 0 0 = true)
  · exact (rfl : block g247 4 0 0 = true)
  · exact (rfl : block g247 5 0 0 = true)
  · exact g247B6
  · exact g247B7
  · exact g247B8
  · exact g247B9
  · exact g247B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 11 := lower_forest (g:=g247) (i:=0) (hints:=268436804) (before_sound K223 V223) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K223 11 [(247,[]),(439,[32,116,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V223 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff785cbaaaa2a40d5b2c2c0e0000000ffff00ff,0x47008a2a22220014b2c0004021212121212121),(0x5217c25ccb4a338e639105b00ff000000ff00,0x61015c248c208318c609105a0b0b0b0b0b0b0b),(0x0,0x0),(0xb5a4677636101c5a51f250f0000ff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff834a4267636001c5a41f250367676767676767),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa5e216834129cb24837ce13ff00000000ffff,0x81e2100101008a00836cc0114141414141414),(0x886cbd4c86db6ed18390d3800000000ff0000,0x88641d4c84db6e908390d38dedededededede),(0x915349287c9ef0209eca5cc0000ffff000000,0x81534908489ee020920808c98989898989898),(0x4ea924f70cd3e0baf803a80ffff0000000000,0x4e0824b60cd340321802280e0e0e0e0e0e0e0),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,8),(32,0,219,0,8),(0,32,218,1,7),(2,0,249,0,7),(64,8,179,0,7),(128,0,123,0,7),(0,2,105,144,6),(0,128,105,18,6),(1,0,218,0,6),(1,32,218,0,6),(16,0,235,0,6),(2,128,105,16,5),(16,2,105,128,5),(16,128,105,2,5),(130,0,121,0,5),(18,128,105,0,4)]
def g251A : List (List Nat) := [[],[113]]
def g251D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x309bd87cc640abf864c640
def g251D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x81093053082541330c74134202b539e302402feb8663ef58640f7e63207bd319027fbb2636f5ce40
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
def K251 := extendKnown K247 10 [(251,[]),(379,[49,100,135]),(499,[131]),(502,[32,99,116,131]),(505,[49,33,114,100,130])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff705c92e8e16429de2c2c0c3000000ff00ffff,0x4500c80a0a020019e2c2004121212121212121),(0x0,0x0),(0x5b95e9144b8a160f633117200ff0000ff0000,0x61995c8004188140d60311520b0b0b0b0b0b0b),(0xbd2e4c76b6101d5a51f240e0000ff00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff83d2e0476b6001d5a41b240267676767676767),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffadea1c8341a9cb24837ce12ff0000000000ff,0xade2180141888a00835cc121e1e1e1e1e1e1e),(0x8064b74c865b6ed18390d3900000000ffff00,0x8060374c06536a408380c28d4d4d4d4d4d4d4),(0x915349287c9ef0209eca5cc0000ffff000000,0x80514908489ee020924818c98989898989898),(0x4ea924f70cd3e0baf803a80ffff0000000000,0x420824f60c5360b21802280e0e0e0e0e0e0e0),(0x0,0x0)]
def g253C : List ColumnInfo := [(0,8,181,64,8),(8,0,245,0,8),(4,0,249,0,7),(16,0,237,0,7),(32,0,221,0,7),(64,8,181,0,7),(128,0,125,0,7),(0,4,89,160,6),(1,0,252,0,6),(4,128,105,16,5),(16,128,105,4,5),(32,4,89,128,5),(36,0,217,0,5),(132,0,121,0,5),(20,128,105,0,4)]
def g253A : List (List Nat) := [[],[114,84]]
def g253D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc01016082000204080031c02c700b1c02f1cb05aa909e36484805ff7050efeba461f74c630bfee8985fd744c3eea1a617f5ce10bfee6884ff764c67ebb4216fdd110
def g253D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x450b55a441d49146ad50a9146a760c68d56e14e4105561d504c5073104a1d491882932ea820c41c522aac892415c2c2479705c00ff50ffd61ff507fd31ff8c3fd30ff843fd10
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
def K253 := extendKnown K251 10 [(375,[49,100,135]),(487,[32,49,132,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),(0x6845947e807eb553a18e5c00000ffc00003ff,0x20450432805eb503a18e14154551545515455),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff031b09581dd19d0eb8a9af003ff00000ffc00,0x30119095818419c0ea8888a0cc330cc330cc33),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffbe5a8c481b2fce82f63582900000003ff00000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb45a0848092bce80762582943d0f43d0f43d0f),(0x61cf8224a5a2c12a43cd4d9ffc0000000003ff,0x61c1820485a2000241c50c92a8aa2a8aa2a8aa),(0x4c99308a5ccbae3c49575370000000000ffc00,0x4c88200a5c4ba63c0157535f33ccf33ccf33cc),(0x6a64d6ea9e8415f7a43319000000003ff00000,0x4a24d6a2968411778012190bc2f0bc2f0bc2f0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff952a4f3b5578326d10e4b80fffffffc0000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff842a0d285058002d0020100c0300c0300c0300),(0x0,0x0)]
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
def K254 := extendKnown K253 9 [(443,[32,116,134]),(491,[32,49,132,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g471Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffcec5ad506645fa13808959000000001fc07f,0x50ec4a14026458a13808851a3468d1a3468d1),(0x140d310fe314086c85bae70000000fe03f80,0x4994093109c204086c81aa63264c993264c993),(0x3da113d80a04e3f0791e9001fc07f0000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff9e0c2113d80a0063f0411e800e1c3870e1c387),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc930c93a15435d8c06f7800003f800003fff,0x10013048121100518006558048912244891224),(0x0,0x0),(0x2536e8bc2aa62e3a2248efe0000001fc000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe000110e8bc02a60e022248c1c3870e1c3870e),(0x45c94e4bcb285413844750003ffffe00000,0x44842424b2840138001491224489122448),(0x33aa420534ad14b5cf8813fffc0000000000,0x338a4004348514058c8013e1c3870e1c3870)]
def g471C : List ColumnInfo := [(1,0,470,0,8),(2,0,469,0,8),(4,0,467,0,8),(64,0,407,0,8),(256,0,215,0,8),(0,64,150,257,7),(0,256,147,68,7),(16,0,455,0,7),(65,0,406,0,7),(128,0,343,0,7),(260,0,211,0,7),(0,1,390,80,6),(0,2,325,144,6),(0,4,83,384,6),(1,64,150,256,6),(1,256,146,68,6),(4,64,146,257,6),(4,256,147,64,6),(5,0,466,0,6),(64,256,147,4,6),(256,64,150,1,6),(320,0,151,0,6),(3,0,468,0,5),(16,1,390,64,5),(16,2,325,128,5),(17,0,454,0,5),(18,0,453,0,5),(66,0,405,0,5),(128,2,325,16,5),(128,4,83,256,5),(130,0,341,0,5),(132,0,339,0,5),(257,0,150,0,5),(257,64,150,0,5),(19,0,452,0,4),(80,1,390,0,4),(144,2,325,0,4),(146,0,325,0,4),(384,4,83,0,4)]
def g471A : List (List Nat) := [[],[32,116,134]]
def g471D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6017705c0108cb0c206017b06c012c3041743141700470c100005d0c0b43074305c10418704241ec10818b04243141090c0682dd6d35da8d1672dd5493459d0d86933164a249208d04e1a068015f3906137154ebe720ba6e2a9c7de61741c553af9c82e838aa71f6981c57054f3af0638ae0a9e576538754c53aafcbb08a98a795f876115314f2bf0eb22a629f55651535c453eaab22a6b88a75f39154f7050f36ee9c0aa6b065721d534c950af9c8aeab0661d7375d45604432af23c3aa629e552478754c53cabc3f02a98a7957872055314f2af30a9ae229e55261535c453
def g471D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa182c3042e081c0c130d80100c40580086d80130010b0200602ec16008c305860b0c1c00287050ec10b02080001284100005c1a083830682080041f00141c10383800418010818010b86170434170a860d0c1a183800400102050c00150c4010742fc4e1f0b80241c4808901a0c3020c021e0d0400742e0780c30583f0f00180070c30160c3a17e089395c8183a1a0b89395c81a47c808e316620c3b85907602bf67cef85dbba8732e29bdb6c6a8d159fb39642c6d8ab065eeba16cad359aad5532975109c127a40450865051fb3d8798eb9d1372684ae14d27c4988b8ff1f23185289f1321e01e000bdf8355253f5d64d4e53bfb805d153b7f8558d53df584dc553df564dc553df563dc553df580dc553df574dc553df5741c553df7715c153df4715c153f5d8454c53f5d6454c53df5645c453df9645c053bf78154d43dfb53dc143df953dc143bef82597319ff8755331df7515c331d7f7559531bef8259531bfb8050d31dbf74d4d60dbf7454d60bf78154d60dbf74d4560dbf7454560dbf744c560f778154d50f748154d50ddf7354d50bf78154d509fd83dc9509fc874c950f5d534c950f5d534c550dfb7158150df97558330df97158330bf78154d30bf78154d20ddf734c910bf582d4510dfb7558110ff35158110d5f8754c53f578154c53f548154c53d5d535c453bd583d4731f5553d47319f7815d531f5553545319f7815d7309f7815d5309df835d510d7775d451095f8754c53d55535c453
def g471H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6444f337940020800000210007598e65400002067000004a0770fc180800414009404aa30ee000004240000370001d3001cb001ac000160dc02
def g471D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x7480b24341c18100804622080c1a08343018100804148c80d06040288411c1c14706c305181b0c341814100c08005e0470a1e1d1707811c182c1814100c010874849870a042c643c21c1a0c68342c1814100c080060a1c1a180c74241e04705060504031d2218745c70246050d0b06050402c34025241814100c08047470245ca1d45802410347c20d06050403020941182434301814100c0b06005ca18450980171460241d16005c60c0701880d4a18341814100b0d0600609461c4a0817143418141008070e009090c01884a1d170e00306844a08874610342c1814100c08888190d0c06050403028001172c301814100c05087480d0605040302411c20746218701c205c7120c060401881d1d1820485c4c3001c221058341c1814100c083202045cc1c17160c58341814100c0a0070905031d4a2214712a205c445c3498018141c5c00708851c4a881811190e05285c8461d864608811c171c201c04602c88618c1070e8a1463044c441c3c61d1718c10907cac8232b209031410c1ca09070e1c745f04932b201c71d171a0ccac809072074642f0c630728241c9931087c1ca0e1b0600145e285b7f5b62d6568cb2f58e2bf55dcadb5622ac553ca8353a298549ca3751228353ec9db4e226b53449934c425d52c49534a024b523490747a238519c8c345a228510487742820c50047d73d41de4e9c73338e1bc4d7c69733a19a4c8c62730c1824bbc5c32d01654b0c5772a614f4a4c50b27a133494448f242117486441b2000f9477c3a71c00da46ac3431900bc459c2ab14609b44b424710a08143bc1c70da067430c1730ac04e423c107076032417409b03e01640640170003feb24a7ff55253ffae8a9ffd6454ffeb1aa7ff5c153ffac829fff5350ffea9a87ff59731ffac998ffd54cc7feb2a63ff59131ffaa898ffd634c7fea1a63ffd4d60ffaa6b07ff51583fea8ac1ff4c560ffaa6a87ff72543fe992a1ffdc550ffaa2a87fd31543ffa9a61ff54d30ffea4987fd524c3fe99261ffd4530ffaa2987fd53483fe98a41ff54910ffa64885fd7598efeb8cc77fdd563bfee2b1dfd7594efeb94a77f5c653bfae129dff7154ffbb8aa7fd1c553bfee0a9dfd7114efeb80a77f5d643bfae321dff7550effb8a877fdd541bfee6a0dfd75cc7eea9e637f5cb31feea398dfd70cc6ffbaa637f5d531fbca698fdd534c6ffb9263fd54531bfee098dfd73d43bea9ea17f5cb50bfae3a85ff73543bfa9aa1df54d50bfee4a85ff71543fcb02a17f5d730bfae5985fd71cc3fcb06617fdd530bfaea985ff724c2ffb8a61fe54130bfae6907f950482ffbaa217f5d510bfee6885fd73442ffb92217f5c910feea2887f531443fa90a21fe58110ff2a0887f930442deba4c77b5ca63ebea729df77154edeba0a7d754c53beae229df97014efdb82876fdd160 else 0x4315050c241c150c441402324110e04541440907810644145d0464904064382818005151e00148c34180052310310a04981854381150510310e041441a0c09044206190c541431a0c4305103019120440c05404381141a0c805c40683412017142e0d04188051e0c8341000b1868320c005c50b4107098015082c20d00170d042c20c0b4180106830005c48017190d06005c6444280190b110a00642c40d0b028010642d046044180190b107504485c4120b0a005870307801618101c140c04603e2870c1a081c302c140c04001a2890b0503008a411c1c1c1814100c080400745c90b0c0b060504030100420d28342c1814100c08001d0430b0d0c06050403020107400b2c342c1814100c08010430ac4c3c201c0241b130f0b009050d0c060504030201400b28342c241814100c08001d0430c0d0c06040201)
def g471H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x14c88228000001a7c0018e42a9e800171000003ce0830000036f7bc9508eedb0000012d73551a0004b757000001e6714f140000000069e8593e40079be4664f06000001a13bb8f57e6acd0500d943c04b70000000008bd490c4000000000000010495d001cc000468d7a0039799272daabd1791000001527008740039a0000000008e80000123cdb88b7ec000000a5a20001ba532001c6233000ce48e7c31a70a6c0800000f100017680000000283e3890a003fedb17b6000000ab00150242510d60000240144d21c04
def g471D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20851420a8a24198821c78a264090f0478a263060a5cc09832a407240860a243c1952121274305080c101005cc4194264073c498831098710408121e0c4262080e243c426904101c4860a70bca9004392243860a0644a48889065e086148460e74e0f8328409203891f04bca103891f0524a0e207121c08b1f29108204873a5e08a104882c2438f03292082219bf578ae019dacc51c95d101db32c598940f11741f01f000ff593fe63ff58ffe53ff54ffc53ff90ffd43ff507ff31ff4c7fd60ffd43fd50ffcc3fd30ff483fd10
def g471H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ad372ea77aa1ecf304000cdd3de61c00109426b09bda600123d2a200065564f85a8202844702ca11e000e0c6c01a8000000f0aa1fe32001e2a001673c0ef49e259360013da001b2d25d697e300000013ce56a57a66600159920320957f474a6448a001c53dc987982c1d3baba48a824132d5e60000fcc001eb7cb2001f96a417c15d92d7a42c860acac444449e0588da3af47e15284c0000012b91bc001f9a6a788e8dfc11e516bd4a9c22001cb0f5ceae80668d9c7038000328ce00ba029c7c427899434e9c000c6ca621ba217480c3603e0001b600000059ec5f269e560005e30bf5a00000000014c600000428924a0006cc001ec34a5a93fe1bd5a1494a001a3bc9141884641bc2e3d0001fbe8d86e2caadcaec920a001da326e0b5e014d127ac422f04ec2000ebc0891a0e700231c88010210a00a0810500200000204100020c000
def g471D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x25101ff
def g471H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x342bbd880000000000a800000000003e65420b62b24f07e2da24c000e341b1143400094005c0ce001cf424000000000169b1245000005aac05ac002b98389dc7010a0020
def g471L : Nat → Packing
  | 6 => (23,4,6,0,0,9,0,g471D6)
  | 7 => (62,3,6,0,0,11,0,g471D7)
  | 8 => (114,2,6,0,0,13,0,g471D8)
  | 9 => (18,1,6,0,0,11,0,g471D9)
  | 10 => (1,0,6,0,0,0,0,g471D10)
  | _ => emptyPacking
def g471I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 6 43 5 10 5 1 g471H7
  | 8 => lookupWord 21 137 5 11 6 1 g471H8
  | 9 => lookupWord 39 193 7 12 7 1 g471H9
  | 10 => lookupWord 8 53 4 10 5 1 g471H10
  | _ => fun _ => none
def g471 : Forest := ⟨471,10,fun i => g471Y[i]?.getD (0,0),g471C,g471A,g471L,g471I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P6_0 : block g471 6 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P6_6 : block g471 6 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B6 : block g471 6 0 23=true := (@block_merge g471 6 0 6 17 g471P6_0 g471P6_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_0 : block g471 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_2 : block g471 7 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P7_14 : block g471 7 14 48=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B7 : block g471 7 0 62=true := (@block_merge g471 7 0 2 60 g471P7_0 (@block_merge g471 7 2 12 48 g471P7_2 g471P7_14))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_0 : block g471 8 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_10 : block g471 8 10 65=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P8_75 : block g471 8 75 39=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B8 : block g471 8 0 114=true := (@block_merge g471 8 0 10 104 g471P8_0 (@block_merge g471 8 10 65 39 g471P8_10 g471P8_75))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471P9_0 : block g471 9 0 18=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g471B9 : block g471 9 0 18=true := g471P9_0
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
  · exact (rfl : block g471 5 0 0 = true)
  · exact g471B6
  · exact g471B7
  · exact g471B8
  · exact g471B9
  · exact g471B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g471G : graphValid g471 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low471 : Lower true (varsX 471) (graphGoal 471) 11 := lower_forest (g:=g471) (i:=0) (hints:=8858371908) (before_sound K254 V254) g471G g471T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K471 := extendKnown K254 11 [(471,[]),(477,[49,100,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V471 : Known true K471 := extend_ok (m:=471) V254 low471 (by decide +kernel)
def g475Y : Array (Bits × Bits) := #[(0x6e1be36cec4440a35203000000000007fc01ff,0x6e1ba240ec4440a35002a8d46a351a8d46a351),(0x6bdacc591e606033dc40000001ff00003fe00,0x2b5a8450144060319c4229148a45229148a45),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8ccb50020515076f1e8007fc0000ff8000000,0x38c8b50020411062e1e00984c26130984c2613),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb040cbb35424ab01a0bb00003fe0000003ffff,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff904041a210208800a01945229148a45229148a),(0x0,0x0),(0x99718ac2a998d9a8a1cff8000000ffffc0000,0x408ac029009180a1c160b0582c160b0582c),(0x2e6a165acbca6174053400003ffff000000000,0x2c0a1618ca8a61740420984c26130984c26130),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd52160534a2adc6d5842ffffc0000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5214053482ac4051002e070381c0e070381c0)]
def g475C : List ColumnInfo := [(1,0,474,0,9),(2,0,473,0,8),(8,0,467,0,8),(128,0,347,0,8),(256,0,219,0,8),(0,2,329,144,7),(0,8,147,320,7),(0,16,328,131,7),(0,64,146,265,7),(0,128,329,18,7),(0,256,147,72,7),(16,0,459,0,7),(64,0,411,0,7),(130,0,345,0,7),(264,0,211,0,7),(1,16,328,130,6),(2,16,328,129,6),(8,64,146,257,6),(16,2,329,128,6),(16,128,329,2,6),(64,256,147,8,6),(18,0,329,0,5)]
def g475A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def g475D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x61fe1b7550931
def g475D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa206901e0d7f75d0931d7f7550931
def g475H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x40
def g475D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x22824028844343450428c921a2825428c4f0112025321936911e3090fbb041176eaded64a403ffa1663ffd0931ffa8498f9f4390efdb82875fdd531
def g475H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x38bb00000180001e12
def g475D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x45138114861148d38114072864ee32048728632e80d48728480d45218c2881ae80b34830a206ba01cd20c22034e486a8481e0c04b1805400ff90ffd43ff10fff41ff507ff31ff4c7fd21
def g475H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x34000334916cc00c00a0400000cb00000000040000000000000000014da5000208008
def g475D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x73401ff
def g475H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x224000000000000254000000000000000000c6003007c988000000000000085000000000000000a0c0048bd80000051c00c840000000001410000000000000000000000292003c40000000000002b1000003a000000c200000ed0000000000000003a30000000000000000000000000f5c00000001cc000000000000003d10000000000000000000000000000000000000000000000000000253
def g475L : Nat → Packing
  | 6 => (1,4,5,0,0,0,0,g475D6)
  | 7 => (2,3,5,0,0,4,0,g475D7)
  | 8 => (6,2,5,0,0,8,0,g475D8)
  | 9 => (8,1,5,0,0,9,0,g475D9)
  | 10 => (1,0,5,0,0,0,0,g475D10)
  | _ => emptyPacking
def g475I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g475H7
  | 8 => lookupWord 1 11 0 7 1 2 g475H8
  | 9 => lookupWord 2 29 2 10 3 3 g475H9
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
theorem g475P8_0 : block g475 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g475P8_3 : block g475 8 3 3=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g475B8 : block g475 8 0 6=true := (@block_merge g475 8 0 3 3 g475P8_0 g475P8_3)
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
def g501Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb98ae94063697bd80511410000000fe03fff,0x108e04000690b9801104142850a142850a1),(0x0,0x0),(0x412e841a8114a21e6afaea01fc07f01fc000,0x23000604180100a21a603862060c183060c183),(0x0,0x0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa41303ed1b46c0aa358d9e0003f80000007f,0x4a241203290b06c02224899e2c58b162c58b16),(0x18213b3a308358678cf699000000001fff80,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8c18211b22308250658cc698b972e5cb972e5c),(0x6e65e8bc6aa6761a02486fe00000fe00000,0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff004e61e8ac28264402024861c3870e1c3870e),(0x8b9a4e4bcb285c13a44750003fff0000000,0x8a9a0c4b4b005c11a4401d1a3468d1a3468),(0x6754920534ad14b5cf8813fffc0000000000,0x63108005342d10a58f8011e1c3870e1c3870)]
def g501C : List ColumnInfo := [(16,0,485,0,8),(32,0,469,0,8),(64,0,437,0,8),(128,0,373,0,8),(256,0,245,0,8),(1,0,500,0,7),(4,0,497,0,7),(144,0,357,0,7),(320,0,181,0,7),(0,16,356,129,6),(0,64,180,257,6),(0,128,353,20,6),(0,256,177,68,6),(1,16,356,128,5),(1,64,180,256,5),(4,128,353,16,5),(4,256,177,64,5),(16,128,353,4,5),(17,0,484,0,5),(33,0,468,0,5),(36,0,465,0,5),(48,0,453,0,5),(65,0,436,0,5),(80,0,421,0,5),(96,0,405,0,5),(132,0,369,0,5),(160,0,341,0,5),(272,0,229,0,5),(288,0,213,0,5),(384,0,117,0,5),(20,128,353,0,4),(49,0,452,0,4),(68,256,177,0,4),(97,0,404,0,4),(129,16,356,0,4),(257,64,180,0,4)]
def g501A : List (List Nat) := [[],[100,135],[32,116,134],[32,132,118]]
def g501D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9d2213c6cc15243c6090c0c023bf26c0ee8a863be1b7250550cd7c26e4b02a13db90619538c23bf26c3cc310477e4d874c6208efc9b03ba2415d591dce314823bf26c3a6308557e5582dcd10cafc2ee6b92211de981cd724432bf0a39ae488673dcf8254110
def g501D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x800100410b8204040030008001040078204070008620b800f0003080028808128580018944a10400748c10003040000008001010a0800104000000820004100020800106860d0c10002080002410202004a0a121404100090424010b0008000143040a0820004020b00161b0022082140984c0040000000008215a18543040000d8108000800000f06860d0c107034007020850821068120820d0a84004c1a104c1a00200401000078200690a105010020080000000140985772eb5d0b956cad1d94b0b5febcd6aac9556a7d40a6348a80ce99c7376674a491921a374688b314e26c3e85f0a60d41480affdfcbf37c8f79e7bc9774ed1d2b9670ee05b936c6ccd5da4342654c49862fd5cab59682ca588ad557aa0522a0939a5b4988d112a1f43284d06a073f0780e89cb38a6b4cf198324630be96e2be540a093223442c7e0e41bc3185b8a814424c468870f01c82d04b08a0d81802a0480780c0009fd80dcd629fd81dcd429fd80dcd429fd83dc5429fd80dc5429fd81dd1329ff815d132ddd63dc5329fd83dd9509ff835d950b7f83595509fd83dd1509fd81dd150b7f83551509fd81dcd50ddf7358d50b7f8654d50f5d5350d50bfb8050d50ded63dc950ded43dc950def7250550e7d6558150def7258150bdf8654e30bdd8654e30ddd635ca30ddd535c630ddd728c630bef825d5309fd81dc930ddd764c930bed829c530bf9809c5309fd8788530bf98088530b7f8548530bef82541309ff835c620ddf835c620ddc835c6209fd87986209fd878c620df5718c6209fd874c620df5714c620ded7448620ded73486209ff835d9209fd81dd1209ff835d1209ff815d1209fd81dcd20ddf7358d20bef8350920fcd634c920ded42dc520aff8650520ddf738c520fcd328c520bbf8458120cfd7654e109ff835c610ddc835c610cfd76546109fd874c610d7d754c610ddd734c610df9714c210ddf82dcd10ddd82dcd10ddd80dcd10ddf735cd10bde871cd109fd83dc910ddf73dc910ddc73dc9109ff835c910b7f855c910bdf835c910ddf735c910ddc735c910ddf7358910ddf7350910bfb8050910ddf734c910bf98394110fdb7394110fd87394110bfb8354110fdb7354110fd87354110ff14154110ddf7354110bef8254110fdb738c110fd9538c110fdb734c110fd9324c110ff2214c110ff1214c110ddf734c110ddf73481109dd83dc5429bd84dd9329fb805d1329ef825d950d7651dc5509ef825d630bdb8054e30bd9808c6309ef825d5309bf845da209df835c6209bf845d9209de871cd1097f855c9109df835c910fd2318c110
def g501H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x20800a1000000000010d000000038c000000000070400000000000032c00000000000000000000c6d2000000000000091c00003c000000e29890000000345000006aac300000000000008
def g501D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x438710481f1205221c40345068148870e14281816061d203471c1546850148871c30282518100a1c7c8c2150d0c408c20a1608301810083a1c4c70c0201c40e870f1c061d204041d0148870f14141d203c40601870a481415201c3c40c0a0402410f221c3a15041c3c5000f220c143c8830c0a0402470f186805191e1454781091210302d18100c0800383604a46850830103d1c8451a0c0a85040281470f2430281810091c247860d471f10302c2824100c08004c90210230e1c285830c0604020e87131c14301008043a1c7100685070914421d207c40d0187481014281a1d207c5060187480d14302818100a1d04488091f0838141d20345050901071f14302824100a1c7c70b2208302c14100c0800383504a4709120c100c0800403c3834041814b030f220c4038343c4c50c0b0a098685c4c3c2c0412f130f0907021a14714130c0b0a09040302002b130f0b021a150470c0a04020109471c4830281008051c34819100e470f1440151c3c414100f0e0d8605412014404c3d0450604030200100e0d0f05412c244821109850fc1c8831c3b0417003f20887100e0f0dc1c8c70605261a17231c4a5351c28653fc9e34e626d534c9974c425d52d495b4a624e524c91347e23c51bc8cb45a228511487342e213506c8234081fe4fcc7d33e21ed4f5478f3bc1d74e9c7373941c44dec6e73661ac4d4468f33c1984c8462330017c4bcc5db2de1674b145732b01524a6c51728013c49c44c725812748e446722810a48143f71e80f047643931ba0d7469433318e0c145c42d71600aa451427f12a091442c2070f807043441770ac04e422c0ff076032416408303c01640740130003feb1ca1ff58d50ffa86a87fd41543feb02a1ff59630ffaea987fd654c3feb1261ff50930ffce2987fd714c3ff10a61ff48530ffaa0987fd63883ff30c41ff8c620ffa63107fd63483fea1a41ff98520ffac2907fe41483fea0a41ff8c520ffa62907fd60483fea0241ff59610ffaa7087fd51843fe98c21ffdcd10ffae6887ff72443feb9221ff58910ffa84887fd32443fea8221ff4c110ffa40885ff7358affb82c57fdcd42bfee2a15ff7050affbb2657f5d932bfee8995fd744cbeeb1a657fdc532bfee0995fd76942feba4a17f5ce50bfae3285ff76542febb2a1df59550bfee8a877d54542ffb9aa1df54d50fdee4a85ff71542febac61f754e30bfae5185fd718c3ef18c617fdd530bfaea985ff724c3ee992617fdc530bfaed105fd74882feb9c417f5c620fda43105ff76482febb2417fdd120bfae8905ff73482feb9a41fb50920fda64905ff71482febac217f5ce10bfae5085fd71843fca8421fe4c210bfee6887df73442feb9a21f71cd10bfee4885fd72443fd28221fe54110ff460887f930442feb98217f5c810bdee4a857d75843f98842177dcd10 else 0x83411c0c1070300e01042c6180a050380410b1c2d100e00803860c0b4280448318310e042c7451a0b434022150c742c3401b090d005c3438542401310504c20640130d0c7834343400b2211047032144000c4409102504001a14505140a004825044418012091048251200185448012091048250a00185120944020e14482600190458012090c302509120050a020d80110c40743c484411a850f16110c2c644848341141018150431413410d003421e1209434140184205006c3450581400e170d1900543430581400b221418144c3120981064014181506221c6c6870d1b0c181506221c5c60905018887171b045c3)
def g501H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6681d0c8400000151f3c6c0012b10007838000e06d30f496a3d0a4000195a8d9112b0a8000000a3cf39f808000e5eb6f80010ec03b0000001c40000309713a339296000000000000000042d9826fa526b800000000000004abce5e4670bdb01038000000715f8dd06000000037213090000003f7e7f6000778400141e64d8000000c75f9909d0357c90202919c00189e00059458c563d9a911c400004200000000000000007970760294000514fe2ecab000005294bc26612000000162dc36c80089e9159cf6877172f230003b6ddcbe27115491e7d999900030138aa223000212b67640f00031225d2a93a1c6ac309bad654ca45874200000061a000000071b44710b0000597fc9b8500000005c7c0001305068003266000000000282d2dafad402be2786512d2d4f852000f29466d036000000181d7b4000b384698000059b182248c6832b4b30003168000000215000000022eb0d59c8c2c818c8cc00000000018bc174710b0f8089d39fbdb98bc20000f5400006ab84aaa10006a7f6d3a1ac25b0e68de3d771958bafde20bd0c2106c87111704b6c40a1411a32680fc7e249b5331a4c3363786e20854884636065d95498000146416d95586b000567c00115e0086822abba40000397e8d5645000000085791900000026d80009c800021e0480070880012461e638954000d0831a900600d1c000a64608f20148004004004502e
def g501D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6c30521046880e4060a5e08d101c70c14a8d032038e1878e83203851c30582887c80e3861c364470214742182c70320f8e18741901438c182811320f871c2031c34341911c292060860b2238c4070f1b064470c1499ae347f5c663d58484f12e87511400ff58bfd42ff4cbfe50ff543fe30ff4c3fe20ff483fe10ff443fc10
def g501H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x163942080d6070219bf10001be2ca60000000001a3d20b51c00000002690000d4a000bee7860000000000000104aa33d1133384c600086b000283c00009a00000000008b2c2766ae0004ec9ba5852257934000000000020400010d9200742000000122a0000001ec1d5433732a13c0d88000083649c00000032b000103b2330000000000c8480013d20000000000001640b71d074000000d015421d1525454998f000034a0007c9d8e369900010508c3649cce89bda90000f2268c000000ac4400e8000a018231d1dc5aa28559192c0000000000000001e58d664e24c8438a4070158000000b0e0000001a2f0000002464000000613c00000000009140000006a8922406e9d7806408c46c406564876b15b8efe55c42c265e5e2669b91c23c09000000143400000000000006240000000000ceb5c20000000000d2ac9a4eb1e6b4e52a9c0000001e2d9364cae64115c96eea4000672800266123ea09592202e000a850002062c53e13e73498f66a80ab04e0b2000fc580010bf2ddb288000000000ee38a440000000000000000000eafdf7f00674e8292a61ea7bc9310ed9380abde707841800000039a8000000000326000008e0005b5000000000000031753e1c1b000699c00188b0000d240001b40007208000e1000000025a646002e0002cb400000000000000000005b2ac7eb4dc4a800105842ea13573969760451008d30dbd07c257760001e0b00074b0ed8000482118b00e000000090c4a0000000007ce3e00010d00e50e1038830800079c00cd2c90481400032c40c00011400000800010020841ca0c7004006
def g501D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x240e1ff
def g501H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3e6000000029b00000d8bb72e54a00348e07a35923835c00b9c000000574c00c958b0a5d46080000000a1d0900198003a84a800a12c60000000000d0f99001f37d000718619
def g501L : Nat → Packing
  | 6 => (14,4,6,0,0,7,0,g501D6)
  | 7 => (119,3,6,0,0,11,0,g501D7)
  | 8 => (114,2,6,0,0,13,0,g501D8)
  | 9 => (12,1,6,0,0,10,0,g501D9)
  | 10 => (1,0,6,0,0,0,0,g501D10)
  | _ => emptyPacking
def g501I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 3 59 2 10 4 2 g501H7
  | 8 => lookupWord 52 293 6 13 7 2 g501H8
  | 9 => lookupWord 52 337 6 13 7 2 g501H9
  | 10 => lookupWord 8 53 3 10 4 2 g501H10
  | _ => fun _ => none
def g501 : Forest := ⟨501,10,fun i => g501Y[i]?.getD (0,0),g501C,g501A,g501L,g501I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P6_0 : block g501 6 0 14=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B6 : block g501 6 0 14=true := g501P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P7_0 : block g501 7 0 16=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P7_16 : block g501 7 16 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P7_112 : block g501 7 112 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B7 : block g501 7 0 119=true := (@block_merge g501 7 0 16 103 g501P7_0 (@block_merge g501 7 16 96 7 g501P7_16 g501P7_112))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P8_0 : block g501 8 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P8_4 : block g501 8 4 67=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P8_71 : block g501 8 71 43=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B8 : block g501 8 0 114=true := (@block_merge g501 8 0 4 110 g501P8_0 (@block_merge g501 8 4 67 43 g501P8_4 g501P8_71))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P9_0 : block g501 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B9 : block g501 9 0 12=true := g501P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501P10_0 : block g501 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g501B10 : block g501 10 0 1=true := g501P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501T : checkedTables g501 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g501 0 0 0 = true)
  · exact (rfl : block g501 1 0 0 = true)
  · exact (rfl : block g501 2 0 0 = true)
  · exact (rfl : block g501 3 0 0 = true)
  · exact (rfl : block g501 4 0 0 = true)
  · exact (rfl : block g501 5 0 0 = true)
  · exact g501B6
  · exact g501B7
  · exact g501B8
  · exact g501B9
  · exact g501B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g501G : graphValid g501 (boundsBefore K475) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low501 : Lower true (varsX 501) (graphGoal 501) 11 := lower_forest (g:=g501) (i:=0) (hints:=9126806788) (before_sound K475 V475) g501G g501T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K501 := extendKnown K475 11 [(501,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V501 : Known true K501 := extend_ok (m:=501) V475 low501 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[(0x5013fd0121dec000000000007ff001ffc007ff,0x4003e001215ec1012024048090120240480901),(0xfb782eb470cf000001ffc00000000003ff800,0xeb382e3070cf0550aa1542a8550aa1542a855),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa4090b24accbe000ffe00000000ffe00000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff84010b202c88e0330660cc198330660cc19833),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb6c440e755ec9800000003ff80000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffb60440c755ec9b0f61ec3d87b0f61ec3d87b0f),(0x142409981084bfff00000000000000003fffff,0x10040908108008aa1542a8550aa1542a8550aa),(0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff99cb6c20909480000000000000fffffc00000,0x399c14c200010eccd99b33666ccd99b33666cc),(0x2f84832ac312800000003fffff00000000000,0xf80830880124f09e13c2784f09e13c2784f0),(0x69435055d24307fffffffc0000000000000000,0x61405014c0430700e01c0380700e01c0380700),(0x0,0x0)]
def g255C : List ColumnInfo := [(8,0,247,0,11)]
def g255A : List (List Nat) := [[]]
def g255D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ff
def g255L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g255D11)
  | _ => emptyPacking
def g255I (_ _ : Nat) : Option (Nat × Nat) := none
def g255 : Forest := ⟨255,11,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
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
  · exact (rfl : block g255 8 0 0 = true)
  · exact (rfl : block g255 9 0 0 = true)
  · exact (rfl : block g255 10 0 0 = true)
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
def g479Y : Array (Bits × Bits) := #[(0x3572828dae8540940000000000000007fc01ff,0x2462828dac840092a351a8d46a351a8d46a351),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffacc25c05d4b922d400000000001ff00003fe00,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffacc25c0590b920d48a45229148a45229148a45),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5bb752892cc00740000ff803fe00000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc5ba7528828800741e0f0783c1e0f0783c1e0f),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc50ca682a014bdc801ff000000000ff8000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc50ca480a00491c026130984c26130984c2613),(0x597a4572e20291880000007fc000000003ffff,0x5118017242009109148a45229148a45229148a),(0x0,0x0),(0x61978650913580ffe00000000000ffffc0000,0x21150600013480c582c160b0582c160b0582c),(0x200501d0256e86700000007ffffff000000000,0x50080254606026130984c26130984c26130),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd2849abb11c02703ffffff8000000000000000,0x10000a131140260381c0e070381c0e070381c0)]
def g479C : List ColumnInfo := [(1,0,478,0,11),(2,0,477,0,11),(4,0,475,0,11),(8,0,471,0,11),(16,0,463,0,9),(64,0,415,0,9),(128,0,351,0,9),(256,0,223,0,9),(0,2,333,144,8),(0,8,151,320,8),(0,16,332,131,8),(0,64,150,265,8),(0,128,329,22,8),(0,256,147,76,8),(17,0,462,0,8),(18,0,461,0,8),(72,0,407,0,8),(132,0,347,0,8),(260,0,219,0,8),(1,2,332,144,7),(1,16,332,130,7),(2,16,332,129,7),(2,128,329,20,7),(4,128,329,18,7),(4,256,147,72,7),(8,64,150,257,7),(8,256,147,68,7),(16,2,333,128,7),(16,128,329,6,7),(20,0,459,0,7),(64,8,151,256,7),(64,256,147,12,7),(66,0,413,0,7),(128,2,333,16,7),(128,16,332,3,7),(129,0,350,0,7),(256,64,150,9,7),(18,128,329,4,6),(20,2,329,128,6),(20,128,329,2,6),(65,256,146,12,6),(68,256,147,8,6),(129,2,332,16,6),(129,16,332,2,6),(144,2,333,0,6),(257,64,150,8,6),(260,64,146,9,6),(320,8,151,0,6)]
def g479A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def g479D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x123cc2460c0600fb2ec96a1751d564193106d96e0b50ba8eab20c9a815c3705a85d47559064d414e1380d42ea3aac8326702f4fcb5d47559142583381797e1aea3aac8a12c19c0bdc5d5b31d56450960
def g479D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4628200000000000000000000000000000007e18207e182001f860de1ce485449f4e2652c9348235148742204fc7b391bcd8693318cc05d2d15ca8512712c9045210fc78391b0cc54270f06c300f003253f0fba5d47560a64c94fbaecd751d582993253f2d7568c7560a64d255b36c598594751934966cdb0661651d464d269b26c1985947519349c6c5b0661651d464f037c1e63759d5641930a7ae5b36a07559064ca95b36c5a81d5641930aeae5b06a07559064caa9b26c1a81d5641932ac6c5b06a07559064e03ec96a1751d564193a0d705a85d47559064e839c06a1751d56419320feeb985d47559064f03798dd675e4564193255f0fba5d47560464c957baecd751d581193c0dea7759d56460464d837cb5d475591811934a5ea5b31d56460464c95bc3ee9751d580193256eebb35d47560064c95bcb5d5a31d580193316f0fba5d475d9160cc5bbaecd751d764583316f2d7568c75d9160cc5bc3ee9751d564583316eebb35d47559160cc5bcb5d5a31d564583352f0fba5d47550960cd4bbaecd751d542583352f2d7568c75509609e8bc36de755914258370af2d751d56450960fc0bc35d4755914258300feeb985d475590649837cb5d475591811936055d5b31d564604649c2bcb5d475591425837025d5b31d56450960
def g479H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa2e300b6f035001d1194002
def g479D7 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xe28205c3b8570016025140f8608000007c304003e182001f0c100e29c308e18293563d11f862511592b1c3e19c0be18770f864c9e0420cd38ff0c339271c298ff0fe14c5f8228c5609f0be0fc0f8637c398a17c2e0df0f8209c1204fc298e21c5e8271c3f86714238bd04e387f0b80704f8625c3993c038208337827c338ff085e08727e11c713827c33a41fc3f85e048d85c15e1f80f841dc3f01f083f85b0fc007c3b8674ae0df0be18dc3b865c3e95c1a648dd2b837c1f85c33e18dd2b835c3993f0be0f0c1fc674ae85e03e18b70fc674ae85e02648d928e3fc338bf04539792be087f0ce285928e49c7f827145519313e1873eb3df3bd3b13a539938d3813752fb2d92b72952732671ed1cb15111909f09305b04f043020f90f84f62f56f4af28f1cea2e96e74e68e5ce50e44e22e16e0ade8ddcdd0daeda2d6ad48ce4c96c48be4b96b5eae4a54a1c9b89549068ce88081c7b873e6da68c6125c45765284984083782d22581c814e1000c804e0013a7ecda79d7649925e7d9b4f3ab0532696fba5d47560a64f29f66ba8eac14c92f5ecda79d7815931ead1b42cc0ea3263e9a2681981d464c7e342d03303a8c989fae9985947519393ad8b30b28ea327279b0661651d464e56f63cc4eab20c98afe61a79d564193c1fcc6eb3aac83272b7b1e617559064c57d72d40eab20c9aa76cda81d56419355ad8b503aac8326ab9b06a07559064e56f63cc0eab20c9e0fe61751d56419395bcc4ebc8ac8327c37759d79159064e56f30baf22b20c96ad6e075e456419395bcc0ebc8ac8324bd7b369e7560464d2ef74ba8eac08c9e55ecd751d58119395bd4ceab2302325ab5b79d56460464e56f52baac8c08c9cadea475591811925edd9b4f3ab0032697bba5d47560064f2b766ba8eac00c985fae4a85d9755534bad8950bb2eaaa4edbb369e75d9160d8f774ba8ebb22c1f16ecd751d76458276dd9b4f3aac8b06c7bba5d47559160f8b766ba8eab22c13f2ecda79d5425836b5dd2ea3aa84b07d4bb35d47550960bd536f3aac8a12c1fa2ecd7559142583a17cba85baacb326e0da3508755966492df74ba8eac14c9a535d5a31d582993437d3eeab2b05325a4db31d56560a64e07f31baceab20c9a0f6a1751d56419381fcc2ea3aac8324977ba5d47560464d4aacad18eac08c9e0ddd67559181193c1aba8eab2302325a95b31d5646046492f774ba8eac00c9a565d5a31d58019343dd3eeab2b00325a59b31d56560064b4d3643aacac00c91ad6e7a45da645472add9f52ba8eab0655ba9e8d751d560cab774bab263aac131eee9751d76458362cbab463aec8b04c7bba5d47559160d8b2ead18eab22c135aee9751d5425836a4bab463aa84b07c2b759d56450960bd1766baac8a12c1f0a5d47559142582f44d98eab2284b066b0a95d16454560 else 0xf860800000000445f87f0be058416a382b90198a0fc1040f87f0be0fc00582d040662fc3f85f00160b413e185b0f616c00580945000d8150800016020700adc3b85700160c07c304)
def g479H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x22e000000000000001232000000000000000000000000000000000000001c860000000007a6000001e30000000000000000000000006001b40000000000000000000000000001a4383923e000000000000000000000000000000001aa200000000000000000000000000144600000000000160400000000000000000044e001c4a0000000000000000000000000012b80000000000008220000000000000006240000000000000000000000000000af20e000000000000000000000000001ac2ba32be000227e4000000000000000000000000000000193c00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000182c000001a343cc2b000000000000000000000000000000000113600000100c000000000000816000000000000000618001cba0000000000000000000000000000000000000000000010aae116a4001050000000c1221a000e52eb4000000001c3c000000000000000000000000000000000000000000000000000814000000000a54000000000a0200000000064800141c001e45c3a00000000121e6280000000000000018a74360000000000000000007a400000082a000000000000808000000e2000000000000000000000000000000000000000000000000004c0000000000006a8e0a00028000200
def g479D8 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0xb95dc9ee3d70e383dc18df06ef3745b7edb26d03639b02d746b63569a9ad31685b39596ac8f634b12186cc155ff2f9d796baf5c72da168eb265852bcd590a9d53e29314429f64efa6f933097c4b024e92328f8461a2390bc83d40b9fecfb47be3ce9e04ec073a38a1bccda46b134d19e4cb063c30d97e8ba85b82ce15d8aa052f28c13f09b64b024791a487c4181f68f3074c37b1aa8cbc61c2ed1638a844f624b11788103da1cc0d806502e615709b04681fc0e2060826c0ea0590198070000afde85869d664baf69e75d9264afb69e7560a64ef3e8d7560a64afd69e75e0564f5ddd675e0564bf5e8d75e05649f7e8d979d464cfd685981d464cfe681981d464eafe627559064baf69e7559064eafe617559064eafe607559064fad9d79159064fad5d79159064fad1d79159064afd69e7560464ef5e8d7560464afe69e7560064ef6e8d7560064cfd684985d954bbe69e75d9160fb6e8d75d9160bbe69e7559160fb6e8d7559160bfa69e7550960ff2e8d7550960dabe55425da64dab50b9759664d1fe5f7559664f8b50b7559664b9768c7559664f8b5087559664f0fdd675d9264abbe957660a64e5bdd67560a64af3e8d7560a64e5b5d47560a64af368c7560a64afa6807560a64abbe9d6560a64e9bdd56560a64e9b1d56560a64e5ddd675e0564af5e8d75e0564cbbe55825d864c9f661651d464cafe627559064f0fdd67559064cafe617559064aaf6a07559064cafe607559064f0f5d47559064abde957660464e5ddd67560464af5e8d7560464e5d5d47560464e9d5947560464af568c7560464ead5957460464ead9d56460464ead5d56460464ead1d56460464abee957660064e5edd67560064af6e8d75600648fe6a47560064e5e5d47560064af668c7560064afa6887560064abee9d6560064e9edd56560064e9e1d56560064eae5957460064aede85865d254a5f2a1765d554afae8976e0154bade9974d9151dec5d190d9151bade917699151db95d99299151ced2617459151ceda617419151db95d99219151de95d19219151dbc5d99019151dec5d19019151fa95da64509519f6e8d979d560d5eea5751d560f56e8d751d560f1edd675d9160bb6e8d75d9160f1e5d475d9160bb668c75d9160bba68875d9160f1edd67559160bb6e8d7559160f1e5d47559160bb668c7559160bba6887559160f5add67550960bf2e8d7550960f5a5d47550960bf268c7550960faa9d56450960faa5d56450960faa1d56450960fac5d36454560fac5d16454560e2b609765d064e0f5d9855d064cade8798590648afea19759064cade639159064e275d97460c64e2d5d97460464cadea56460464aade9d6460464aad69d64604649adea5641915195eea5751d560d565d5931d560bb468c9654560bb468e76545609bc2a56454560fa85914254560 else 0x540808c530c2314c332c330ccb08c3070cc2b010f0cc2b010c0d0260781782e07800648a1bc3f0801f0245a107f0fc2f040091e86180af042c0cc507c10b00a0ec3b0ac0f041c0b0606c1508070dc2700150b05314c332c330ccb08c530ccb0cc332c20061f8703134c530c3134c308c530c230c1334c530c3334c30a1153684f0d4b15118198a92d84f0e4d1fc0134c7f0fc1f0b841d1192c8af0606613c0f0ec727c0c30c9f04c7f0b841d11f009bc33c308ac71cc7c13c3317c2c186337c332c3833c3c0b0c31cc518cdc33023644c3302f0cc510c9c0b0c31cc514c7f0f02c30c5148605f04337c332c621b04f07c085fc371c7833c046fc3089c71b0af0f0c31cc5f086c28cdc300bf085f0d4d8454b1109423c1f0147f0bc32708072c70b3c0f0fc2f06c523c3f08c531fc1c106b2c2c072c7b17c1f03c2f0c9f0104f0fc20b0c7f04c5201cb1c2cf03c3f0bc1b148f07c33170410cb22bc3c13c2334687304f0cc7317c2c18733704367c2c185f0b06c13c3314508bc08211cf0fc2b1c70270431fc2317061906c23c0f0fc237c603c8a71f410b0cdf03c3f09c52b4103ccd2282c71dc5f0bc0f0cad040f229c5f0fc2f002c71c932fc3f0704f08cd1a1cc13c331cc5f0b061ccdc10d9f0b0614c7f0f04c1bc23146f0b00c13c331453270431f06f08c51b04f0cc5c18d2140632f04f0fc2334632fc1f0822c3bc371c708a1c46f0ef0fc271c783906f0fc1f08df1a04f0fc0a2fc2230662bc1333c242fc318cdf0f0b27041344cf0f8151bc21944f0f8115246f086f0f8112944f08562d46913c3e04571a44f0d01f014cf08662c44f0f81f03c25187e0644f0c5167c5e07c0f0d9f94457358b11bc3e07c21707e2dcd113c3e07c2918762c5192bc3e04cc1a45e0247f084f0fc2e004b1bc512d4970f80f0a451b0ec334a317c331fc2c188c3b4a32f06337c21b0ec334ac1bc2f0cc51f0ec334a324c5c1bc231c8c3b0c128c5f0f063487d2b06317c331fc1f0b0c20cbd28cdf07c2c306d2b06f07c2c33c33147d2b06324c5f04c7f0b0c23063144af0fc1c30d21f4ad0b80e30c7317c31ccde30cbd2b42e006e334ad0b80f0cc51b4ad0b80e30c7324c51c2c71e8cf07c3929c51dcb71dc5f068c92bc31c2b09c2c71e8cf07c3929c527c3d0686f089c1660310cda3341f0fc23288f03c32465f128bf03c3f07c253460b3c0f0fc20945f0fc2f041c17c506fc0073c3f08151b09f03c1f08df170bf020ff0fc2334622bc3f0bc00b0583fc3f0bc03345f0fc2f020f3345e07a4f03c3f082c1b801bc5ff07c2f0f9c1f801bd4bf07c21439c1ca2a705ef0a6416c7288cda7021f085e1fc2f0c602704d058cf0f643285f337933c51e0eeff776bb6dd60e8a734)
def g479H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1a9600084c80000012b7f148001c1ee3b320f926862000900234900b02600028319614150005928000052e15000147fe5070b94d712621ec1220f086e000f4c000275e89420fd850000a1881aa0c245000000058750392020004b0084662e40250b00000006219b2e07c00011cdada3600110004249824e13b03d8ce48f2100005807010747d4de939043a20be4d834c8be42405b82b8338480000102475f3d0001931c5b0af212ecc684482b50b68dbb26e46be4412e43744f51eb02540ce4d65f28ca471844313b038001f40ac918d18a2d900006308000e95f178003406a1a2a0c3901994487120c100223c029062c38402781162210001
def g479D9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x92d6cb162b20a8328f8a0226d09782514912233488821308071f5078f1ce06fc1ab866918b45e816b056714d04ef12cc45c105c3c90e7c3630cc02d90abc27c08dc1f2069017104f80f002d007800a8000dfec34eb325ff65e75593fecebc0ac9ff575e0564bfecbcea327f7e4d751927f930b2ae96fd959da64b7fcaaed325bf65f65992dff2eb2cc9e7f7559664f3e3aacb327af59574993d7cebb24c9bef7560a64df73ab05326fb5d5829937d8eac14c9d7f759d564dfb3af02b26fd5d781592dff2abb0c9d7f759d464befc9aea324ff66075193cfaca3a8c9ebd655d064f5f3aac8327af5d564193d78eab20c9bf67560464dfabab02326fd1d5811937f6eac00c9bfa7560064dfcbab00326fe1d58019377b0cba4a93fc985d954ebebb2eaaa6fe5db80552fef28bb2a37f7965d151fdaba6c8a8fbd5da64547f6ae9322a3fb57459151f7abb0c8a8fed5d064547fcaeca12a37f995e1d60bfcca90eb05fe65f85582ff32e42ac17f9979d560fedc9aeab05fe65774582ff72aba2c1efb75d9160f7d3aec8b07be5d764583df0ebb22c1efb7559160f7d3aac8b07be5d564583df0eab22c17f997d5160fbcbaea8b05fee5d54583ef4eaaa2c1f797555160ff53aa84b07fa5d542583fd0eaa12c1ff17454560bdbc8b0d3a5ee643659d375b0cc14e93f79161a74bdcc810cba56fa63765d2f7321b2ae95bd969d174cdfcc2e83a66f619741d27ef22c34c967d959da64b5fca2ed327ab509769927f720c2cc96bf9459664e5ebb2e9325af65f649935daecc14c9aed6560a64bd6c94e8b26ed9d38159376ae9c0ac9aed825d864d3ebb30a3272f5d97419367b0aba0c9abf9859064b5fcbac8325af65d64193d6f22b20c9add7660c64dceba306326bd5d98119376ae8c08c9af97660064d7cb2b00326ee5d1801927ef22c34a93fb90616549fbc8b0caa4fee4186553774e9c02a9bb974e0154df2c8b042a57d65c86546fab26432a37f19021951beac9ceca8dfc64276546fcf24bb2a37e59221151bf2c94e8a8dfc64364547d6ec9322a37e592991519fa4c2c8a8cfda6064546beb2e322a3eb56419151beac98c8a8df964864546fe320322a3fa66450951fd2b2284a8df664f87582f732843ac16fa989d960b7cca4ecb057ea5c85582bf32e42ac17d99321560bf8c890ab073e5db75582f7329baac1d7b759d560bf8c8ceab073e5d975582fb726baac13fa981d560ebcba8eab05ee65075582fb3263aac17e9921d560bf8c88eab04fea6374582f732f3a2c1eb974d9160b7dcbac8b07ae5d164582fe323aa2c13f89855160f79cb2a2b07bc25951583de4eca8ac1ef17654560fd93a2a2b07ec5d151583de6c8a8ac1ef16454560fb9aa2a2b07dc55151583fc284a8ac11bf985d07495fcc2c8326ad59181192db3273b2c1ea96450960 else (if j<2 then 0x6184f0787c212088526d14960ae1a1381c2e093c0e1f0609c22f8dc3e0c13845f150ccd63f038704e085c8433159704e070f821723825fe070c4e2c1a1708c34302acd63f0109c3e1170b423358f868670f85c00a9547a6f0387c1088707638199b0be070f83c20e13c1e070f85042f8d470253517c3e070b822227820ae070f842c1b87c2e0c10be2f0f85c18217c50af0387c2160bc1e10705e201383c0837085e342c0cc766f0039c3e143c985f0f81c207c19be38198ecd8770f83c20e100662b2c39c3e0f0a1c470c1d06e1705be361616080670387c28211040a41787c1e108870570017c30670836385017c3e0f0838342e80cd6388909c3e0a7384505387c1117093e330781c3138a452307cc5c3e17021638808c1e3170b81241e36c03170f85241a8e6226f03841e108e62e1f0842281495c0e199e482c84405c2270f81241f038bc2f038658160f81c5e1443c3e117074fe071785e070f84460d9381c286f17c0e198871070f81c2160b8545f038646e106c726e070b8be070f84460d929fc0e9381c3e10b0723708362f130385c5f03861b288f81c286f17c3237089c46070a1bc5f0386621c89816333387c0d21288e09268e5ae10aa3839904447e0f0f850c1f825fe1f08382a1895c1a3937861ce10b082291f83c3e1470622f0f85c18e0a5fe0f08a11c1490413017f87c28e0e4da591f83c3e12707c660383c2e197c6c07048a47e1f0b383e0387c2320b0526d2c8fc1e1f09383e009345a3934b3c1e167092291f83c3e10ac6c012f87c1e1117386f23004523f0787c2110f80e0f088f9c280c4ac07048bc3ce1487c01148fc3e10b063208c8fc1e170c383f0787c20e17c566b1c95c3e170438392b860ce0f08be313488c76692b87c2e0c30924104aa5fe1f0a38388a8a4b11f0f85c10e11c3e119138204d19c3e11905830ab87c22f8b05302198f4166d2f87c24e13c3e1191382603845fe19905a0d2e8a21e1f09383980bf41b270f849c1c9e4b30114bfc3e127085170b864b4e0b41e1a8ac89c14441c0f89381c3e170481607381c3e170461622b87c2e003c61188a8e5e8e70b825a2119c3e09284d18b42fcff33c9cdcb324cb7f291c933210c70b174c4770e1c207021bf2af73bc4eeb3b906dc6b5becfdb22ec2baf2eb86ac9aabda99a9fda62e922a30a862a00a7a29d9a7189b726a0996e5f2962653b939247290923d68e223438c1e2c28a1a21d87861a585ca124835a08880c5fbf7d7deff7a7de6378c1deb76e1d6a7429caa714dc056eddb846d21af16af9a82693da13675d992651190862e986360c17d95e7576a5c716ce5a49629572558454b54f1526945e50ad3f84f1539b4d7d3084b0d275489d1eb4675158444d0d741dd03b4020fc33df8f423bf4eca3a5ce523834dc835c4d2c33e4cb43174c182fb8ba else 0x1206d180542505028a208a43c08b014285619011642858630e022c850a0d22e0c8782c0e005e4b24320d21e0b03801792c825f0387c1e1070443d1c9bc0e1f07844b11104be070f83c226e107c270c97c1e1088603703824be1f089b842045c1e012f85c3c231c84d88b810ce1f0785846393c3e0707848c2f8c1b26b1f81c18270e0dc26294c50bf0445c065c13870c63941b668318fc0e0f0e44c5259a0c65b1d8bc1e070e44486e19c10bb1e09c0e18898a562b1986c270c8e45e070b82531d0c840ab3618088570387c26298156682c10864231d8b0c8570385c3345e0ae0f009bc3e112f0848903e1e8e61383c0e191c8bc2c3180d0c8260f0526f0781842cf0b0c6024108423f0781c3e11150c50883e1e8df0781c2e1d1d3850bf87c0e0f08385f1c14c71613781c3e170608c529962c268298ec5e070b83c382160a167018fc3e170608c52438c707b3411c0e1c1b850462961c07b3410cb63b178104e170e0c6088380f047018fc38270a0cc52c441c62b2f83c3e141a1cc728381b63b378306e1f0a1cc52838cd65b1d8bc1e141b870e28441c0df058fc38370a1cc52b87c0e17063e8c191408e070f85c10e07c8e0f0385c385a706e08af87c24fa70623f038781e1128b8391c4046c0f009b8be192b844c2c892026c2f024a23f0f85c0a31647c0f0217c3e127e88442c9446a670f81c24f86c9901348e44c0d321646e1f0b804a3303c017c2f87c24f97081786e17c0e1f093f46204ca0c0f0317c331170823f049bc2e192e383f048fc3e112e38311497c1e170c9b1c1c8bc3e17049b1c18964a2208f8380c611785c326964b21e03844d378dc123f0f844b8e0dc1e170e385f1596c52570785c363c70810b1d9bc1e1f0a38c52196cd63b1783c2e1c7081188494c5e0f0f851c63925f65d2a0cc52511387c1e14318e631e0c2c66d2b87c1e14318a532c88cd63b1695c1e170e18552a0c2b628b387c1e14318e57048bc2e193638370785c38e17c525d1783c2e1936383f0785c38e1905669178247e170c971c20585d66b1e854ae0f0e38c5299acba117694c762f07871c28594213b1f822be1c718a498091412ff0f849c51104b24518adc0e1f0a1a411b83c2e1c7c50ff0f81c10e060605e1e1a08067038704e112c0e1f07851f1499c3e070b821f188dc1e170e3e2f0f81c2e09303e370f8422e07043e309387c2e0704448c1c160a0441b81c3827088e017f87c1e1088626d1f81c30521383c220234da3a7515c0e1f))
def g479H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x150800000000000034940000000954000000001800000000000000000000000000000000000000000000102c00051b30d0000126800000000043b000000087e000000000000000000000000004238000000000000000000000000071680000000000000000000000000000005300000000000000006db0000f1e000000000000097b8000000000603000000000000000000000000005990000000b3a207c0000000000000000000000000000121e32480030bf843000000384380b00000034b800000000000000000000000000000000484c00000020480026fe0000000000000472000411000000000000008a400022c183b82a0000000000000000000000000000073a80000000000000000000000000000000000000040f8001a170000000000000000000000045dbb88002c3a0000000002176000e078000000000000000000000000061a4000000d1b800000000000070cc00000000000000000000000002e7c00000000000000000000000000000000000186200020a0000000000000000000124e117d9cc0000008a7d0d14dac05000000000143d0000000001e7c000000000000000000034ac82e808d994000000a3d0000001e1b822800284cc604038000000000320000076e000700000000000022a00000000000000000000000000000367a000a0600000010420000000000000e18000377400091f800000000021a800000146a0000000000000000032c0000007230965c5000000000000000000005828e780000000000001c3a37c8000000000a11800000000000000030f2878000000000185100070b566a000000000000000000000000000000000000000000a1500000000009020003449841c33118c00000000000000000000000000000000000000000000017f0000000000000000000000000000024329c5f00fb1a9f00000000000000a6e000000000140d0006088001e7d000000000000000025d8000000f3f8000000000000000000000098ab89400000040d7b36cd600000015d647002913bc0c8000eef0000003838000c3780000000000000000000000000000000000000000000006fb000000386c271d308002c3000000000000000000000000000000eb5800000000000000018a062b9090930000e08000000000000000012e800063933d8000000000010615c00124b000559c0000009139188001a3b00020f000000000000000000000000000000000000713c0000000000000000acc0000001cbc000c3380000000000000000c9000000000014e000000000034b60000000001c0400000000000000000004edbc2c0004dd800000000000020400000000800100200202011030120000001001102030012
def g479D10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x510c80c8b8387848e38423a2a58e60e16195908ebf8583868a38391910e034025a2e0e161ce23984645008e9b838785388a511c01125a3a2a6e1e0e14e379846440d00388b838785388e5b20322e1e160a38e100c8abf8785824438423afe160e1a28e0e8e8a964585838638403e1e0e0610f8c39823181863e312110e0203e1e0e06112398209818658523a62312038fe1e06160920f878183843e30e61e0e0610f8c380e0a09878183844608e020583e061e1161239838187843e312110fe1e1606082118238084981865824405908e03e1e0610790080d8781838436061e091081610190d082b81878448fe08302606182e111804986080d8384396056061e160820f8182080d845e305e061e103078d87820d841c2910f8e0202e1e060e11258098381865c4e3c2864260e196e11590580a09818782524e4108f8e02e1e0610790498187843e2e1e00fe1120a401e3e0b86498184c4482b16161e0120c590a85024d818748c449191030e60e161af900c8e9b838784383a3a6e0e1e10e0d005639858782be38360e1e10e0b8783843826091618e08588a8300558784c9384fc83d75e44eeb75639c5c6cdfb6ec36f5b44d876b63515a3ccf366832c5924c7362830a580cbe35dc2e256dcb4758c2bd559caa7534292543c9ff4ea26c530c95f49e24651e48d345422150c48474102024fe47db3de1e84f0c7673a41c84de46cf35019f4cb463730c1794b745872ac14d4a244f326812d493447322a10b48243f71ea0eb472436f1a60ca461c2fb16a0ac452427312c08f444c1ff0f006f43341770b0052424410707002f413c08303201340740270003ff59574fff75993ff9d664ffe75593ff5d564ffe75193ff5d464ffc75193ff5d954fbe869d3ef61a74fbf659d3ef59674bfd879d2ff61a74bfd859d3efe1974fbc865d3efd9574fbd655d2ffe1574bfd851d2ff61e64bfd86993bf9da64efd76992ff61664eff65993bf59664fbd74992ffe1564fbe74593ef5d164ff781593bf5d864bfd85193ef5d064bfd87952ff61a54bfd85953ef5d254bff86552ff61954f7e75553df5d554fbe74553ef5d154ffb80552ff61854ff786547fd21951ff676547fd5d951ff784547fd21151ff674547fd5d151ff764547fd99151ff564547fd19151ffb87583fe21d60ffb85583fe21560ffb75583fe9d560ff975583fe1d560ffb74583fe5d160ffb54583fe55160bbd879d3eb60a74dbf749d2fb60a74dbf765d36f5d974dbe745d2dfa1474b7d851d2efa1074dbd741d2fb60874bf5811d3afd9264bed82992fde0564b7e85192df61464ebd64192f760c64bf581192fe60064f3f54952fb60a54bfb80552fb60854bf581153ed9d151fb574547ddd5151f7554547f950951efa76583be5d960fba74583ee5d160efb64583be59160fe942583fc54560 else 0x160c0a09878183843e384458643229125c661e060e14223984837190c188e449b81878385088a72396461226c5434261e06160a29a96168e8b090d189a5f14598187858278f0e0d86a3a6926060c261e122c31c38169a1a8e8a965f83098185870c712110f8f0e0dc260e023e1e122c31c0c45838187844838461e060e10f8e0d878185823e38360e061e1230f8d83818784383e303050e61e0e061020f930e09821a1987818458483438e06e08261606185940e8c99878183843e403e1e0e061230f8e0f878381848c3e3a62361e0e0610f8f081449838781843e4608e026003e1e11605930c1986098183843e40602608561e0611610180d829a8e4581878458512038326a3e00661e0e1421783818784444830622a5c26061e0e111123e0c8a960a1981878385085832f8261e0616091100a181509878381844848526a3e08e61e0611612481a0d0a8e089a0f0d198785818214786008ae1e061160e480e0c9a8f81878384385030260e061e1120e48083e0ebf87818582445030e60e16002618f901a0f0a17878184098218503828fe0e16005e191130c3983878184083e442859161e061608e101a140e178785818238482d160e06161920e380a0f150983858186485430e0260e1e1601210480f878583803e4442060e16191120c0e0b81863f820984184e1e06112160b87858048582e061e112160a88b987803f84483c0e1e06112160c0b87818448583028fe061e112160e8cc43f8781844838fa3c0c5c2e1e06116123e168e0b030b1781878458585c08fd261e06116103e0b03170a4981868d84365a2e0c02fe1e10e1)
def g479H10 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x7f22380000000000000286d0000000000000000000000000000000000000000000000000000000000000000000000b11f00d0000000000188fe0c80000000000000000000000000000000000000000010380000000da4ec0100000000000000000200399bc0000000000e2948933113c6ff11400040d40000000000000000000000001038000000341062c8000000000000000000000000f16400000000000002c5f00000000000000000184c0000000000000000000000000000000000016dc00000034a800000000000000329c00000024af0001c9e000000000000000000000415c0000001c85b66800000000000000000000000000001a40000000c09c000000388a00000000001c3b000104b000000000000005258000000267800000b40003015418f80000000000001c8c00140000000000000000000000000002c3f0000000612800000000000000000000000000000000000000000000000000000000000c224000000000000000000001298000000000000000000000a260000000000000000000003c410000000000103400000000000000f2ba8400002cabe1f40004124000d192c2f12a99b40000000000306ec1740000000d41550000000000000000000000000000000900000000000205b00034799160000a0ac000000000000000000002c500000000000024b0000000a2b000000000000000000000000000000000000000a20c0000000000000000000000a6000000000000000001839000000000dc0000000000d0c707c0000000900803e0000000000000021efe8ef20000086cc000000283d000000000000000000000000000082b55a9f189a76000301400000000000000000000000000000000000e207474f062c91000385a0000000092700c0000000000000000000000000000000000000000000001eb7000000000000430000000d2dc0000000000000000051a80000000000725c00000000000194000a2cc000f090000000000000000000000000f02d09900008a100000004184000a02800000000000000000000000000000000000000302400000000000002b9200000000000000000208b721c000000000000000000000000000000000018220000000000000060a800000000003a6c0000000000000249b000345e00000000000000207400000000000000000000287500018530002066000000000008710000000000342610eae7b521800000000000000000000067cf1e8000c67c0000000000000000000000000000000000000092c4000000000000010680000000000109d0000000000305c91e2c19a2700070003c774144000b07000000014670002882000000000000000000000000349f0002ea3114988d00000003083c25904a869128c000b1b00000000108101840064800000026b04300000b040081444 else 0x92d800000000000000000a138000f15bcb090c000000000000000000805e85500000000000000000000000000000000806000387e000000000000000000000c03c0000000000ba4ac7310b000000015960000000000000000000000000092000042100000000001c360000000000341a00000000000000c150000d2800000000000000000080780000000000f0204488181a14000149a000300400000000000000000000042200009058000000000000000000a578700003c950000000b0a2033525000020440000003c6b264800000000000000000006ea4700000000001c3c0000000000000000000000003c46e6800000000000b13c0000000000000000000000000000000c688000000084d0002c76000000000039b20000000000000000000000000000000000000000000000000000000000034a2000000000000000000000f08c00000036a900000000000000000000032a40000000000000000000000000002d99b07c000000000000036b5104c42e00000005108cb5000382900018720000000000000060b4000000000000000000000000000008400034a40002c)
def g479D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2c0c14e073f0e0418410b0c14384447e1c08308a58182a4381e1c083082161c28c0d0e041841090e14304182a0c381096161c2c0090e0c20c42c0e18e0549060438410b0e18284490a0c38088a581c31f38161c083082161e1c08308f8c1e1c28104f8c042c0870920c003418708e0d93db744486f8364afa266012030060007fe74ffae9ff1d3ff327fd64ff8c9ff953feaa7fc54f7ce9ef5d3faa8ff960
def g479H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xb7458954e3359a4000847b0180030c40005093028000e0452600000000000000000000000000000000000000000028de65a92b80008400000003994cc30170000000000000000510e84c0000001b0a093024000000006a00000008658ac00042e00000001c2017f5ad08de06d270000000000000000000000000000000000000000002c45c1c3128001472702000415228c00000010340000000000002581870d2680028be000006000000134d0000000001912000284c000e5d00017200000000003ba9c66000ca6000000146cc8b688c0000000000000000000eee00000017170000940000000000000000000000000020040000005d54000000000000000124b00000000010450006b1842b84fe028000cdca4a000000000000051df121986016000218c000000000303c000000000000000156d0000003c4e000000000000122100048b8001a3a0000001cd645500068f9465a30733800000022800000000014180000000001e3d12f08200016410007948000bdb0003025c56000000000108400011b00000000008200000000000000000000000000028c50b7e1d6088000000000234683906e0000000000000000e3200000000004818001c00a340000003c70000000000000025800000000000000000000000000f008000001051000502d8b2000000000000000000000000880140002b1c0000000005bb400103c8758000000e070000000000000000286c8a74604a9000000000033690fdc3e000d08000000000010d0000852000d1500038d4a1e0023111243102420303000021070910203
def g479D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3001084ff
def g479H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc60000000000000000000000192801330015b6b6000000000000001ec00000000000000035800000000000000060d3381000000000000000000001140000000748000000060c000000000000000005c000688001d325af341e120e000000000000000000000014d000000000070e007f800000000004040a0032c00000000010b800a400010148
def g479L : Nat → Packing
  | 5 => (7,7,6,0,0,6,0,g479D5)
  | 6 => (43,6,6,0,0,9,0,g479D6)
  | 7 => (83,5,6,0,0,12,0,g479D7)
  | 8 => (128,4,6,0,0,13,0,g479D8)
  | 9 => (184,3,6,0,0,14,0,g479D9)
  | 10 => (113,2,6,0,0,13,0,g479D10)
  | 11 => (13,1,6,0,0,10,0,g479D11)
  | 12 => (1,0,6,0,0,0,0,g479D12)
  | _ => emptyPacking
def g479I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 11 2 8 3 1 g479H6
  | 7 => lookupWord 15 331 3 12 6 2 g479H7
  | 8 => lookupWord 28 139 7 13 7 2 g479H8
  | 9 => lookupWord 40 593 4 13 7 2 g479H9
  | 10 => lookupWord 54 811 3 14 8 2 g479H10
  | 11 => lookupWord 34 347 4 13 7 2 g479H11
  | 12 => lookupWord 7 107 3 10 4 2 g479H12
  | _ => fun _ => none
def g479 : Forest := ⟨479,12,fun i => g479Y[i]?.getD (0,0),g479C,g479A,g479L,g479I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P5_0 : block g479 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B5 : block g479 5 0 7=true := g479P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P6_0 : block g479 6 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P6_5 : block g479 6 5 38=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B6 : block g479 6 0 43=true := (@block_merge g479 6 0 5 38 g479P6_0 g479P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P7_0 : block g479 7 0 34=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P7_34 : block g479 7 34 49=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B7 : block g479 7 0 83=true := (@block_merge g479 7 0 34 49 g479P7_0 g479P7_34)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P8_0 : block g479 8 0 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P8_17 : block g479 8 17 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P8_100 : block g479 8 100 28=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B8 : block g479 8 0 128=true := (@block_merge g479 8 0 17 111 g479P8_0 (@block_merge g479 8 17 83 28 g479P8_17 g479P8_100))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P9_0 : block g479 9 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P9_5 : block g479 9 5 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P9_101 : block g479 9 101 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P9_108 : block g479 9 108 70=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P9_178 : block g479 9 178 6=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B9 : block g479 9 0 184=true := (@block_merge g479 9 0 101 83 (@block_merge g479 9 0 5 96 g479P9_0 g479P9_5) (@block_merge g479 9 101 7 76 g479P9_101 (@block_merge g479 9 108 70 6 g479P9_108 g479P9_178)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P10_0 : block g479 10 0 40=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P10_40 : block g479 10 40 64=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P10_104 : block g479 10 104 9=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B10 : block g479 10 0 113=true := (@block_merge g479 10 0 40 73 g479P10_0 (@block_merge g479 10 40 64 9 g479P10_40 g479P10_104))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P11_0 : block g479 11 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P11_4 : block g479 11 4 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B11 : block g479 11 0 13=true := (@block_merge g479 11 0 4 9 g479P11_0 g479P11_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479P12_0 : block g479 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g479B12 : block g479 12 0 1=true := g479P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479T : checkedTables g479 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g479 0 0 0 = true)
  · exact (rfl : block g479 1 0 0 = true)
  · exact (rfl : block g479 2 0 0 = true)
  · exact (rfl : block g479 3 0 0 = true)
  · exact (rfl : block g479 4 0 0 = true)
  · exact g479B5
  · exact g479B6
  · exact g479B7
  · exact g479B8
  · exact g479B9
  · exact g479B10
  · exact g479B11
  · exact g479B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g479G : graphValid g479 (boundsBefore K255) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low479 : Lower true (varsX 479) (graphGoal 479) 13 := lower_forest (g:=g479) (i:=0) (hints:=8858396484) (before_sound K255 V255) g479G g479T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K479 := extendKnown K255 13 [(479,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V479 : Known true K479 := extend_ok (m:=479) V255 low479 (by decide +kernel)
def g503Y : Array (Bits × Bits) := #[(0xfffffff8000000007fffffffffffffffffc000001ffffff220691f524e446aeae40804ac42298aa9c285400000000000007ff001ffc007ff,0x420001520a10003520a10002520a100014822002c11001420029180208446a2a4400042c40290a08c085520a4148290520a4148290520a41),(0xffffffffffffffff8000000007ffffffffffffffe000000d9584892129806c813c949d4a6e6c7e01a541c00000000003ff800000003ff800,0x804522604c02292604c02293604c02291904012482009265150489202900688028848d4a6e6c2a01a440c658cb19632c658cb19632c658cb),(0xfffffffffffffffffffffffff800000000000000000000041e14c0022169f64813296237e871097190d80007ff001ffc00000ffe00000000,0x160b800000b03800000b03800000b05e00020f000107801c04000220297440102800276051096190c800380700e01c0380700e01c03807),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffffffffffffffff808b6248d743f051058cb030d5402e6b21724000000ffe00000000000003fffff,0x984c009004c24009004c24009004c2600804480402240808902481543b0410100b02011002c4b0132008a1142284508a1142284508a114),(0x76018cf4912109835ab4398a38a4678927f1a00000000000000000fffffc00000,0x14e07004e0a703804e0a703804e0a70380104870082438056010c74912108015ab4398808a0670922f122dc5b8b716e2dc5b8b716e2dc5b8),(0x58c775f0c81ad0c6107fa8c30d96300d09c27ff800000000007ff00000000000,0x18ff800000c7fc00000c7fc00000c7fc00008f800047c00018c665d0401890c4107da8c30d923001014201f03e07c0f81f03e07c0f81f03e),(0x1936a52ce9099033fc550b45031181042a831800000ffffffff80000000000000,0x1f00000700f80000700f80000700f8000020f00010780000826a524c8080032fc5503010010010020811310620c4188310620c4188310620),(0xced20222199622b270da64a1083af831e6a663fffff0000000000000000000000,0xe0000007ff0000007ff0000007ff0000003f00001f80000ce120022199420b230d824210822c821e6a243e07c0f81f03e07c0f81f03e07c0)]
def g503C : List ColumnInfo := [(2,0,501,0,11),(32,0,471,0,11),(64,0,439,0,11),(256,0,247,0,11),(1,0,502,0,10),(4,0,499,0,10),(16,0,487,0,10),(128,0,375,0,10),(0,2,357,144,9),(0,64,182,257,9),(0,32,466,5,8),(16,2,357,128,8),(128,2,357,16,8),(1,32,466,4,7),(4,32,466,1,7),(17,0,486,0,7),(48,0,455,0,7),(132,0,371,0,7),(144,0,357,0,7),(144,2,357,0,7),(160,0,343,0,7),(5,32,466,0,6)]
def g503A : List (List Nat) := [[],[32,116,134]]
def g503D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc6608173029b2b26a958d3258120e2cac82a5634c9604839a22a78458d3258120
def g503D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x11008000000000006660800011983f0fc119870d00f4e8dcd0c4b8ac8c80746848014b7ae29858d325821fd5d130c8264b072d89858d904c960c5df2dd132cc1a418b7e9ba36616348317dd3740cc2c69063eba2e819858d20877f74cc708b1a411faae6a94c9604831f55c152992c09067a8a9e113258120dd9552b1a64b0241db22a5634c960483f45c22c6992c09066c8a958d3258120
def g503H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe7002a
def g503D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x82000a0042a080090300830299600acd44080c08001000208038180020001000200040008003208fc40c00791c2c9f802f0020006c00b2dc010a0187820a040040020141028205040a0e1c1000c081c1d382019ccc100010002005156e00c00ac3c2000215040002b0f0a6601f007e00400080015428025428026082001c10383a7040a081c1938333040000000000f069789131000af83c333102be119873b2734e09a330a5e49b92b1f632c5688f0e2073ff7e0f85e93cc78ce95cfb876ded81a8b42654c6d862e25a6b115aaa652ea45412734c897923237450889009fb3c6750e29bf372684c01712c454c9d9232284387f8f01c2348618b414a27c4c89311a21c4087b0a212c10800cefe9192e0d60aefe9192e0d60bb768b8358d60cf764f83e0960afb68b83e09608ffea583e09608ffaa78360960cefe538360960cefe518360960dafe516360960db7e4d6360960cf768e984c960cfb68a984c9608ffaa2984c960af768e984c960afb68a984c960af7e8d984c960afbe89984c9608ffaa4984c960db7a61634c960eb7261634c960cfe261904c960fb658d904c960aefe919261930af7e8d9261930afee819261930cbfe598660930cef61b94609309fe69b9060930deee5390609308ff6a69858930abf69a9858930afb68a9858930abfe999858930afbe899858930beee919258130bf6e8d92581309feea58258130bbee998258130beee918258130aefe9993e1120cef65993e1120afbe899660d20afee819660d20cefe5b9460d20cef65b9460d20afe69b9060d20eeee539060d20af7e8d8660d20aefaa78460d20cefe5b8460d209fe69b9060d20eeee139060d20cefe919858d20cf7e8d9858d20cfee819858d209fee819858d20cef6a78458d20cef6638458d20dede139158d20bfae899358120cfeea58358120ebee998358120eeee9183581209feea58358120bbee998358120eeee118358120faee116358120fb6e4d6358120feae139258120bfa68f9258120fba58f9258120bfaaa53258120dfa2a53258120feae113258120cb7261634c960cede139158d209fa2a53258120fb258d3258120
def g503H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xab000010400050b4000011ccfa4000000059a7b2e10018034802cc00004b8d0c112
def g503D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1941616508459710849854612c4a00f131049943660531819831228c42066a518989424c60081d12959849121150c57104598425a1093285809894511a5a1156614571044307a5c40c00e48414011211c181711006150f470e4f81943619365e013804c3c3076508159c24ba1602725163c8454315e10f0e9410f0e48a541401a1c1154661111055849c3c4e1670854ad819f84506e1670e8584549c9850fe1150c4834a0838451541a0b31116121c30f2c456012143c9f845440ac4c7e3e2e0e1a6231380483e0c4e3e2e15318a9879b138f8b82971c9a6a5c4e3e2e1e0c72382978f8b87124c7a5e1c4e012143f8f8b87829c60fe0130e9f138f8b878194746e2e1e00f16978f8b87803c62ae7e3a5e2e08f1d138b87803c584e0e2e10f159780478b843c6c5c46766e2e3e0a10a278f8b8298545c5c4a6e3e2e1e067223f9d878f8b80547e10f150c423e9f8f8b80547e244e315102b1713838f8b84cc80aa0e3e2c5c4b31f14a29f8e9b8b13848e0e3e2a71517804b899854566e2e10fe015a71c56138b8714cc6a7e1e3e215169f87819b8f88547a6c50ac4e3e2e01f39b34326b1d315b1230aafd2f7af22e8ae12d7ad22c6abb2b3aac2aaaa1293a8c284a7b273a6e268a5d255a4e24aa3d239a30226a21215a0e2029fb1ef9e61de9d31c99b81b09a318f97e16e96315594e13e93312591610a8ff0f18de0d28c10b18aa09a89107f87005e85304783802a81f00f80037ff25c1ac1bfd92e0d60bfec9706b07f7e0d83582fff24c1ac1bff93e0960dfec9f04b05ff64f825837ff07c12c1bfd83e0960f7eb1f04b07efe5182582fff26c12c1bff8360960dfec1b04b07bf58d82583fdf04c12c17fe984c960dff4c264b06ff661325837f930992c1ff9904c960dffc930c986ff649864c3fbf26c32617ff9261930bffcb304986ff619824c3f7f28c1261ffb9060930dff4c2c4986ff661624c3ff724b0261ff99258130ffcc12c0986ffe59834837fb2cc1a417ff9660d20dfec3306907fee4183482ffb30b1a41fbf8458d20ffdc9ac0907fe64d60483ff306b02413fd92e0d60f6fc1ac6b04ff64f82582f7f28c12c13fe984c9609fe4c264b07b758d325827fb25c3261bdf93619309ffc930c985f7e4d864c27fb2dc12617bf9460930bfdc8304987f6e4d604c37f704b0261bbd93e11209fecb706904ffe598348377f28c1a41bfb9060d20ddfc2306905fee41834827fb30b1a41bbf8458d20bfbc8ac6907eee11604837f706b0241bf98358120f7cb1ac0907fae4960483fd264b02413bf9460d20
def g503H9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x78d681f9faa2000418d1ee90e010002128003162dd8c58006cf0910000cb000288e22b91e9569990b8002000a3f2080000000000018788ef1691a80000000000009370331868ffa0000421e0c61740400031200000072708f182819215e848000a680000029d80dd2480590961b18a8000000000000cbd1d2dc00000020e2259a300000051cd1450ca17a4fd06f2600078200000a7254cc00051e29000000051b800242cde009b1f000148e5000049a094800000380c05000183ea408730618b78800041c0007c3000793ad1ddd0004a1114005d087806060c240140129463
def g503D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x32c7c78b0e04d10889807e5c78b09323344c78b0e04b1c88f1336122971e2c054a8f8d2e2c38134423065c78b08f263e72b8f160c23c7223d2c4c78b0e08c9ca899f08fc18f115210158b8f144c2cc889963e3c587026232c4c78b0931a2664b8f160c31c80a9f1e2c38078e3e260cb8f161264074b8f160c23c7083f2e3c5870278c481cf9b063c45470e9b1e2c05464d147e789871e2c054a099a2e1c7831272a4e5c8223e3c5863102b3e68b8f16088454da1f34642c47820f65c6b4f622b4d51a6545c7c0dc97427a4346087c07c003ffe0d60ffd83583ffe0960ffd82583ff4c960ffd864c3ff60930ffd624c3ff60d20ffd63482ffe0d60efd63582ffe0960bff864c2ff61930bff824c3fe58130fbf84482ffe0d20bfd83483fe58120bf78158eefe1120
def g503H10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1738688001121c5c81781f492b7160d43e001496000375c0b80943869a000847629231462000000d5f573b5db78000001e45c11e5ac68418a86634001442001849e2ec3dc71876001e41316001a7e000894001c7a80021402090d82c00004cf7661b09800103a06bc5f50946d064a05802480c1200020ea5304e00168200066f884a90c78001067e3600005421c00085600028e223e7c84a00000000000107483200162725800048c719e50000000a0708b82a273460000706000824000000883830210405000010f04001811628086196408f
def g503D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x9648e28531e69478e08a11089c69448e28603c99e61448608e2549ae783c00ffac7ff583fe987fd20
def g503H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa59dc000000000000000b431a43d2400592000010441c006c4888008371800001e5000620000000000000b1f82000000078a0069e00000000006a8000000000506004acc80014a000e1000000005200009801b58000010
def g503D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xe6290620808ff
def g503H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6d00000009c034800000852016c000
def g503L : Nat → Packing
  | 6 => (3,6,5,0,0,5,0,g503D6)
  | 7 => (15,5,5,0,0,8,0,g503D7)
  | 8 => (79,4,5,0,0,11,0,g503D8)
  | 9 => (78,3,5,0,0,12,0,g503D9)
  | 10 => (23,2,5,0,0,11,0,g503D10)
  | 11 => (4,1,5,0,0,8,0,g503D11)
  | 12 => (1,0,5,0,0,0,0,g503D12)
  | _ => emptyPacking
def g503I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 6 2 0 g503H7
  | 8 => lookupWord 4 29 2 9 4 1 g503H8
  | 9 => lookupWord 23 139 5 12 7 1 g503H9
  | 10 => lookupWord 23 127 7 12 7 1 g503H10
  | 11 => lookupWord 7 73 1 10 5 1 g503H11
  | 12 => lookupWord 1 17 0 7 2 1 g503H12
  | _ => fun _ => none
def g503 : Forest := ⟨503,12,fun i => g503Y[i]?.getD (0,0),g503C,g503A,g503L,g503I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P6_0 : block g503 6 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B6 : block g503 6 0 3=true := g503P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_0 : block g503 7 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P7_1 : block g503 7 1 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B7 : block g503 7 0 15=true := (@block_merge g503 7 0 1 14 g503P7_0 g503P7_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_0 : block g503 8 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P8_4 : block g503 8 4 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B8 : block g503 8 0 79=true := (@block_merge g503 8 0 4 75 g503P8_0 g503P8_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_0 : block g503 9 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_1 : block g503 9 1 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P9_33 : block g503 9 33 45=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B9 : block g503 9 0 78=true := (@block_merge g503 9 0 1 77 g503P9_0 (@block_merge g503 9 1 32 45 g503P9_1 g503P9_33))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_0 : block g503 10 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_2 : block g503 10 2 11=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P10_13 : block g503 10 13 10=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B10 : block g503 10 0 23=true := (@block_merge g503 10 0 2 21 g503P10_0 (@block_merge g503 10 2 11 10 g503P10_2 g503P10_13))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503P11_0 : block g503 11 0 4=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g503B11 : block g503 11 0 4=true := g503P11_0
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
  · exact g503B6
  · exact g503B7
  · exact g503B8
  · exact g503B9
  · exact g503B10
  · exact g503B11
  · exact g503B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g503G : graphValid g503 (boundsBefore K479) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low503 : Lower true (varsX 503) (graphGoal 503) 13 := lower_forest (g:=g503) (i:=0) (hints:=8858371396) (before_sound K479 V479) g503G g503T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K503 := extendKnown K479 13 [(503,[]),(509,[49,100,135])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V503 : Known true K503 := extend_ok (m:=503) V479 low503 (by decide +kernel)
def g507Y : Array (Bits × Bits) := #[(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff89a064d420000000000000000ffffffc001fff,0x80024542921490a485242921490a485242921),(0x674daf4920000000003ffe0000000003ffe000,0x2749a748230b1858c2c61630b1858c2c61630b),(0x0,0x0),(0x1cd11a92a000fff8000001fff0000000000000,0x18901a90a067033819c0ce067033819c0ce067),(0x508e11a0c0000007ffc0000000000003ffffff,0x50861080c41420a105082841420a1050828414),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd6387d99200000000000000000007ffc000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffd638598916deb6f5b7adbd6deb6f5b7adbd6de),(0x235040475fff0000000001ffffff8000000000,0x21404003409804c026013009804c0260130098),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff90128a2d80000007fffffe0000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff8010082518e0c7063831c18e0c7063831c18e0),(0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffae2930685ffffff80000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff862920681f00f807c03e01f00f807c03e01f00)]
def g507C : List ColumnInfo := [(32,0,475,0,11),(0,32,474,1,10),(2,0,505,0,10),(8,0,499,0,10),(128,0,379,0,10),(256,0,251,0,10),(0,2,361,144,9),(0,8,179,320,9),(0,128,361,18,9),(0,256,179,72,9),(1,0,474,0,9),(1,32,474,0,9),(16,0,491,0,9),(64,0,443,0,9),(2,128,361,16,8),(8,256,179,64,8),(16,2,361,128,8),(16,128,361,2,8),(34,0,473,0,8),(64,8,179,256,8),(64,256,179,8,8),(128,2,361,16,8),(130,0,377,0,8),(160,0,347,0,8),(256,8,179,64,8),(264,0,243,0,8),(2,32,472,1,7),(8,32,466,1,7),(10,0,497,0,7),(16,32,458,1,7),(18,0,361,0,7),(18,128,361,0,7),(32,8,147,320,7),(32,16,328,131,7),(32,64,146,265,7),(48,0,459,0,7),(64,32,410,1,7),(72,0,179,0,7),(72,256,179,0,7),(96,0,411,0,7),(144,2,361,0,7),(146,0,361,0,7),(258,0,249,0,7),(320,8,179,0,7),(328,0,179,0,7),(3,32,472,0,6),(9,32,466,0,6),(17,32,458,0,6),(33,2,328,144,6),(33,8,146,320,6),(33,16,328,130,6),(33,64,146,264,6),(33,256,146,72,6),(34,16,328,129,6),(34,128,329,16,6),(40,64,146,257,6),(48,128,329,2,6),(65,32,410,0,6),(96,256,147,8,6),(129,32,346,0,6),(160,16,328,3,6),(288,64,146,9,6),(35,16,328,128,5),(35,128,328,16,5),(41,64,146,256,5),(49,2,328,128,5),(49,128,328,2,5),(97,8,146,256,5),(146,32,328,1,5),(161,2,328,16,5),(161,16,328,2,5),(162,16,328,1,5),(289,8,146,64,5),(289,64,146,8,5),(296,64,146,1,5)]
def g507A : List (List Nat) := [[],[131],[49,100,135],[49,113,100,129],[113],[113,131],[129,49,100,115],[129,115,100]]
def g507D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5c1bb07d990e14209db83760c96e2928ae0dd870e9e85d0b403227edfa65499160e40e09fa7e598354931902da4718b864d7290110b691c62e193d4a40442da4718b864d5290110
def g507D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5c01c50424531a30f30625c1ac30503a311706842b2a28cc0c4ec26c10884370b706b2a274174b05b06d0c111902842442140ea446c1910b4a8b50d464100443b0ad2a18444c384b0e081506084448384a0e0dc0835060ec1d816c38605b111b07f0047636f60c38c3d817c061988b12e0db06b0fb322b833c26c1ac3ecc8af10f09b07b0fb322ac4bc43c26c1ec3ecc8c86c14213bb0696ee2ab1a385084e8c8ec1a5bac6b8a8e13af09b06b10578284eac46c1a5bac6bc21508e944e2ab4bb0e225138aad2ec388f09b0eb4b06622512d2ec3bc21508bc17b0fb07605f01b323017ec1d817c07058db91f0fc17b0f605f01b4d866349903156f10f0d14c26c1ec4ec3ecc88d11a0d329326215158304efc1fc29c401f0e14272832272621d5f8a84e9d30813a72832272621c404ef8a9cc1ca0a72760c71072822ca4882c42c9893e13753392b52491dd1a1165141105081045038fe4fa8f84f78f54f18ef4ed0eace58da4d38cb4c30bacb10a5c9a892487080479872c6a860c5584bc49842c3c03542a02341c815c0d806c001cd6e81a0e615314eccfdbaa5c8b07206a9fa65c99160e40d53f4da9322c1c81667edd526458390354fd32a4c8b0720599fb75498358640e53f2cc1ae498c818af6a396d493190391fcb30ba926320729f9660f524c640c97f4fcb2a498c81a67e9d835493190394fcb306a92632066db966835260530c9bf4fcb2a4c0a61b96e9b52605504c372dd32a4c0aa09866db96683524c530c9bf4fcb2a498a61b96e9b524c5504c372dd32a498aa0985ed1b32617258110bda3664c6a4b02217b46cc9854960443bc95c326b9480887790b864d7290110ef276cc9ae520221de46d9935ca40443bc95c327a9480887790b864f5290110ef276cc9ea520221de46d993d4a40443bc95c326a9480887790b864d5290110ef276cc9aa520221de46d99354a40442f68db130b9260885ed1b6263524c110bda36c4c2a498221c17e5f8654d524c71add8752c290a9877119354d7290110cd232cd190b202215a46d8a864e40442b48db54ac9c80886713a5a959390110ad236c52b27202215e06c8a564e40442b48db10ac9c80886691a664f5390110
def g507H7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x436200100000340800d169
def g507D8 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then 0x7290110fcc54d7290110deca635290110dec64f5290110deca615290110dec64d5290110fd454d724c110b7ce9d524c110f9654d7258110de664d7290110de664f5290110b6ee9d5290110de664d5290110c67e5f8354964b47e9d5259153e725d920e0153aea6979460232aeae954360232ad369673e0132af268273e0132af268253e0132bcc2819454d71ed154d62e0171e9c54f8058171eb84cb8058171ed454f8058171e9654d6060351e87e195454d31ea3e19544c931a2fe9d5261a40ae368b9560e40aa769a9560e40cc7e569560e40a67e9d9560e40ae36889560e40ae56849560e40ea35959260e40a67e9d5260e40aa7e999160e40aa769b5360e40cc7e575360e40ac7a973260e40ac76973260e40cc76635394e40ce360d9294e40ce35899854e40ce36498314e40ce560d9114e40cea615908ca40ea3595834ca40cec60d909c640ee1689835c640ec560d535c640ee160d625c640ee160d325c6408e76a293d46408e7ea583d46408e76a583d4640ca765983d4640ce360f9254640ca7e59834c6408d7ea58521530cd36159221530ad669780e0930d365839760530cb658298d4530cb658198d4530bd268b8554130bd26888554130ed2e158254130af26a26254130e9658385d4d309f2e819294d30db2597904c930bf0e81325c530f9454d605c5309bce8196d4d10b9ce8165d4d10fd054d7058910bb8e81654c910bb468c9858110bb468c8558110f9454d7258110cece1e9890110ceca638590110dac65b8590110bac6988590110dac6588590110be468c8590110be468e6590110daca616590110de4aa19390110de42a19390110de4e999390110de46999390110de4e959390110de4a959390110de46959390110de42959390110de4e159390110de42159390110de49959390110de45959390110de4e899390110de46899390110dac5959390110bac69b5390110de464f5390110de4a615390110de464d5390110dac65b8290110de464f8290110dac6597290110de464d7290110fe054d6290110de464d6290110dac65b5290110de464f5290110dac6595290110de464d5290110de4a613290110f645d93290110fa85953290110de464d3290110bb4698984c110bb469a954c110dd4e56954c110b74e9d954c110af4aa0954c110bb4698954c110bf0688954c110bb4698854c110af4aa2654c110bb469b534c110f94597534c110da65959390110cd261590a0a53ae268f9460232e9454d8058271e9454f8058171ce260d908ca40ce460d909c640ad26a28548330cd266120d4f30b946965358110b9469732581109ac6a76590110da4d959390110da45959390110dc464f53901109e46a65390110dc464d5390110da46595390110de064e6290110de064d62901109e46a73290110de064e3290110da46593290110 else 0x7520c6413981cd019dff9bfab7edcfcf1f853ee37d36f979f1bbdef7b4ef5a9e913cc47924f129e06bbd07726ed59d713a847462e7d1ce6b9b17314e4b1c5c388670bee031bd737716e68db85b62b67d6c6ad7b5addb5686a14d309a37b4276766cd2997bb2836476c7cd8c5314d620ac32184030385fb4bdf1794aed65d1cb8c16e92da05ac6b49966f2cac58c8b0455df2b815646ab6d53eaa3553c4a6694a928ff5142a139408a7b34e949c0935d26724c1296ad2a1251049bc9285227240647928e311a222fc45948a61133223f440486bd0b921404232837104fa06240607fccfd01f4d3df47af4f3a9e173b8875f0e949cf7395e719ce0a1bb637086d48d901aee356269a4d1099d9333864f8c7598b9310e60d0bf617ba2efa5d58b9216fd2d6a5a0cb1815e82b2a55b8a9894f4296e51bca0313d4272e4d6898912d52530499891a12022348457087410a0206e3fe87de8f801e443b947598e6b1c3037986da0d771a8a344c6658c9918a22ff85e60b8f16782ba454b0a59144e27d44e1899112be2430451885b103c1f843d2075c0e281b3033c86310bd2162c2a7051109d41288232841d07aa0e3419d02f205ac0a9012882090356058c08d80de016e01bc0190000afe6835260331cbfe1990d4931ee75cb9160e40ee7d4b9160e40ee754b9160e40ee75c99160e40ee7d499160e40ee75499160e40ee7d498358640ee75498358640ee760d7258640cef66172cc640ee760d72cc640cef66352cc640ee760f52cc640dafe59724c640ee760d724c640aef6a3524c640dafe5b524c640ecf617524c640ee760f524c640dafe59524c640ee760d524c640bf668352e0530b77e9d52e0530db7e597260530db7e5b5260530bf66835260530b77e9d5260530db7e595260530bf66835258530b77e9d5258530fd6d4b8154130fd654b8154130fd6d498154130fd65498154130fd6d496154130fd65496154130bf668352cc530b77e9d52cc530db7e59724c530db7e5b524c530bf6683524c530b77e9d524c530db7e59524c530fd6d4b3154130fd6d493154130fd65493154130fbc2617258110fbc2635258110fbc2615258110ff4261724c110ff4e59724c110ff4659724c110ff4263524c110ff4e5b524c110ff465b524c110ff4261524c110ff4e59524c110ff4659524c110cd7e839854c53cd76839854c53ed6ea55360053ec7e175298d43ec7e155298d43ec7e175258d43ec7e155258d43df24839054d61ea7e195454d31e97e19535c931e97e1953d4931c3fe5f8654931e97e195354931ea75959160e40ee5699835c640ec76155358640cafe59854c640ed6601855cb309b72a565605309f52a5865c530bb6e99815c130bb6e998154130bb6e99315c130bb6e993154130b76e9d52cc130f9c54d7258110deca617290110dec64d) else (if j<3 then 0x5708e39ca60a8423988b07e13c160a31264c7042622c1785f06654208e084ca60a3266385f092440e994c1464c630fe16c7e0ab066344809122c1f85b1f82848890326381d615250488909263483f0ba518509012324c7d2942a1138e1141a8712024685294180eb0a92921848c931984324f08c8b488a60643e83921e0bc2b94a1424549912501ac8f13e2388a144874a0864585121d1e21216156234a0960fc2191615a505d1c0764a48661524c6d040754a68ea14a4c6f08a1949e8ea14a506526a214350a54c2821f0ba53c268e615a0a499008544682f0be0d4a8411c1af0b078298446bc2e4c23c1210f85d1fe0088111d0e3b0b90de0247c9451c378092924d4708c2e4a780926a38514466021062501c99808220ab5444f03b0982bc298f31c48469268464a42213c0785d2904049b0b8223f80f0584108d0b1563583d0be03c2511617a507223a3d9086c2e4a6109260c85145253c06109262d85d11e030ad891585d94f0b24f0823218d118707741bc2f839100c816926501919307e223ee0d61ecc84015c2b8f22a441ca0b64fc1a1222a440248de0ec9a88a20124532862340993a202d94511442c98865340d153262515d0264cc889e16ca584f0728ac9a1262040a162be0fc284107e303371ae25c383e62be0fc289d07e5388f0be0c4eb15178303371ae25c38a1f07e158a84225c2b94082100210ae21d5b8407ce98570ae501f040178282d710e11c1bab13bc55d310e1fc183e62a124507ce518ab9310198a113ae4d8ab94185089d727e0dc43150923841730e4c21080f9cc39317824a1729e168804014c468132744041436509459312ca783b2684819b1518248a12501004b0b60ec7a88a2164c6142276c1f85b1f456c98f60ecca91b262583b13c56ccd931588394f0a64e8ae81b1038a113be16c7d83a2b64c7b0f60ec7f85b1aa44200f60ecc715b281005e0d61d48da61019d98e2b6984b1e8498ad93118ae8171164c4a21a04c999112c7f85b07e10c8910b2639a2c17e028302ff07e14c403e278360b329e008719318d5f80e2a0bcd30a0cf0598f3282f05f006ac1682f34c2f06c16653c010e3263188f01c54cc02f328360ba0c64cc47803283091c17613c019321c6507e0d82cc9f8021c6506c17c0bc01931226506708a8bc2f83728e4d877062247f85420845110a0cbc2e260800f05a1f03a1a074ab44780165116878c0cbc284094c0f05d0be124703491f2506329e1449910f004446529e1449a10f008446329e14c9f83122443c00f63fc289122160fc00c4a02004e53c2b15080203fe0ce53c2b93f060cc7b27e0fc21912202846b29e17c2783144646c991023c2f83f08644880a11aca785f0764d440331820785a2b698c88b6ae8a8420ec7f85f08644881931ac7f85080284940b63fc2a88b26242598423 else (if j<4 then 0x3d044df4369619c2b83d05a1b4b0b60f41696d0c258750d60f410960f432350e4758303ba094aa35180ec8eb07a551a8b61ec1a860e4ce8490f60f416861884087d0920d196821a46088b068c94a8b08510c87d0920f410c07647487d08886c189ed2a4232b0aa56c388886c2e84b0627b4a8c62241e8230e218514523641e8230e2a88b0f60d4359916c1a8885ea55108a078c4086d0ba1341681d0123cc39587c4c08930fa1341681d004288b0f616c1a95b4c884720e21e41e821102907d05a583306e1c2306e1d418663e43585b0960ac08b770e40a531f21ac2d84b05606c0387506530730e60ec108c1ec12830c1998820e21e41e8110c3e1191a41c43c83c05a045110a2283d8350d6645b06a2217a95442298820e21c43684906078720f87c251141ec2a95b4c884626ac1cc3983b02e04660e61e43584306e04660f21ac2283111f583702e0188199b0e3888b06e04c6a3b36ec411f10e07c0310b0e696198ce12c1b02c17e02c3d991f05b84b06e22c3d9918c4b8860ce12c1b0270182ec3d99281790eb07e00c69b7c16c551f12621c258370182c17abc1c17b06b06c08c6b8836f82dc22a12bc0315c1761ed343319c2780c1761cd2c3319c458760cc08d2e0b708689509305208c10826e2c5f0104209c14822e2c68264861442605e291bb1e0dd85d87d1c3617b1f60d85d87d1c311bb1fa0b0068461761f471163f41600d0960d85d87d1c4708e05e00c5f06527c587c196038130892962e498ec2341f0262ba1f4c8da2504702d03e158ae87264451551342341f02f014414991a1743ca6264242131d82ac304415c2388a14484220ba1b41587615a234b0da09485220642683617e0344e87d323593e17e0d4322111c52471546214a584e16485478fa3ec1188243a505d2760b44e83c16620ca9212044582d1fa1490e941b83d82d13a0cc460b32a484814582ec1f803278446c1760d48f80326c42cc8f626c1b15621666c98d626c1a81b3364d940d626c1a91621a04c9d991c1b03505a84ac1b1062b6508b1f61fc2d83b1a101940e84ac3b1062b698513a286c7f85b060cec9b282146d83d1180ac4f80c1761ecc92626c1833c1664f140d60d90d87c1dc1acc8d60ec4f02e0d666c98c2768758546b63ec1f02b1bc549d10622c1f0231264f40f1020198a113b616c7d83e0564f8a92a2685a93a222189d1760f4708e13c048ba26e385e21e08d1784e22898190e0b810d1024689a888d81c88111329a2c5b0a44088a8b3282c13f0b650881115163614f09a470818ae1e3606e0b620630922d48d0f164248b5234505909a2287c450f0321442722c8f8b24fc1f85928c238158b1d83308e0524ec58a62705193c22219832610830426530519331c29ab06a077051a6141a994c1463c1e0a620cc194082201d329828c999514c9f8 else 0xc6a030c4183e0461c602b030044879024c86333608c3b83b0c281d31ce0ec159586a318770ae0ec123334b6547313611c198733360ac30e4dc0e98f31d616c242130ee0ec15952cd2c2131e61ec2b85b08e0ec1595294438)))
def g507H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1624b53000189c021929116fcb4000000000000000000000000000000000002426c270000000000000f0a80000000004010000000000e07e1be4da000408885dc3342ec0f000000160910ee1a3040000932a0140000000000000001426d2800000a800000000010968000003930000000000000000000000014c5c0800000018200000000000000000000b0d8000824000216000000000000d38380014160000001414e070000000c3823200000000000000000000000000000000145e000000094c00c000e27a14685b42ad11a8a200300372a800000000000068c000000000048500014250005cb8000000d158000019c1000000000002180000001416000000000201a0000000000000000000000383e0000000000000e29f188000000000c115093a80a80b40
def g507D9 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then 0x8b9480887ec58a40443f66a520221fb15290110fd899480887f426130443fa72c98221fd1964c110fe9caa60887f4a5530443fa32a98221fd0954c110fe9c2a60887f421530443fa4ca98221fd1654c110fe9c9260887f464930443fa70498221fd1724c110fe8b1260887f4d4930443fa2a498221ef1654c110fe9a9a60887f454d30443fa264982216fb9059510bedc82a6887b359532443f92e099221afb8558110f6ca9ac0887b64c9604436f70ba82217d993d4110faca9ea0887ae59640443f32a720221f993290110dedc2a60887b6595304437d70a90221ee96548110fe4a9a40887d654d2044369b0b414a77c990a0a539e7c830529d97e598154ee9f24c0aa755f9760153f2cb0300a9de62418454f79241c02a774d9294d539afcc2a629ed554d8114f6b2a6c00a7b1f8554d43bccc8664a1ee6e5180cca79f20c1c65aeb6560232d74b2b01196eae51808cb752a8c0465bc99360232de529b01196f254d808cb75286c04659cf76e0132ce6bb700996b3d97804cb59acbc0265e4d6554d32be3c826538ed554d809c7caaa7b04e3e555358271d78c02c138de5e4d645c7e8aa6b12e37c7904c971fa2a9a64b8ed554f805c7caaa7b02e3e555358171d79c02c0b8e9759583d474bb0ca9ea3b4d53e0951f26b2a64a8e97e19534c759f0c992632bf9561a409cfcab07206a7d958390353acac1c81b8e9260e40dc6c9307206e39898390371ac4c1c81b1f5360e409cecc4a7204e76615390353b0ca9c81b1d8554e409cecc665205e66433290371b07194817a9908ca40d4ec3265206e360d3290372b0738c817b1909c640d5ac32e3206e560d719026bb3142e61b55859c730daac2ae3986f2e1520cc3e950a90661bc98548330fa4c2a41987b2d9520cc3d92ca90661b5985483309aec9d0b984d766353cc3e9241a9e613cd988cb30be4c8465986b6583854c35b2c0c2a616d990d9530ce6bb304984f3662624c2fa32138a61ed1609c530f68b02e2985b6659504c2f9321192617cb904c930baccae60986f260b304c3e92a7902617559594f10baacae65885f464332c42de321b2a216f39059510baacaca6885f464253443ea720a9a217d39054d10fa2a9cc4887d154d62442eab2b992217d190cc910f39a9ac0887b494d60443ce2a6b0221ed15358110f69992c0887b88c960443da264b0221ee13258110b78cb6a0885f464f50443ea2a7a82217b29890110f59b2c80887ac59640442f632720221f335390110fc929c80887cc54e40443f22a720221fa26290110fd0b1480887e4cca40443f446520221f913290110fd099480887b4d9530443da2ca98221fc2624c110fe0b1260887d4d4d30443ea2a698221fc2324c110f2ca9ac0885e664e40443e92a690221b495360232da4c2a419879454d60442d632d202217919390110 else 0x2f00996f39cf804cb79ca7c0265f579654d71f9aca2a6b8df9e41325c76eaa7c02e3be562e0171df299700b8f9d54d605c7dca64b02e3f555358171fe2992c0b8efce01605c6f9f20992c33dd90a0f51daea9b01a8ebe58180d467db21c12a3aed60e0951be7c8264a8ef34cb8054677f30aa663b3d8555331bcfc9aa998fc755153cc7f1aa899663beb2060331d5fc32a898de7e4d544c75bf0ca9a63f1d5454d31fc6aa26498eb7e19324c76b930a9a43b5d53e0121d5eb930d206afd498690357aa4c3481b9f9560e40dcf4ab07206e7655839037392ac1c81b9f9260e40dcec9307206e75c98390373ea4c1c81b9d5260e40dcfc8b07206e76458390277f2ac1c81b9f5360e40dcf99307206e74c98390277b3129c81b9d8394e40f8fa9ca7205eb64a5390277b30a9c81b9d8354e409decc0a7206e760c53902f6b2229c817b99014e40dd6c2c65207675d93290375b0a99481ead654ca40ddac1ce3206ed60d71903e6aa6b8c81fa5625c640fd2992e3206e760d6190277b31a8c816bd96d4640bcf49ea3205e764f5190373b07a8c81b9d8354640bd7c92a3204ef6633190373b0798c816bf964c640dcec1a63206e760d21902bbf2ea9661fcb9848330fe4c3a41987f261520cc3eb30a90661bd960e1530be6c970a985b765a854c36bf0b42a61bd96061530aefcbb0a986d7614854c2f9b2442a617d59121530dedc0704986f3e1d824c379f0ac1261ecd6560930dedc0304986f3615624c2fb321a92615df9754930aefcbb02985b7e59814c3f8b04b8a61fc5625c530fe8b02e2984f7a63514c27bb31a8a616dd96d4530f2eb2ea2985f6643514c2f9f24a8a617db9048530fe4c12e0987f2589704c3eb70aa8261f588554130fe5412a0987f2609504c3f94c4a8261fc96254130fada92a0987d6549504c35f2c1c2a61af96061530b7cc86ca985b765b534c36bf0ba9a61e5d65d4d30becc86a6985f364a534c2fb720a9a617cd9214d30beac88a6985f6640534c2ebd2b9926175d95cc930de7c2a64987b3595324c2fb720992617f1909c530faaa9ae2987f14c9714c3de2c0b8a616df964c530faca9ae0987f24c9704c3eb2a6a8261fca3254130fe4992a0985f6657304c3dd6cb90261ee965c8130fe529e40987f254f204c3eaaa6b96215f79754b10b7acb10a885f564c854427ed3132a217d59399510bf9c82ca885bd65b53443ceacba9a21f566554d10bf9c82a6887d554d72443f8aa6b1221fe17058910faaa9ac48857de5d52443baaec99221ee5654c910f784c2c0887bce1560443de10ab0221ef35358110f78a9ac0887bce0960443de2e4b0221ef35258110f78a92c0887bc4c960443ee70ba82217f193d4110fb8a9ea0887ece1640443f610b20221fb26590110fd8b2c80887ecd4e40443f62a720221fb38290110fd) else (if j<3 then 0x865182617fb17b717871761173b170116db16ba168f16641639161815e815bd1588155d1537151b14fa14d414a414881471145a142f141313fc13db13ba13991378134d131812f212c712a6128512731261123b1224121211e711d011be11ac11901179115d11461125110910e310b310881058102d101b10090fe80fbd0f9c0f850f690f520f400f290efe0eec0eda0ebe0ea70e950e7e0e620e4b0e2f0e180e060dea0dd30dad0d820d660d450d2e0d170cfb0cdf0cbe0ca20c810c650c490c320c110bff0bd40bae0b970b6c0b500b250aeb0ac50a9f0a880a710a4b0a2a0a1309f709d109ba099e09870970094f0933091708fb08cb08af08890872085b083a081407f307d207c0079f07790758072d070706e606ca06b3069c067b0650062a05ff05f205d605b0057b056405430527051004ef04c404a8048c0470044a0433041203e703cb03af03930377035b034e0337031602fa02d402ae02970276025f023e021d020101e501c901a8018201660140011000ef00d300b200960070004a0029001200006ff5c980cc77fea4c06637fd90d4931fdeb92c3207ef5cb31903f7ea598c81fbd724c640fdfa9263207ef54931903fbae5c0a61fdf52e0530feea9702987f75c9814c3fbea4c0a61fdd5260530feeb92c2987f7d49614c3fbaa4b0a61fdd72cc530fefa9662987f754b314c3fbae498a61fdf524c530feea9262987e75ca6350ff3ea531a87f9d5298d43fceb92c6a1fe7d496350ff3aa4b1a87f9d5454d61befc82a6b0fd754d72587f9ae0992c3fcd504c961befc8264b0fe755153cc7ebaa6b9663f5d53d4b31dfcb830198fe7551534c75ff0cb9263f5d535c931d7fc36a498fd754f524c75ff0ca9263f5d5354931ddec2ac3207e754d61903f3a64b0c81bbd85cc640ddec2a63207d761572cc3ebaa6b96615ff9754b30f6eb2b02987f5619714c3fb702b8261fd9815c130fecb0ae0987f6e05504c3fb302a8261fd96154130faea9ae4985fe643524c2bff2ea9261fdb315c130fec98ae0987f6cc5504c3fb262a8261fd972cc130feda9660987f654b304c3eeaa6b9621f75535c910ff8b9260887fcd4930443fe2a498221f5d535c910affcbaa4887be5c960443df6a4b0221ef95258110fdcb9480887eed4a40443f72a520221fd9724c110feda9260887f65493044373f06b92c9b3f85d4964bcec9ea4b26e7e0f52592b7f2ea92c9b3f8554964dcfc1aa4b24fbe418294f6bea6c04a7beb2060253dafc1702a9ee7e198454fe3ea4b22a7f1d5259153de6b1700a9dee2418454f6bf30a98a7bbb9460053daea9b0029de76566350f73f0b31a87b9f8558d43d9fc2ea6a1de76565350f67f0aa9a877af9550e32df4cab01195f3e41714cb79ae3c0265dcd7654132fe4b02a0996775db804caf9b2129a657af9550d32d76b else 0x4a122080643f0bc0145c1f094a123498208594c488c2007c2529c2a161f62a200dc2d1f0ae17440b84c2b4408c27094792208127858c85f0b47f0848821c01264327c1922880642f06c9922880662f0bc192288064288d444161f60c24880392288700c98905b1fc292288064331f05f0ac1e0c1f700c99105b5648a20190b0592849922198b05e2a4a126198b05e2a4a126198bc2f060922a880a940801329c2e2020084093bc2f0650a503122c9f06940642923c1b27c2322880663923c2f07c2322880643d118a8922008c7f0a2022b40b2233568ad02c88848f08c8a2140b263122c7f0a20064940d4462acc502c98a48b0740b56940b05b29c2a2a200a1fc1783706c9892308105f0a8ab4dc021c3c1784b568a8842e13c1b27c2122081423e1344d0fc2f07c212208142488105f0ac7850508dc2f078341c1f0a2086bc2f078162a3709835318707c2c1fc2a21c1708888423d0e88705c208088a7a3d1183092230801f0d8370bc1922270bc1e2a1c930490548d548b94898486d4847481747e747c647a04775474046f746b84692465d462845f845cd458e45684542451244e744b244824452442243f243cc43a64380435f4339431342e842c742a1427b4255422a420941c54195416a4144411940ee40c340ac4090406a4044401e3ff33fcd3fa73f723f3d3f123ec93e9e3e6e3e3e3e0e3ded3dbd3d973d6c3d413d023cd23ca23c813c5b3c2b3c053bdf3bb43b933b633b383b033ac93a993a693a2a39ff39de39b83988395d3946391b38f538cf38ae388d387638503834381337ed37d137bf379e377d3766373b370b36e536c4369936733643361d360135ea35c435a835873566354f352434fe34e734c134aa34933477346034493432341133fa33d433b8339733763355332a331332f232cc32a63285325a3239321831fc31d131a1317631463120310430e830b8309c307b3050302f30092fe82fbd2f9c2f802f5a2f392f132ef22ec72ea62e7b2e502e202dff2dca2dae2d922d712d4b2d2a2cf02cd42cb32c832c712c322c112bfa2bde2bb32ba12b7b2b552b2f2b132ae82ac22a8d2a622a3c2a1129eb29c5299f2965293a290f28f328d228a7288128652849282d281627fa27e327cc27a62780275f2743272c270b26f426bf2694266e26432631260b25e525bf2599257825572531250124d124ba24992487246b24452424240823e723c1239b237f23592338231c22fb22da22af228422592233220d21ec21bc21912161213b210620e520c920a3207d2052203120011fc71f8d1f5d1f321f071edc1eac1e7c1e511e261e0a1dee1dd21dac1d861d6a1d491d281d0c1ceb1cca1cae1c8d1c621c3c1c201be11bbb1b951b6a1b441b0f1ae91ab41a8e1a5e1a3d1a1719f119d519b9199319771956193a191418ee18c818a7188b1)) else (if j<6 then (if j<5 then 0x2c9901794305b11c2b1ec1f008ab26530781700cc4178ab2820118170105b318a866d30f50c1624c20200ac0416ca14214326311ac041620142140923f00c1f0bc231e4882105b264f0749e05880662e0b8162a20098321d85956240ec2f0987605c060cca11c1b27072209e8a24e0d07080260ac1f010760cc98d81709871268806636058712849e0c198d8161c4a127830663144c2706ca32740a1d8810ca41dc2a21c1e045132740e2a541dc260587503833263c6a17c1781706c9a2a9e9105f06c9e05830923700ca22a49a20910c55e20198655e2a198744f0941e1d8350e1f0f47d060f8662421088801c21c170bc262908826c5914106e4a86421304a8641d16478781d0d4046f1e88c288e1b9141e8845f09c1256198a0810e0f866202614717c004c0f8c0983e9904d0a8a1782614243c004c0f8f08705c2f09c192849c22859218d07c2d1e0860208926430108705c2423c2e1ec0c264c21c170bc242307826c591c2a5020068884c2007c2f082062313064322788705c2065889161311c2c1fc2222898643042882222009c22221904c1b8a88c4c19250205745b1c1c0ec2486c70918b2bc170aca30809d16447c1596619280fc64190fc261cc5e28287d0741f1a094251787869ac1d45e1e211687f008a03e2e0a459238a094260a63511848a43e0a636282604141641c6115709078922e0b42517878922e0b4227b44517878e1860a45a5548a29c021e4027c04208704c2826846051984c8a8d8140f0a866222809e049989c2e05c1a2a190a8460555a2a190aca70a0881d0506e37082106f0507a2878caf05c2b28200c21705c2b28200a2006b0534c1e0ad586b050782043c2c14d3080c70cd5b1c2107c1121c2f08ca1230504247044870bc252848866388e1ba141e881170a08f074a5268521c4709c107a8506e2f044870bc251e48a1449901002341921c170bc251e48e024997c1121c288147a141e0f08f0bc20814894c190f47a148752625561aa141e081ad0bc251d47a154a0e0707c4f91e4a068352885223478820f0947a154a0bc2929c192608023858fc251d85d1e250bc222385d1e2a21c012688888870049a222221c170888926910d05d3088222190a9170bc0126940a91621c0222558a88705c2f0947d0688f014392098200a023858bc2929c192608023858f0870049c22202253050188908a1647f0b140643217c1d27c2d28c7444388c85f0b4a31d1b8c8592bc170b4a080361709b1c1d09c291e10e16470d42a17c203e47f004a0e85d0a4751fc0528308342b0885b1147f014a1105f0b4a7074991c510e85f0a200645307832165586a1907828206503e19090822708864270bc251e88d06908c49f07c2929c260587616470b41f098151f876163a17c2d1fc261d81700499014080152885f0b880802927c2f08 else 0x530fc07080812947616498fc0126081118594c312c49c218591c530c06216441264a860530e10f01c2f094a02147616499341701c2f0947d1c0821649929ad0b4a278224305d0bc031d4a0c5b97a21061914c1c956208a56416c420e5b94c9a8f5141905a6a55a7832430594cc716e2c17c2b094a31c210c4a50d05f09c13305b8f43417c2331c1144530f4a217c2a3f1b8b4a21702c0110a3f1b8f4a217828781408030424a616471262f090892811127858d081260892985c4232164410dc24224a126191041f01c2d280802385926470485c21c2d2908842201041f000810e08929858f10f004a10c08e16498e8585049f000f94c3507c070a438214791a08e164f0141f0b4782008927859083205c2f08ca42249e16911341f01c142008e16558fc0507c2f09c142147c228592657008591e0f9281a8d8222385d1e908ac1f01c22224c6174a0f90d0bc051e85a234a0f85d044a843c2f0644082470502a2088a43478d05b07c270488a21c01314a120650c0570bc27064992888a42511608a0fc2c17c27048831e88d4490968870505f0bc252888926909217a2710c160817a0896e464305f05c2e2147d06199088f0505f0b8851f418664344c0a43c2d1e885068885e4a21c170bc251e88a43418664c1341f098750f816174c9185d07c260444e1c49866402c499104a07c283e49c2a4a0642927421224a07c2e05c050849e164a122391240f0749c2a488663927081104a0642944499224a421858c1f1268a928c4066311219217140802e054cd0f8ad12200c887014442b859563700c2a1748b282d0b47d0f0ad10200c4460541e1644e5049866430941e05c031185d263e058592255c642866c6b12c3b02c0077c2f06881101f18c0b00c9f061fa20248e88302c03281fb261f0e19b0105b2848a20193264300194162492288080387705b07c031fc2a0d443261f14c1d2305e21c0332c98ec1b0fc031fc2c1748b1b880805700c3e2105d2219b4c3c16c4b0bc030648a20c98644928c0a2a49a20198c447010592888126508e1792648f010594c940fc1b268aa20248aca22140a2ac98a19a20ca22b40b26c88ec1b268ab22248a19922ca064c9a50306448892940802b0ac1b1e885028ab263b134430794502ccb263b12c2b068ad02c9b223d10c1b3194328200d4433194066d30a48b1fc2b0740b26940e19b1ac4b0e1f417c022bc1f0a1787e641784b11c2f0617a2a5e1019b1b84b12c3a04c014305f07c2a2a211a16a0d8130105f0aca0802112c4300d5b090587cd30ec030aca4161f0805e0e16b1083308c1b02d5f018a85ed316c0b00c9f061f22a248ec0b00ca22ac987c30661794305b27c022aca101794305f06c9b108a892405b8170105e0ccc326211105f001f330c9978305f05a04c1f0ac7f008ab264b078131305e2bc033) else (if j<7 then 0x3b09c051709b1c2f0b1302008c26c58dc2b290811689c22351615a3f19088c82703b0a8822345b284043c28268824d45a223a0ac261e63090860bc207548b17878ec5c518a16425170785059091570145c28c88b458510a164251648e1e5909459238a164217982d094461f228d4223145e28225445d0887f008a5223e11831578b07c2f0109c0c08b17130d040660a0270ac60340b0042087426180cc580fc2e29c261d08066440e8742019898a70bc261c9987c340dc270b8a61d45a263a2bc1d274a1168886a3f0a4a709875161a8c0d70688d29499161ae2a470a4a709873161a8d84e0d81126c5c22342a45b4d08c6a2a2bc1d014a5268422145918270bc1d018ad29499168f93065288470bc1d268a8644129c2927c1e05c261d833164e13c260587126c5e0c3e0541a2a195262a1282a388a87c2c0f0361fc2e05c261d0e4604c22c2c15073262b06c7b0f08c1c200c11306c2b1f08c15073264307c2b2820880210c11310d5b090506ad30fc2b0aca06a1e0803044c4306c1356c234c209010b0620b26cc084306ac9c141e3302b06c4f09c1414ccb263b06cc709c1328200cc2b06cc709c1066d30ec132bc2f061a8843042c3308c170bc18822211c2802ca0821b8843044c27044832905078c9900d843c2b1f0512048b2647044870bc2306c7923053264f0a00d2848122200d11043c2d074983b4a12085122550e4812848e142d284812648e142f0b4a06a8506e1e0dc1121c212220042248e4a03a4821449922306610d0941d040ed28851224852659124312648e142846499508514c4f8c84521c170bc251f48a44191385526c7074821141f05c2f089132910d22851266521c2b2849923850c8506b4a13e224347a154a1502a424a223c23224861547914a614c88688b07c2120c8e154a0f4450d4170bc1882238e04504122144a926480f4111049921850b07505c210c4651c49e14441d417094712049e1438420ed2743509c25054721553140ed074106b4a70b4a880441d417094712648614383b4112bc2f06851221a900e923c2f068506b4a8e445044870bc192a190e10d094af0bc193e208e1083b41d05c2d1fc251c8550d499785d07c162044e2249866430047c17c2a20889261910882224c328190a1922305f0055a503417c2d1f41a21c0126889103f01c2b094a444c70e110824c126210a4a04247127858a1ad001e156178ac2528c746e206a4a61647878286b8587853082090e4a0842442087004a6164a926384241d1e85a2088d263b10c2b098586aca0c8606a1e05e558a889571aa66251f41a2019223498cca6169151c21300610c8591141f09c1128189444507c0709c11138592645054710c478424a6163e174112a10f0bc1910209185d289e0690c2142f00c46174a0e85d0ac270147b114a0fc0127c210d47616 else (if j<8 then 0xe43b0ac1c0540f00512454ab4c620f42307803334343e3d08c1e0017c434ac3e3a0ec2d08c1e00d34430fd2a4c2ec3313c130b85d10c99011c2ec286f4231ec1e16c6d1c50450bb0b42306c7e17473264b0d42504c4f04c2e17443264870c2d04c7b074731b85c504844c2d0941306c7e16c9d1c4e0543b01843170862c3f0b81700c5e0d8b1803d078161143e0d4ce2c3e0583130c5e2cca0d8130aca61049b178b0f8170141e0cc59278b0e13e0640128c59265162a422341d0f4ce2a9a8d80d02c050e5be2a9f0e02e05c031f08b291a8f82128c062ac59270f8e8aa1141e05c02214cd26460941d0f8ad328f8c10d1542e0540a1147d0f41f008aa21469b44e0940b01c2e2b43a3e99128450b8122bc022143d4c440d42e08c014c8fa64388ec981141244855214b109130f4112d441218508e412d44d0b43504c9d1185114152b4887c25094152a1953e2d07c02218592688d323e1741d128650f4ca643e1741e204492619e22392943503c1b260fc42a490c43014785185d28908ec170147b1cc35289a8ec330242b09c051ec131c90d28543105b05c026b42d1ec3528cb1447305515134185ecaa6a411cc230749d12c2d065130505d444a242ca9d05b0509d1341b10cb082460941a21c122344e1690d32491bc2f09c162285d1e1896e4e2185f09c150788912498664b03c051e88d289a8c0f30d80308c131d47a434a1383d1341b2b05a229a8f83b0944d0705b2a90a3e441743307c031308b32c99017822c296f10c16c3b1fc0306c6c50614510c16c2b07c030f1434c4c1341f09c061d8112785d324e1741d0f4ca50990cc1b13c0416ccc50c98ec3b07c2f00c7c16c6c502012c2f0105b0e19c50d30f41e1d8150f835329f0f826038161c4490f880664233c030b07327880cc6e0ac1b03c030f076202012c4b07c070ac9c1d880664312c430ac241cc1e0540e20c9941f41c8731fc2e058830740b1b8a970731ec2b078162140e2ac9938430705b13c060583332c9921785a8730b1ac16c7b07c0604c6e2a6416c1f00c3e0419e2ad31144a2285d0a87526351fc2a2e8721743a22382f82043c2d1e46e1741e1c482fc2d068751e85d1a889044e1649e22251f41d0a8722e85d0e889142d0747a2285a1d498e19f0b8a42009c22188fc02260802345a4c3117c2b1ec1c22198cc1b0f4a87c202f8a7078984545b1c3b1ec3d174706e2f0ac1b1f45b0f470d11701c2e2889d16c70e1b86a4507a1e0a1303e190709b01141171343e3026190501303e178c1e91d8586e2509c2f0611328c9a17471141045c2d09c1b26ca21747120e8444a42085927088f801280802249e16370a4a70649c2010a1708905170b87c2045c22108e89b0cc1303c26221306e191243505c251d0c128c58ec331dc23281f0ac251709b1c2115c2b094a70109b1c else 0x11a812c1c0308c0dc0604c3b325402c1f010ac238105f1a904380d8210981103c02658f93043074150d4b0b07307414034347c341c47118c1d0500d2b1f104cc1d42504c1d0cc38f0711c43d08c1d051913d4a931913d0730b423074130f4a92c1d05c030eccd0c311cc1d05c005f4ac6a3b0ac1d05c030f43266d3110f913423074150343700ccb0e543e4791d42d08c1d03c010f4116e17c434a9d10c3f42b0b4230741503c034cc3d2a651083b07413334b50c3a1483d0cc1d04c0f009bd114b1491510c2b0741700d320f4352c5422c1c0540e01403334346a4b070150308f0017d2b1a9108a))))
def g507H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x2068131e6e800330e9a36400030150001ab99404e927f0f10b80000387d7094621e80d800070740003814680a0000000000000000000532a41300ce000000000000000e244000140f000090c8415bf34a0132199c70c811782e608a6293a5c90ee3978f364c7a58dbd0cfe1c6841d4f0f9e3229c0003cef000122ad44fd0a260a7e64d0e10000c4d20002c1228ad000180f6807709253238ba3476800075c9c37604050c0000040cc00024bd000063a0024382901e4011102850bf204e0003c6b39e7826db351c530000a3c46384000409e80b5cb784188000f09643cdc4e18d2f975bb8c0efc4d3215500bd42c70d1911e216d86501350000000000030c70000000056352acb0a30220895000050ea000000000000000c05a43fd04d00000003861a8000001c3076697019906a208e461288621d481aa2688000f12600000004acea1236206810489740ec00026668847403001ac030e1cbe03b239287112e340dde04400020d40116e39c000000053b5e04bc698000501a466eceb91c851a0a37f0821077a06441f205888a5111861b00679872000022250dee054859a0003831d1ba507fa798000001c725d47c40002069718b83180210065a021e2d8d64b87b3dc20003e4b105f000000000f8541f012be24201b10600000000341b80000000606a0cc80000001a17000021bc800480c1573a41bd01000000000000000000000001e88b13b832e8dc800062e00000000280bc01ff07946d48af000000020df028851e061c166e61ec7191e2c320e00000000035e024e92bc9db636243d0cee2168e2d54160000e37647ad05ee8e6000004bc0000000000140ac264d0f1f174a104cf0380690870b87866c80193bdc19902ce86de15062800005079213752fc000000000000001e4a800000004b7da79689950bcb36242e80172104000241c80004178000000048ef0000000000058e30001e2e40006014000182a4000403c700a20314108000249e0000000702dc1b8000000060ec00000000c020000817d4a1c00000000000e3acc5de8d5004a000245be4ce0001201d4cd0000000071e80001046b9800000cd7599831c00001c37e08e0001a1540000000000060a8000000000000001064f0dee0d0000000049ac71080002c3980000000000000028c40001e4a0000603b0000000000048b20000000000070b3392ec2500000000524c0001c5080000000000000000a300000003831000000000000000000000700000000604f0001c0f800000000001c3a6c3f384e2170415c000388d0000000000008e5000067bb01a188a003e8103c42f898e0a40002a37289a0000000000010ae0095424092612100c55010820880030040011860c014018634000102c00504b04508130264e00908228124a08104b2080401004050800c100080604d2c2082040 else 0x3929000107b400028960001a2b000000003)
def g507D10 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then 0x7f754f31fdd32cc6ff60331fbd544c7f754d31fdd324c6ffe0121fbe53903ef54e40fbc53903ef58640fbf51903ef54640fbf31903ef4c640fbd21903f7a1730fdd85cc3f760b30fdd72cc3f7d4b30fdd52cc2ff61730fdf53cc3f754f30fdd32cc3f7e1530fde854c3f761530fdc854c3f7e0930fdd824c3f75c930fdf524c3f754930fdf814c3f760530fdd614c3f7d4530fdd514c3f748530bff854c2ff61530eff654c3bf59530fdf534c3f794d30fdd534c3f714d30fdf324c3f74c930ff6714c3fd5c530fdf314c3f74c530ff9704c3fe54130ff753c43fd54f10ff572c43fdd4b10ff552c43fd4cb10ff785443fd21510ff665443fd59510ff753443fd54d10ff782443fd5c910ff562443fdd4910ff552443fd4c910bff85443bf59510fdd53443f74c910ffb50443fe48110bbf85593e761253fce8294ff360a53bdd8094edf61653f5f5394efb60a53f5f8154fd760553f5f8054fd760153f9d8454fe759153bdf8054fd794d53bde8314fd754c53bf58114efe60053bbf8550fe798d43f9d6350fcfd4d43f9e5350fcf54d43f9d5350fe7cc943f9d3250ef760332eef658cbeb55232bed838cbf394e32fcd538cbeb50e32bed808cbf3e0532fcd714cbf3e0132fcd704cbf354132ddd764cbe759132bdf804cbbbd9532eed654cbeb55132fce534cbf354d32fad434cafbe0132f75539c7ed50e71fe5329c6fd60271ef7609c7bd58271fb5645c7dd54d71fb5435c7f958971fe5325c6fde0171ef7605c7bd58171f5d53587f34c961afd86d479f59751bde83d46f760f51f5d53d479f59551f5d53546fbe0951fcd32546dfa1731b7d85cc7d754f31bed82cc7f34cb31aff864c7d754d31fcd324c7d754d21bbd83903e794e40f9d53903e7cca40fae32903e74ca40fad32903ed9c640fb571902f7e1730f5e85cc2f761730f5d85cc3b7d9730edd65cc3f3a0b30fcd82cc3f59c730fd571cc3f648330b7e85cc2df61730f5f53cc3d754f30bed82cc3f38cb30fcd32cc2f7e1530bdd854c3b7d9530edd654c3f3a0930fcd824c3f398930fcd624c3f59c530fd5714c3f65c130fd9504c3d7d4d30f5d534c2fb60930fce324c3f34c930fdb304c3fac8130ef765c43bd59710f7753c43f594f10f7553c43f554f10fd732c43f98cb10fd532c43f94cb10ef765443bd59510f7753443f594d10f7553443f554d10fe662443f958910fd732443f98c910fd532443f94c910ff350443fc4c110f5d53443f34c910ef960443ee90110fd930443fa48110b9f83592d761653bcd8294ed761732bd980ccaf360e32f4d538cafa60232dcf764cb735d932ecf654cbb359532bcf804cbd3d4d32f4d534cbd554e71fc5329c7d554d71fc5325c6af61a40b9d83902d761730bcd82cc3f248330bcd824c3d554f10f5553443bc58110fb240443f44c110 else 0xb0241e022a9885a4c784c2d5628190a934400b012805a98784a351287c00bf0b835082c505e170702c243a0c3e1e04ab8a8f8405c1f0785c003a20383b0b83812062b101e120b439046b85c1c0b01152a120b816015715880e17c2e0c1c0b088c13c18430585c20502232242182c2e122811c004c8818430585c243c2380099210c1610238587e002640430585c20441f80099185c243c2232170b10c16130026888c88c0238561e0109132323854ae0b0a94c0210263a13008e598ac52410d1646158f86c2e112811190b84088d46426121c3e87890ec26003114170184829261e2e2f09800c4505c2e0c1c0a088b85c260f040a142182c2044950b1b08110986216282f09828844700ab1c8e1385860484927090285c3880391a05091f124811585900bc2e0d2310c00c88c2e0d03281605094382f0b838ae008a8614f429a1d2f5a4f5488e8ead17ea261431e82acfec9f2b3cb27664e879c61378a6d34d4f9a15333a644cc4d98112ec65bacb1e956b297a50849b092a1240a44cc842900d1ebe3ac47018d8b19ba31045e48b0914fe26fc49a88ab10421dcc36b865f0b6213c420f835f05aa08e40e0811300c9ff6bf9f7e90fbe9f5abe677c32f709eba3ce77920f09dddf3b4c75eaea79d313a26739ee52dc75b8797032dee5bba37266d9ed9e1b0335706a44d399a47b426679ece05999b2ee6540c99190fb1e3633cc541885b0bd60dec0857e9af975eb6bbed756ae5f5c22b7316ccad665a1eb3956592c6d5886afd55e12b7d5682ab85552aa69547ea77d4d629795220a309443284a500a9f253b4a7364dd09a45333a62b4c0297392cda55f49ec930d23aa44b480c8ee11c2a352461a8b691582262442887850d7218442c684e508c20dc4164822102f20193fde7ef0fc49f3b3e227b30f3f1e423bfa7704ec29d4939f67320e419c3e37ce6f18dc99b69366c6c30d5f1a8234b06828cd9995c3252636cc421848303c5f64bd317582e4a5b80b56967a2c7c57e4ae315932aae5400a6b14a328e050f4a0993d727484d7c99a92e72544499891e11ee2376459088690ad20523f487c20f511e063b4073c8e191bde37386d20d711a7c342c6678c93189c30485f40bb517042cf45808ac51500291050409d51320257448c08af10d421003fd87b60eac1c4436a867e0c6017642c5853d0a1412f024d846808460fc01da038106ae0cb417d02c70528098411701f2037e05e80a8010b017a02040270000ffd72587ff5cb31fff52cc7ff5c931fff524c7ff54931ffd72cc3ffd4b30ffd52cc3ff5c930fff524c3ff54930ffd72443ffd4910ffd52443ef5c964fbf52593ef54964bfd8594eff60253fdf8154fef61153bff8054eff60053fbf5350fef54d43ff5605c7ef55161fdd53587f74c961bfd80d47ef55151bff80546ff61731fbd54cc) else (if j<3 then 0x5427801307c51404f00260f8b84884030b834a60926228882cb0b8410e84c2e0e168e210585c18a2168e1b0a940842c22211b06224a24c2011858e10c2e0c430b0f8c10c2e130694c124c222285948f080461693170a83c26091e1185a4c8c00430585c243c2213459213130a080204f082188a2c4c303c261f19082109c3c3e40170811190986e28470b0f10a2c5034411607c16030b84204444c322d1c860c04c7c2a291c86c220b00184a103e098608c22210d84c106116941d72a24421b0982458ac84240f008e898b0f81a2e268e151784c140c3013188e94c284c50461717801587c481e1708214a444268b20428a1461529800987c808608642b1e0a2895885161f15162b1f11840fc3c7c1c3e288b0f881f8a0f83458f83e0f0a0d0687c511629121f144587c48a22e1e9110298b82acb010f140f0f8a22c50241509808a2445c5e003114140a3082e0054280785116443e288b14090542601230f45c507844082d8bc2e0e0c4722058b844195647182b0209e001010130e1609e001c26880d0209e002a11130c13816002015130c1f09c1205801989a2a460c2813880cc582c0c298309c54663c0b0b14c005426101e15028a617090ec0418264c384c3e0c0d02250447c2e1707151f08068104c223e1422ab8a8f840ac0b1785c18230010230b048360c3e321a2aab0f8c8483e02058587c0c7d15203a90c2e0f058410a441448450f82486170894488cc9846130440248a1148617088f48c292640470490c2e111e40488c898461304988524c608aac7c46101d841f2391f0a4a0f085423e1494152807c1a4c20118588884a60d2628190a10c1610223d858dc708617061f190a9409e145040142710c1a4c224918230b03e151e28190f0b142ac3e3214308f4a42c3e286222940842d1e302f0510c2a3d078088a4c90a04c230b10210b2507c642a530693140c8508617061f190a18098446420461785478a064342c50ab0f8c8503e0308421bc2c7a391c6f0b1e883c09c2f0428c2a50804108261185e0892401c0e401aa9a163c195635858f04108470b802029a168e22168455a388428d43085c06103e8f85a509208602085c26011f0b4a121844218178442e0b008f4a1413062210d84c0608178549e0d2839511d07c10430b844a0461621261307c2e130611858d481a84c310b1e0a07c10430a4047c2c7844255635858f05448a0178517e0c43800f9310c16005f8441c86220b531509c28a480224c3e490f0a940f8c8484e0d261f198b09c2e0c3e3217090220438922c2709028742d2630a617854787c64342507848740a16931c530b84aac3e321b0a941410048142e2049200a93c2a5050321709834a24d2210198f0b84e170628190c3e8142e2a40248c40c06151e1585a44784e01561585a446c223d221085a4c62042d4c2819 else (if j<4 then 0x21c8b09c40a0481c0a030080204100a900a8100400371e8d422332045154004f0b034a24e048b88969480e022b85c1a4c223e26030041c55263e18038008e1605831a8545e4c130702402522a9345c7c94a4110185c1c55261f1913068220d261f190d02c06161f848704c208b24648300e15289048900808804803e249186198c908834124d209485244a412230b834b4292038391284c2a0b088e484292650390694c2a412a401d04014ae1706911f0e844161706951927c70e0390a8fc2239270a481222400461694498a0644200650b248a080342d0b8047a0c2011498c89252250782c0442229985a4ca46a0e1785c0612208f43c44805c2d0a83c1602208788a98665000210b1b8447a321c668008c2d2893140c88400ca164914100642c06008f41840229319120c41a030b0b4a1048042244484400d6163c558f8540215290b1a8f0804089088341202164155908910c2f008320a6126422107801aa6216931e0e83c061113824cc2d26420f0094c142f089820108541e0217844c6094c33261682c06152b831a90881987d1a8943a15090bc00870a82c1a54827c2d0c820b61511832091c917885088249e0308104742d4c58bc261085a0c6a82c2a512a402c5e2141a0b018547e111c1085a4cc0380c018585a508237211209c28000a941ac2c6e3c2617854a0f050401a4213859243e4018448440608209485a4c78484e068310c2f0aa2c024f0694080445e70350182086121611248848050cc428441a09010b4a040229317982e10e01078547840230b499580c10430b8441a3c230b499405c0252161f478d47908610b804a42d1e2820048108e030b831aa545e4c2d09004a8870b830f90490c0330885c160243118823c1694302686c10470b80c202d278317a524311510e5019a00530b49a503e32210032859243e40181283c06121d024cc2d264a35070bc2e011f848721e04402e1685c021f090287298664c2d0b8047a0d261f19100240e0f00930a84092404102804a055263e1c66104024c2a9485a4480520d261548924619a0216934a0a0643a00650b248a0803215078047855263e1d128381602509985a4c842a0d1e1585a45263a0e05804c42e509420108581602169894298664217010b41a3d26281910020080306930a8f47c440e030249c40923036170224c54803416008fc220e050e8342d265039138481438171049918447a0e050e05c4126408929854985c1c0b089114c1c4c20114588874781d061f198b858a04c3e33142007c2e1227838a044664e14281f19082809e004c1f171628c2c5300130f8e82252547c22250a8441a086e9519108b1f1009246150a801a8dc7a8b1e0e88c111c7a8b1b8c17c2a122811c188a268b471584c022f0449200c8741e14281f198c100987c66204e090381400510b190983e50 else 0x2108381601331649c40825429070181457009949c44a1bc291501408d70b0247a1d0715c0236227c110702c02662a938f902145216090240a3d0e83c04551b1f350b0441c090f808aa9a3e492907808842d329388908346e17010b47a1e5040250a83c042d0ea6940cc890a0e2089c260b011185a4d325a0f0110c2e13048d85c451e8720188541e02210b43e130511530ccb80067090287216171049928d82a0e1702c023e20878a900b42a0e0501c021e2115530cca448110b1185c3926385f0b0447c39070b46c44982215068f8742e2293204401c007c4c32180e0300615171408044804a0903801e8dd2a331c00371aa2c7a3c1b0114c2a2c7c40230f80098a116260f8c2108801290b498a07438004585c1a50430b141284c043d1714488d08c1c09009449c4117162529020b62c2185c1ace10932397088123f0a8383601271624108bc00502015098c0884c1607021161)))
def g507H10 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then 0x4d183b820d530bcf16f80000000060d7886fb01460000b8da217db8306000000004006c00000000000050550000181bfe0a19678802c0816f08d9a0228c1360000e20a10038000000000000401538044e0ac90319876b01c230aeb0f180000000005b9785880000022b040cc24d000000000000030308000282b4403d0000186e400000000b014f8512406869f300005825000000000a0238000341edc1ba185680000000000000034d069c53820000908e0000143000000d00b987658130206800001e5db400c814a00000073192ec2123307100000833c8a03a0e6800000000e07dc0650000241b50164e3010000083c5b1c800005865b83ece095000000002808a0000b07cb02bf600f89e200ea0000000000000000000000000000001304c17cc0000d1c700000857800000000000000003e06600000000000038ad2908e0000000000001289b4104e013d410e0000f011a97fc011e000000000000382e20000000000003c414000000000c4e981eb219454bb80000000001bc604cb858c0000c051f85b7149800016109ccc5e03fc0000000000000009f021d05b8c09c5934c80e1c16e10b2e0606c03ea0aa646800001e3a2c1c1101018524000061ebd0a900002c22f69c900007134903950202a02d683ed0990000090ba4a33d8b7a8116e25a9c7f340ca00000000285980000a12a68fb80003e3e8000020f98862400000000004698300000029d584e0483b0000031f8c817d820800000000000002826833e018d0000787fea3eb813e80009039ec3b600003078405a4000000000000381d241840000b900e931400000000506980003817480cd901d3a62e6375d1b940a980000018be09704c40e6f1c25ee4b2f06b80000228200000000405a1416960c790930b53e816541298c85d8675205c0000000000002f2e012000000000000000000040ce000000001e42a00000822683ce0000c0d000000000001bd000078348000101b714aa40045e2ea000020a300000e18145b6c0bd80001032bf1b2bc4e0000022de61a8000000000232a40088026a84d882cfa1b600000000000013a08e01fd80ac000000000000216cc0001c88e60ac106e241dca173e28880001a2a2c1d570d9a082000000000a0f50000302edb9e500000000340a4110300000000083682177901b800000000014b000002794000000000604184200068404881250009004020e68200e01091c4449d0a0830004740813e00200500008014055030000180003cd89000000e0258a000450003340c10400100000e682810a080011e000044a1c6084608000144c2820038803103408b181000a0a04c840400489020400002243801800180020c3020000a830e040860408803020008300100010004a810a003000400100000c80b0c2400e020c000083c3000004480120c002 else (if j<2 then 0x73b0daaa388000000000000000000000c0e40000384c80000000000000000342b80000707a286ca00ab80250000000000000000040530000000000000801b000000001815692efa42bf93c00000000038530105480d0f01e5847e8b4a41d7c0ef986b00bc981cb70cb80003c30428a45471800000152215b60831879042f8000040778000041fce1e10000000014317e124d0d28000181d20108808c227180001c1e5b47600001114690e800003868880960000005b00003c18c0000806b00000000041ab0000507c400000000a417c82cc0000c08cd09e300d5c24500e30000301b9cbe2014100004856403520000dcebc84ec000009f70000017b9c1f025c2c03ab6810432309ca34de000000000f0b96067c0128c3dd617a50f90000000000000608d0000042c3a02f0000707be83d93949b00d000000001e151686d000014127e04000000000000000000000000000000145fcd860c827d401b405e308d817e5824e00000000000000000804142ef000038084414f60e43626e80b1214ec26fc840dc3bdc56170388000281e7e12800000000000000000c001c81b0000041e0c0b13a75dc28ea02ef853b144381980000a8e3004d5007310b2100aaa665c032a0e6d01940638e38b00a20000701dcc3423034000058708000100b900000000041f40000907e1c2d082220000d033a861c813c89f680d3746f591c1e1330000028100001205900000000000000000f8536841c8c0a894910080000380c8000000000000103f8000012ee9809800000000000000000201141f9b8e800001440a407f50f4c677b0befa12c000011691239c0000206c000000001c0a101035679a8381e1f7d035800020224000050a6ea79a83f00000600b08440431941c70000000000001c0a00000000000000000084f62800b831fe1980000000000000000062159d35bd05b25a3d0220000091bdc0e570e8f837000f5e5f0d00f00001828bc148e2ad80003016ba0ded036f02f20bdbe1210004f024680900000d052e03a18c07882bb2b1a266a02400000e0b6e1772c3ba0000c0d260621bb1ea0be00000024b421e85642016ec2dc83da40c824ef2027782f0405f000021318617a0000910189386c25a202c00007272e430dc14220039a7168263212e00badc2ff81d6102841022057c0001c4b302fa00002c27f40a40000513580001a03162b0187d283778056000069802c0c0000048fe940280000000040d1f80754233c1f592ad000000001c0db0000411858ad5216ac89ec87c11a9a020070437c7f800000192609b883740001a09c589d80000c1974030a8afd88041376000040b5800000000219b00003864c0001a0b8f03b181e4c9a9c0ab40310000281b3f805e0c500001835561130040b03500001813020c800000000021d3e0f35680e02ae0000b0793 else 0x4021000000000000000001d0b800002067180ed036000000000404e512e0e4b70000745ec00000000000000001c0de0005c05d80000000190bc000000001d1c2000030d7016b80001a19a9015740240000000010a83c37ce17c61c6b02480000000000000000000018067a19910a038140000000000000307264a7500120000706c4817a000000000821494100000b081703b441c0b53a00001a5c8c0fc2805a082e02fd0989c8ed301f442e082fdc0b790400000040500000e02648611008c112c00750000321b3a078f0458000000000000a048106b7c2e1201810eb60496801e0000c0e8180e00001c4b15054205c8839ee4c30000281f00000000030053104c0001207200000000042aac16cd08eb042c081600001256e810c000091400000082224b8780b0d0c28000363e6b9d8000070268000091f6200a50174000181c3525b000010257610c5819403ddc38b606a706fe0032239a000020f400001421a407b12dac276102ff001c15031a76f53a8e1c4f4a8884520bf5f1be90331a0d1c0480000a02bac392cb6481ce3080a057542fa0000ed0370310d03d00c9c8dc7076000012104e04b3020d33c0c81d4029f91888bfbd1ff0068d46ff13ba40ae2056f874a016382071009a87f5c0420000dcddf0306c3f5605b0000384280001a08e00004030c827401fe0000083f6e2bc000060fd8000240b9600b00004c0a400000000708f0000000010004509e800000001a04e82d5a029e61660000f86b783c502000000000000000000000000000000000000a))
def g507D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x6025116450b062629003e5809145898842c1c142400a08991a080604502617004c3e4810445c2c1c0080b10140802260500202a4c48501c181110a4289c0080a961a120e060205170b062b00226020145c2c18ac00f90140602050a1f002a2620506848381944042c1858f94061a120e5f00210b0509064222167068483c042c1810a858814090b061c1622342410842c18a400889999516290b09050700266648042c24188410885900621050b081e2300264c5c28841421081c0089315170904070030263c58188414240089599131709003e1e28345829440078a0c110b09070414303c042c241c1080885920f010b09050616384c042c241810f85900413010b0650163c5c2c241c1400d17090500562c1c3e53be39b3743453122ef2c429925e2332181ed1c61a317c15113210b0f00d50ba0930740510320170007fe53ffaa7ff14ffeb0fff51ffaa3ffcc7fe98ffd21ffe61ff4c3fe887bd64fbca7f754fdea1fdf32fdc65f74cbf6997f671feae3ef903ef987dd30fee21fd443aea9fcd32
def g507H11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then 0x610838000018b6f2c9011220f0e0e45009f015707d212fa40e353242c0110f8526e87360a6f007f248d11ce013f05c0090b122f0337c620000c032b0fa4086201800000000c07b0000a2ef6019b4d2f42560e700000000d518142de0cab03c903440c26904d0a0d0d774702056e8e961283c7a4804c8b73d100000905d0000790c1d26d0f300000000422a60ab00000000366ab32b6505f07f7073e4c60000c4a8600c0099e60f112e0000803d62c8e11930adb0ba38230000f32220672530f0d8e0df6665a0ce450f700a0000b10dd016505968ecb22bc118c8d6d0ece04cc004a0400000e910a13102e8350b889a20b6804f1023830160a28038fce480d400b4e07090f9a2cb532e0000646c769df104bd0564d350a5cce55050000096a0a031d8ad602c32df107a70e9d12650b9000000000000a044601db0766d300000a328282cd41e0c840000000000005105f46178350000305a808c74d5703e0000f8267439b11f7c8bc065f03ad09ba0bc7047b52a805ff063812dd0ea011ed8c9652b752d80e35cb650a370d340c4f4412064b4524107b093a4ba3cb7b404c125704d94c7403f090510c11089952f0509309a80c5f82440d6a097302454ad3111f8ce88ea6c1ed101a528851af0b5c0e0d071302a208d032c40d140fc50e858cf307cc828ac6ca4ca206ba0395020b10620dac124311b3026f0350000a42ff09c000040cfa06960a98054c0bd10dd002870f50000f81f282730576027306de4d4e40334d60095604840cd0000a10230ef4323b05b0000604a0000e4620000e52c310ab0680000942a30eb709f401e00000000e51100f8501b20f1b503dd2f4051200b712a0000b2d3a061f822b82100002663f08ea0bb21300000747d90720000e0a7a0122529c0b0a32fd0aaf4848a6a100e009830bef329000030fba087000040d200000000032560b10000f02e202b74c1c5103133a06e80d0d01f14c8000064cc40b200003092204520660000000000000000b82e705e000050cbd022a04bbd326053f0c8368ec09d2103710800a10000d083000000003003b08400007055a0db000000000000b0060000a5020000f803dc0cc0f4151b0000501000005690f0e100000000e2d230e5000000000000fc70502167010000a07e0000d0fe913230af0000603020ee62fe72fb0000a10e4c0e204e00f7b1170000a11a0000a043e0d9387500009469000044a5a10cd468c0ff0000e48b0000b50ca0cc003700001401121f210a18041a0101970b2e5a170008070f1011015b13100429080000032809070c10100411270001062b020a0c4500044b021b1d012204230f022d030e012414000a023103330d030919030427030104010412040421006e00020000000b000004050701020001022103050d010100011307060319001105100414003800 else 0xb4d7b4b70000c50d1331601c20250000404200003113dd0240a468cc70d530945005d0c7000078364326c1270000901a1078f91fd0bf00000000000068c30000000070b726170000426a0000f0a8a096806f000092f7e8e8008850290000f86bf2d400000000000065041829e0740000002f000000000000ecc45115e0de52eef8dab0e6806000007902ed0cf4f8e121000000003011a0c60000c0f2d058812c000000008c76000048320000a0c97833b075708f3899111095141077c0520d0d34a612c7c00de4cd052515278017910b686ea116b40cc8776001608234e1b2fc342bc0ed409e60f6c12382de702d30fde00040c3f0360d04303bf109b0c044afb00fd0aca8000000bb010000e43700000000a080b085b0b342f2000058ed1834c4b05423e12070e240623ae83467608100ae9d250000ad27708ae90342c6906ac0468014b1007129b041e09168c23d1412f1300800008247a11d90b85d11a5062d03ec230000712bc0796002000068dbbe92508b0114a04960dc0000000034b6606c0c)
def g507D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x161420304006ff
def g507H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x515753000304000000a136580003d8395e5730b719591782000851c1aa10b47618602cd66430346121030007480003000000005697830007520002d150e000f0f000000000000000000397042000506855000000609e14eb400096b808b0170d15c00021c000000fd700000000000011181bfc874f474607559000e4ebc740cbd5000000698816d17796805000c0a00000000000075600000064d0400330c355886000420
def g507L : Nat → Packing
  | 6 => (5,6,7,0,0,8,0,g507D6)
  | 7 => (51,5,7,0,0,12,0,g507D7)
  | 8 => (245,4,7,0,0,15,0,g507D8)
  | 9 => (523,3,7,0,0,16,0,g507D9)
  | 10 => (308,2,7,0,0,15,0,g507D10)
  | 11 => (29,1,7,0,0,12,0,g507D11)
  | 12 => (1,0,7,0,0,0,0,g507D12)
  | _ => emptyPacking
def g507I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 8 3 1 g507H7
  | 8 => lookupWord 17 179 3 13 6 3 g507H8
  | 9 => lookupWord 86 521 6 15 8 3 g507H9
  | 10 => lookupWord 192 1151 7 17 10 3 g507H10
  | 11 => lookupWord 129 641 8 16 9 3 g507H11
  | 12 => lookupWord 16 103 5 12 5 3 g507H12
  | _ => fun _ => none
def g507 : Forest := ⟨507,12,fun i => g507Y[i]?.getD (0,0),g507C,g507A,g507L,g507I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P6_0 : block g507 6 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B6 : block g507 6 0 5=true := g507P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P7_0 : block g507 7 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P7_8 : block g507 7 8 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P7_11 : block g507 7 11 40=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B7 : block g507 7 0 51=true := (@block_merge g507 7 0 8 43 g507P7_0 (@block_merge g507 7 8 3 40 g507P7_8 g507P7_11))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P8_0 : block g507 8 0 22=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P8_22 : block g507 8 22 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P8_118 : block g507 8 118 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P8_145 : block g507 8 145 40=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P8_185 : block g507 8 185 60=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B8 : block g507 8 0 245=true := (@block_merge g507 8 0 118 127 (@block_merge g507 8 0 22 96 g507P8_0 g507P8_22) (@block_merge g507 8 118 27 100 g507P8_118 (@block_merge g507 8 145 40 60 g507P8_145 g507P8_185)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_0 : block g507 9 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_5 : block g507 9 5 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_101 : block g507 9 101 53=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_154 : block g507 9 154 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_250 : block g507 9 250 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_346 : block g507 9 346 88=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_434 : block g507 9 434 65=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P9_499 : block g507 9 499 24=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B9 : block g507 9 0 523=true := (@block_merge g507 9 0 250 273 (@block_merge g507 9 0 101 149 (@block_merge g507 9 0 5 96 g507P9_0 g507P9_5) (@block_merge g507 9 101 53 96 g507P9_101 g507P9_154)) (@block_merge g507 9 250 184 89 (@block_merge g507 9 250 96 88 g507P9_250 g507P9_346) (@block_merge g507 9 434 65 24 g507P9_434 g507P9_499)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P10_0 : block g507 10 0 30=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P10_30 : block g507 10 30 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P10_126 : block g507 10 126 66=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P10_192 : block g507 10 192 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P10_288 : block g507 10 288 5=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P10_293 : block g507 10 293 15=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B10 : block g507 10 0 308=true := (@block_merge g507 10 0 192 116 (@block_merge g507 10 0 30 162 g507P10_0 (@block_merge g507 10 30 96 66 g507P10_30 g507P10_126)) (@block_merge g507 10 192 96 20 g507P10_192 (@block_merge g507 10 288 5 15 g507P10_288 g507P10_293)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P11_0 : block g507 11 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P11_2 : block g507 11 2 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P11_17 : block g507 11 17 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B11 : block g507 11 0 29=true := (@block_merge g507 11 0 2 27 g507P11_0 (@block_merge g507 11 2 15 12 g507P11_2 g507P11_17))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507P12_0 : block g507 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g507B12 : block g507 12 0 1=true := g507P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507T : checkedTables g507 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g507 0 0 0 = true)
  · exact (rfl : block g507 1 0 0 = true)
  · exact (rfl : block g507 2 0 0 = true)
  · exact (rfl : block g507 3 0 0 = true)
  · exact (rfl : block g507 4 0 0 = true)
  · exact (rfl : block g507 5 0 0 = true)
  · exact g507B6
  · exact g507B7
  · exact g507B8
  · exact g507B9
  · exact g507B10
  · exact g507B11
  · exact g507B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g507G : graphValid g507 (boundsBefore K503) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low507 : Lower true (varsX 507) (graphGoal 507) 13 := lower_forest (g:=g507) (i:=0) (hints:=13153361988) (before_sound K503 V503) g507G g507T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K507 := extendKnown K503 13 [(507,[]),(510,[32,116,134])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V507 : Known true K507 := extend_ok (m:=507) V503 low507 (by decide +kernel)
def g511Y : Array (Bits × Bits) := #[(0xfc1dc1841010ac9b6a12fd4a29420d78422084286240dc641e655961003331290000000000000000000000000000ffff0000ffff0000ffff,0x501d810010100c912802f942204209584020840862409c641e61504100132008490149014901490149014901490149014901490149014901),(0x12004140638074705a714b6860e9f4350bba35706021f86ae70064c52b3184a00000000000000000000ffff0000000000000000ffff0000,0x982004040218060305a704b6060a1f0350a0a34706001f868e70044c5231184a185518551855185518551855185518551855185518551855),(0x2cb21e243ee4890915ea094281a9381a448598d760130300a3680c70001524e00000000ffff0000ffff000000000000ffff000000000000,0xe20b2082432e4090101e8090281a9181a448180d26001030083480450001104c003300330033003300330033003300330033003300330033),(0x3e1828c33050d02099a2090677769b12650c02852444c14cd8b3c99a5f66c80000ffff0000000000000000ffff00000000000000000000,0x3e0828c22050d00019a0090257369b02610c02802444404cd833c992534248030f030f030f030f030f030f030f030f030f030f030f030f),(0xfe12de11b1658035481800319804b1a08bfe740628964a19590e021ac9008305000000000000ffff000000000000000000000000ffffffff,0x202521181658024401800008804a0a08a5e500008864019400e02128900030520aa20aa20aa20aa20aa20aa20aa20aa20aa20aa20aa20aa),(0x844467a688b16203688fefc5844e0233865b6091a6212020ea59fa3b048b1400000000000000000000000000000000ffffffff00000000,0x804465a480b1620360062dc58446021386436091a62100208a09ba3b048b10b6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6ccb6cc),(0x20836914d0bb60801e7441059a10034704812891dce8150c091a4126eb49438ffff00000000000000000000ffffffff0000000000000000,0x2003691050aa20801c4041019a00024300812811d8a01108000800268a4942004f004f004f004f004f004f004f004f004f004f004f004f0),(0x1678b49240653e88604734111a1204d0d0184d0d050355e31080984158fe810000000000000ffffffffffff000000000000000000000000,0x1448948240011488200734111a1004c01010490d050204031000980048ee010c700c700c700c700c700c700c700c700c700c700c700c700),(0x2c0e10c9851092174201266e6da408ec114c2518af9228986014c31a44820d2ffffffffffff000000000000000000000000000000000000,0xc0c1041851092164201266c40040004114c0500051228902014c3004082092f800f800f800f800f800f800f800f800f800f800f800f800)]
def g511C : List ColumnInfo := [(1,0,510,0,13),(2,0,509,0,13),(4,0,507,0,13),(8,0,503,0,13),(32,0,479,0,13),(16,0,495,0,12),(64,0,447,0,12),(128,0,383,0,12),(256,0,255,0,12),(0,2,365,144,11),(0,32,474,5,11),(0,16,364,131,10),(0,64,182,265,10),(0,128,361,22,10),(0,256,179,76,10),(16,128,361,6,9),(64,256,179,12,9),(128,16,364,3,9),(144,2,365,0,9),(256,64,182,9,9),(320,0,183,0,9)]
def g511A : List (List Nat) := [[],[49,100,135],[32,116,134],[32,49,132,118]]
def g511D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x393c7e2f0f82210f1dc789e3f93c5e0b371489c033beda952c3ac95f5ecd86e4574
def g511D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x11e4e3e2e1e0a60f21a19a271f93178b838dd0a0ae3e2e1e0e4100f227118027fca95d984dfd61b915d27fca961d64
def g511H11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c0a
def g511D12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23931e2c38080f2064582d05a84d93160c748cc98f160c24480f2068791931618b8f00c287088d931e2c11708d28709109e364c78b061165880d8b1e1c044811a33098f931e2c1149819ac5b9223588311400ffebb309ffd865d3ffb0eb25ffe5984bffcbac97fd97593f7b08b25fde4574
def g511H12 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1740090101100
def g511D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4462279238a180540b141a269238a04894c7a0592286380644b844800ffd84ffd74ffd64
def g511H13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3051c8a003cef00149003880000b2000000000000460000000003245718000000000000090aac0022
def g511D14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x41cc520c41013ff
def g511H14 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8268000000000000000071400600e500
def g511L : Nat → Packing
  | 10 => (2,4,5,0,0,7,0,g511D10)
  | 11 => (3,3,5,0,0,8,0,g511D11)
  | 12 => (8,2,5,0,0,10,0,g511D12)
  | 13 => (3,1,5,0,0,8,0,g511D13)
  | 14 => (1,0,5,0,0,0,0,g511D14)
  | _ => emptyPacking
def g511I : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 1 3 0 5 1 0 g511H11
  | 12 => lookupWord 1 7 0 7 2 1 g511H12
  | 13 => lookupWord 3 37 3 9 3 2 g511H13
  | 14 => lookupWord 1 17 0 8 2 2 g511H14
  | _ => fun _ => none
def g511 : Forest := ⟨511,14,fun i => g511Y[i]?.getD (0,0),g511C,g511A,g511L,g511I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_0 : block g511 10 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P10_1 : block g511 10 1 1=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B10 : block g511 10 0 2=true := (@block_merge g511 10 0 1 1 g511P10_0 g511P10_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P11_0 : block g511 11 0 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B11 : block g511 11 0 3=true := g511P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_0 : block g511 12 0 1=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_1 : block g511 12 1 4=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P12_5 : block g511 12 5 3=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B12 : block g511 12 0 8=true := (@block_merge g511 12 0 1 7 g511P12_0 (@block_merge g511 12 1 4 3 g511P12_1 g511P12_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g511P13_0 : block g511 13 0 3=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g511B13 : block g511 13 0 3=true := g511P13_0
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
  · exact (rfl : block g511 8 0 0 = true)
  · exact (rfl : block g511 9 0 0 = true)
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
theorem binaryLower (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
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
