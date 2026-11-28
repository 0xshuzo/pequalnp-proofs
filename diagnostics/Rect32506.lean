import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_32506.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_32506
open PEqualNP.CircuitLowerBounds
private def word80 (xs : List Nat) : Nat :=
  xs.foldl (fun a b => (a <<< 80) ||| b) 0

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

def inputs : List Sig := [(BitVec.ofNat 512 (word80 [0xaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa,0xaaaaaaaaaaaaaaaaaaaa])),(BitVec.ofNat 512 (word80 [0xcccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc,0xcccccccccccccccccccc])),(BitVec.ofNat 512 (word80 [0xf0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0,0xf0f0f0f0f0f0f0f0f0f0])),(BitVec.ofNat 512 (word80 [0xff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00,0xff00ff00ff00ff00ff00])),(BitVec.ofNat 512 (word80 [0xffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000,0xffff0000ffff0000ffff,0xffff0000ffff0000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff0000,0xffffffff00000000,0xffffffff00000000ffff,0xffff00000000ffffffff,0xffffffff0000,0xffffffff00000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffff000000000000,0xffffffffffffffff,0xffff,0xffffffffffff00000000,0xffffffffffff,0xffff0000000000000000])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffff0000000000000000,0xffff,0xffffffffffffffffffff,0xffffffff000000000000,0])),(BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffffffffffffffffffff,0xffffffffffffffff0000,0,0,0]))]
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffeffff,0xfffefffffffffffefffc,0xfffefffaeeeeaa00ffff,0xfffffffffffffffffffe,0xfffffffefffffffffffe,0xfffcfffefffaeeeeaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  | 0 => (word80 [0x1000000000000,0x10000000000000001,0x10000,0x100000000,0x1000000000000,0x10000000000000001])
  | 1 => (word80 [0x10000000000000000,0x10000,0,0x1000000000000,1])
  | 2 => (word80 [1,0x10000,0,0,0x10000000000000001])
  | 3 => (word80 [0x10000,0,0,1])
  | 4 => (word80 [0x100000000,0x1000000000000,0x10000000000000001])
  | 5 => (word80 [0x1000000000000,1])
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
def kwProbe (xs q : Nat) : Row := Fin.ofNat 512 ((xs >>> (9*q)) &&& 511)
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
def polarCell (ws : List Sig) (T v : Sig) (p n : Row) :=
  bit p T && !bit n T && ws.all (fun w => (bit p w==bit n w) || w==v)
theorem polarCell_sound {ws T v p n} (h : polarCell ws T v p n=true) :
    polarOnly true ws.toFinset T v p n := by
  simp only [polarCell,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  refine ⟨h.1.1,h.1.2,?_⟩
  intro w hw sep
  have e : (bit p w==bit n w)=false := beq_eq_false_iff_ne.mpr sep.1
  simpa only [e,Bool.false_or,beq_iff_eq] using h.2 w (List.mem_toFinset.mp hw)
def polarWord (T : Sig) (ws : List Sig) (k v : Nat) :=
  let a := ws.getD (v &&& 15) zero
  let b := ws.getD ((v >>> 4) &&& 15) zero
  let pos := kwProbe (v >>> 8)
  let negs := kwProbe (v >>> 35)
  decide (k+1=ws.toFinset.card) && decide (a≠b) &&
    polarCell ws T a (pos 0) (negs 1) && polarCell ws T b (pos 0) (negs 2) &&
    polarCell ws T a (pos 1) (negs 0) && polarCell ws T b (pos 2) (negs 0)
theorem polarWord_sound {T ws k v} (h : polarWord T ws k v=true) : Impossible true T k ws.toFinset := by
  simp only [polarWord,Bool.and_eq_true,decide_eq_true_eq] at h
  exact polarCross h.1.1.1.1.1 h.1.1.1.1.2 (polarCell_sound h.1.1.1.2)
    (polarCell_sound h.1.1.2) (polarCell_sound h.1.2) (polarCell_sound h.2)
def polarSeries (g : Forest) (k start n : Nat) (data : Nat→Nat) :=
  (List.range n).all (fun j =>
    let r := (data 0 >>> (64*j)) &&& ((1 <<< 64)-1)
    if r=0 then nodeVerified g k (start+j) else polarWord (targetOf g) (stateSet g k (start+j)) k r)
theorem polarBlock {g k start n data} (mode : g.mode=true)
    (ok : polarSeries g k start n data=true) : CutRow g k start n := by
  intro j lo hi
  have h := List.all_eq_true.mp ok (j-start) (List.mem_range.mpr (by omega))
  have e : start+(j-start)=j := by omega
  dsimp only at h
  split at h
  · left; simpa only [e] using h
  · right; rw [mode]
    apply polarWord_sound
    simpa only [e] using h
theorem mixedLower {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[5,7]⟩,⟨.or,[2,3]⟩,⟨.or,[0,6]⟩,⟨.or,[0,1]⟩,⟨.or,[7,11]⟩,⟨.or,[3,8]⟩,⟨.or,[6,7]⟩,⟨.or,[6,8]⟩,⟨.and,[12,4]⟩,⟨.and,[13,10]⟩,⟨.and,[15,9]⟩,⟨.and,[14,1]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 15 := rfl

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


def sevenInputs : List Sig := vars 255
def sampleSeven (r : Row) (i : Fin 8) : Bool := bit r (sevenInputs.getD i.val zero)
theorem sevenList : List.ofFn (fun i : Fin 8 => sevenInputs.getD i.val zero) = sevenInputs := rfl
theorem sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

theorem sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
theorem allSevenRequired :
    (∀ i : Fin 8, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 8, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

theorem physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 8 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 8, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

theorem replaceShort 
    (lower : Impossible true graph 13 sevenInputs.toFinset) (gates : List Gate) (o : Nat)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 15 ≤ gates.length
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
def g41Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g41C : List ColumnInfo := []
def g41A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g41D3 (j : Nat) := if j=0 then 0x7 else 0
def g41L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g41D3)
  | _ => emptyPacking
def g41I (_ _ : Nat) : Option (Nat × Nat) := none
def g41 : Forest := ⟨41,3,fun i => g41Y[i]?.getD (0,0),g41C,g41A,g41L,g41I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41P3_0 : CutRow g41 3 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g41B3 : CutRow g41 3 0 1 := g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : mixedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g41 0 0
  · exact mixedEmpty g41 1 0
  · exact mixedEmpty g41 2 0
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := mixedLower (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(100,[32,16,83,67,100]),(104,[48,16,33,82,66,100]),(137,[117,101]),(145,[67,117,101]),(146,[16,67,117,101]),(194,[16,99,67,117]),(196,[32,16,99,67,117]),(200,[48,16,33,98,66,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g27Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g27C : List ColumnInfo := []
def g27A : List (List Nat) := [[],[64,49]]
def g27D3 (j : Nat) := if j=0 then 0xf else 0
def g27L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g27D3)
  | _ => emptyPacking
def g27I (_ _ : Nat) : Option (Nat × Nat) := none
def g27 : Forest := ⟨27,3,fun i => g27Y[i]?.getD (0,0),g27C,g27A,g27L,g27I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27P3_0 : CutRow g27 3 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g27B3 : CutRow g27 3 0 1 := g27P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27T : mixedTables g27 3 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g27 0 0
  · exact mixedEmpty g27 1 0
  · exact mixedEmpty g27 2 0
  · exact g27B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g27G : graphValid g27 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low27 : Lower true (varsX 27) (graphGoal 27) 4 := mixedLower (g:=g27) (i:=0) (hints:=67) (before_sound K41 V41) g27G g27T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K27 := extendKnown K41 4 [(27,[]),(51,[83]),(53,[33,67,83]),(75,[96,16,49,67,84]),(77,[96,16,33,50,67,84]),(83,[16,99,83]),(86,[16,32,67,99,83]),(89,[48,65,33,96,32,82]),(90,[16,48,32,66,98,82]),(99,[96,16,49,84,67]),(113,[80,65,33,99,32]),(114,[96,65,32,83,50]),(163,[83,116,100]),(166,[32,83,116,100]),(170,[48,32,82,116,100]),(240,[96,65,32,83,113,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V27 : Known true K27 := extend_ok (m:=27) V41 low27 (by decide +kernel)
def g45Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g45C : List ColumnInfo := [(4,0,41,0,4)]
def g45A : List (List Nat) := [[],[48]]
def g45D4 (j : Nat) := if j=0 then 0x1f else 0
def g45L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g45D4)
  | _ => emptyPacking
def g45I (_ _ : Nat) : Option (Nat × Nat) := none
def g45 : Forest := ⟨45,4,fun i => g45Y[i]?.getD (0,0),g45C,g45A,g45L,g45I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45P4_0 : CutRow g45 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B4 : CutRow g45 4 0 1 := g45P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : mixedTables g45 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g45 0 0
  · exact mixedEmpty g45 1 0
  · exact mixedEmpty g45 2 0
  · exact mixedEmpty g45 3 0
  · exact g45B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K27) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 5 := mixedLower (g:=g45) (i:=0) (hints:=1283) (before_sound K27 V27) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K27 5 [(45,[]),(57,[48,66,80]),(101,[32,99,67]),(102,[32,16,83,67,100]),(106,[48,16,33,82,66,100]),(139,[33,117,101]),(141,[117,101]),(149,[67,117,101]),(150,[16,67,117,101]),(154,[16,50,66,117,101]),(177,[64,82,115,32,99]),(195,[16,32,99,67,117]),(197,[32,99,67,117]),(209,[98,67,50,117]),(212,[32,16,65,99,117]),(216,[48,16,66,97,33,117]),(226,[16,82,115,66,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V27 low45 (by decide +kernel)
def g105Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf1fe003ffc0f9f3f1f,0xe003ffc0f9f3f1fe003f])),(BitVec.ofNat 152 (word80 [0x241e49248a2142a241,0xe49248a2142a241e4924]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe750fc7fff01fffe7,0x50fc7fff01fffe750fc7])),(BitVec.ofNat 152 (word80 [0x400012491042040400,0x1249104204040001249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff8af1f8ffffe03ff8,0xaf1f8ffffe03ff8af1f8])),(BitVec.ofNat 152 (word80 [0x800024922084080800,0x2492208408080002492]))),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0x959c924c308103095,0x9c924c3081030959c924]))),(0x0,0x0),(0x0,0x0)]
def g105C : List ColumnInfo := [(1,0,104,0,4)]
def g105A : List (List Nat) := [[],[83],[96],[96,83]]
def g105D4 (j : Nat) := if j=0 then 0x1f else 0
def g105L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g105D4)
  | _ => emptyPacking
def g105I (_ _ : Nat) : Option (Nat × Nat) := none
def g105 : Forest := ⟨105,4,fun i => g105Y[i]?.getD (0,0),g105C,g105A,g105L,g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4_0 : CutRow g105 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B4 : CutRow g105 4 0 1 := g105P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : mixedTables g105 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g105 0 0
  · exact mixedEmpty g105 1 0
  · exact mixedEmpty g105 2 0
  · exact mixedEmpty g105 3 0
  · exact g105B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 5 := mixedLower (g:=g105) (i:=0) (hints:=50331651) (before_sound K45 V45) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K45 5 [(105,[]),(108,[32,16,83,99]),(147,[33,49,65,81,113,97]),(153,[48,84,116,100]),(169,[80,48,118]),(198,[16,50,98,117]),(201,[117]),(202,[16,99,117]),(204,[32,16,99,117]),(210,[64,16,49,117]),(232,[80,16,33,66,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V45 low105 (by decide +kernel)
def g55Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffc07ffffffe00,0x3fffff80ffd386b20f0f])),(BitVec.ofNat 152 (word80 [0x41a8128d052280541a,0x82502916291304a21111]))),((BitVec.ofNat 152 (word80 [0xfffc00007ff01fffff,0xc007ffff01a37d4800f0])),(BitVec.ofNat 152 (word80 [0x81311b160644c89893,0x136232244d835c485555]))),((BitVec.ofNat 152 (word80 [0xffffffff80001fffff,0xfff80000003f407df000])),(BitVec.ofNat 152 (word80 [0x5c05c18178702e01c,0x380bc38703340753333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffff,0xfffffffffe663f7600ff])),(BitVec.ofNat 152 (word80 [0x160260205808130120,0x2404c00000642314aaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0x19dd38dff00])),(BitVec.ofNat 152 (word80 [0x1803800060001c01c0,0x38070040808c9308cccc]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g55C : List ColumnInfo := []
def g55A : List (List Nat) := [[],[33,84]]
def g55D4 (j : Nat) := if j=0 then 0x1f else 0
def g55L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g55D4)
  | _ => emptyPacking
def g55I (_ _ : Nat) : Option (Nat × Nat) := none
def g55 : Forest := ⟨55,4,fun i => g55Y[i]?.getD (0,0),g55C,g55A,g55L,g55I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55P4_0 : CutRow g55 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g55B4 : CutRow g55 4 0 1 := g55P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55T : mixedTables g55 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g55 0 0
  · exact mixedEmpty g55 1 0
  · exact mixedEmpty g55 2 0
  · exact mixedEmpty g55 3 0
  · exact g55B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g55G : graphValid g55 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low55 : Lower true (varsX 55) (graphGoal 55) 5 := mixedLower (g:=g55) (i:=0) (hints:=1348) (before_sound K105 V105) g55G g55T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K55 := extendKnown K105 5 [(55,[]),(87,[16,101]),(93,[48,33,65,16,96,80])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V55 : Known true K55 := extend_ok (m:=55) V105 low55 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf007ff0ffffff007ff,0xff87ffffd45c460f83ff])),(BitVec.ofNat 152 (word80 [0xa0500a201000a05014,0x1100082401806108421]))),((BitVec.ofNat 152 (word80 [0xfff8000ff87ffff801,0xfff87fc05373b2007c00])),(BitVec.ofNat 152 (word80 [0xc0622c40a122c46258,0x8a012108527132b5ad6b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x280b002c20b008060,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb04c08b044c090481,0x30004c100d06c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc07000c00700e0701,0xc04470211aa6018c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,2,41,16,5),(2,0,57,0,5),(8,0,51,0,4),(16,2,41,0,4),(32,0,27,0,4)]
def g59A : List (List Nat) := [[],[83]]
def g59D4 (j : Nat) := if j=0 then 0x4fd5120 else 0
def g59D5 := limbs80 #[#[0x480e140fd42fe20fd20,0x4088]]
def g59H5 (j : Nat) := if j=0 then 0x20 else 0
def g59D6 (j : Nat) := if j=0 then 0x18989f else 0
def g59H6 := limbs80 #[#[0x6e900000000000000,0x0,0x600200000000,0xc80000000000000]]
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 1 43 0 7 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : CutRow g59 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : CutRow g59 4 0 1 := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : CutRow g59 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : CutRow g59 5 0 3 := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : CutRow g59 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : CutRow g59 6 0 1 := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : mixedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g59 0 0
  · exact mixedEmpty g59 1 0
  · exact mixedEmpty g59 2 0
  · exact mixedEmpty g59 3 0
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K55) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := mixedLower (g:=g59) (i:=0) (hints:=67) (before_sound K55 V55) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K55 7 [(59,[]),(117,[80,65,33,50,48,99]),(118,[96,65,32,50]),(122,[96,65,32]),(182,[112,81,32,49,66,67,99]),(186,[112,81,32,49,67,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V55 low59 (by decide +kernel)
def g61Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ff80ffe03fffff,0xffffffffff98eb9d81ff])),(BitVec.ofNat 152 (word80 [0x8050050200408000a0,0x14010000800003899249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff80000ffffc07ff0,0x1ff80ffc0619e0e8e00])),(BitVec.ofNat 152 (word80 [0xa61562c2a8a150ac3,0x584a1a290b419a0eb6db]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xfe0000ffff9f8a637007])),(BitVec.ofNat 152 (word80 [0xc8198483313261302,0x606c2c32121b88422492]))),((BitVec.ofNat 152 (word80 [0x7fff,0xffffff000009f56c0038])),(BitVec.ofNat 152 (word80 [0x2f05e070bc1c385c0b,0x817030bc1c09f4646db6]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x30060000c00000600c,0x18040c0202444304924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g61C : List ColumnInfo := [(4,0,57,0,5)]
def g61A : List (List Nat) := [[],[80,66]]
def g61D5 (j : Nat) := if j=0 then 0x3f else 0
def g61L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g61D5)
  | _ => emptyPacking
def g61I (_ _ : Nat) : Option (Nat × Nat) := none
def g61 : Forest := ⟨61,5,fun i => g61Y[i]?.getD (0,0),g61C,g61A,g61L,g61I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61P5_0 : CutRow g61 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g61B5 : CutRow g61 5 0 1 := g61P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61T : mixedTables g61 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g61 0 0
  · exact mixedEmpty g61 1 0
  · exact mixedEmpty g61 2 0
  · exact mixedEmpty g61 3 0
  · exact mixedEmpty g61 4 0
  · exact g61B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g61G : graphValid g61 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low61 : Lower true (varsX 61) (graphGoal 61) 6 := mixedLower (g:=g61) (i:=0) (hints:=1283) (before_sound K59 V59) g61G g61T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K61 := extendKnown K59 6 [(61,[]),(103,[96,49,32,33,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V61 : Known true K61 := extend_ok (m:=61) V59 low61 (by decide +kernel)
def g79Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fff0007ff803ffc01,0xfffffffffff245f3f007])),(BitVec.ofNat 152 (word80 [0x502a8350250681482d,0x550950a414040f37b6d]))),((BitVec.ofNat 152 (word80 [0x1ffffff800003fffff,0xffe001ffe001b15bc038])),(BitVec.ofNat 152 (word80 [0x854c2a62b62b159148,0x2986d84c8661a159c6db]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffc00001,0xfffffe00000ce425d1c0])),(BitVec.ofNat 152 (word80 [0x6703383384c19e270,0x4e04e06f0b88a425d6db]))),((BitVec.ofNat 152 (word80 [0xe00000000000000001,0xfffffffffff22fedae07])),(BitVec.ofNat 152 (word80 [0x7803c03c0701e0380,0x700700700c022d0c8492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x1800c0040000200001,0x80180180100452820924]))),(0x0,0x0),(0x0,0x0)]
def g79C : List ColumnInfo := [(2,0,77,0,4)]
def g79A : List (List Nat) := [[],[33]]
def g79D4 (j : Nat) := if j=0 then 0x3f else 0
def g79L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g79D4)
  | _ => emptyPacking
def g79I (_ _ : Nat) : Option (Nat × Nat) := none
def g79 : Forest := ⟨79,4,fun i => g79Y[i]?.getD (0,0),g79C,g79A,g79L,g79I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79P4_0 : CutRow g79 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g79B4 : CutRow g79 4 0 1 := g79P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79T : mixedTables g79 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g79 0 0
  · exact mixedEmpty g79 1 0
  · exact mixedEmpty g79 2 0
  · exact mixedEmpty g79 3 0
  · exact g79B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g79G : graphValid g79 (boundsBefore K61) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low79 : Lower true (varsX 79) (graphGoal 79) 5 := mixedLower (g:=g79) (i:=0) (hints:=16778851) (before_sound K61 V61) g79G g79T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K79 := extendKnown K61 5 [(79,[]),(94,[64,33,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V79 : Known true K79 := extend_ok (m:=79) V61 low79 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(1,0,90,0,4),(2,0,89,0,4),(8,0,83,0,4),(16,0,75,0,4),(64,0,27,0,4)]
def g91A : List (List Nat) := [[],[97,67],[16,99],[16,48,64,96],[48,100],[48,65,96,16],[64,49],[64,97,48,49],[96,16,49,67],[96,65]]
def g91D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g91D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g91H5 (j : Nat) := if j=0 then 0x20 else 0
def g91D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g91H6 := limbs80 #[#[0x65aa00510000000000b6,0x63000000e29e0000,0xc00037000000008b]]
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (2,1,3,0,0,4,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 2 29 0 8 1 3 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : CutRow g91 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : CutRow g91 4 0 1 := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : CutRow g91 5 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : CutRow g91 5 0 2 := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : CutRow g91 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : CutRow g91 6 0 1 := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : mixedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g91 0 0
  · exact mixedEmpty g91 1 0
  · exact mixedEmpty g91 2 0
  · exact mixedEmpty g91 3 0
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K79) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := mixedLower (g:=g91) (i:=0) (hints:=16777283) (before_sound K79 V79) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K79 7 [(91,[]),(115,[97,67,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V79 low91 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff0ff0ffc03f,0xf0ffffff24d65b0000ff])),(BitVec.ofNat 152 (word80 [0x282a140a202282a2a0,0xa2820820048653999999]))),((BitVec.ofNat 152 (word80 [0xffffe000fffffffc0,0xff0ff0c6353900f000])),(BitVec.ofNat 152 (word80 [0x42b098ac45402b030a,0xc4142242823539777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xff000fff39b5260f0f0f])),(BitVec.ofNat 152 (word80 [0x80c0203001840c0403,0x184080383100222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x300c0c0860830080c,0x200304034828444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0301000800c03030,0x8c08c084480c4888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(0,2,41,64,5),(1,0,106,0,5),(2,0,105,0,5),(8,0,99,0,4),(32,0,75,0,4),(64,2,41,0,4)]
def g107A : List (List Nat) := [[],[83]]
def g107D4 (j : Nat) := if j=0 then 0x5ed4132 else 0
def g107D5 (j : Nat) := if j=0 then 0xc8404fd32 else 0
def g107H5 (j : Nat) := if j=0 then 0x90 else 0
def g107D6 (j : Nat) := if j=0 then 0x23468bf else 0
def g107H6 (j : Nat) := if j=0 then 0xc else 0
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g107D4)
  | 5 => (1,1,3,0,0,0,0,g107D5)
  | 6 => (1,0,3,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g107H5
  | 6 => lookupWord 1 2 0 4 0 0 g107H6
  | _ => fun _ => none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : CutRow g107 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B4 : CutRow g107 4 0 1 := g107P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : CutRow g107 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : CutRow g107 5 0 1 := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P6_0 : CutRow g107 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B6 : CutRow g107 6 0 1 := g107P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : mixedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g107 0 0
  · exact mixedEmpty g107 1 0
  · exact mixedEmpty g107 2 0
  · exact mixedEmpty g107 3 0
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := mixedLower (g:=g107) (i:=0) (hints:=16777315) (before_sound K91 V91) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K91 7 [(107,[]),(121,[96,65,33]),(171,[80,48,118]),(179,[16,80,67,112,96]),(242,[64,81,32,49,115]),(248,[80,65,32,98,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V91 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff1fc7fc03f,0xe1fe1fffd599a00000ff])),(BitVec.ofNat 152 (word80 [0x1450a8a0a40942a2a1,0x450441084589a9999999]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff001ffffffc0,0x1ffe1fc493e300f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c2c8500b0305,0x88280411093a33333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffe007fffff,0xfe0001ffbe1b40f0f00f])),(BitVec.ofNat 152 (word80 [0x6103010300620c0406,0x3088203a1202222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800402040080100808,0x400040000004444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x180c080100603030,0x118111824444c8888888]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,5),(4,0,105,0,5),(8,0,101,0,5),(64,0,45,0,5)]
def g109A : List (List Nat) := [[],[32,99]]
def g109D6 (j : Nat) := if j=0 then 0x2709f else 0
def g109L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I (_ _ : Nat) : Option (Nat × Nat) := none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : CutRow g109 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : CutRow g109 6 0 1 := g109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : mixedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g109 0 0
  · exact mixedEmpty g109 1 0
  · exact mixedEmpty g109 2 0
  · exact mixedEmpty g109 3 0
  · exact mixedEmpty g109 4 0
  · exact mixedEmpty g109 5 0
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := mixedLower (g:=g109) (i:=0) (hints:=33555715) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 7 [(109,[]),(155,[16,32,48,64,80,112,96]),(185,[64,82,115,32,99]),(203,[33,117]),(205,[117]),(211,[33,97,67,117]),(214,[32,16,65,99,49,117]),(217,[64,98,48,50,117]),(218,[48,16,66,97,117]),(230,[16,82,115,67,98]),(234,[16,82,115,66,100,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g110Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc00ffc07fe03fff,0xe007fc0ff810c7b401c0])),(BitVec.ofNat 152 (word80 [0xa4a96a528d2a458a25,0x4b5129a292d0c7b5b6db]))),((BitVec.ofNat 152 (word80 [0xfffff00007fffc07f,0xfff8000ffff706cc0e07])),(BitVec.ofNat 152 (word80 [0xc1304c1b160c891309,0x8261b2c3249302cc9249]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000007f,0xfffffff0000be8947038])),(BitVec.ofNat 152 (word80 [0x1c0701c180f0e1c0e,0x381c303c70b60949249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000000007f,0xffffffffffe6fe67803f])),(BitVec.ofNat 152 (word80 [0x60180602030102030,0xc02000400049c212492]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffff80,0x1911bbffc0])),(BitVec.ofNat 152 (word80 [0x80200800040000040,0x10040008000000024924]))),(0x0,0x0),(0x0,0x0)]
def g110C : List ColumnInfo := [(2,0,108,0,5)]
def g110A : List (List Nat) := [[],[50]]
def g110D5 (j : Nat) := if j=0 then 0x3f else 0
def g110L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g110D5)
  | _ => emptyPacking
def g110I (_ _ : Nat) : Option (Nat × Nat) := none
def g110 : Forest := ⟨110,5,fun i => g110Y[i]?.getD (0,0),g110C,g110A,g110L,g110I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110P5_0 : CutRow g110 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g110B5 : CutRow g110 5 0 1 := g110P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110T : mixedTables g110 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g110 0 0
  · exact mixedEmpty g110 1 0
  · exact mixedEmpty g110 2 0
  · exact mixedEmpty g110 3 0
  · exact mixedEmpty g110 4 0
  · exact g110B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g110G : graphValid g110 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low110 : Lower true (varsX 110) (graphGoal 110) 6 := mixedLower (g:=g110) (i:=0) (hints:=18896224) (before_sound K109 V109) g110G g110T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K110 := extendKnown K109 6 [(110,[]),(151,[48,33,16,84,118]),(157,[16,32,48,64,80,118]),(199,[48,16,33,101,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V110 : Known true K110 := extend_ok (m:=110) V109 low110 (by decide +kernel)
def g143Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffc003ffc01ffe00f,0xfffffffffffeddea003f])),(BitVec.ofNat 152 (word80 [0x80a81a8128340a4160,0xa02a094148524c6a1249]))),((BitVec.ofNat 152 (word80 [0x3fffffc00001fffff0,0x7ff001ffc0118f681c0])),(BitVec.ofNat 152 (word80 [0x15315315b158ac8a45,0x314c6d89919918f6b6db]))),((BitVec.ofNat 152 (word80 [0x3ffffffffffe000000,0x7ffffe000031f070e00])),(BitVec.ofNat 152 (word80 [0x19c19c19c260cf1389,0xc2704e0de2e31f0736db]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x7fffffffffcbfdc7007])),(BitVec.ofNat 152 (word80 [0x1e01e01e0380f01c0e,0x380700e0300b3942492]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf800000000036237fff8])),(BitVec.ofNat 152 (word80 [0x200200200001000000,0x4008010000000004924]))),(0x0,0x0)]
def g143C : List ColumnInfo := [(2,0,141,0,5)]
def g143A : List (List Nat) := [[],[33],[48],[48,33]]
def g143D5 (j : Nat) := if j=0 then 0x3f else 0
def g143L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g143D5)
  | _ => emptyPacking
def g143I (_ _ : Nat) : Option (Nat × Nat) := none
def g143 : Forest := ⟨143,5,fun i => g143Y[i]?.getD (0,0),g143C,g143A,g143L,g143I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143P5_0 : CutRow g143 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g143B5 : CutRow g143 5 0 1 := g143P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143T : mixedTables g143 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g143 0 0
  · exact mixedEmpty g143 1 0
  · exact mixedEmpty g143 2 0
  · exact mixedEmpty g143 3 0
  · exact mixedEmpty g143 4 0
  · exact g143B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g143G : graphValid g143 (boundsBefore K110) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low143 : Lower true (varsX 143) (graphGoal 143) 6 := mixedLower (g:=g143) (i:=0) (hints:=1907) (before_sound K110 V110) g143G g143T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K143 := extendKnown K110 6 [(143,[]),(158,[16,32,48,64])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V143 : Known true K143 := extend_ok (m:=143) V110 low143 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ff80ffe03ffff0,0x3ff80ffff909e9b81c7])),(BitVec.ofNat 152 (word80 [0x41a8251a0a458a02a1,0xa8251a148a00928b9249]))),((BitVec.ofNat 152 (word80 [0xfffc0000ffffc07fff,0xfc0000ffc068da648e00])),(BitVec.ofNat 152 (word80 [0x8530b62c2c891314c1,0x30b62c191348da44b6db]))),((BitVec.ofNat 152 (word80 [0xffffffff0000007fff,0xffffff00000ff10e7038])),(BitVec.ofNat 152 (word80 [0x1c038300f0e1c0701,0xc038301e1c02d10e1249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fff,0xffffffffff99af6d003f])),(BitVec.ofNat 152 (word80 [0x1602c040b01020580a,0x2c000a000192c606db6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x18030000c00000600c,0x30040c0202504304924]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,4)]
def g167A : List (List Nat) := [[],[32]]
def g167D4 (j : Nat) := if j=0 then 0x3f else 0
def g167L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g167D4)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,4,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P4_0 : CutRow g167 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B4 : CutRow g167 4 0 1 := g167P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : mixedTables g167 4 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g167 0 0
  · exact mixedEmpty g167 1 0
  · exact mixedEmpty g167 2 0
  · exact mixedEmpty g167 3 0
  · exact g167B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K143) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 5 := mixedLower (g:=g167) (i:=0) (hints:=1397) (before_sound K143 V143) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K143 5 [(167,[]),(174,[32,48])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V143 low167 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc03fe1fe1fff00f,0xf87f87ffff856420703f])),(BitVec.ofNat 152 (word80 [0x50282814404400a0a0,0x51011002098064049249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffc001ffe1ffff0,0x7ff87f01c9c9c381c0])),(BitVec.ofNat 152 (word80 [0x60b03058828042c0c1,0x620a01042181c98db6db]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0001fffff,0xff80007ff233d69c0e07])),(BitVec.ofNat 152 (word80 [0x80c040600308830101,0x800c2208021380892492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf800000000001fffff,0xffffff80013c2ae00ff8])),(BitVec.ofNat 152 (word80 [0x50282811411140a0a,0x500050402c02724924]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffe00000,0xce2917ff000])),(BitVec.ofNat 152 (word80 [0x60303001800180c0c,0x4604460846010724924]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(4,0,169,0,5)]
def g173A : List (List Nat) := [[],[117],[48],[48,117]]
def g173D5 (j : Nat) := if j=0 then 0x3f else 0
def g173L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g173D5)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,5,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P5_0 : CutRow g173 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B5 : CutRow g173 5 0 1 := g173P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : mixedTables g173 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g173 0 0
  · exact mixedEmpty g173 1 0
  · exact mixedEmpty g173 2 0
  · exact mixedEmpty g173 3 0
  · exact mixedEmpty g173 4 0
  · exact g173B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 6 := mixedLower (g:=g173) (i:=0) (hints:=1283) (before_sound K167 V167) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K167 6 [(173,[]),(229,[32,99,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V167 low173 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff007fe1ff0fffc03f,0xfff0fffff95e0200f0ff])),(BitVec.ofNat 152 (word80 [0xa0501440220028281,0x40220020980602111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff8001fff0ffffc0,0x1fff0ff01c35b90f0f00])),(BitVec.ofNat 152 (word80 [0x2c06058814020b0305,0x81402042183511333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000ffffff,0xe0000fff23b566f0000f])),(BitVec.ofNat 152 (word80 [0xb028160058442c0406,0x5844280213164666666]))),((BitVec.ofNat 152 (word80 [0xffffff,0xfffff000134bf8000ff0])),(BitVec.ofNat 152 (word80 [0xc0b058116088b02828,0x16000b040348e8cccccc]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc060018000c03030,0x18088c08468880888888]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(4,0,177,0,5)]
def g181A : List (List Nat) := [[],[112,82]]
def g181D5 (j : Nat) := if j=0 then 0x3f else 0
def g181L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g181D5)
  | _ => emptyPacking
def g181I (_ _ : Nat) : Option (Nat × Nat) := none
def g181 : Forest := ⟨181,5,fun i => g181Y[i]?.getD (0,0),g181C,g181A,g181L,g181I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181P5_0 : CutRow g181 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g181B5 : CutRow g181 5 0 1 := g181P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181T : mixedTables g181 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g181 0 0
  · exact mixedEmpty g181 1 0
  · exact mixedEmpty g181 2 0
  · exact mixedEmpty g181 3 0
  · exact mixedEmpty g181 4 0
  · exact g181B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g181G : graphValid g181 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 6 := mixedLower (g:=g181) (i:=0) (hints:=1284) (before_sound K173 V173) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K173 6 [(181,[]),(227,[96,33,16,65]),(241,[112,82,50,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V173 low181 (by decide +kernel)
def g206Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc07fc01ff03fe07fff,0x7fc0ff81fed6800e07])),(BitVec.ofNat 152 (word80 [0x950a8d44a68a4b282a,0x35129a292ca6d6849249]))),((BitVec.ofNat 152 (word80 [0x7fffe0003fff81ff,0xff8000fffe0725a07038])),(BitVec.ofNat 152 (word80 [0x26130986cb0c924c4c,0x261b2c32493725a49249]))),((BitVec.ofNat 152 (word80 [0x7fffffffc00001ff,0xffffff0000074b4381c0])),(BitVec.ofNat 152 (word80 [0x381c0e070c0f1c7070,0x381c303c71c74b449249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80000000000001ff,0xfffffffffffacd3c01ff])),(BitVec.ofNat 152 (word80 [0x2010080010000080,0x40200040000000092492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x532dffe00])),(BitVec.ofNat 152 (word80 [0x4020100020000100,0x80400080000000124924]))),(0x0,0x0)]
def g206C : List ColumnInfo := [(2,0,204,0,5)]
def g206A : List (List Nat) := [[],[118],[50],[50,118],[33],[33,118],[33,49],[33,49,118],[49,33],[49,33,118],[49],[49,118]]
def g206D5 (j : Nat) := if j=0 then 0x3f else 0
def g206L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g206D5)
  | _ => emptyPacking
def g206I (_ _ : Nat) : Option (Nat × Nat) := none
def g206 : Forest := ⟨206,5,fun i => g206Y[i]?.getD (0,0),g206C,g206A,g206L,g206I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g206P5_0 : CutRow g206 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g206B5 : CutRow g206 5 0 1 := g206P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g206T : mixedTables g206 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g206 0 0
  · exact mixedEmpty g206 1 0
  · exact mixedEmpty g206 2 0
  · exact mixedEmpty g206 3 0
  · exact mixedEmpty g206 4 0
  · exact g206B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g206G : graphValid g206 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low206 : Lower true (varsX 206) (graphGoal 206) 6 := mixedLower (g:=g206) (i:=0) (hints:=285238880) (before_sound K181 V181) g206G g206T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K206 := extendKnown K181 6 [(206,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V206 : Known true K206 := extend_ok (m:=206) V181 low206 (by decide +kernel)
def g213Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff87fc3fff00,0xffff1ffed2e680007c1f])),(BitVec.ofNat 152 (word80 [0x222894451108808a4a,0xa02444252268a5294a5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffe0007ffc3ffff,0xffffe11773400f83e0])),(BitVec.ofNat 152 (word80 [0x40b018162050082c0c,0x2c140089146346318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c120980261113010,0x30588900a8d154a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c0e0438221c060,0x40600e104b9898c6318c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80201000400020080,0x80801000000021084210]))),(0x0,0x0)]
def g213C : List ColumnInfo := [(1,0,212,0,5),(4,0,209,0,5),(16,0,197,0,5),(64,0,149,0,5),(17,0,196,0,4),(68,0,145,0,4)]
def g213A : List (List Nat) := [[],[98],[32,100],[32,64,96],[64],[64,98],[96,32,66],[96,66]]
def g213D4 := limbs80 #[#[0x9bd89544426d6215110,0x31825f635474]]
def g213D5 := limbs80 #[#[0x7c54443f280885bd4940,0xfea8885f95110beaa221,0xbd4940bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201141080d176b,0xc110204810001]]
def g213H5 (j : Nat) := if j=0 then 0x49006820528100 else 0
def g213D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x3140cc503]]
def g213H6 := limbs80 #[#[0x100345c1e144454201a0,0xd230,0x4d5c000000031a136640,0x143a2400a0000684c]]
def g213D7 (j : Nat) := if j=0 then 0x1605f else 0
def g213H7 := limbs80 #[#[0x4000075700980000002c,0x6c87439d4c4401541228,0xe1]]
def g213L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g213D4)
  | 5 => (10,2,3,0,0,7,0,g213D5)
  | 6 => (3,1,3,0,0,6,0,g213D6)
  | 7 => (1,0,3,0,0,0,0,g213D7)
  | _ => emptyPacking
def g213I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 11 0 8 2 2 g213H5
  | 6 => lookupWord 4 29 4 10 4 2 g213H6
  | 7 => lookupWord 3 19 2 9 2 3 g213H7
  | _ => fun _ => none
def g213 : Forest := ⟨213,7,fun i => g213Y[i]?.getD (0,0),g213C,g213A,g213L,g213I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P4_0 : CutRow g213 4 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B4 : CutRow g213 4 0 3 := g213P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_0 : CutRow g213 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P5_1 : CutRow g213 5 1 9 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B5 : CutRow g213 5 0 10 := (@joinRow g213 5 0 1 9 g213P5_0 g213P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P6_0 : CutRow g213 6 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B6 : CutRow g213 6 0 3 := g213P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213P7_0 : CutRow g213 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g213B7 : CutRow g213 7 0 1 := g213P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213T : mixedTables g213 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g213 0 0
  · exact mixedEmpty g213 1 0
  · exact mixedEmpty g213 2 0
  · exact mixedEmpty g213 3 0
  · exact g213B4
  · exact g213B5
  · exact g213B6
  · exact g213B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g213G : graphValid g213 (boundsBefore K206) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low213 : Lower true (varsX 213) (graphGoal 213) 8 := mixedLower (g:=g213) (i:=0) (hints:=33555972) (before_sound K206 V206) g213G g213T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K213 := extendKnown K206 8 [(213,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V213 : Known true K213 := extend_ok (m:=213) V206 low213 (by decide +kernel)
def g233Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1fc7f80fffe1ffc03,0xf8fe1fe1fea15e03803f])),(BitVec.ofNat 152 (word80 [0x440911224444408888,0x1204444400a10e492492]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe007fff01ffe3fffc,0xfffffe3d41851c0fc7])),(BitVec.ofNat 152 (word80 [0x81002040808001010,0x20080080000000249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffffe0003ffff,0xff001fffc3ba900071f8])),(BitVec.ofNat 152 (word80 [0x1122440811108a2222,0x409091000b0a90924924]))),((BitVec.ofNat 152 (word80 [0xffff8000000003ffff,0xffffe000007f28e07e00])),(BitVec.ofNat 152 (word80 [0x60401830606110c0c0,0x80200608907508492492]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3066bff8000])),(BitVec.ofNat 152 (word80 [0x818060408180030303,0x4c11811230261924924]))),(0x0,0x0)]
def g233C : List ColumnInfo := [(1,0,232,0,5)]
def g233A : List (List Nat) := [[],[117],[80,118],[80,96,112],[96],[96,117],[112,80,101],[112,101]]
def g233D5 (j : Nat) := if j=0 then 0x3f else 0
def g233L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g233D5)
  | _ => emptyPacking
def g233I (_ _ : Nat) : Option (Nat × Nat) := none
def g233 : Forest := ⟨233,5,fun i => g233Y[i]?.getD (0,0),g233C,g233A,g233L,g233I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233P5_0 : CutRow g233 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g233B5 : CutRow g233 5 0 1 := g233P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233T : mixedTables g233 5 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g233 0 0
  · exact mixedEmpty g233 1 0
  · exact mixedEmpty g233 2 0
  · exact mixedEmpty g233 3 0
  · exact mixedEmpty g233 4 0
  · exact g233B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g233G : graphValid g233 (boundsBefore K213) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low233 : Lower true (varsX 233) (graphGoal 233) 6 := mixedLower (g:=g233) (i:=0) (hints:=50331651) (before_sound K213 V213) g233G g233T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K233 := extendKnown K213 6 [(233,[]),(236,[32,16,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V233 : Known true K233 := extend_ok (m:=233) V213 low233 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf8a5b238c872c00f83ff])),(BitVec.ofNat 152 (word80 [0x28002a00250014805,0x38252220002282108421]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x1f582a4bb06d80007c00])),(BitVec.ofNat 152 (word80 [0x14c814c41b62099019,0x9b582a4b806196b5ad6b]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73623e14bd881f00000])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,0x53623614ad88e739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858e56c4e4f7e00001f])),(BitVec.ofNat 152 (word80 [0xb80338019c00ce0130,0x50c14c4a4d4c6318c6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4579a17773c00007fe0])),(BitVec.ofNat 152 (word80 [0xc013c009e004f001c0,0x4029014771c294a5294]))),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x2881c809500318c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(4,0,59,0,7)]
def g63A : List (List Nat) := [[]]
def g63D7 (j : Nat) := if j=0 then 0x7f else 0
def g63L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g63D7)
  | _ => emptyPacking
def g63I (_ _ : Nat) : Option (Nat × Nat) := none
def g63 : Forest := ⟨63,7,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P7_0 : CutRow g63 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B7 : CutRow g63 7 0 1 := g63P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : mixedTables g63 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g63 0 0
  · exact mixedEmpty g63 1 0
  · exact mixedEmpty g63 2 0
  · exact mixedEmpty g63 3 0
  · exact mixedEmpty g63 4 0
  · exact mixedEmpty g63 5 0
  · exact mixedEmpty g63 6 0
  · exact g63B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K233) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 8 := mixedLower (g:=g63) (i:=0) (hints:=1347) (before_sound K233 V233) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K233 8 [(63,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V233 low63 (by decide +kernel)
def g95Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xd925ba38c873c00003ff])),(BitVec.ofNat 152 (word80 [0x28802a40252014805,0x1925322080239294a529]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x3ed8224bb06c800ffc00])),(BitVec.ofNat 152 (word80 [0x14c014c01b60099019,0xba58224b006086318c63]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73623e14bd881f00000])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,0x63623614ad88e739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858e56c4e4f7e00001f])),(BitVec.ofNat 152 (word80 [0xb80338019c00ce0130,0x58c14c4a4c4c6318c6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4579a17773c00007fe0])),(BitVec.ofNat 152 (word80 [0xc013c009e004f001c0,0x4028814771c294a5294]))),(0x0,0x0),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x1801c809501318c6318]))),(0x0,0x0),(0x0,0x0)]
def g95C : List ColumnInfo := [(4,0,91,0,7)]
def g95A : List (List Nat) := [[],[64,49]]
def g95D7 (j : Nat) := if j=0 then 0x7f else 0
def g95L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g95D7)
  | _ => emptyPacking
def g95I (_ _ : Nat) : Option (Nat × Nat) := none
def g95 : Forest := ⟨95,7,fun i => g95Y[i]?.getD (0,0),g95C,g95A,g95L,g95I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95P7_0 : CutRow g95 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g95B7 : CutRow g95 7 0 1 := g95P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95T : mixedTables g95 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g95 0 0
  · exact mixedEmpty g95 1 0
  · exact mixedEmpty g95 2 0
  · exact mixedEmpty g95 3 0
  · exact mixedEmpty g95 4 0
  · exact mixedEmpty g95 5 0
  · exact mixedEmpty g95 6 0
  · exact g95B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g95G : graphValid g95 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low95 : Lower true (varsX 95) (graphGoal 95) 8 := mixedLower (g:=g95) (i:=0) (hints:=16778819) (before_sound K63 V63) g95G g95T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K95 := extendKnown K63 8 [(95,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V95 : Known true K95 := extend_ok (m:=95) V63 low95 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xf648eca538cb000000ff])),(BitVec.ofNat 152 (word80 [0x81481480aa04a81481,0x4648a4a5084999999999]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0xfa11a858ab3000f0000])),(BitVec.ofNat 152 (word80 [0x1590a62530b6c29906,0x6f811a818ab377777777]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf2190dcd100f00f00])),(BitVec.ofNat 152 (word80 [0x19e13809c02700de0b,0x808d2180dcd133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2152f483bb80f00f00f])),(BitVec.ofNat 152 (word80 [0x1e01c00e003800e00c,0x50b4031b022222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x2000003000c0030010,0x1125000020644444444]))),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0xc00200c003000c0020,0x60043e000088888888]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7),(4,0,107,0,7),(0,2,45,64,6),(1,0,110,0,6),(8,0,103,0,6),(6,0,105,0,5),(9,0,102,0,5),(10,0,101,0,5),(32,0,79,0,5),(64,0,45,0,5),(64,2,45,0,5),(12,0,99,0,4),(34,0,77,0,4),(36,0,75,0,4)]
def g111A : List (List Nat) := [[]]
def g111D4 := limbs80 #[#[0x50d32543c2551434c950,0x542d2615434c950ac886,0x54c7650d50b4b8454d32,0x19150d19545cc6454316,0xe856450d32d472659173,0x58d32d46b1619434cb51,0xd4639e1d644cb51ac784,0xdd143585328e583dc964,0x50300ca774991614cb61,0x2b509511f3864b132034,0x8c10]]
def g111D5 := limbs80 #[#[0x762b1a65a8f49534c950,0xf9286992a139dc964d4,0x439caa286a8769544c95,0x50e72a9a1aa13e1d9435,0xd47e2a1a65a8dd973191,0x532f8a86b0a65b959132,0x34caf3ba2c2996e66458,0x4d43f1ca8a1a65e35514,0x50d033db2aa0a071d545,0x597409eaeda8e819e595,0xd43543e5b1a64a84ef72,0x650d50af2eaa1aa1d654,0x8d53542bcbae86a84fb7,0x7255150af6e8a9aa1d6d,0x19154542bdb9aa8a876b,0x97219150e76c8aa2a1ce,0xadc9645435cb20c8a85e,0xc5434c941bb6e6b22a17,0xb95d932d47733b264a0f,0xed56350f51be6e0a1ea3,0x33d5d943d475ab2287a8,0x8cf576d0f51d6ac9a1ea,0xa3b9dc964d467bba2c7a,0x997cb7050d329eee6b26,0xa65735d5434cbe2b8a86,0x69974d5454d32b9eeaa1,0xa2653bdd9544cae7ba2a,0xc8995eb7059132b9ae72,0xb0287bc5076050ee6b9c,0x2cba1cf975d8143de2e3,0xb1ca93b5cf6255277b9,0x154903b1a8a036009f6e],#[0x652f560a344208ea6f31,0xe84409f8f6783a9c8d0,0x893e9c4ca59269046a29,0xeae96eb458ab956a852a,0x86ab499ecc64b1986c05,0x6f076ba9cee470b79b6d,0x41520a355c03fc7cbd9e,0x98205204183481540812,0x5821412008b6614301,0x9882]]
def g111H5 := limbs80 #[#[0xcc7273a900b80c2,0xae600f400f1000027a00,0x5b35ed008]]
def g111D6 := limbs80 #[#[0xe55150de54d50fa4c950,0x4cb51bdd8d41f94c941d,0x8532bd59351bd58f51f9,0x143f354d32f350d32f95,0x40fe54140bbd8954bed8,0xfe54340bfd9540fdd45,0xdf55150bf59740fdd474,0xe19150fed0d50fe50d50,0xd9150fe99150fe59150f,0x5132fdd0f51fd50f51fe,0x132fb59132fb95132fb5,0x43ef55143f754d43fb99,0x3bf59743ef55343ef951,0xfd50540bf58e54df5515,0xe58d50bfd9150bf59540,0x59532fd50d41fed8d50f,0x9543fd58543fed8143fb,0x154bfd9153bfd9543bf5,0x54bfd8d54fbd8954bfd8,0x10840cc12012000bf582,0x50270468810e41a42e85,0x3a86d8d51922f45d0b11,0x8a693e26a498889021e6,0x219b324618bb96b2be55,0xda3ae750e41bf3666b4d,0x3de7b0f49e63c6780ee9,0x950b009fe3f67e0fa9f2,0x8e05081e3814a0b1a382,0x521a98985088c0b54207,0xb316d098921624ac1a2b,0x8c98065e033421780c18,0x12186100180490161505],#[0x2141841840802040c50,0x1a48a0312a248084a892,0xa48089201289228084a8,0x41a05b41a81049841121,0x4045a48066a692020883,0x40801c4089105108144,0x1840062141]]
def g111H6 := limbs80 #[#[0xc06481801ca2c2a81340,0xcb5fa817f211629a1080,0x60023772400ed003000f,0x6640554a08609d6e2f4,0xc8e2fe14ec9fe9000a,0x10036b003bb8955e1c71,0x65528ce8d9d1e6ef1980,0xc0039b00240000f02ba7,0x79cffd357ad691bf3d72,0xf07353aa90dbf991beb8,0xa1138]]
def g111D7 := limbs80 #[#[0x751faa0fd4c7f4a1f950,0x87fd50ffa07f503da65f,0x3fca9fd54fea9ffd0ffa,0x3a58aa6439c8a6390f80,0x20e148a85c9dbea12c84,0xc08b45429e2650908a8c,0x944606142bd40c2da290,0x1864422a30a91460830c,0x1328548a303206125118,0x708a143208384543221,0x1]]
def g111H7 := limbs80 #[#[0x57e41008042846a0107c,0x1d500000133a,0x96448f00072c96007d20,0x1843a08fc18a29aec,0xdda000d9d866aaa8000,0x75df0780000000001e7f,0xb1e28a05c00000118008,0x1001c9cc9f46e90018d7,0x33a0c188a1c4d100014,0x68000000000000208560,0xb39200034001a200000e,0x24e63cb8000b6000008]]
def g111D8 (j : Nat) := if j=0 then 0xa61013f else 0
def g111H8 := limbs80 #[#[0xf300dd00000000615a,0xd70000007600180489,0xcabb2000000a000,0xd50000]]
def g111L : Nat → Packing
  | 4 => (14,4,4,0,0,7,0,g111D4)
  | 5 => (64,3,4,0,0,9,0,g111D5)
  | 6 => (55,2,4,0,0,11,0,g111D6)
  | 7 => (14,1,4,0,0,9,0,g111D7)
  | 8 => (1,0,4,0,0,0,0,g111D8)
  | _ => emptyPacking
def g111I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 3 23 4 8 4 0 g111H5
  | 6 => lookupWord 16 73 6 10 6 0 g111H6
  | 7 => lookupWord 13 89 5 10 6 0 g111H7
  | 8 => lookupWord 3 37 0 8 4 0 g111H8
  | _ => fun _ => none
def g111 : Forest := ⟨111,8,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P4_0 : CutRow g111 4 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P4_2 : CutRow g111 4 2 12 := by
  apply polarBlock (data:=fun _ => (word80 [0x8001001904a,0x242008020028248a6031,0x400020108c024420400,0x20108c0244208000028,0x248e424208000028248e,0x42420800004090944241,0x207201108424100020,0x8110a884093200820040,0xa0882421080081009042,0x9320404004024482121])) rfl
  decide +kernel
theorem g111B4 : CutRow g111 4 0 14 := (@joinRow g111 4 0 2 12 g111P4_0 g111P4_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_0 : CutRow g111 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_3 : CutRow g111 5 3 14 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P5_17 : CutRow g111 5 17 47 := by
  apply polarBlock (data:=fun _ => (word80 [0x10001008450,0x9520400020110c02453,0x400020110c024530100,0x1008450095200840101,0x80484430010001008450,0x94108004100a0c04443,0x4000040245021520400,0x820110c0244204000201,0x10c024530800810090c0,0x444300a0810180420940,0x400820110c024420404,0x411048603208004100,0x90c044320800410090c0,0x44320404004120506043,0x208100a04209100104,0x1018050484204040041,0x2850604308000040a094,0x42530102020180902832,0x8000040a09442530800,0x100a0c4425301000100,0x8450095100220040a012,0x212000620040a0122120,0x800410090c044420400,0x82442285204000201,0x10c02452002072011084,0x241001020028841a2821,0x1020019081628420100,0x11110854093204040040,0x24502143010011008450,0x9310104010084500942,0x820201808824210404,0x402450214301000100,0x84500952010202008412,0x283200a40100a0484451,0x400420110c024410400,0x20110c0245304040009,0xc426043010011018050,0x9420084010084484441])) rfl
  decide +kernel
theorem g111B5 : CutRow g111 5 0 64 := (@joinRow g111 5 0 3 61 g111P5_0 (@joinRow g111 5 3 14 47 g111P5_3 g111P5_17))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_0 : CutRow g111 6 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_13 : CutRow g111 6 13 26 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P6_39 : CutRow g111 6 39 16 := by
  apply polarBlock (data:=fun _ => (word80 [0x10400190c164853,0x4040041205060540020,0x8100a042092000a41101,0x80484552010401018050,0x48530102020180902843,0x1020201809028430084,0x1018048444100840101,0x8048444100220040a012,0x21300084010180484441,0x820201808824310082,0x2018088243100a41101,0x8048455200a411018048,0x45520084010180484441])) rfl
  decide +kernel
theorem g111B6 : CutRow g111 6 0 55 := (@joinRow g111 6 0 13 42 g111P6_0 (@joinRow g111 6 13 26 16 g111P6_13 g111P6_39))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : CutRow g111 7 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_6 : CutRow g111 7 6 8 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : CutRow g111 7 0 14 := (@joinRow g111 7 0 6 8 g111P7_0 g111P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P8_0 : CutRow g111 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B8 : CutRow g111 8 0 1 := g111P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : mixedTables g111 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g111 0 0
  · exact mixedEmpty g111 1 0
  · exact mixedEmpty g111 2 0
  · exact mixedEmpty g111 3 0
  · exact g111B4
  · exact g111B5
  · exact g111B6
  · exact g111B7
  · exact g111B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K95) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 9 := mixedLower (g:=g111) (i:=0) (hints:=16778595) (before_sound K95 V95) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K95 9 [(111,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V95 low111 (by decide +kernel)
def g119Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8001fffffff00ff1d,0x200797b23c000003f03f])),(BitVec.ofNat 152 (word80 [0x520d4825205216141d,0x390b2391451451451]))),((BitVec.ofNat 152 (word80 [0xffffe0007fffff0063,0x6e8ba06688003f000fc0])),(BitVec.ofNat 152 (word80 [0x604981360464242623,0x2609a066085145145145]))),((BitVec.ofNat 152 (word80 [0xffffffff800000009d,0x8e68c9a5400fc0fc0000])),(BitVec.ofNat 152 (word80 [0x800e00380178383815,0xa48c1a54030c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffa0,0x49e585ccf40000000fff])),(BitVec.ofNat 152 (word80 [0x49012404980000080,0x49e40508c6aaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0x91,0x75183e5b43f000fff000])),(BitVec.ofNat 152 (word80 [0xe003800e00404080,0x64102e4800c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x7001c007000808048,0x91260010930c30c30c30]))),(0x0,0x0),(0x0,0x0)]
def g119C : List ColumnInfo := [(1,0,118,0,7),(2,0,117,0,7),(4,0,115,0,7),(0,16,100,3,6),(16,0,103,0,6),(32,0,87,0,5),(64,0,55,0,5)]
def g119A : List (List Nat) := [[],[16,101]]
def g119D5 (j : Nat) := if j=0 then 0x4ef7259654 else 0
def g119D6 := limbs80 #[#[0xbd8954bb58854be58054,0x59654fbd8954cfd5254b,0x4018a1141f3185b2c0bf,0x81102628]]
def g119H6 (j : Nat) := if j=0 then 0x9 else 0
def g119D7 := limbs80 #[#[0x47888807f953faa9fc54,0x2a547436598a1d90ea61,0x190e]]
def g119H7 := limbs80 #[#[0x92000080c8007564,0x610000000023]]
def g119D8 (j : Nat) := if j=0 then 0x468817f else 0
def g119H8 (j : Nat) := if j=0 then 0x128c808cc0000 else 0
def g119L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g119D5)
  | 6 => (6,2,3,0,0,6,0,g119D6)
  | 7 => (3,1,3,0,0,7,0,g119D7)
  | 8 => (1,0,3,0,0,0,0,g119D8)
  | _ => emptyPacking
def g119I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g119H6
  | 7 => lookupWord 1 19 0 8 3 1 g119H7
  | 8 => lookupWord 1 11 0 7 2 1 g119H8
  | _ => fun _ => none
def g119 : Forest := ⟨119,8,fun i => g119Y[i]?.getD (0,0),g119C,g119A,g119L,g119I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P5_0 : CutRow g119 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B5 : CutRow g119 5 0 1 := g119P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_0 : CutRow g119 6 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P6_4 : CutRow g119 6 4 2 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B6 : CutRow g119 6 0 6 := (@joinRow g119 6 0 4 2 g119P6_0 g119P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P7_0 : CutRow g119 7 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B7 : CutRow g119 7 0 3 := g119P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119P8_0 : CutRow g119 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g119B8 : CutRow g119 8 0 1 := g119P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119T : mixedTables g119 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g119 0 0
  · exact mixedEmpty g119 1 0
  · exact mixedEmpty g119 2 0
  · exact mixedEmpty g119 3 0
  · exact mixedEmpty g119 4 0
  · exact g119B5
  · exact g119B6
  · exact g119B7
  · exact g119B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g119G : graphValid g119 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low119 : Lower true (varsX 119) (graphGoal 119) 9 := mixedLower (g:=g119) (i:=0) (hints:=16778564) (before_sound K111 V111) g119G g119T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K119 := extendKnown K111 9 [(119,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V119 : Known true K119 := extend_ok (m:=119) V111 low119 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffff83fffff242e8,0x44f46d0000000fe03fff])),(BitVec.ofNat 152 (word80 [0x80a4010808040240a0,0x4444d42850a142850a1]))),((BitVec.ofNat 152 (word80 [0xffffc1ffe06b488,0xfcbc20003f8001fc000])),(BitVec.ofNat 152 (word80 [0x12c08a00410822b088,0x78b40162c58b162c58b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000001ffffbd84e,0x91211a01fc07f000007f])),(BitVec.ofNat 152 (word80 [0x3002c10805001804c,0x1121120c183060c18306]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3000000001fff80])),(BitVec.ofNat 152 (word80 [0x240930001260480456,0x6810b2a952a54a952a54]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774fe0007ffe00000])),(BitVec.ofNat 152 (word80 [0x3801c0210380881601,0xa282203060c183060c18]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00e00421c01044912,0x484005c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,2,41,80,6),(0,16,104,3,6),(1,16,104,2,5),(2,16,104,1,5),(17,0,106,0,5),(18,0,105,0,5),(64,2,41,16,5),(66,0,57,0,5),(3,0,104,0,4),(3,16,104,0,4),(9,0,114,0,4),(10,0,113,0,4),(33,0,90,0,4),(34,0,89,0,4),(40,0,83,0,4),(72,0,51,0,4)]
def g123A : List (List Nat) := [[],[83],[96,65],[96,65,83]]
def g123D5 := limbs80 #[#[0x50940483aa5954250120,0x30eab65]]
def g123D6 := limbs80 #[#[0x25fba2ca907a94250120,0xdbec6a12217edc14244,0x837db2a80906f9655012,0x20fd6e4a8241fa509504,0x4837cb22a09077954541,0x520bf6e8a8241bed9150,0x2483d6aa284906bf6450,0x9120ddecaa1241bb5954,0x644827fbaac8904fd755,0x59520ddee4b2a413f5d7,0x1654835fba2ca906bc74,0x4d89509fae9b2a413fdd,0xd3604867fba6c4a84fd7,0x75d81429fae1b22433f5,0x825221f1c191613004fd,0x643403d3a3734312e2b2,0x4615e5b5855524f4c494,0xce09008426]]
def g123H6 := limbs80 #[#[0xc0000036000240000020,0xa]]
def g123D7 := limbs80 #[#[0xe54120fe50120b7d8d10,0xd9120bf59120fb50920f,0x8950bfd9520bf59520bf,0x142bfd9121bfd8121bfd,0x20ff50520ff50910bfd8,0xff58520ff50931ff545,0xff59520ff59120ff5512,0xf58950ff50950ff50930,0x58542ff58142ffd8950f,0x5353f8b9224520a400ff,0x6b5a867f9221f7d9b860,0xb08c0afcbdaf0baae4b2,0x10b9310780305c6b14c3,0x30c686212c21c9101092,0x60601250827050120c4,0x303952101ca12201c305,0x70c941c203002141c30,0x80e19284060480e548,0x6a0611143868a0c0e445,0xe3405070e0c00c222840,0x189850d1061c2070c140,0x442c30634304]]
def g123H7 := limbs80 #[#[0x1310e4b81c042b510731,0x1400000000a32e3bcc10,0x2c0697f1600000000f,0x8930e8500042be22,0xc42180000001a00000,0xa40000000000090c0000,0x23703d128eb000000005,0xca34c1013a2a00000485,0x643ce00072]]
def g123D8 := limbs80 #[#[0xd21fea87f4c3fa41fd10,0xd210c024007f50bfa63f,0x10882640e230f161cea5,0x2259222891464009648e,0x98c23071648a3221300,0x18040899222cc2059018,0x1c65258e]]
def g123H8 := limbs80 #[#[0x44c00000001d8ac1280,0x568180032e0000000000,0x1a3c002140018,0x40100000000000000000,0x4f51e44001d800000000,0xa18c00000784000001c,0x5ce001c48000009,0x287000d04000c3000000,0xb80000122c0000064600,0x2e5800a20c995,0x92c0240000031a000000,0x14c001e6000143,0x3c278a0000000000000,0xccfd9c116b6ea636e0e0,0xf4400000000000001,0xedc00000000518002b1]]
def g123D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g123H9 := limbs80 #[#[0x86b86100014005,0x78800dc0000000000,0xa000000025d900227460,0xa00036200000030,0x158006080]]
def g123L : Nat → Packing
  | 5 => (2,4,5,0,0,3,0,g123D5)
  | 6 => (29,3,5,0,0,8,0,g123D6)
  | 7 => (26,2,5,0,0,10,0,g123D7)
  | 8 => (7,1,5,0,0,9,0,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 17 0 6 1 1 g123H6
  | 7 => lookupWord 8 59 4 11 5 2 g123H7
  | 8 => lookupWord 11 113 3 11 5 2 g123H8
  | 9 => lookupWord 3 41 1 9 3 2 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : CutRow g123 5 0 2 := by
  apply polarBlock (data:=fun _ => (word80 [0x4102094486,0x12100041020944861210])) rfl
  decide +kernel
theorem g123B5 : CutRow g123 5 0 2 := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : CutRow g123 6 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_2 : CutRow g123 6 2 27 := by
  apply polarBlock (data:=fun _ => (word80 [0x4102094486,0x12310443020944863231,0x210110c84611300041,0x2094486123100410209,0x44861231004102094486,0x12310041020944861231,0x410209448612310041,0x2094486123100410209,0x44861221004102094486,0x12310041020944861231,0x410209448612310041,0x2094486122100410209,0x44861221004102094486,0x122100602050a8162360,0x410209448612200041,0x2094486122000410209,0x44861220004102094486,0x12200041020944861210,0x410209448612100041,0x2094486122000410209,0x44861220002000506816,0x1160014021108c540b61])) rfl
  decide +kernel
theorem g123B6 : CutRow g123 6 0 29 := (@joinRow g123 6 0 2 27 g123P6_0 g123P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : CutRow g123 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_1 : CutRow g123 7 1 11 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_12 : CutRow g123 7 12 4 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_16 : CutRow g123 7 16 10 := by
  apply polarBlock (data:=fun _ => (word80 [0x210050681611300041,0x2094486123100410209,0x44861231004102094486,0x12310041020944861231,0x4400c1603442510041,0x2094486123100410209,0x44861231004102094486,0x1231040400190c466054])) rfl
  decide +kernel
theorem g123B7 : CutRow g123 7 0 26 := (@joinRow g123 7 0 12 14 (@joinRow g123 7 0 1 11 g123P7_0 g123P7_1) (@joinRow g123 7 12 4 10 g123P7_12 g123P7_16))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : CutRow g123 8 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : CutRow g123 8 0 7 := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : CutRow g123 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B9 : CutRow g123 9 0 1 := g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : mixedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g123 0 0
  · exact mixedEmpty g123 1 0
  · exact mixedEmpty g123 2 0
  · exact mixedEmpty g123 3 0
  · exact mixedEmpty g123 4 0
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K119) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := mixedLower (g:=g123) (i:=0) (hints:=16777283) (before_sound K119 V119) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K119 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V119 low123 (by decide +kernel)
def g125Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffffffffffffffff6,0x88e80739cb0000007fff])),(BitVec.ofNat 152 (word80 [0xa402900400802006,0x88200708484a5294a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff0003ffe01fff00e,0x7249cc0cf0003e0f8000])),(BitVec.ofNat 152 (word80 [0xac06b0128340a416e,0x5049c00cd018c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffc00001fffff3,0x4ccf90e21807c1f0001f])),(BitVec.ofNat 152 (word80 [0x13004c01b0580c8240,0x40cd80e2101084210842]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x94f7681bb100000003e0])),(BitVec.ofNat 152 (word80 [0x5c097025c0612f0380,0x14d76813b1b5ad6b5ad6]))),((BitVec.ofNat 152 (word80 [1,0x1710a38776f801fffc00])),(BitVec.ofNat 152 (word80 [0x600180060080300401,0x7002001222108421084]))),((BitVec.ofNat 152 (word80 [0xc,0xe9177e4005fffe000000])),(BitVec.ofNat 152 (word80 [0x800e00380101c00800,0xa8121e0005c6318c6318]))),(0x0,0x0),(0x0,0x0)]
def g125C : List ColumnInfo := [(4,0,121,0,7),(8,0,117,0,7),(16,0,109,0,7),(0,16,108,1,6),(64,0,61,0,6),(1,0,108,0,5),(1,16,108,0,5),(32,0,93,0,5)]
def g125A : List (List Nat) := [[]]
def g125D5 := limbs80 #[#[0x26ebb4a9185d77155230,0x9dee4b2a813ddc56550,0x2ebb8aa8a1cf7715974,0xf624c3]]
def g125D6 := limbs80 #[#[0x755230bdd8554b759230,0x59540fe54140f795230f,0x5150bf59740bfd9540bf,0x154f755143bfd9150df5,0xbf58254fdd8554bfd8,0xa0907b706a503b2b2010,0x61201d6422e42cbc0b0,0xe18010062080431241b,0xc41001188262021882d2]]
def g125H6 := limbs80 #[#[0x9af900da0000000a4000,0x6000000007]]
def g125D7 := limbs80 #[#[0xd50ffa07f503ba87de30,0x38291a0b007f953faa9f,0x2c339644b0d912a25647,0xce9512c32144bb0ce951,0xa69152e3bad2448]]
def g125H7 := limbs80 #[#[0x2dd34d5c60077005b508,0x86900003ceaf300f100f,0xb]]
def g125D8 (j : Nat) := if j=0 then 0x681117f else 0
def g125H8 := limbs80 #[#[0x0,0x36800,0x6e0000000000000100,0x5000000000000,0x0,0x0,0x1c00000000,0x0,0x3580000000000000000,0x540000000000000000]]
def g125L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g125D5)
  | 6 => (14,2,3,0,0,8,0,g125D6)
  | 7 => (7,1,3,0,0,8,0,g125D7)
  | 8 => (1,0,3,0,0,0,0,g125D8)
  | _ => emptyPacking
def g125I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 17 0 7 3 0 g125H6
  | 7 => lookupWord 3 19 4 8 4 0 g125H7
  | 8 => lookupWord 1 113 0 7 3 0 g125H8
  | _ => fun _ => none
def g125 : Forest := ⟨125,8,fun i => g125Y[i]?.getD (0,0),g125C,g125A,g125L,g125I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P5_0 : CutRow g125 5 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B5 : CutRow g125 5 0 6 := g125P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_0 : CutRow g125 6 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P6_2 : CutRow g125 6 2 12 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B6 : CutRow g125 6 0 14 := (@joinRow g125 6 0 2 12 g125P6_0 g125P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_0 : CutRow g125 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P7_2 : CutRow g125 7 2 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B7 : CutRow g125 7 0 7 := (@joinRow g125 7 0 2 5 g125P7_0 g125P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125P8_0 : CutRow g125 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g125B8 : CutRow g125 8 0 1 := g125P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125T : mixedTables g125 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g125 0 0
  · exact mixedEmpty g125 1 0
  · exact mixedEmpty g125 2 0
  · exact mixedEmpty g125 3 0
  · exact mixedEmpty g125 4 0
  · exact g125B5
  · exact g125B6
  · exact g125B7
  · exact g125B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g125G : graphValid g125 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low125 : Lower true (varsX 125) (graphGoal 125) 9 := mixedLower (g:=g125) (i:=0) (hints:=33555715) (before_sound K123 V123) g125G g125T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K125 := extendKnown K123 9 [(125,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V125 : Known true K125 := extend_ok (m:=125) V123 low125 (by decide +kernel)
def g126Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xd60912f74a68000f801f])),(BitVec.ofNat 152 (word80 [0x481610542128429028,0x540812f642414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0x60153daec91001f003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,0x601538aa4810c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c4f2134e803e007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc171,0x3184b2034e00c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bea0b99e80000001f])),(BitVec.ofNat 152 (word80 [0x1c0a7014e029c0181,0x283e80999aeb5ad6b5a]))),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa117cb687c0007fe0])),(BitVec.ofNat 152 (word80 [0x38007000e00200,0x2680154908318c6318c]))),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x88024400212421084210]))),(0x0,0x0),(0x0,0x0)]
def g126C : List ColumnInfo := [(4,0,122,0,7)]
def g126A : List (List Nat) := [[],[50]]
def g126D7 (j : Nat) := if j=0 then 0x7f else 0
def g126L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g126D7)
  | _ => emptyPacking
def g126I (_ _ : Nat) : Option (Nat × Nat) := none
def g126 : Forest := ⟨126,7,fun i => g126Y[i]?.getD (0,0),g126C,g126A,g126L,g126I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126P7_0 : CutRow g126 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g126B7 : CutRow g126 7 0 1 := g126P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126T : mixedTables g126 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g126 0 0
  · exact mixedEmpty g126 1 0
  · exact mixedEmpty g126 2 0
  · exact mixedEmpty g126 3 0
  · exact mixedEmpty g126 4 0
  · exact mixedEmpty g126 5 0
  · exact mixedEmpty g126 6 0
  · exact g126B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g126G : graphValid g126 (boundsBefore K125) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low126 : Lower true (varsX 126) (graphGoal 126) 8 := mixedLower (g:=g126) (i:=0) (hints:=18961728) (before_sound K125 V125) g126G g126T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K126 := extendKnown K125 8 [(126,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V126 : Known true K126 := extend_ok (m:=126) V125 low126 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffffffffffffff,0xfff04daced850000f0ff])),(BitVec.ofNat 152 (word80 [0x40580a002a00940148,0xa70450c410511111111]))),((BitVec.ofNat 152 (word80 [0xfffc007fff0001fffc,0x3df427164c000f0f00])),(BitVec.ofNat 152 (word80 [0x829053014c06d80990,0x3335e426144c33333333]))),((BitVec.ofNat 152 (word80 [0x7ffffffe0000,0x86557cdf800f00000])),(BitVec.ofNat 152 (word80 [0xce19c2a7054e0ade1,0x5c086557cdf877777777]))),((BitVec.ofNat 152 (word80 [0x7fffffffffff,0xff968d73ae0b0f00000f])),(BitVec.ofNat 152 (word80 [0x1702e033806700ce02,0x60068873ae0a66666666]))),((BitVec.ofNat 152 (word80 [0xffffff800000000000,0x8bacf93a6f0000ff0])),(BitVec.ofNat 152 (word80 [0x1803003c007800f003,0x80081ac182a244444444]))),(0x0,0x0),(0x0,0x0),(0x674250407afffff000,(BitVec.ofNat 152 (word80 [0x400080010000,0x88888888]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(4,0,155,0,7),(1,0,158,0,6),(2,0,157,0,6),(8,0,151,0,6),(16,0,143,0,6),(0,4,27,128,5),(5,0,154,0,5),(6,0,153,0,5),(9,0,150,0,5),(10,0,149,0,5),(18,0,141,0,5),(20,0,139,0,5),(128,0,27,0,4),(128,4,27,0,4)]
def g159A : List (List Nat) := [[],[64,49]]
def g159D3 (j : Nat) := if j=0 then 0x1921506107558910 else 0
def g159D4 := limbs80 #[#[0x50d50443c85514254110,0x4427421d4354110f1154,0x6107558910aa48655142,0xd49109e1809d52144269,0xf8143d494044278e0171,0xd4940442e86135250110,0x443e058943501109e187,0x5d54350110f817250d40,0x54110d937550d4044364,0xb60855895044398d9562,0x5c352442786027550910,0x44370e0d70d4910dc143,0xe1974d49109e3845c352,0xd49109c7835db5244239,0x9c5831d56244269e1176,0x5d0654434c5417419510,0x48639e057499520c3565,0x61373583528cf835c265,0xe0c8b098806830180233,0xd1b9a1897159412910f8,0xc2aa927a624a321a01e9,0x1304002]]
def g159H4 (j : Nat) := if j=0 then 0xf0 else 0
def g159D5 := limbs80 #[#[0xaf0b86a4887914350110,0xbccea90a2133dcd60d4,0x43f1a9280885e571d491,0x10fc2c4a8221f8509504,0x443b8aa2a0887d143541,0x910f4aa8a1221dcd5150,0x2443e2a1ea4885e67550,0x4910bcaeda9221795d35,0x6244372b2ac4885e776d,0x55110bc8eab1221b9d95,0x150482daba0ca884f476,0x4541409dae932a41da55,0xc265486f3b82a290f395,0x21541109dee0b0ea53b5,0xd952144372b2a42887e1,0x77254510be6e0a8a21b9,0xdd9751442f8b86a2885e,0xed76d4910bd2e1a92219,0xf85c940443f0b1280884,0x7b36450110f62a8a0221,0x17cdd540442f8baa8088,0x87e37254110fc6a4a822,0x217cdd150443e9b9aa08,0x887736554110ee0caa82,0x221795d942443d3b2284,0x4887c54358910fc2e1a9,0xa221f4dc143442f3ba2c,0xa8884f77655110bcee4a,0x32a21795c865442f8b86,0x2ca886756519510baae6,0x8b2a2175dcd65442f3b9,0x96ca886776599510b6ee],#[0xe2aa241f2dcd50482f2b,0xb86a4a04ed7199520bce,0xec690aa13b5db52502f4,0x6ba6c4a84ed71d8950d9,0x9ee5b1aa1b3d4b635427,0x7bb8ac9a84dd74d8d50d,0x9bee6b06a33b5c362546,0xb67b9ac1a94ef7158352,0x61a8500d8013bdd160d4,0xe3d0e8370d02a08e2087,0x85f9725293e4c9264690,0x892187f9e4761be6c99,0xa12789b260952488f23,0xb92d8b32c0ad2a8a729,0xd1338cb320c5308bf2f,0xe9398e3380dd368d735,0x1013f8fb3e0f53c8ef3b,0x119459134410d4290741,0xe01cb92b4a1254891f47,0x6153040000a20a8049c2,0x200000000802000007a,0x68200d04004087040684,0x604]]
def g159H5 := limbs80 #[#[0x2aad450df01003c004c0,0x88000c380000000,0x73334003d600000,0x24e4782344b6c000008b,0x1090001a00000e4119,0x1889784800808003c400,0xf60002555ce3c4ae3701,0xc6002850000000011]]
def g159D6 := limbs80 #[#[0xc50110bb58910f948510,0xd4910f950910fc54110f,0x4b10f550d10f958910f9,0x520bb59120fa54120f9d,0x21b7d8d50bbd8950bb99,0x2bbd8951bb99521f9545,0xfe54110bb58752bb5835,0xbd4910fdd4510fd54510,0x19510fdd5110fd55110f,0x9510fd99510fd59510fd,0x940fe54140fb55120fdd,0x50df55150fb48550fbd4,0x1bfd8151bf59350dfd51,0xbf59510fb58910bf5835,0xdd9110fd59110bfd9510,0x59540fb58940fb54520f,0x4950bfd8550bfd9540bf,0x150f7d8d50fbd8950fbd,0x51fbd4951bf58750bfd9,0xfb58752fb58352fbd89,0x22b8961f866138300600,0x65b9565112c469023a8d,0xa88a107f9ec739b66918,0x2b5acaaca9aa3a7694a3,0x2db366d2330c630cbeae,0x2e7396e438ae137ede37,0x2f33c6f03baed3aeea3a,0xb0214128a8d0ca1e80fd,0x3890a038a86c30b02030,0x428a834e2c14845d07a0,0x680e83026a8343206343,0x4a4ca8334a1c38700801],#[0x3443196833180a9005a8,0x316209004240d0930b0,0x35130814055014035014,0x19234308140340151340,0xcd0440428cd1c3141341,0xc100d1050400c200d0]]
def g159H6 := limbs80 #[#[0xc806186213886100c20,0x7000b00000c846100001,0x1ee3d108102d2ab4,0xa1900000014521a000,0x300014de31a46a4f7160,0x2b9000832a0bb3a81872,0x880000008b600014e137,0x7c4334870fc2644cfb44,0x51b000000000212b3cd1,0x3f00013800000072131c,0x74b98e9255208240004,0xf35c2d00040915000,0x9600030108901400034a,0x48b000507144000d3e6,0xc3b000000d4900083900,0x8500062c51f904000e05,0xccc5e1d630000115fc3a,0x1b8134000000000e4128,0x786a2b2034a7,0xe000c40000000d52f0a0,0xe13f29000851000000c2,0x11933000f28436000000,0x606f423b760db2740c0,0x622f2f80e01000000]]
def g159D7 := limbs80 #[#[0xf52f690fb483ee21f510,0xa3ff50fea87f503fa21e,0x87341245e1a007fd47fa,0x83152081230f96d2ed42,0x815b14a8e2b748309042,0xad82902360850990335,0x14c14290504345690504,0x14c14d15a]]
def g159H7 := limbs80 #[#[0x5600203402210216500a,0x9c4616ca060380575020,0x3246d687b2713e000006,0xc24404db1d45ab269701,0x14a200026c001598d6d1,0xe7a2fb42001bc000b48f,0x423001857851d8000520,0xba30268004860e0f0b82,0x20c940040d5bbeb57bec,0x25c000a835d24f0a5b40,0xaa7c5474003d1001,0x3000b05421cb70300e00,0xfbc00000229f36e80d,0x1a648f000c0b3d5eb8,0x20be6faac00000]]
def g159D8 (j : Nat) := if j=0 then 0x9a8013f else 0
def g159H8 := limbs80 #[#[0xc80137f3000018899100,0x79400ca005112a67289,0x58f426951003f0590,0x5e800000004f20e]]
def g159L : Nat → Packing
  | 3 => (1,5,4,0,0,0,0,g159D3)
  | 4 => (29,4,4,0,0,8,0,g159D4)
  | 5 => (83,3,4,0,0,10,0,g159D5)
  | 6 => (57,2,4,0,0,10,0,g159D6)
  | 7 => (11,1,4,0,0,9,0,g159D7)
  | 8 => (1,0,4,0,0,0,0,g159D8)
  | _ => emptyPacking
def g159I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 4 0 0 g159H4
  | 5 => lookupWord 8 59 5 10 5 1 g159H5
  | 6 => lookupWord 24 149 5 12 7 1 g159H6
  | 7 => lookupWord 18 97 6 11 6 1 g159H7
  | 8 => lookupWord 5 31 4 9 4 1 g159H8
  | _ => fun _ => none
def g159 : Forest := ⟨159,8,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P3_0 : CutRow g159 3 0 1 := by
  apply polarBlock (data:=fun _ => 0x208005024348432) rfl
  decide +kernel
theorem g159B3 : CutRow g159 3 0 1 := g159P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P4_0 : CutRow g159 4 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P4_5 : CutRow g159 4 5 24 := by
  apply polarBlock (data:=fun _ => (word80 [0x20,0x4021102094000200402,0x11020940020004020920,0x124201c0201221088421,0x410028550812320208,0x520834902110000010,0x49048442100000082502,0x84420200040209201242,0x10000050251c84420200,0x24020520122010000050,0x251c843110000050251c,0x84420208005024349031,0x2080050243490210021,0x4022102093210001080,0x25108121100020802520,0x82101000800825028830,0x10000050251c84421000,0x8450a844100210402,0x21040941100000502514,0x84421000005025148442])) rfl
  decide +kernel
theorem g159B4 : CutRow g159 4 0 29 := (@joinRow g159 4 0 5 24 g159P4_0 g159P4_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_0 : CutRow g159 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_3 : CutRow g159 5 3 25 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_28 : CutRow g159 5 28 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x41041221002004022102,0x94000a0840221020d20,0xa0840221020d200020,0x4022102095000210402,0x41021130100000804528,0x84530021005068161130,0x2000402092012520041,0x402410412100108000a,0x1412883101004002290c,0x82211000001049049053,0x10000008250288530200,0x64020920164201c02012,0x21088421020800520834,0x90320108002a041a8831,0x10001080492081430200,0x4020920125302802402,0x9201642100010804920,0x81320108000a04128831,0x10008008250288520200,0x2402052012310108000a,0x41288310108000a0412,0x88210208005024349042,0x200202a102a12321000,0x10804520814302002402,0x5201231020024020520,0x12310200240205201231,0x2001402052011420208,0xa042290320108000a,0x4128821014014024110,0x9410108000a04128820,0x108000a041288200060,0xa40221020b2010000050,0x2d1c845301004002290c,0x82210200240205201242,0x2006402092016420100,0x1402091009410060a402,0x21020b10002800522816,0x81300280240205201231])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P5_76 : CutRow g159 5 76 7 := by
  apply polarBlock (data:=fun _ => (word80 [0x2800824022,0x81400041040241041221,0x60a40221020b200020,0x4022102095000c10402,0x41041631020004020920,0x12530020040221020950])) rfl
  decide +kernel
theorem g159B5 : CutRow g159 5 0 83 := (@joinRow g159 5 0 28 55 (@joinRow g159 5 0 3 25 g159P5_0 g159P5_3) (@joinRow g159 5 28 48 7 g159P5_28 g159P5_76))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_0 : CutRow g159 6 0 19 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_19 : CutRow g159 6 19 19 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_38 : CutRow g159 6 38 19 := by
  apply polarBlock (data:=fun _ => (word80 [0x20,0x84022102092000410402,0x41041231002084022102,0x9200020840221020920,0x210050681611400028,0x824022815000410402,0x41041231004104024104,0x12310041040241041231,0x60a40221020b300021,0x4024102114000210402,0x41021140004800824024,0x82410021407078161130,0x108000a041288420108,0xa041288420060a402,0x21020b300060a4022102,0xb300108000a04128842])) rfl
  decide +kernel
theorem g159B6 : CutRow g159 6 0 57 := (@joinRow g159 6 0 19 38 g159P6_0 (@joinRow g159 6 19 19 19 g159P6_19 g159P6_38))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_0 : CutRow g159 7 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P7_5 : CutRow g159 7 5 6 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B7 : CutRow g159 7 0 11 := (@joinRow g159 7 0 5 6 g159P7_0 g159P7_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P8_0 : CutRow g159 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B8 : CutRow g159 8 0 1 := g159P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : mixedTables g159 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g159 0 0
  · exact mixedEmpty g159 1 0
  · exact mixedEmpty g159 2 0
  · exact g159B3
  · exact g159B4
  · exact g159B5
  · exact g159B6
  · exact g159B7
  · exact g159B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K126) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 9 := mixedLower (g:=g159) (i:=0) (hints:=1859) (before_sound K126 V126) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K126 9 [(159,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V126 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xfa61e88178cb000f00ff])),(BitVec.ofNat 152 (word80 [0x1481400a804a01481,0x4a40a081484911111111]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0x7800d87cab700f00000])),(BitVec.ofNat 152 (word80 [0x1590a62530b6c29906,0x67800d81cab777777777]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1ce23b09cd10f000f00])),(BitVec.ofNat 152 (word80 [0x19e13809c02700de0b,0x80c423909cd133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2143f483bb8f000f00f])),(BitVec.ofNat 152 (word80 [0x1e01c00e003800e00c,0x40f4031b022222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x117d0a387760000fff0])),(BitVec.ofNat 152 (word80 [0xa00000b002c00b0010,0x11350220206cccccccc]))),(0x0,0x0),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0xc00200c003000c0020,0x29102e000088888888]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(4,0,171,0,7)]
def g175A : List (List Nat) := [[],[48]]
def g175D7 (j : Nat) := if j=0 then 0x7f else 0
def g175L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g175D7)
  | _ => emptyPacking
def g175I (_ _ : Nat) : Option (Nat × Nat) := none
def g175 : Forest := ⟨175,7,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : CutRow g175 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : CutRow g175 7 0 1 := g175P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : mixedTables g175 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g175 0 0
  · exact mixedEmpty g175 1 0
  · exact mixedEmpty g175 2 0
  · exact mixedEmpty g175 3 0
  · exact mixedEmpty g175 4 0
  · exact mixedEmpty g175 5 0
  · exact mixedEmpty g175 6 0
  · exact g175B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 8 := mixedLower (g:=g175) (i:=0) (hints:=1395) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 8 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff0007ffffff00ff5,0xb261513c2a0001f07c1f])),(BitVec.ofNat 152 (word80 [0x2a035012805216141,0xb0605114080842108421]))),((BitVec.ofNat 152 (word80 [0xffffff8003fffff002,0x17e8d44785003e0003e0])),(BitVec.ofNat 152 (word80 [0x44c12609b046424262,0x1360d40781294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffffc00000009,0xd8c2c299d107c00f8000])),(BitVec.ofNat 152 (word80 [0x17003801c017838381,0x98c2c018d118c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffa,0x4fe283ab8f8000003ff])),(BitVec.ofNat 152 (word80 [0x980240120098000008,0x48a2828305294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1711a3877600000ffc00])),(BitVec.ofNat 152 (word80 [0xe00b805c02e0040408,0x711228326e739ce739c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0xc00600300080804,0x40150240048421084210]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7),(4,0,179,0,7),(0,32,146,5,6),(2,0,181,0,6),(32,0,151,0,6),(16,0,167,0,5),(34,0,149,0,5),(128,0,55,0,5),(17,0,166,0,4),(130,0,53,0,4)]
def g183A : List (List Nat) := [[]]
def g183D5 := limbs80 #[#[0x35b2a6c2a9eb554d8553,0xc]]
def g183D6 := limbs80 #[#[0xb58853bd58453be58053,0x54531d7d4e53bdd8553b,0x5131f794d31f754d31fd,0x731bfd9531bf59531ef5,0x31ef55331f754f31fdd4,0x1df54f51df54d51bf597,0xfdd8553fd18553bf58f5,0xf95153ef55153bfd8553,0x95253ef55253bf58653e,0x483c2a1200bf59653ef,0xc96908a847e78726c666,0x8d2ccc6c0bab4aea8a29,0x11f0085c070c7202ded,0x147c03c]]
def g183H6 (j : Nat) := if j=0 then 0x1b8 else 0
def g183D7 := limbs80 #[#[0xd51ff98ff4c77ca9bd54,0xa7fe53fea9ff14ffea3f,0xd0bf4d9f0ba3e0f803fe,0x478c0c291228c059d445,0x82453c60628a72c60614,0x828c1239451818e314d1,0x8a3028e410ce58c07194,0xa41460918e41]]
def g183H7 := limbs80 #[#[0x45187661c0340880,0xd200d3800014242803b2,0x132c00fa80000f39beae,0x78e350702d636c1f1496,0xad700298000058400009,0x4]]
def g183D8 (j : Nat) := if j=0 then 0x3421017f else 0
def g183H8 := limbs80 #[#[0x330068000086f00089a2,0x1100000000a500000000,0x4a7000000000000]]
def g183L : Nat → Packing
  | 5 => (2,3,4,0,0,3,0,g183D5)
  | 6 => (27,2,4,0,0,8,0,g183D6)
  | 7 => (10,1,4,0,0,9,0,g183D7)
  | 8 => (1,0,4,0,0,0,0,g183D8)
  | _ => emptyPacking
def g183I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 5 1 0 g183H6
  | 7 => lookupWord 6 41 6 9 5 0 g183H7
  | 8 => lookupWord 2 29 0 8 4 0 g183H8
  | _ => fun _ => none
def g183 : Forest := ⟨183,8,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P5_0 : CutRow g183 5 0 2 := by
  apply polarBlock (data:=fun _ => (word80 [0x20004020920,0x12420200040209201242])) rfl
  decide +kernel
theorem g183B5 : CutRow g183 5 0 2 := g183P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_0 : CutRow g183 6 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P6_5 : CutRow g183 6 5 22 := by
  apply polarBlock (data:=fun _ => (word80 [0x2200a0d02a,0x2140002200a0d02a2160,0x2200a0d02a21600022,0xa0d02a2140002200a0,0xd02a2160002200a0d02a,0x2160002200a0d02a2140,0x2200a0d02a21300022,0xa0d02a2130002200a0,0xd02a2140002200a0d02a,0x2140002200a0d02a2140,0x2200a0d02a21400022,0xa0d02a2160002200a0,0xd02a2130002200a0d02a,0x2130002200a0d02a2140,0x2200a0d02a21400022,0xa0d02a2160002200a0,0xd02a2130002200a0d02a,0x2130002200a0d02a2130])) rfl
  decide +kernel
theorem g183B6 : CutRow g183 6 0 27 := (@joinRow g183 6 0 5 22 g183P6_0 g183P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : CutRow g183 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_2 : CutRow g183 7 2 8 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : CutRow g183 7 0 10 := (@joinRow g183 7 0 2 8 g183P7_0 g183P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P8_0 : CutRow g183 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B8 : CutRow g183 8 0 1 := g183P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : mixedTables g183 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g183 0 0
  · exact mixedEmpty g183 1 0
  · exact mixedEmpty g183 2 0
  · exact mixedEmpty g183 3 0
  · exact mixedEmpty g183 4 0
  · exact g183B5
  · exact g183B6
  · exact g183B7
  · exact g183B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 9 := mixedLower (g:=g183) (i:=0) (hints:=1348) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 9 [(183,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff622e,0xa02d1a40000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x28028008400040220a,0x20011201041041041041]))),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02952,0xa662f48003f00003f000])),(BitVec.ofNat 152 (word80 [0x304b04500210822902,0xa462d40b2cb2cb2cb2cb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x91d84280fc003f00003f])),(BitVec.ofNat 152 (word80 [0x400c01608405001884,0x81584086186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6956a9bf00000003ffc0])),(BitVec.ofNat 152 (word80 [0x809009800026048044,0x9142994514514514514]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc4000003ffc0000])),(BitVec.ofNat 152 (word80 [0x2e02e0108b8088171,0x18a08c78e38e38e38e38]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104411,0x42800060820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,7),(2,0,185,0,7),(8,0,179,0,7),(16,0,171,0,7),(32,0,155,0,7),(128,0,59,0,7),(0,2,41,144,6),(0,32,146,9,6),(1,32,146,8,5),(8,32,146,1,5),(10,0,177,0,5),(16,2,41,128,5),(18,0,169,0,5),(33,0,154,0,5),(34,0,153,0,5),(128,2,41,16,5),(130,0,57,0,5),(9,0,146,0,4),(9,32,146,0,4),(17,0,170,0,4),(24,0,163,0,4),(41,0,146,0,4),(50,0,137,0,4),(136,0,51,0,4),(144,0,41,0,4),(144,2,41,0,4),(146,0,41,0,4)]
def g187A : List (List Nat) := [[],[112,81,67]]
def g187D5 := limbs80 #[#[0x54950443d254d3254120,0x482da6153254120f6372,0xe0d5254120e696354950,0x930c0f4932549504c2da,0x3d8]]
def g187D6 := limbs80 #[#[0x3e899260887315454110,0xed2a4a8241dc5495044,0x83f4992a0904bd75d912,0x30f9aa699241de54d504,0x443e6a92649877952541,0x110fe2e4a8221fc5c930,0x483f5b92a0907f37254,0x4520d7ec898a41be58d5,0x3248376b2a64906bf645,0x54920bdeea992417b5d5,0x553482f7b9aa4906ed63,0x558d209faeca9a417ddc,0xcd6548377b92ca904ff7,0x6254130fb264a82613fd,0xd95324c3edb9aa0986fb,0xd75d8930bbeea99261b7,0xf9d9325427eb96ca984f,0xfd75d81329fae7b12a13,0x2a9488e3c1686816004,0x6803e9e8ee74389b8c66,0x936984aa491e8c44a190,0xad966b056aa94ea450a7,0x6441312190c64482bc5c,0x81f002c605120d899c00,0x1912080c46108014120]]
def g187H6 := limbs80 #[#[0x154900004000002a84,0x3cfcbac0]]
def g187D7 := limbs80 #[#[0xd55110fc54110fc4c110,0xd9120ed95310ed95110e,0x4910fd4c910bfd8910af,0xb10fd4cb10fdd8910fd5,0x20fb4c920fe54120fd54,0xbf59520bf58d20fb549,0xbfd8930f74c930fe5413,0xfd8132bfd8950bfd9530,0x54d20ff54520ff4c520b,0xc950ff54540ff54930ff,0x950ff59530ff58930ff4,0xff58132ffd8950ff58,0x1dc2f8470730be12c148,0x4700c496e2b45188b102,0xc984ae0560a01282203c,0x93f77b8ee9cc37d6c4c,0xc590419161542483d062,0x54c84649058b20832213,0x6cb8f0c20f0064b04a86,0x2482246420e1200b823c,0x8224682488a40b803c63,0x8d130a3243c64a483344,0x2812a4882f1929210a94,0x8b860604a9218a134618,0x2704592189c64c221a51,0xc9314a860a0491318a94,0x84860d14181242870808,0x100c1c4181832a182812,0xcc97244c48884c11122,0x3248a0634386]]
def g187H7 := limbs80 #[#[0x12888b042000302,0xa000000000000008e800,0x21900000249ca230,0x55b000000000007840,0x0,0x3140000000000000,0xd00,0x0,0x40000000000000000828,0x900000000000321a23a5,0x1c78d5001b5be,0x90d60c00000000000000,0x65f000000003d4,0x8c00000b0e8800000000,0xb00000074d81000001a,0x60aa31e5d0ff1b886002,0x10000000000000033800,0x40,0x0,0x1e0000000000,0x30680000000,0x24000000003840000000,0x10f000000000003,0x2c941cd11e418738c,0x0,0xf120]]
def g187D8 := limbs80 #[#[0xd30fe907f443ee21f510,0x83fd31fe90ff543fa81f,0xf05a210a82a007f4cbfa,0x89220191b558cb75121c,0x402cf1c892204068604,0xc02551849638521c8922,0x89563491130e58a19082,0x80b28f1a38a13e420500,0x893892c812280f584264,0x50396090984b0]]
def g187H8 := limbs80 #[#[0x56742544268040340202,0xe3b81000798ac1e6,0xd0512000000000012540,0x7c0061a426d44004,0xa0000000052d93c00005,0x8386ec30011074968389,0x40921b1717f8da4e1212,0x78e09400063f02000003,0xa02fb200000000000286,0x161f088000015546b50,0x92e4f7d8c11a3d690000,0x61129930c3700939]]
def g187D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g187H9 := limbs80 #[#[0x6000001d304000000002,0x73c140000388000075,0x1030000000,0xa8000000000000000000,0x10004800000000000006,0x690000149f,0x1c6db800000000604000,0x6a0022,0x5e]]
def g187L : Nat → Packing
  | 5 => (6,4,5,0,0,5,0,g187D5)
  | 6 => (37,3,5,0,0,9,0,g187D6)
  | 7 => (34,2,5,0,0,11,0,g187D7)
  | 8 => (11,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 13 3 8 3 1 g187H6
  | 7 => lookupWord 12 181 3 11 6 1 g187H7
  | 8 => lookupWord 13 79 6 11 6 1 g187H8
  | 9 => lookupWord 4 71 2 9 4 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : CutRow g187 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_1 : CutRow g187 5 1 5 := by
  apply polarBlock (data:=fun _ => (word80 [0x141840205041a200108,0x182c070094302001050,0x2c341131014184024104,0x1a100200240205201220])) rfl
  decide +kernel
theorem g187B5 : CutRow g187 5 0 6 := (@joinRow g187 5 0 1 5 g187P5_0 g187P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : CutRow g187 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_1 : CutRow g187 6 1 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_5 : CutRow g187 6 5 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_10 : CutRow g187 6 10 27 := by
  apply polarBlock (data:=fun _ => (word80 [0x14184024104,0x1a310021040241021130,0x280042201281500048,0xc26034825101418402,0x41041a31014184024104,0x1a510021040241021150,0x1020008841228210200,0x10502c34115201418402,0x5041a40030300088412,0x38420041040241041221,0x208402210209200020,0x8180e062092002000402,0x920126210008180e160,0x88540021005068161120,0x141840241041a210208,0x522834904200280042,0x2012814000200040a012,0x216000200040a0122160,0x3030008841238310041,0x4024104121002002402,0x5201241020024020520,0x12411000208045208243])) rfl
  decide +kernel
theorem g187B6 : CutRow g187 6 0 37 := (@joinRow g187 6 0 5 32 (@joinRow g187 6 0 1 4 g187P6_0 g187P6_1) (@joinRow g187 6 5 5 27 g187P6_5 g187P6_10))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : CutRow g187 7 0 6 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_6 : CutRow g187 7 6 17 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_23 : CutRow g187 7 23 6 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_29 : CutRow g187 7 29 5 := by
  apply polarBlock (data:=fun _ => (word80 [0x480082402482510041,0x4024104123100410402,0x41041231010200088412,0x28420048008240248251])) rfl
  decide +kernel
theorem g187B7 : CutRow g187 7 0 34 := (@joinRow g187 7 0 23 11 (@joinRow g187 7 0 6 17 g187P7_0 g187P7_6) (@joinRow g187 7 23 6 5 g187P7_23 g187P7_29))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : CutRow g187 8 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_2 : CutRow g187 8 2 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : CutRow g187 8 0 11 := (@joinRow g187 8 0 2 9 g187P8_0 g187P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : CutRow g187 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B9 : CutRow g187 9 0 1 := g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : mixedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g187 0 0
  · exact mixedEmpty g187 1 0
  · exact mixedEmpty g187 2 0
  · exact mixedEmpty g187 3 0
  · exact mixedEmpty g187 4 0
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := mixedLower (g:=g187) (i:=0) (hints:=67) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 10 [(187,[]),(246,[96,65,32,50]),(250,[96,65,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xe88328939da000f00fff])),(BitVec.ofNat 152 (word80 [0x50028008000080,0x28020090848111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff8003ffc03ffc0,0x194d3584ce100f00f000])),(BitVec.ofNat 152 (word80 [0x2a05606b0250682905,0x99413484cc1333333333]))),((BitVec.ofNat 152 (word80 [0xffffffc00003ffff,0xcd31ac6e2090f00f000f])),(BitVec.ofNat 152 (word80 [0x4c09804c0360b03209,0x101ac4e201222222222]))),((BitVec.ofNat 152 (word80 [0xfffffffffffc0000,0x2535a45ba5f000000f0])),(BitVec.ofNat 152 (word80 [0x702e01700b80c0bc0e,0x2511a453a1666666666]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c7720000fff00])),(BitVec.ofNat 152 (word80 [0xb005802c0102c010,0x41c4220132ccccccccc]))),(0x0,0x0),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006003002030020,0xa44120014888888888]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(4,0,185,0,7)]
def g189A : List (List Nat) := [[]]
def g189D7 (j : Nat) := if j=0 then 0x7f else 0
def g189L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g189D7)
  | _ => emptyPacking
def g189I (_ _ : Nat) : Option (Nat × Nat) := none
def g189 : Forest := ⟨189,7,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : CutRow g189 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : CutRow g189 7 0 1 := g189P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : mixedTables g189 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g189 0 0
  · exact mixedEmpty g189 1 0
  · exact mixedEmpty g189 2 0
  · exact mixedEmpty g189 3 0
  · exact mixedEmpty g189 4 0
  · exact mixedEmpty g189 5 0
  · exact mixedEmpty g189 6 0
  · exact g189B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 8 := mixedLower (g:=g189) (i:=0) (hints:=1283) (before_sound K187 V187) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K187 8 [(189,[]),(231,[96,49,32,33,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V187 low189 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xd62932b74a48000f801f])),(BitVec.ofNat 152 (word80 [0x481610542128429028,0x540832b642414a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe0003fff801,0x601555aee91001f003e0])),(BitVec.ofNat 152 (word80 [0x90a402980db01320cd,0x601550aa4910c6318c63]))),((BitVec.ofNat 152 (word80 [0xfffffffc000001,0x39c4d2534e803e007c00])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc171,0x3184d2034e00c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff,0x428bca0b99efc000001f])),(BitVec.ofNat 152 (word80 [0x1c027004e009c0181,0x281c00999aa94a5294a]))),((BitVec.ofNat 152 (word80 [0xffff00000000000001,0x22fa317cb68000007fe0])),(BitVec.ofNat 152 (word80 [0xb8017002e00200,0x26a2154b08739ce739c]))),(0x0,0x0),(0x9d26ecc07137ffff8000,(BitVec.ofNat 152 (word80 [0x200c0018003000400,0x88220c40200421084210]))),(0x0,0x0)]
def g190C : List ColumnInfo := [(4,0,186,0,7)]
def g190A : List (List Nat) := [[],[50],[65],[65,50]]
def g190D7 (j : Nat) := if j=0 then 0x7f else 0
def g190L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g190D7)
  | _ => emptyPacking
def g190I (_ _ : Nat) : Option (Nat × Nat) := none
def g190 : Forest := ⟨190,7,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_0 : CutRow g190 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B7 : CutRow g190 7 0 1 := g190P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : mixedTables g190 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g190 0 0
  · exact mixedEmpty g190 1 0
  · exact mixedEmpty g190 2 0
  · exact mixedEmpty g190 3 0
  · exact mixedEmpty g190 4 0
  · exact mixedEmpty g190 5 0
  · exact mixedEmpty g190 6 0
  · exact g190B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 8 := mixedLower (g:=g190) (i:=0) (hints:=270619968) (before_sound K189 V189) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K189 8 [(190,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V189 low190 (by decide +kernel)
def g207Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7ffc01ffffffffff,0xffc035677a50000f000f])),(BitVec.ofNat 152 (word80 [0xd01482c82a4252148,0x29c035454a5555555555]))),((BitVec.ofNat 152 (word80 [0x7ffffffff0007ffc,0xf354385e8000f000f0])),(BitVec.ofNat 152 (word80 [0x5615914814c1b60990,0xccf304385e8333333333]))),((BitVec.ofNat 152 (word80 [0xff800001ffffff8000,0x26278cbf400f000f00])),(BitVec.ofNat 152 (word80 [0x9819e2702701380de1,0x7026078c3f4333333333]))),((BitVec.ofNat 152 (word80 [0x1ffffffffff,0xfe580f6a35b0f000f00f])),(BitVec.ofNat 152 (word80 [0xe01e03803801c00e01,0x80180a2a358222222222]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffe0000000000,0x24f859c3ef0000fff0])),(BitVec.ofNat 152 (word80 [0x200000c006003002,0xf041802444444444]))),(0x19b82850c0fffff0000,(BitVec.ofNat 152 (word80 [0x4000010008004000,0x888888888]))),(0x0,0x0)]
def g207C : List ColumnInfo := [(2,0,205,0,7)]
def g207A : List (List Nat) := [[],[33]]
def g207D7 (j : Nat) := if j=0 then 0x7f else 0
def g207L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g207D7)
  | _ => emptyPacking
def g207I (_ _ : Nat) : Option (Nat × Nat) := none
def g207 : Forest := ⟨207,7,fun i => g207Y[i]?.getD (0,0),g207C,g207A,g207L,g207I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207P7_0 : CutRow g207 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g207B7 : CutRow g207 7 0 1 := g207P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207T : mixedTables g207 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g207 0 0
  · exact mixedEmpty g207 1 0
  · exact mixedEmpty g207 2 0
  · exact mixedEmpty g207 3 0
  · exact mixedEmpty g207 4 0
  · exact mixedEmpty g207 5 0
  · exact mixedEmpty g207 6 0
  · exact g207B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g207G : graphValid g207 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low207 : Lower true (varsX 207) (graphGoal 207) 8 := mixedLower (g:=g207) (i:=0) (hints:=16778851) (before_sound K190 V190) g207G g207T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K207 := extendKnown K190 8 [(207,[]),(222,[64,33,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V207 : Known true K207 := extend_ok (m:=207) V190 low207 (by decide +kernel)
def g215Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffe001ffffff01fc,0x5f8b8545600001f0001f])),(BitVec.ofNat 152 (word80 [0x588544d44944522c50,0x5f83814465294a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffe001ffffe01,0x98b361b240003e007fe0])),(BitVec.ofNat 152 (word80 [0x900980980d80644899,0x989300b0410842108421]))),((BitVec.ofNat 152 (word80 [0x3ffffffffe0000002,0x54dc3874c007c00f8000])),(BitVec.ofNat 152 (word80 [0xe02e00e00e017870e0,0x549c3870c318c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffe,0xa08ef66320f8000003ff])),(BitVec.ofNat 152 (word80 [0x13009009009800002,0x200c76030a5294a5294a]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc0000000000000002,0x4970938fdf00000ffc00])),(BitVec.ofNat 152 (word80 [0x1c00e00e00e008102,0x160830f0c6318c6318c]))),((BitVec.ofNat 152 (word80 [1,0x37050a181ffffff00000])),(BitVec.ofNat 152 (word80 [0x20010010010000000,0x108421084210]))),(0x0,0x0)]
def g215C : List ColumnInfo := [(2,0,213,0,8),(1,0,214,0,7),(4,0,211,0,7),(16,0,199,0,6),(64,0,151,0,6),(17,0,198,0,5),(18,0,197,0,5),(20,0,195,0,5),(65,0,150,0,5),(68,0,147,0,5),(128,0,87,0,5),(19,0,196,0,4),(21,0,194,0,4),(69,0,146,0,4),(129,0,86,0,4),(132,0,83,0,4)]
def g215A : List (List Nat) := [[],[32,100]]
def g215D4 := limbs80 #[#[0xa9a878e1826017119543,0xc3326e8c08e0]]
def g215D5 := limbs80 #[#[0x5c46550ef46047054d43,0x4c33cd917118153cf180,0xe0974d4330e596454d50,0x54140cbb7059154cc27a,0xc9d43dd953d03c650d53,0x54d43d43a3e095458f40,0xd4336dc16350f50d5b70,0x5437259350cbb7059143,0x54d43c3f65dd15350f3a,0xcd876dc15350f66dd070,0x5c46550f5554d7119543,0x50f1e54d7019543c7565,0x2037159543c75535c465,0x58a43cf380dc56550f3c,0xcdb8754d6014fb2e0153,0x54d6214fb4e015358453,0x14fa6dc16454c53ecb80,0x5917118153cdb80dd953,0x59353e5b805db5394f3c,0xcce53dc964d4f3354f72,0x46403a342e2822140e00,0x827c76706a645e58524c,0xbeb8b2aca6a09a948e88,0x18c100201cac4]]
def g215H5 (j : Nat) := if j=0 then 0x1bc else 0
set_option maxRecDepth 16000 in
def g215D6 := limbs80 #[#[0x27db82ca987595354130,0xbb2e7a8661d654f50cc,0x277b92caa067965d433,0x439dee4b26a1a755163d,0x50e7ab88caa1cf970195,0xa439eee2b2a873edc165,0x114f6ca9ac029ecd5358,0x4c53d9aa6b10a7b554d6,0x6054e6fbb2a629e9d645,0x59353cbaeda9ca77c5c4,0x540cc3dcaa281984ef72,0x454f30bf2e9a8661be59,0x4d505035eb22a9986dd6,0x5350d509feeca9e81de5,0x58d43d43aea9a87a875d,0xf7454d43d7ac8a1ea1b7,0x6dc15350fec382a6a1db,0x9e5454d43f3aa8a9a87f,0x775d65350fcf2a4a6a1f,0xdf57119543b7ae9a9a87,0x1fa549504837db20c0a9,0x86f96454130fb2a6a826,0x61b7591534c3edb82a69,0x986bd6455130bdee4aa2,0x2613fdd9544c27ebb2a8,0xa984ff7559130df6e0b2,0x2a613fdd1654c37db82c,0x81987d953503309fae93,0xa8661f654f50cc2fd3aa,0x6a1986f965d4330fb2e7,0xaa661f6dc153cc37cbb,0xb2a9985ef7255330bf6e],#[0xeab26613fdd954cc27eb,0xba2cb986fb70597309fe,0x286a82813f5d265cc27f,0xcaa2a0a077b5354140f7,0x3aa6a1a81eedc143503d,0xdebaa86a06bd6550d40f,0xbf6e0a9a816fdd543502,0x3ddb82a8a04ff7654d40,0xb7ee6aa281ebdc95450,0x377b92caa06fb705954,0x409fae732a813fdcd655,0xd035eb2a87a079d5350f,0xf40b7eeaa1e816f5d543,0x3d036eb1aa7a05fb7054,0x8f40dbea6b1e813f5d95,0x63d027fbaac7a06bd545,0x58f40dbaeab1e81b71d5,0x954d036fbaac7a06de75,0x359740b7ee6aa681ebdc,0x4f505427eb9ccba04ff7,0x74d4150bf2e7a82a1de5,0xdd9435436fb1a86a85f9,0xd74d8d50ef6e0a9aa13f,0xedc143d427eb9ec8a84f,0xff7650f509faeca1ea17,0xbedc163d43bdb82a7a84,0x6ef72593509fee8b1ea1,0x7b754f6050e7fb9ac9a8,0x1cfd75d8143d7aa9b028,0x879f1955350efdb82a6a,0xa1cfd7654d43cfecaa9a,0xa87e71d15350eefb92a6],#[0x6a1f5c6554d43f3ee8a9,0x9a87b71d95350fafb2aa,0xcaa1e7f65d4d43bbced2,0x32a879f5946550efcb80,0xacaa1dfb70595439fcec,0xb2a879fd956550efbb8,0x82caa1efb7059543df0e,0xe6b2a87bddc56550e7fb,0xb2ccaa1cff7359543dbe,0xae1b2a873f5ce6550f3f,0x7aa2c521eed5458a439f,0xbeeca9c87f6dc15390f7,0xefb9aa921def7255243d,0xcfccaaa4879f5955490e,0xf3eb2ea921ddd73d5243,0x3df4a8b00a7be5516014,0x4f7b2a2c229ef5545845,0x53ddca8b10a7bb551621,0x14f6eb22a629fdb7054c,0x153d7ca8b20a7b7dd953,0x54efd3b0c0a9ef96418,0x8153df6c5b02a7be58b6,0x6054f7db1ec0a9fdb53d,0xd8153df0c9b02a7f6dcf,0x36054f7d326c0a9ef964,0x4d8153df2a1b02a7bed9,0x4b6054f7ca96c0a9cfd7,0x72d8153df2e5b02a7bed,0x1536054f7db9ec0a9efb,0xa54d8153df2a9b02a7be,0xe1d36054f7daa6c0a9ef,0xfa74d8153df2e9b02a7b],#[0xbb54b6254f7dba6c0a9e,0xddd74d4d539fae9b12a7,0x7775ce5454eefb9aa8a9,0x9ebf6495153e7ea92a2a,0xa7af9936454f5eb20c8a,0x29cfd72d91539fae1b22,0xca7775d35394faf2a6a7,0x929f5e74d4e53ebae9a9,0x6a7be50160d4eeeb9ca,0xc5a9eed4258b539fae8b,0xb26a7af50164d4e7eba2,0x2c9a9cff7059353d7e80,0x4b26a7afd0964d4f5ea1,0x92c9a9eef7259353dd8e,0xd615c218280360027fb,0xe36c6a8c816828046078,0x24ba95327e4ac8b9031d,0xf21d73866d8d81aa32c6,0xa5448e8e90fa1240a7e0,0x8596af958a9d5209f130,0x4bf17b2f05d4b916f2d,0xcb193320634c51873086,0x1ab350694d119f338664,0x33806f4dd1b73686c4d7,0xb0754e91cf398724e31c,0x7b4f51e73c8784ef1db3,0x5011ff3f87e4fb1f33e0,0xd2174288450720b41081,0x2f4588a5132234408750,0x4889051f23b4708d5192,0x89652b2534a093525247,0xc53726b4d09953125f4b],#[0x432835009f53d2774e89,0x29b530a554928f518a25,0x3560ab5552a7548a854f,0x90b15612bf578ae55b2b,0xb756d2d75a8b45672cb5,0x5792ef5d8ba5732e35c0,0x5307608c057f2fb5f0bd,0x1f638c658b313620c358,0x668cc59732b650c95913,0x8d25a3343680cf59d337,0x85af35b6b0d55a934f69,0xbb3736e0db5b53676c8d,0x38b710e15c137f6f8de5,0xbc03e008ae0303e45c7,0x13c02e0085e010ee010e,0x1c011e382e0282c3c02,0x5e01050c105e0105e01,0x43840c16205e0105e01,0x4141040002010b802178,0x4050828410604210083a,0x50644110080041a2c218,0x90210884281094426544,0x4608a04]]
def g215H6 := limbs80 #[#[0x548000,0xef0012100,0x28700109632000000000,0x1600049eae000004c,0xe00000e4800000016280,0x8,0x119800000000e8000000,0x1a0800000004580,0x6ea80000000000000000,0x14400000536e692,0x0,0x6200000000001ad00,0x0,0xec000a50000000,0x3080060c6b80,0x2001999a000001ac4180,0x14fa00aa62,0x17a80]]
set_option maxRecDepth 16000 in
def g215D7 := limbs80 #[#[0xb58a43b798f40b758f40,0x58453be58053e7d0e43b,0x9053af59053bb58853bd,0x120d7d4e53bed8153af9,0x30bf99520bf59520fe54,0xbf59130f754d30fe541,0xfe50330bf99530bf5953,0xf59330f754f30fed4330,0x54140bf99730bf59730b,0x9540ef55140ef50d40fe,0xf40ef50f40bf99540bf5,0x40bf59740ef55340bf58,0xbfd8950fed4150bf997,0xbfd8d50dfd4d50df54d5,0xf54f50bf58b50bfd9150,0x59350bf58f50dfd4f50d,0x8143bf99443bf59443bf,0x543f794d43f754d43bfd,0x43bf99543bf59543bf19,0x3bf59243f754e43bfd95,0xf754c53bf99643bf5964,0xe18153bf99453bf59053,0xd8953bfd8153fed8153f,0x4e53bfd9153f7d4d53bf,0x353bf59653bf59253f7d,0x30bf59353bf58b53bf58,0xff54d40ff55330ff551,0xff50f50ff50d50ff54f4,0xf19543ffd4d43ff54d43,0xd9543ff99543ff59543f,0x5153ffd5243ff55243ff,0x153ff19153ff95153ff5],#[0x30ffd5130ff95253ffd9,0xffd4f40ffd4d40ffd53,0xff54d50ff58950ff5495,0xf59150ff55150ff58d50,0x55350ff58f50ff54f50f,0x8143ff58143ff59350ff,0x153ff95053ff55053ffd,0x53ff58953ffd8153ff58,0x3ffd5153ffd4d53ffd89,0xffd5253ff99153ff5915,0x18000ff99353ff59353,0xea0cc0ae090072054036,0x619e18015c13e1201080,0x25824022820a1ec1ce1b,0x2430c2f42d62b2294276,0x63d23b43963783603423,0x49e48046244a4324143f,0x6454652850a4ec4d44bc,0x46306186005d05ac5825,0x7206fc6de6ba69c67865,0xf27ce7b0798780762744,0xa8b288e87085282e8107,0x96c94e9309128fa8e88c,0x2ca0e9f09d89cc9ae984,0xaaa4a9ea8ca74a62a4aa,0xaceac8ac2abcab6ab0aa,0xf8af2aecae6ae0adaad4,0x2b1cb16b10b0ab04afea,0xb46b40b3ab34b2eb28b2,0x7c051211301c4870243,0x5184287c051071301449,0x10a1f0144287c0510a1c],#[0xa1f0144467c031c4c05,0xa3043ce37030538dc0c1,0xc0c10ac0c0cec0c0cdc0,0xc313030a10e130304288,0x710ec211c40709c3c089,0x8701ca144c211c42b020,0xb0343c083034cec0d104,0x91430f034a10e0f03442,0x24484ec0910ac09144c0,0xc1c0f10387024a143870,0xec0c0cec0c0ce3303448,0x3cc10337038410ec0c10,0x303042b01432b0303370,0x5107130144283c0d10a1,0x44313018a2303041c4c0,0x840f038710a1f0145c8a,0x3c053f0383081c033c10,0x1f01452841f014508110,0x41f014a1441f0144284,0x28510a1f0145287c051,0xc918f010e23030410717,0x4f0f0384130303130303,0x1c41c5c0a10204a0f01,0x13038c10a107c0514417,0x850c10842b0144c0f304,0x38440c32021120431044,0x1031040ca84410384e10,0xa4914040c60ca103291,0x20c42840c32812924501,0xd28440c488a10310489,0x40c22840c30c80a1103]]
set_option maxRecDepth 16000 in
def g215H7 := limbs80 #[#[0x10402001200000060,0x33115000000006139000,0x301210264d0020100904,0x64800000000013060004,0x1a780004971982000b,0xa900000000000000000,0xaa0000000001000,0x365a034001f8c000000,0x98000000000604000000,0xeff2ac00075,0x24744dd00000000000,0x5800006508,0x23400e8000000,0x2326000000,0xe6564999ac00,0x5667d70539be48800000,0x2d0000000f328d0185d0,0x146000667799c444e847,0x45580030cc000e38dd03,0x40000000000000000000,0x334000000021fc17,0xa8000a37598849c00000,0x620000000000e0b00068,0x59e40010,0x0,0xb31400067e00071c8000,0x60000006ab7812aa646a,0x38f4000000000388,0xc25000000132041500,0x8e072080000,0x0,0x484b12c0000005f2c],#[0x1147d18000,0x53a639507a2000000000,0xbc818000000000000185,0x25c720800126d00010,0x59034619fc2f00f9140,0x5f26d390b40003,0xbcffd1a0000007a6683e,0x8ce8003c1000065a,0x91e800000,0x8c1ca000000000099100,0x1400000000000000000c,0xeb300072f3a61c2c6,0x1a3000011a4,0x29b0000a23c290adc000,0x12be000000,0x1429c3e000000000000,0x880000d3b03621ed4a80,0x38980000000000000a,0x0,0xdb20004930000000,0x4230000000001e3573e,0x5b68001cd64487d6c00,0x0,0x448000000acd29780000,0x7,0xf3a80000013536cb69d0,0x2320000000,0xe7488000000000000000,0xfc000f6702b135c00037,0x1921028928ce5a,0x0,0x1cb26bd0000],#[0x2b2000501a5a6,0xdc4,0xc9c000000000000,0x7769e000328800000000,0x1c0000000ec4f39f6195,0x71dc000c07b,0x1026000000722c,0x15870db0000003872000,0x0,0x0,0xa4e80,0x0,0x215c0000000000,0x3076,0xb81811b049081ed94000,0x19b19737bf257000210,0x8000000000000000000,0x1c,0x38700000000,0xe2f00000000002138000,0x2d8000000000,0x9a6f000040a000000000,0xc2e00020c49a542,0xdc2000000087f00000,0x294e00056780000000,0x0,0x9124897c6031e3c23c64,0xf4dd08800000026af4d,0x0,0xa305f000000344c07600,0x1,0x6b4c45116f9b80008980],#[0x16f800108508f0000001,0x10f6000f47000141d061,0x593c9b8000270800,0x1c40000000293400,0xc6eaa6ac40000cc00000,0xa7ed6000000008840004,0xd0a00075ee540ec72282,0x9a0000,0x12d400000017aa000000,0x3ba18000120000000000,0x67f892106a5c106000b4,0x3abc0,0xcb0000000000354a0000,0x754e1280000000000003,0x816eec21cba12000124d,0x1298000001401000714,0x800000055400020e000,0xba000618d59400044060,0x31280000004ada71ee,0x1c480000000]]
def g215D8 := limbs80 #[#[0xf40fea07fcc3fa61fd20,0x87fd43fe21ffd43faa1f,0x3fea7fe53fea9ff14ffc,0xb2d629239964882a0a80,0x606d8303b0d1e5b0472,0x94304885834340607111,0x9028817b60c142e6c182,0x8147110f028a9441821c,0xa43c0a20490608410547,0x791d060]]
def g215H8 := limbs80 #[#[0x60400018440040082000,0x210480010,0x28db68200c000,0xc0004cc0000000025880,0x7280013b9f5c0039168a,0x0,0x64003c200000000000,0x0,0xd7eb3c000000,0x14386680000000,0x354c00000000,0x206c000000,0x3da03a5b47c4f6430f00,0x958979e6ecb000237800,0xdd4000000000003,0xd700000000024040000,0x3cab1d287c00000000,0x341b358000,0x25a40010280,0x47800000000000000000,0x30000000000000000000,0x21,0x4b800000000000000000,0x64000000000000000001,0x2ec800040249c0000033,0x45800000000372c00000,0x2,0x422c30a000062c0000,0x116c0024d400,0x0,0x3d468150bc0,0x6000103fcec00000000],#[0x3c12ce7,0x80000000000039912c40,0x15ccda9d98002d3,0xa615c003cb7920000000,0x14300000038,0x58c00000000000000000,0x0,0x18d00,0x0,0xb0000000000000000000,0x9140000000000001dbd1,0x25e310,0x20f8000,0x16745d80,0x19dc00,0x35c59b8000000,0x0,0x0,0x2cc4000000000000000,0x40000015c80000000000,0x24fdc5,0x2580000000001d0c,0x101c0000000000000,0x12800000000000000000,0x249b883db648d,0x21c00000000000000000,0xfdc00000000015400,0x27b5d4800286a0f4,0x0,0x0,0x2d68002050,0x0],#[0x0,0x3f934003d84000000000,0x3de4002844000000002d,0x490001ce0000000c733d,0x94000000000000000fad,0x38,0x8374c0002194b3859c00,0x1000000351800204a167,0x2700019,0x39400000200800000000,0x34774de,0xd42c000000000002f400,0x3024000000002105d2,0x3974002888002f74000,0x0,0x52400056000,0x30840014cbce8000000,0x251c0,0x1a78000000002d0,0x19afbb0000000000,0x3d500,0x345c00000]]
def g215D9 (j : Nat) := if j=0 then 0x2100ff else 0
def g215H9 := limbs80 #[#[0x15600,0xac0d6a3310,0x1c82b0020800005ed48,0xa00000bbad6e70e00000,0x1a800000000000002,0x1ab69d9f8c000,0xbb0000000000000,0x41005c400a6ce00]]
def g215L : Nat → Packing
  | 4 => (2,5,4,0,0,3,0,g215D4)
  | 5 => (32,4,4,0,0,8,0,g215D5)
  | 6 => (226,3,4,0,0,11,0,g215D6)
  | 7 => (122,2,4,0,0,12,0,g215D7)
  | 8 => (14,1,4,0,0,9,0,g215D8)
  | 9 => (1,0,4,0,0,0,0,g215D9)
  | _ => emptyPacking
def g215I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 5 1 0 g215H5
  | 6 => lookupWord 9 137 3 10 5 1 g215H6
  | 7 => lookupWord 68 691 4 13 8 1 g215H7
  | 8 => lookupWord 38 563 3 12 7 1 g215H8
  | 9 => lookupWord 6 67 3 9 4 1 g215H9
  | _ => fun _ => none
def g215 : Forest := ⟨215,9,fun i => g215Y[i]?.getD (0,0),g215C,g215A,g215L,g215I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P4_0 : CutRow g215 4 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P4_1 : CutRow g215 4 1 1 := by
  apply polarBlock (data:=fun _ => 0x84040241084420) rfl
  decide +kernel
theorem g215B4 : CutRow g215 4 0 2 := (@joinRow g215 4 0 1 1 g215P4_0 g215P4_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_0 : CutRow g215 5 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P5_3 : CutRow g215 5 3 29 := by
  apply polarBlock (data:=fun _ => (word80 [0x800,0x4021180444208000402,0x11804442008020025124,0x90100285040301085420,0x4400a1502c42200044,0xa1502c424000440403,0x1044210008404030108,0x4410004400a1502c4220,0x440403010442100a04,0x14020520515102000402,0x9201241080020a058a8,0x4243004400a1502c4230,0x82800a1502a81300088,0x209448a8451004400a1,0x502c4220004404024104,0x4230004010030982c010,0x410209448612100200,0x40301a2115200441403,0x45044320004410a1502c,0x43200021040241021130,0x440402410442510064,0x14024104435002000011,0xc261142080004020580,0x4452006410a1502c4320])) rfl
  decide +kernel
theorem g215B5 : CutRow g215 5 0 32 := (@joinRow g215 5 0 3 29 g215P5_0 g215P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_0 : CutRow g215 6 0 21 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_21 : CutRow g215 6 21 21 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_42 : CutRow g215 6 42 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x641403,0x1044351006414024104,0x4351004400a1502c4241,0x2850403010854420041,0x2094486122100410209,0x44861220028504030108,0x54520041040241041221,0x410209448612200208,0xa042290530208000a,0x4229042028504030108,0x54520208020a04229043,0x280282402281400064,0x1402410443510048020b,0x4868230004104024104,0x12200041020944861220,0x2850402050854410041,0x2094486123108250402,0x41025130004400a1502c,0x42300825040241025130,0x410209448612310825,0x4024102513008000402,0x11804463004414030104,0x43300044040301044220,0x4400a1502c42300044,0xa1502c4230004400a1,0x502c4220004400a1502c,0x4220004400a1502c4230,0x1001028145a090430041,0x2094486123108250402,0x41025130004400a1502c,0x42300021040241021130,0x48020b048682400041,0x2094486123100210402,0x41021130006410a1502c,0x43510800040211804463,0x6410a1502c43310044,0x40301044220006410a1,0x502c4330004400a1502c,0x42200041020944861210])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_90 : CutRow g215 6 90 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x48020b,0x868240028504030108,0x54420048020300848241,0x4400a1502c42310048,0x2094486825100480209,0x44868251004404024104,0x42410044040241044241,0xa14402410215500825,0x4024102513002850403,0x1085442004400a1502c,0x42411000008045208164,0x6410a1502c43410064,0x10a1502c4361006410a1,0x502c4331028504030108,0x54420041020944861221,0x208020b04a290530044,0xa1502c4230004400a1,0x502c42300048020b0486,0x82510285040301085442,0x4410a1502c43300044,0xa1502c424100410209,0x44861231004400a1502c,0x42300064140301044341,0x280082402281400041,0x20944861220004400a1,0x502c4230004400a1502c,0x4230004400a1502c4241,0x410209448612310285,0x4030108545200210402,0x41021120006410a1102c,0x4331006410a1102c4331,0x6410a1102c43310064,0x10a1102c433100641403,0x1044341006410a1502c,0x4361006410a1102c4331,0x6410a1502c43410064,0x10a1502c433102000402,0x5201162082104024102,0x11300821040241021130])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_138 : CutRow g215 6 138 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x2000402,0x5201152028504030108,0x5442004400a1502c4230,0xa040402052051520200,0x402052011520a040402,0x5205152020004020520,0x1152004400a1502c4220,0x4400a1502c42300044,0xa1502c422002804402,0x5201552004400a1502c,0x4230004400a1502c4230,0x2850403010854310041,0x20944861231004400a1,0x502c4231004102094486,0x1251004400a1502c4220,0x410209448612210041,0x2094486122102002209,0xca21252020022090ca2,0x12520041020944861220,0x410209448612200044,0x834024424100440403,0x41044231004102094486,0x12310825040241025130,0x250403010251300800,0x4021180446300440403,0x1044231004404030104,0x42200044008150244231,0xc10209448612210048,0x20b04868251004400a1,0x502c42410200020b04a2,0x90630285040301085442,0x8250402410251600825,0x40241025120006410a1,0x502c43410a0414020520,0x51620285040301085431,0x208020b04a290631000,0x804920826410000080,0x45208164082504024102,0x5130082800a1502a8140])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P6_186 : CutRow g215 6 186 40 := by
  apply polarBlock (data:=fun _ => (word80 [0x410209448612310041,0x2094486122100410209,0x44861221004102094486,0x12310041020944861231,0x410209448612310041,0x2094486123100410209,0x44861231004102094486,0x12310041020944861221,0x410209448612310041,0x2094486122000480203,0x40848241004010024922,0x90100040100249229010,0x410209448612510040,0x100249229010004400a1,0x502c4241002104024102,0x11300025040241025130,0x2840208448a44320825,0x4024102513010010082,0x4180c063028504030108,0x54320285040301085432,0x4102094486125100a1,0x440241021530004400a1,0x502c4231020800020422,0x90420200040205201152,0x2850403010854310200,0x4020520115202000402,0x5201152020004020520,0x11520200040205201152,0x2000402052011520044,0xa1502c4230004400a1,0x502c4230004400a1502c,0x42300200040205201152])) rfl
  decide +kernel
theorem g215B6 : CutRow g215 6 0 226 := (@joinRow g215 6 0 90 136 (@joinRow g215 6 0 21 69 g215P6_0 (@joinRow g215 6 21 21 48 g215P6_21 g215P6_42)) (@joinRow g215 6 90 48 88 g215P6_90 (@joinRow g215 6 138 48 40 g215P6_138 g215P6_186)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_0 : CutRow g215 7 0 11 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_11 : CutRow g215 7 11 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_59 : CutRow g215 7 59 15 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_74 : CutRow g215 7 74 19 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P7_93 : CutRow g215 7 93 29 := by
  apply polarBlock (data:=fun _ => (word80 [0x41,0x2094486123100410209,0x44861231004400a1502c,0x42410285040301085442,0x2850403010854420044,0xa1502c4241004400a1,0x502c4241004400a1502c,0x4241004400a1502c4241,0x4400a1502c42410044,0xa1502c424100410209,0x44861231004102094486,0x12310048020b04868251,0x480082402482510041,0x2094486123100410209,0x44861231004400a1502c,0x4241004400a1502c4241,0x410209448612310041,0x20944861231004400a1,0x502c4241004400a1502c,0x42410041020944861231,0x410209448612310041,0x2094486123100410209,0x44861231004400a1502c,0x4241004400a1502c4241])) rfl
  decide +kernel
theorem g215B7 : CutRow g215 7 0 122 := (@joinRow g215 7 0 59 63 (@joinRow g215 7 0 11 48 g215P7_0 g215P7_11) (@joinRow g215 7 59 15 48 g215P7_59 (@joinRow g215 7 74 19 29 g215P7_74 g215P7_93)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P8_0 : CutRow g215 8 0 14 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B8 : CutRow g215 8 0 14 := g215P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215P9_0 : CutRow g215 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g215B9 : CutRow g215 9 0 1 := g215P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215T : mixedTables g215 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g215 0 0
  · exact mixedEmpty g215 1 0
  · exact mixedEmpty g215 2 0
  · exact mixedEmpty g215 3 0
  · exact g215B4
  · exact g215B5
  · exact g215B6
  · exact g215B7
  · exact g215B8
  · exact g215B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g215G : graphValid g215 (boundsBefore K207) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low215 : Lower true (varsX 215) (graphGoal 215) 10 := mixedLower (g:=g215) (i:=0) (hints:=16778820) (before_sound K207 V207) g215G g215T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K215 := extendKnown K207 10 [(215,[]),(221,[32,49,64,96])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V215 : Known true K215 := extend_ok (m:=215) V207 low215 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x44510a204404101144,0xcc00e249249249249249]))),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(BitVec.ofNat 152 (word80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a39,0x31110186186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3861514514514514514]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044104,0x42ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(3,0,216,0,5),(9,0,210,0,5),(10,0,209,0,5),(19,0,200,0,4),(25,0,194,0,4),(73,0,146,0,4),(129,0,90,0,4),(130,0,89,0,4),(136,0,83,0,4)]
def g219A : List (List Nat) := [[],[97,67],[16,99],[16,48,64,96],[48,100],[48,65,96,16],[64,49],[64,97,48,49],[96,16,49,67],[96,65]]
def g219D5 := limbs80 #[#[0x54950443cc5515150110,0x54237e0d7654910e6962,0x841d51c08df835c762]]
def g219D6 := limbs80 #[#[0x3b4a92a0904df7359510,0xdf2caa0221fc5454044,0x437cb12a088779525411,0x10bf6e8a8221be591504,0x4427ebb2a4885fb70549,0x5109fee4b2a213fdd562,0x15427fb8aca906df7359,0x85509fae5b0aa177dcd6,0x418027eb8ec4a84fd74d,0xe765e0dd9a5713d08b88,0x8516283033f26f2dac28,0x208504282001088c2280,0x4000182000101840410,0x182000]]
def g219H6 := limbs80 #[#[0x34400108000000,0x0,0x318000000a9000,0xb40]]
def g219D7 := limbs80 #[#[0xf58910fe54110fe50110,0x59520fe54120bf59510b,0x8950df54950bfd8550bf,0x550ff54520ff54910bfd,0x2a0d82400ff58950ff58,0x62a24ca34fc6c2e92c78,0xa496219a24a92296485,0x42985aa50869820448a4,0x29650a20449821c60259,0x9a11c90c182518588718,0x1c60e19a6263083]]
def g219H7 := limbs80 #[#[0x2000000000d234829410,0x74300050870ab0000000,0x670fa01110427107000,0xce62242000c1178570d4,0xc0ee4b000b0500068820,0x3104846e09000984363,0x60b000000000222d497]]
def g219D8 := limbs80 #[#[0x489a3407f543fa41fd10,0xa600ab48d58ad424aab]]
def g219H8 := limbs80 #[#[0x489c36613c509611a410,0x1c544738880000172400,0xf362c001936048200348,0x394800d28002d098c8,0xba2596206e0210515a30,0x3d9700000000000a0b28,0x2c]]
def g219D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g219H9 := limbs80 #[#[0x20030a00000b04000012,0xf73d2030004518,0x50000000000000000000,0x424000011a00044000c,0x55000000000d0000,0x48b8]]
def g219L : Nat → Packing
  | 5 => (4,4,4,0,0,5,0,g219D5)
  | 6 => (18,3,4,0,0,8,0,g219D6)
  | 7 => (13,2,4,0,0,9,0,g219D7)
  | 8 => (3,1,4,0,0,6,0,g219D8)
  | 9 => (1,0,4,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 31 0 9 2 3 g219H6
  | 7 => lookupWord 7 47 4 12 5 3 g219H7
  | 8 => lookupWord 7 41 5 11 4 3 g219H8
  | 9 => lookupWord 3 41 2 10 2 4 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : CutRow g219 5 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : CutRow g219 5 0 4 := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : CutRow g219 6 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_2 : CutRow g219 6 2 16 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : CutRow g219 6 0 18 := (@joinRow g219 6 0 2 16 g219P6_0 g219P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : CutRow g219 7 0 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_9 : CutRow g219 7 9 4 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : CutRow g219 7 0 13 := (@joinRow g219 7 0 9 4 g219P7_0 g219P7_9)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : CutRow g219 8 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : CutRow g219 8 0 3 := g219P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : CutRow g219 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : CutRow g219 9 0 1 := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : mixedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g219 0 0
  · exact mixedEmpty g219 1 0
  · exact mixedEmpty g219 2 0
  · exact mixedEmpty g219 3 0
  · exact mixedEmpty g219 4 0
  · exact g219B5
  · exact g219B6
  · exact g219B7
  · exact g219B8
  · exact g219B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K215) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := mixedLower (g:=g219) (i:=0) (hints:=16777283) (before_sound K215 V215) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K215 10 [(219,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V215 low219 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801ffe0fffffffea8,0xe90535840007c00003ff])),(BitVec.ofNat 152 (word80 [0x511441422080410280,0xe8050185294a5294a529]))),((BitVec.ofNat 152 (word80 [0xfffe0000ffc1ff8195,0x6311d29800f8000f8000])),(BitVec.ofNat 152 (word80 [0x601815840504120995,0x63115010e739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff0001fffcd7,0x85e044441f0001f07c1f])),(BitVec.ofNat 152 (word80 [0x802006000608040054,0x1404440421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2edc7a2000003e007fe0])),(BitVec.ofNat 152 (word80 [0x44118008801181021,0x6983a0294a5294a5294]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x18060083010602000,0x902481a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x6018010c02180402a,0x8a020a108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(32,0,203,0,7),(64,0,171,0,7),(128,0,107,0,7),(0,2,41,192,6),(2,0,233,0,6)]
def g235A : List (List Nat) := [[],[80,118]]
def g235D7 := limbs80 #[#[0xa15662e85d03ec43f521,0x498b]]
def g235D8 (j : Nat) := if j=0 then 0x2c21a1bf else 0
def g235H8 (j : Nat) := if j=0 then 0x1b2 else 0
def g235L : Nat → Packing
  | 7 => (2,1,3,0,0,5,0,g235D7)
  | 8 => (1,0,3,0,0,0,0,g235D8)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 2 0 5 1 0 g235H8
  | _ => fun _ => none
def g235 : Forest := ⟨235,8,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : CutRow g235 7 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : CutRow g235 7 0 2 := g235P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : CutRow g235 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : CutRow g235 8 0 1 := g235P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : mixedTables g235 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g235 0 0
  · exact mixedEmpty g235 1 0
  · exact mixedEmpty g235 2 0
  · exact mixedEmpty g235 3 0
  · exact mixedEmpty g235 4 0
  · exact mixedEmpty g235 5 0
  · exact mixedEmpty g235 6 0
  · exact g235B7
  · exact g235B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 9 := mixedLower (g:=g235) (i:=0) (hints:=16777315) (before_sound K219 V219) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K219 9 [(235,[]),(249,[80,65,33,96,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V219 low235 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ffe0ffc1ffffe,0x915365415000f00000ff])),(BitVec.ofNat 152 (word80 [0x4288a2142208402100,0x81532101555555555555]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000fffe0ff81,0xa8697328200f000f0f00])),(BitVec.ofNat 152 (word80 [0xb00c0584050020208,0x88297308033333333333]))),((BitVec.ofNat 152 (word80 [0xfffffffff00000fffc,0xc6b0569090f000f0f00f])),(BitVec.ofNat 152 (word80 [0xc0100600060840400,0x40a05600822222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff0000,0x32aaa8e240000f00fff0])),(BitVec.ofNat 152 (word80 [0x102208800880008810,0x320008e2088888888888]))),(0x4154991e6f000fff0000,(BitVec.ofNat 152 (word80 [0x600c03008301083020,0x1548010644444444444]))),((BitVec.ofNat 152 (word80 [3,0x3f0502078ffff0000000])),(BitVec.ofNat 152 (word80 [0x80300c010c0210c043,0x36000006088888888888]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(32,0,205,0,7)]
def g237A : List (List Nat) := [[],[117],[32,99],[32,99,117]]
def g237D7 (j : Nat) := if j=0 then 0x7f else 0
def g237L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g237D7)
  | _ => emptyPacking
def g237I (_ _ : Nat) : Option (Nat × Nat) := none
def g237 : Forest := ⟨237,7,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : CutRow g237 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : CutRow g237 7 0 1 := g237P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : mixedTables g237 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g237 0 0
  · exact mixedEmpty g237 1 0
  · exact mixedEmpty g237 2 0
  · exact mixedEmpty g237 3 0
  · exact mixedEmpty g237 4 0
  · exact mixedEmpty g237 5 0
  · exact mixedEmpty g237 6 0
  · exact g237B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 8 := mixedLower (g:=g237) (i:=0) (hints:=33555715) (before_sound K235 V235) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K235 8 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V235 low237 (by decide +kernel)
def g238Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x807ffff8007ff01ffc,0x3cb735019000f000f00])),(BitVec.ofNat 152 (word80 [0xb0a0950b504a34148,0xb38b7350113333333333]))),((BitVec.ofNat 152 (word80 [0xff807fffff80001fff,0xf9bb81994600f000f00f])),(BitVec.ofNat 152 (word80 [0x121302602606c58191,0x219b8090461111111111]))),((BitVec.ofNat 152 (word80 [0x7fffffffffe000,0x69728c4a50f000f00f0])),(BitVec.ofNat 152 (word80 [0x1c1c038038070601e1,0xc69328c0841111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffffffffff,0xf96279a7230000f000ff])),(BitVec.ofNat 152 (word80 [0x20204c04c048001200,0x60512721aaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xffff80000000000000,0x98c46290f000ffff00])),(BitVec.ofNat 152 (word80 [0x10010010000400,0x4444444444]))),(0x665163c4cffff000000,(BitVec.ofNat 152 (word80 [0x404060060060081802,0x64042c088888888888]))),(0x0,0x0)]
def g238C : List ColumnInfo := [(4,0,234,0,7)]
def g238A : List (List Nat) := [[],[50]]
def g238D7 (j : Nat) := if j=0 then 0x7f else 0
def g238L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g238D7)
  | _ => emptyPacking
def g238I (_ _ : Nat) : Option (Nat × Nat) := none
def g238 : Forest := ⟨238,7,fun i => g238Y[i]?.getD (0,0),g238C,g238A,g238L,g238I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238P7_0 : CutRow g238 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g238B7 : CutRow g238 7 0 1 := g238P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238T : mixedTables g238 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g238 0 0
  · exact mixedEmpty g238 1 0
  · exact mixedEmpty g238 2 0
  · exact mixedEmpty g238 3 0
  · exact mixedEmpty g238 4 0
  · exact mixedEmpty g238 5 0
  · exact mixedEmpty g238 6 0
  · exact g238B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g238G : graphValid g238 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low238 : Lower true (varsX 238) (graphGoal 238) 8 := mixedLower (g:=g238) (i:=0) (hints:=287331680) (before_sound K237 V237) g238G g238T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K238 := extendKnown K237 8 [(238,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V238 : Known true K238 := extend_ok (m:=238) V237 low238 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffc1f5a0e,0x30aeb200000fc003f03f])),(BitVec.ofNat 152 (word80 [0x28428410040840120a,0xa4b209249249249249]))),((BitVec.ofNat 152 (word80 [0xfc003ff83fffe0206a,0xe661718003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x30130020809002204a,0x244131030c30c30c30c3]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0003fffffb48c,0x995842c0fc0000000fff])),(BitVec.ofNat 152 (word80 [0x408409410920008084,0x99184094514514514514]))),((BitVec.ofNat 152 (word80 [0xffffffffc000008945,0x6156a9c000003f03f000])),(BitVec.ofNat 152 (word80 [0x8218218021c0840945,0x615201e69a69a69a69a6]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e020e01089020,0x18a0cc18618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x30030043002104c11,0x42000060820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(32,0,211,0,7),(64,0,179,0,7),(128,0,115,0,7),(0,32,146,65,6),(2,0,241,0,6),(16,0,227,0,6),(1,32,146,64,5),(17,0,226,0,5),(33,0,210,0,5),(34,0,209,0,5),(48,0,195,0,5),(64,32,146,1,5),(66,0,177,0,5),(3,0,240,0,4),(49,0,194,0,4),(65,0,146,0,4),(65,32,146,0,4),(80,0,163,0,4),(97,0,146,0,4),(98,0,145,0,4),(129,0,114,0,4),(130,0,113,0,4),(144,0,99,0,4),(160,0,83,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[96,65]]
def g243D5 := limbs80 #[#[0x55140443e85092150110,0x443d44855354110f3151,0x5895354110f522154d50,0x54510e5b6254d5044396,0xe6961549504838d59154,0x549504835a5c55254120,0x487995815254521d6b71,0x5c15254521e676054951,0x54d21d67705495148759,0xe5710d95534879544365,0xd9553486976036554d21,0x53f39332d272100a5f80,0x17b756f69635d57514b4,0x1a18003838]]
set_option maxRecDepth 16000 in
def g243D6 := limbs80 #[#[0x277b92ca887595354110,0xed2a4a824137dd953c4,0x866ebaec6a0759535412,0x21cbacaa9843b654d600,0x4872eb9aca10cdf7654c,0x110cbecaa9a43d954951,0x443dca1280887f12150,0x8510df6caa0221ee5514,0x40c83baaa2a2887e5424,0x54140df2caa0641ee551,0x520443f8a8a408877952,0x348110fd2a490221fc94,0x9520442fcba240887d95,0x7548110df6ca90221be5,0x59540443f8a8a80885f9,0x12154110bf2eaa0221be,0xe54950443f910aa0887f,0xfb6254110df2c4a8221d,0xbe59150442fdb92a0886,0x5fb7454110df6c8a8221,0x1f954921443f9b824288,0x86f56548510faaa690a2,0x217d5d5214437bb2a428,0x887d55388510beeea90a,0xa217d5d6214437ab2c42,0x2886f56254510eeaa4a8,0x8a217ddc9514437bb12a,0xa2886f76454510deac8a,0xa12217d5ca514437ab14,0x2c4884fd7650910beee2,0x6b1221bb549624437db8,0xaac4884ff7458910dbaa],#[0xa7b12213fdd5624427eb,0xbaec4884fd74d8910dba,0xac8aa2217ddc5544427e,0xfb92c8884fd7655110d7,0xfae5b22213fdd5644427,0x3ea92ca884fd75d91109,0xddee4b2a21bb1c965443,0x27fba2ca884ff7259510,0x9fae9b2a213f5cb6544,0x43eaa9a43887e5524871,0x10beaea90e21bd59521c,0xc43baa92a3885f775487,0xb10ddaa4b1621bd58951,0x2c427ebaac5886dd5358,0x9710dbaa4b1e213fdd56,0x52482fdb8aa09067d525,0x595209fee2b2a41db545,0x540c83dd20a81904ff74,0x158720fd2a4a0641be58,0x4961c837b28ac3906f55,0x7458720dbaa6b0e41bb5,0x5d561c827fba2c3904fd,0xd5154b209feeab0e413f,0xf59154c8376b22a59076,0xbd41593209faecaa641a,0x7edc5505033ea8acb906,0x6df6348540bf6e090a81,0x1b7d8d515027fbb242a0,0x84ff7159540b7ee8a8a8,0xa19f54b615427eb8ec2a,0xa84fd74d85509fae5b0a,0x2a1bb88762543b690aa4],#[0x6a84fd74d89509fae3b1,0x9aa1d788553543ae90aa,0xa6a875e6154d50ebac2a,0xb22a13f5c764543aeb12,0xec090ef910d81219fae5,0x5b0243bd947604877aa8,0xa6c090edd53d8121ddaa,0xebb02433f5d7604867eb,0xa92a290df770545219fe,0xae128a43ddd9551487ba,0xfb2aa690e7f6554d21be,0xfeeab2a433fdc165487a,0x3ea8eca90cfd70d9521c,0xdeaa2b0443be54160887,0x67ebaac110edd5358221,0x1deac4a8c43dd5495188,0x867ebaac510edd5358a2,0x31cfaa4b2c433fdd5628,0x8c77ca92c118df771549,0xa319faeab1463bb54962,0x5473ea92cb18cff7558,0x81519fae5b02a39f54b6,0x625467eb86c4a8cfd74d,0xd91519fae9b12a3bb8cb,0x1609467eb96c8a8cfd70,0x58a519fae4b04a3be48,0xc86154e7eb96c2a9cff7,0x900b000bbae5b0aa7775,0x7b0d0164250430680940,0x1983245f0af140264450,0x3d4790ef1d03946f0d7,0x34851072084047f0fb1f],#[0x9111f2384648b1132204,0x1372684c49712b250494,0xf298524a31432804f49d,0xc8584af15b2b0554a914,0x5e4bb1732e05b4b51672,0x4c718b310614c117f2f8,0x31a3340674cd19732864,0xbb3706d4d91af3586a4d,0x3a0734e51c7388704df1,0x794f11df3b8764eb1d3,0xf4fd1f73e87c4f71eb3d,0x920f418825032034007,0x2274488850f21b430855,0xf4788e51b2334608b515,0xa89452724b4909152123,0x9a5332634c09752d2574,0x53f27b4f09d53926f4d8,0xb293520a3545287508a0,0xab550a955129f538a654,0x580af55d2b7568ac5572,0xb55692cf598b25632c3,0x4a30454442b856f2db5b,0x62036403080c93028d34,0x4d480e35862030404544,0x3618d880d3522868c4a1,0xe0c8a84003010418148c,0xe0600382004514246a10,0x1004410]]
def g243H6 := limbs80 #[#[0x36165800001800a08a3,0x800127e03a2800000000,0x70e67793a0001a8acd4,0x500838fd681207c30000,0x6adcd600017b1a007d40,0x2400130d985]]
set_option maxRecDepth 16000 in
def g243D7 := limbs80 #[#[0x754d50b7d8d40b758f10,0x59421b758c21be58021d,0x110fe48110be582319f,0x510fd48510fe54110fe5,0x10fd94510fd54510fd88,0xf754d10bfd8910bf589,0xbfd9110bf59110f794d1,0xd48710bfd9510bf59510,0x54f10bf58b10fd54710f,0x4920fe54120bf59710f7,0x320bf59520f754d20fb5,0x20fb54b20bf58720fe50,0xbf59720bf59320f754f,0xbfd8550bf59540fe5414,0xfd9150bfd8950df54950,0xd8121bf59421f754c21b,0x4d21fd94521fd54521bf,0x521bf59521f794d21f75,0x21fd54621bf58221bfd9,0x1bf59621f754e21bf58a,0xbfd8151bf59631bf58a3,0xfd9151bfd8951df54951,0xd8553bf58a51bf58251b,0x910f7d8553f718553bf,0x120ff50520ff55110ff5,0x40ff54530ff55320ff55,0x1ff54d21ff54540ff485,0xff54510ff48510ff5493,0xf59110ff58910ff54910,0x90520ff54b10ff59510f,0x720ff94520ff54520ff,0x550ff94720ff54720ff9],#[0x50ff58550ff88550ff48,0x1ff59150ff58950ff985,0xff54521ffd8121ff5812,0xf59521ffd8d21ff58d21,0x54a31ff54a21ffd9521f,0x8951ff58951ff58151ff,0xff59151ff58d51ff9,0x30d30b809607b059029,0x92001c21a017e14e11e1,0x30a2e12b128f26d24b22,0x304003de3bc39a37f34f,0x350a4e84d44964744524,0x6296005d05ae57e55553,0x4872670b6e26a4682652,0xe85382a7f37bc7a17637,0x9729499208f78c789086,0x8aa61a3fa169e69b698d,0x7b33b18afdae9aceaaca,0xbb1babba5b91b76b5bb4,0xdbbd5bcfbc9bc3bbdbb7,0x5bffbf9bf3bedbe7be1b,0xc29c23c1dc17c11c0bc0,0x53c4dc47c41c3bc35c2f,0x231c018285c65c5fc59c,0x32b20889231c2093600d,0x28318185071068a1018,0xe1e1cb838c6050e30d1,0x383a31898e43186911b1,0xa103841c1510f10ae242,0x852c3b085488a0232068,0x1c20e06087889308d463,0x9a31e2468a8c8880b18f],#[0x63888a38303263488d14,0x1c54202021a023249860,0x5081a18608080a31c316,0xd1018a10344490069610,0x40c1200d145868c8c3c,0x464442e9118810a87462,0x22e542844608088222c8,0x88e00614182802c49644,0x85064888b16323222154,0x99191102840406017185,0x2025453254305264462a,0x441518b95480c40a1820,0x9b2080c1489510284040,0x41a2841614c424300223,0x63430a18b23101821e18,0x8684c048502345464174,0x3972c111820200746507,0xa2050e14305080808046,0x4706345081030d2c1831,0x400d2c3188c110c0473,0x7185850a0c60b0e28406,0x4b960c3020804b0a1808,0x8b096182020380b0a1,0x18d14304c23618e18304,0x61d28a1838c302040202,0x40243844c303981130c8,0x2220c86344046488e0d1,0x201c120109081110c643,0x10504842180e096]]
set_option maxRecDepth 16000 in
def g243H7 := limbs80 #[#[0x18444001090200010202,0x1a0900c00f4410090420,0x4,0x30a,0x3000192a00075d000000,0xc0,0x2d000000000000064480,0xc2a81a5d3c000e,0x46700000000000000,0x119ad5180020f6000,0x1e11000000,0x20000000217000000000,0x1,0xf0480024e20,0x0,0x37020000007238000,0x1693000,0x50000000000000000000,0x19,0xcd600000000000,0x0,0x690c00082c0000000,0x1109c8300072d0064000,0x0,0x89e18a2ac4e000386c00,0x22,0x63c0000,0x1022900000,0x5d2b80000000,0x100800041670bc87c000,0x84b000000,0xdac000000000000],#[0x262387600000000,0x35dc0000000,0xb0528f00010200000000,0x7440000000000000000,0x1140000000000000,0x2c000000131000000000,0x383600000042,0x0,0xc5900000000000000,0x863812d1f115c000,0x31b8000000000,0x165c000000000,0x4857519eb700,0x3c800000000000000000,0x5e00000000000014a40,0xb0200000000009060003,0x800000000061b4000000,0x650700004706af00039f,0x230000000000e5,0x0,0x2b0a0,0x0,0x8015842a5400074ac000,0x195a61f2b3,0xe47d4f800000,0xe0000058000000000000,0x28ce000d22522a8,0x0,0x71280000000000000,0x40000004360000001091,0x6dc800000000000000d3,0x27fd3d000083dd4],#[0x0,0x0,0xe01c352a640000000000,0x7d500000008290000d34,0x6160000000000000000,0x88000000000aa0800000,0x52395000000050e00012,0x35,0x4b50,0x28a00000000007908,0x523c000ab1,0xe0000000000000000000,0xe3c20000d000002a661a,0x19000000000062dc2c52,0x24480000000000d058,0x675d4a00000000000000,0x3062c26000d2682962f5,0x0,0x88a000000000000,0x2c400000,0x10fba1c00040980,0x156c0000,0x55c8001d4e0000000000,0x0,0x1a2000092e000000,0xcc000650800000000,0xb3b93216c00100d00000,0x6,0x222a5039900000000000,0x782c00000084e8000f46,0x117e0c2000000,0x401800000],#[0x0,0x8c8000001c7700000000,0xa,0x61a0002e7c37c0000000,0x2d36d140000002482000,0x623000000066f232800,0x11a81c9800000000,0x0,0xcaa80000000,0x0,0x80000000000000000000,0xe0000300002950000c24,0x2131524000000000266,0xe80000000000000b1f00,0xce80000000000000003c,0xc760003,0x0,0x14c60000000000000000,0x0,0x4c0014a6000000000000,0x390000000041,0x51c00000000000000000,0x6,0xfc180000001078000000,0xeac0000000000000b15,0x3800000000000004ec00,0xa0000000000000000c0,0x1cf4bf05200061280019,0x0,0x29a0001497e0d6074,0x4564000000,0x700078d400000093c000],#[0x1e1,0x1c9e00000000,0x221c0,0x4aa00000000000000000,0x386e00000072ac000,0xf25800000068d000,0x98000000000000000000,0xc3a0000000001a40a3,0x89f98fc0,0x57600000000000000000,0xaae000b4c51c9,0x4000000000000195c000,0x91820f,0xcc000000000000000000,0x38,0xa26004000000221a84e0,0x2520000000d276]]
def g243D8 := limbs80 #[#[0xd20ff887f443bca7dd53,0x43fd50fea07f4c3fe41f,0x7fc63fd31ff10ff487f8,0x780c001fd53ff28ff54,0x318ae24c7e1bc5d13839,0x21a21cd523438f6390d5,0x44708e680426086a1e28,0xc711e20244601a50d11c,0x23151987882c710058a2,0xa8114240e1909826911a,0x46a1e20408019a41438a,0xe39719850e2c66905082,0x308b401a830201718a60,0x1650219838c34068650a]]
def g243H8 := limbs80 #[#[0x12051201100001101020,0x27017023a0000a146,0xd13000000000000,0xe5372c70000000000000,0xf1953c00000000000058,0x3db0910bb3b5ad74c011,0x100000000000000080e9,0x816000000000ccb644d3,0x4000000000d6e000000,0x30153a5b6db4bd5b3cea,0x3b779e88245e000000a2,0x40000000000456000000,0x503000f27000d,0xaaf00000059,0xd5945c000000000,0xac30000000000,0xf3f00000000,0x0,0xb0600000000096b0000,0xd5300000000036,0x323a11e9788050000000,0x20006020000004910003,0x61f0000000009c200031,0x674c5f4f000de3,0x8991410,0xc63783f55000ccd00,0x9cd00051520000000000,0xd636a1c468ae1557364c,0xd4dae200000000088a82,0x69000000e54d6185821a,0xfb18e5a000a0c00016c3,0xe39808321c5],#[0x84672e000000000,0x107b2900092c0000000,0x0,0x1d5a4a000000,0x4949000000000000b5d0,0xc261e8e350006a883,0x817000000000,0x3d0000b960000000,0x64700000000000000000,0x551d2ae000000000,0xb010000000,0xb5200,0x220000008660002c19a2,0x528000000f48e,0xb0d13a00000,0x25000000000000000000,0x82f0002656,0xe4e00030f00000,0x6d400051e00029df1b,0xb2a843000d6243eb9f0,0xe38000b4200000000000,0xc8000010000000000a6a,0xb52b0000000000001458,0xd30a33000000414ed,0x9200000090ae24000000,0x2]]
def g243D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g243H9 := limbs80 #[#[0x28200000b7ce,0x34727000000000000,0xc6dd7d3001c100,0x708000000058a0000,0x1e480000000003100000,0x60000000001c80000,0x78c000000000,0x6200000000706f400,0xa0000000000278000000,0x1d7158a51d,0xc40000,0x69600000000015280,0xea600000000000000000,0x38]]
def g243L : Nat → Packing
  | 5 => (18,4,5,0,0,8,0,g243D5)
  | 6 => (188,3,5,0,0,11,0,g243D6)
  | 7 => (111,2,5,0,0,12,0,g243D7)
  | 8 => (17,1,5,0,0,10,0,g243D8)
  | 9 => (1,0,5,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 7 41 5 10 5 1 g243H6
  | 7 => lookupWord 58 877 3 13 8 1 g243H7
  | 8 => lookupWord 37 379 4 12 7 1 g243H8
  | 9 => lookupWord 7 107 1 10 5 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : CutRow g243 5 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_1 : CutRow g243 5 1 17 := by
  apply polarBlock (data:=fun _ => (word80 [0x6411018104,0x43310442018240648251,0x220281c0a221300602,0x1120864904100220281,0xc0a22110040400190c46,0x6021040400190c466021,0x40400190c4660210044,0x181c064422004040019,0xc466021040400190c46,0x602100622281c0a22320,0x80200188c8660420802,0x188c86604208020018,0x8c866041080200188c86,0x60410a04140209205120])) rfl
  decide +kernel
theorem g243B5 : CutRow g243 5 0 18 := (@joinRow g243 5 0 1 17 g243P5_0 g243P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : CutRow g243 6 0 12 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_12 : CutRow g243 6 12 9 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_21 : CutRow g243 6 21 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x208020b,0x4a2905200641181c064,0x4331040400190c466043,0x40400190c4660430825,0x110c846512000210110,0xc8461120040400190c46,0x6032040400190c466032,0x210110c84611200605,0x90c42703204040019,0xc466032040400190c46,0x603208250110c8465110,0x8250110c84651100404,0x190c46603204040019,0xc466032040400190c46,0x6032040400190c466032,0x40400190c4660320404,0x190c46603208020018,0x8c866062040400190c46,0x6032040400190c466032,0x40400190c4660320404,0x190c46603208020018,0x8c866062040400190c46,0x6021040400190c466021,0xa041402052051510a04,0x11108c64515104403281,0x44e02352040400190c46,0x6032040400190c466032,0x40400190c4660320404,0x190c46603204040019,0xc466021040400190c46,0x60210808001a0884c043,0x48020b008482400a04,0x14020920514004040019,0xc466032040400190c46,0x6032040400190c466032,0x6050019084670320802,0x188c86606204040019,0xc466021040400190c46,0x6021040400190c466021])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_69 : CutRow g243 6 69 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x220281,0xc0a2213000220281c0a2,0x213000220281c0a22130,0x220281c0a221200404,0x190c46603204040019,0xc466043040400190c46,0x604300220281c0a22130,0x220281c0a221300802,0x188c86606304040019,0xc466032040400190c46,0x6032040400190c466032,0x1001028145a090431000,0x11108d44815410001181,0xc1608153082504024102,0x512000622281c0a22330,0x40400190c4660320044,0x181c064423000220281,0xc0a2213000641181c024,0x433100220281c0a22130,0x220281c0a221300064,0x1181c064433100220281,0xc0a2212000220281c0a2,0x212000220281c0a22120,0x220281c0a221200022,0x281c0a2212000220281,0xc0a2212000220281c0a2,0x216000220281c0a22110,0x208020b04a290520404,0x190c46604308250110,0xc8465120040400190c46,0x6043040400190c466032,0x40400190c4660320404,0x190c46604308250110,0xc846512008080182c0e0,0xc05400622281c0a22330,0x60500190c4670430062,0x2281c0a2233000622281,0xc0a22330080800120884,0xc043040400190c466043])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_117 : CutRow g243 6 117 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x220281,0xc0a2216000220281c0a2,0x212000220281c0a22120,0x40400190c4660430064,0x1181c064433104040019,0xc466032040400190c46,0x603200220281c0a22130,0x40400190c4660430022,0x281c0a2213000641181,0xc064434100220281c0a2,0x215004420182c064a261,0x40400190c4660320022,0x281c0a2212000220281,0xc0a2212000220281c0a2,0x21200064140301044341,0x641181c06443410022,0x281c0a2213000641181,0xc064433100641181c064,0x4331040400190c466032,0x40400190c4660320404,0x190c46603200440181,0xc064424108250110c846,0x512000440181c0644231,0x641403010443310802,0x188c86605308020018,0x8c866053080200188c86,0x60530041020944861221,0x40400190c4660430020,0x4024102115004040019,0xc466032004102094486,0x122100622281c0a22330,0x440181c06442410404,0x190c46604300622281,0xc0a22330004802030084,0x824100200281c0a22160,0x220281c0a221300020,0x281c0a2216000410201,0x44861210100011108d44,0x8154040400190c466043])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_165 : CutRow g243 6 165 23 := by
  apply polarBlock (data:=fun _ => (word80 [0x440181,0xc064423100440181c064,0x423100622281c0a22330,0x641403010443410404,0x190c46604304040019,0xc46603200220281c0a2,0x2130040400190c466043,0x220281c0a221300442,0x502c144325104040019,0xc46604300220281c0a2,0x213000220281c0a22130,0x220281c0a221300022,0x281c0a2213000220281,0xc0a2213000220281c0a2,0x213000220281c0a22120,0x4040011084660320602,0x5028960326100220281,0xc0a2213000220281c0a2,0x213000220281c0a22130])) rfl
  decide +kernel
theorem g243B6 : CutRow g243 6 0 188 := (@joinRow g243 6 0 69 119 (@joinRow g243 6 0 12 57 g243P6_0 (@joinRow g243 6 12 9 48 g243P6_12 g243P6_21)) (@joinRow g243 6 69 48 71 g243P6_69 (@joinRow g243 6 117 48 23 g243P6_117 g243P6_165)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : CutRow g243 7 0 7 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_7 : CutRow g243 7 7 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_55 : CutRow g243 7 55 13 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_68 : CutRow g243 7 68 10 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_78 : CutRow g243 7 78 33 := by
  apply polarBlock (data:=fun _ => (word80 [0x210110,0xc846112000210110c846,0x112000220281c0a22130,0x220281c0a221300404,0x190c46604300220281,0xc0a2213000220281c0a2,0x213000220281c0a22130,0x220281c0a221300028,0x1128846815000280082,0x4022815000220281c0a2,0x2130040400190c466043,0x40400190c4660430041,0x2094486122100440181,0xc0644241040400190c46,0x6043040400190c466043,0x40400190c4660430404,0x190c46604304040019,0xc466043040400190c46,0x60430028011288468150,0x40400190c4660430404,0x190c46604308080182,0xc0e0c05400220281c0a2,0x2130040400190c466043,0x208000a042290520404,0x190c46604304040019,0xc466043040400190c46,0x6043040400190c466043])) rfl
  decide +kernel
theorem g243B7 : CutRow g243 7 0 111 := (@joinRow g243 7 0 55 56 (@joinRow g243 7 0 7 48 g243P7_0 g243P7_7) (@joinRow g243 7 55 13 43 g243P7_55 (@joinRow g243 7 68 10 33 g243P7_68 g243P7_78)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : CutRow g243 8 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_2 : CutRow g243 8 2 15 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : CutRow g243 8 0 17 := (@joinRow g243 8 0 2 15 g243P8_0 g243P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : CutRow g243 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : CutRow g243 9 0 1 := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : mixedTables g243 9 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g243 0 0
  · exact mixedEmpty g243 1 0
  · exact mixedEmpty g243 2 0
  · exact mixedEmpty g243 3 0
  · exact mixedEmpty g243 4 0
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K238) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := mixedLower (g:=g243) (i:=0) (hints:=16777284) (before_sound K238 V238) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K238 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V238 low243 (by decide +kernel)
def g245Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1fffff724e,0xb0ac1300000fc0000fff])),(BitVec.ofNat 152 (word80 [0x28428408401040324a,0x20a01209249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc003fffe0ffe02922,0xe663708003f000fff000])),(BitVec.ofNat 152 (word80 [0x300b00500200822802,0xa44350030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc00000ffffbd84,0x995842c0fc000000003f])),(BitVec.ofNat 152 (word80 [0x408c09608425008984,0x99584096596596596596]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156a9c000003f03ffc0])),(BitVec.ofNat 152 (word80 [0x821021800086040005,0x411429e4924924924924]))),((BitVec.ofNat 152 (word80 [0x9171,0x18b1dc3f00003ffc0000])),(BitVec.ofNat 152 (word80 [0xe00e010838089160,0x18a08418618618618618]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300300210c0104411,0x42000160820820820820]))),(0x0,0x0)]
def g245C : List ColumnInfo := [(32,0,213,0,8)]
def g245A : List (List Nat) := [[],[98]]
def g245D8 (j : Nat) := if j=0 then 0x7f else 0
def g245L : Nat → Packing
  | 8 => (1,0,1,0,0,0,0,g245D8)
  | _ => emptyPacking
def g245I (_ _ : Nat) : Option (Nat × Nat) := none
def g245 : Forest := ⟨245,8,fun i => g245Y[i]?.getD (0,0),g245C,g245A,g245L,g245I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245P8_0 : CutRow g245 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g245B8 : CutRow g245 8 0 1 := g245P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245T : mixedTables g245 8 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g245 0 0
  · exact mixedEmpty g245 1 0
  · exact mixedEmpty g245 2 0
  · exact mixedEmpty g245 3 0
  · exact mixedEmpty g245 4 0
  · exact mixedEmpty g245 5 0
  · exact mixedEmpty g245 6 0
  · exact mixedEmpty g245 7 0
  · exact g245B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g245G : graphValid g245 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low245 : Lower true (varsX 245) (graphGoal 245) 9 := mixedLower (g:=g245) (i:=0) (hints:=33555716) (before_sound K243 V243) g245G g245T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K245 := extendKnown K243 9 [(245,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V245 : Known true K245 := extend_ok (m:=245) V243 low245 (by decide +kernel)
def g252Y : Array (Bits × Bits) := #[(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff8007fffffc03f,0xe5c3109b84e000f00f0f])),(BitVec.ofNat 152 (word80 [0x140150350250148585,0x2143009904c111111111]))),((BitVec.ofNat 152 (word80 [0xffffff8007ffffc0,0x1a4b2dc05c400f00f0f0])),(BitVec.ofNat 152 (word80 [0x260260260360190909,0x9a4304804c4111111111]))),((BitVec.ofNat 152 (word80 [0xfffffffff8000000,0x7718e0d9950f0000000])),(BitVec.ofNat 152 (word80 [0x382b813813815e0e0e,0x7518e0d985777777777]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffff,0xc8137847ab90000f00ff])),(BitVec.ofNat 152 (word80 [0x408c04404404600000,0x107842831aaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xff0000000000000000,0x45c463c762f000fff00])),(BitVec.ofNat 152 (word80 [0x3001801801801010,0x40c0204302444444444]))),(0x33a4d3e0015ffff00000,(BitVec.ofNat 152 (word80 [0x80c006006006002020,0xa05160010888888888]))),(0x0,0x0)]
def g252C : List ColumnInfo := [(4,0,248,0,7)]
def g252A : List (List Nat) := [[],[50]]
def g252D7 (j : Nat) := if j=0 then 0x7f else 0
def g252L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g252D7)
  | _ => emptyPacking
def g252I (_ _ : Nat) : Option (Nat × Nat) := none
def g252 : Forest := ⟨252,7,fun i => g252Y[i]?.getD (0,0),g252C,g252A,g252L,g252I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252P7_0 : CutRow g252 7 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g252B7 : CutRow g252 7 0 1 := g252P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252T : mixedTables g252 7 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g252 0 0
  · exact mixedEmpty g252 1 0
  · exact mixedEmpty g252 2 0
  · exact mixedEmpty g252 3 0
  · exact mixedEmpty g252 4 0
  · exact mixedEmpty g252 5 0
  · exact mixedEmpty g252 6 0
  · exact g252B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g252G : graphValid g252 (boundsBefore K245) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low252 : Lower true (varsX 252) (graphGoal 252) 8 := mixedLower (g:=g252) (i:=0) (hints:=573003008) (before_sound K245 V245) g252G g252T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K252 := extendKnown K245 8 [(252,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V252 : Known true K252 := extend_ok (m:=252) V245 low252 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf3a38808b46acc81d5,0xe080000000000fe03fff])),(BitVec.ofNat 152 (word80 [0x41218800946a4c00c5,0x8010a142850a142850a1]))),((BitVec.ofNat 152 (word80 [0x92add040298bc3743,0x1b400001fc00001fc000])),(BitVec.ofNat 152 (word80 [0x610adc040218ac3741,0x9458b162c58b162c58b]))),((BitVec.ofNat 152 (word80 [0x7508f40f734115d35,0x84000fe0007f0000000])),(BitVec.ofNat 152 (word80 [0x83508f00f334104d15,0x843870e1c3870e1c387]))),((BitVec.ofNat 152 (word80 [0xf25c4eb7aac1d04140,0x69007f0003f80000007f])),(BitVec.ofNat 152 (word80 [0x25c46862281904100,0x6803060c183060c18306]))),((BitVec.ofNat 152 (word80 [0x85835f63a014663a,0xd68000000000001fff80])),(BitVec.ofNat 152 (word80 [0x84035b618010403a,0x56aa54a952a54a952a54]))),((BitVec.ofNat 152 (word80 [0x116648158062bf0a8,0x15ff800003ffffe00000])),(BitVec.ofNat 152 (word80 [0x20001080023b028,0x118c183060c183060c18]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0xca120700442000002,0x43060c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(4,0,123,0,10)]
def g127A : List (List Nat) := [[]]
def g127D10 (j : Nat) := if j=0 then 0xff else 0
def g127L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I (_ _ : Nat) : Option (Nat × Nat) := none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : CutRow g127 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : CutRow g127 10 0 1 := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : mixedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g127 0 0
  · exact mixedEmpty g127 1 0
  · exact mixedEmpty g127 2 0
  · exact mixedEmpty g127 3 0
  · exact mixedEmpty g127 4 0
  · exact mixedEmpty g127 5 0
  · exact mixedEmpty g127 6 0
  · exact mixedEmpty g127 7 0
  · exact mixedEmpty g127 8 0
  · exact mixedEmpty g127 9 0
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K252) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := mixedLower (g:=g127) (i:=0) (hints:=16778563) (before_sound K252 V252) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K252 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V252 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff607e8a2c1076819,0x3208000003f000fc0fff])),(BitVec.ofNat 152 (word80 [0x28202e08241036008,0x10081041041041041041]))),((BitVec.ofNat 152 (word80 [0x2c635900a8df1f6,0x45280000fc000003f000])),(BitVec.ofNat 152 (word80 [0xcc2863090088d71f4,0x4508b2cb2cb2cb2cb2cb]))),((BitVec.ofNat 152 (word80 [0xfb234c3c9788551,0x5050003f00003f000000])),(BitVec.ofNat 152 (word80 [0x570fb234c3c9288151,0x104071c71c71c71c71c7]))),((BitVec.ofNat 152 (word80 [0xffe4b9325eaa878214,0xb440fc0000fc000003f])),(BitVec.ofNat 152 (word80 [0x9804b912508a848214,0xa406186186186186186]))),((BitVec.ofNat 152 (word80 [0x10b84759f40b063,0xa8e3f00000000003ffc0])),(BitVec.ofNat 152 (word80 [0xe00109046582408003,0xa8e14514514514514514]))),((BitVec.ofNat 152 (word80 [0x22c1b057070590e,0xe5540000000ffffc0000])),(BitVec.ofNat 152 (word80 [0x4090430501802,0xe5178e38e38e38e38e38]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19d049c814980680,0x9c8ffffffff000000000])),(BitVec.ofNat 152 (word80 [0x1040090814100400,0x60820820820820820]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(4,0,187,0,10)]
def g191A : List (List Nat) := [[]]
def g191D10 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g191D10)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,10,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P10_0 : CutRow g191 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B10 : CutRow g191 10 0 1 := g191P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : mixedTables g191 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g191 0 0
  · exact mixedEmpty g191 1 0
  · exact mixedEmpty g191 2 0
  · exact mixedEmpty g191 3 0
  · exact mixedEmpty g191 4 0
  · exact mixedEmpty g191 5 0
  · exact mixedEmpty g191 6 0
  · exact mixedEmpty g191 7 0
  · exact mixedEmpty g191 8 0
  · exact mixedEmpty g191 9 0
  · exact g191B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 11 := mixedLower (g:=g191) (i:=0) (hints:=1347) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 11 [(191,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g223Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x455940de86000003e0,0x7ff400c3f317b713])),(BitVec.ofNat 152 (word80 [0x550401e065294a529,0x9248934800132b51610]))),((BitVec.ofNat 152 (word80 [0xae80190fc800007c00,0x7ff8000010c00181e9d])),(BitVec.ofNat 152 (word80 [0x8e80110f88c6318c63,0x1861986000040000169d]))),((BitVec.ofNat 152 (word80 [0xe96243a034000f8000,0xf8000000021003e05fff])),(BitVec.ofNat 152 (word80 [0xe96243a035ce739ce7,0x38e3b8e0000000005fff]))),((BitVec.ofNat 152 (word80 [0x528ef8788001f0001f,0x7e004201c046bef])),(BitVec.ofNat 152 (word80 [0x528eb860818c6318c6,0x30c330c00000000069ef]))),((BitVec.ofNat 152 (word80 [0x32792f85403e000000,0x1ff818183fe0078c66])),(BitVec.ofNat 152 (word80 [0x30292e8041294a5284,0x628a2289003a48024962]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x986220219c000001f,0xffe0001fe03ffff87048])),(BitVec.ofNat 152 (word80 [0x318c6308,0x430c031dc03b9fdb0000]))),((BitVec.ofNat 152 (word80 [0x9420942027ffffffe0,0x1fffc0000000b0])),(BitVec.ofNat 152 (word80 [0x10,0x84104402178000000000]))),(0x0,0x0)]
def g223C : List ColumnInfo := [(2,0,221,0,10),(4,0,219,0,10),(8,0,215,0,10),(64,0,159,0,9),(1,0,222,0,8),(16,0,207,0,8),(128,0,95,0,8),(5,0,218,0,7),(9,0,214,0,7),(18,0,205,0,7),(20,0,203,0,7),(0,4,27,192,6),(17,0,206,0,6),(65,0,158,0,6),(80,0,143,0,6),(7,0,216,0,5),(19,0,204,0,5),(21,0,202,0,5),(25,0,198,0,5),(64,4,27,128,5),(128,4,27,64,5),(129,0,94,0,5),(144,0,79,0,5),(192,0,27,0,4),(192,4,27,0,4)]
def g223A : List (List Nat) := [[],[64,49]]
def g223D6 := limbs80 #[#[0x70596ca9a2dd56458140,0x957154040873e8d98dca,0x2e89655cd50103d63a25,0x103c6b925d96554040f5,0x6458140f1ae89955d950,0xd56559160502eaba2595,0x34b97565a6458140f0e5,0x58140d665d5932116050,0x9161d655033998564c84,0x39755915458240c79e8b,0x150c73e8b9361d65903c,0x59160542e3ba45956458,0xa39d16458150baa68a74,0xd8e5519699160542e99,0x16054373154644845815,0x6488458150dac5919121,0xaa591922116054372954,0x5437195464c8458150d,0xc8458150da6591932116,0xe8b9361f605433998464,0x43371856448059150c73,0x59150c7c61d91201645,0x59320164543369856488,0x1cfa2e4d87d9150cd661,0xd950c7365392e0d76543,0x25c5609431cf94e4b835,0x9a46548059160d786599,0x60a67e957460c7458363,0x17745831cfa2e4d85dd1,0x4e4d85dd160c67593936,0xa796a7726067059719e6,0x725971cfa3663729c165],#[0x4d80dc965c7361393603,0x96a191a03725971cf84e,0x1f0e0642c130803400c7,0x74371a0c45c2b1409444,0x54a44f261248c43200f4,0x81b4d46732184bc5b2c1,0xb44215047f3e1e4ec733,0x3e2f8028]]
set_option maxRecDepth 16000 in
def g223D7 := limbs80 #[#[0xb92a02074c5517154040,0x81c397655150103a52a8,0x957254040eb8b2ae2a80,0x103ab2cab9aa02075a5,0xcbb2caa8081d39765515,0x2a02055ee5d6554040e3,0x5e792595711038f32abb,0x82594408f7cc2cab9081,0x31daedc12ca2065b5d7,0x930eb28811ed97e09651,0xc2055be49865d4408f7c,0x975591605029df24c2ae,0x58140e5dbaac8b0281cb,0xf3326422c0a05ae65a64,0xeb2a815e992dd560502,0x47be4987595408fbc8b,0x361d659023df24c3acb2,0x150f1cb22a8b02a11df9,0xf26c3ec0a847be4987d8,0xb22a11ef9261f645423b,0x73e0f825d9508efc9b0f,0xc56094339f25c1aeca86,0xe78b22e2b04a1de1925,0x8b92c12873cd91715825,0x4a1ceb645c9609439d2c,0x619825c650e5cba2c8b0,0x71942be321b22e328679,0xf4c86c8b94a15f190a19,0x2c8b0679615825c460a,0x16e99220164582de3224,0x48059160b6cc9900b22c,0x58333ae8c18e8b059e65],#[0xc930bba2c11bf985d074,0xe0b2c77e4d85dd1608f7,0xcf83dc9705963f730b80,0x29c165cf3b9303382cb9,0x6b9f26c06e4b2c7b6637,0x2c0a82815e591a037259,0xa07ae5956458140f5cb2,0x6455160903adaebc12ca,0x5240e7cbaac8b0481eb9,0x7f08aa2c0a872f5d9645,0x8b02a1e7965591605436,0x7ae9d16458150f5cba2c,0x9d160542df32d322c0a8,0x50bf8c8908b02a16f996,0x26422c0a85fa64884581,0xa2a177b905d954542fb3,0xc6448059150b9fca2eca,0x164542fd324402c8a85f,0xdbcb2b013a2a17d99320,0xb2aa0207dae496554040,0x81d79955d950103af2ec,0xdb8259440ef3c92cab88,0x51033db2fc12ca2067b5,0x7c12ecb2881d6f825d56,0x2ea2067be498759440e7,0xcef9261576103adf24c3,0x6458140f5cc82c8b0281,0x397aeab22c0a07aee41,0xab0eb02819bd75e11605,0xa047fe5587581408fec,0xb7559160503b72eab22c,0x58140f5cbaac8b0281db],#[0xd770ab22c0a07ae61564,0xc8b0281eb89859160503,0x73e5d76458140edcbac,0x521160503b72ea422c0a,0x140edcbaf08b0281bb98,0x724b2ac0a076edd78458,0xb0281d797559560502fd,0x3ee597558140e7c4b2ea,0x9660502fd724b2cc0a07,0xcfcc32eb30281d79755,0xac26c0a067ee61759814,0x2813ef926176050337ae,0x61f8259540cbebab0bb0,0x655033dd0fc12caa067b,0xf7bb704b2a819ed76e09,0x12caa067b65f8259540c,0x1c7c965d5655033dd2fc,0x18759540e3fcb2eab2a8,0x5023ff20c3acaa067ee4,0xc930eb2a819f79161d65,0xcaa065fe558759540cf7,0xff9661d655031ff2cc3a,0x65d5408fec870eb2a811,0x31fec1c32eaa063f5838,0x700bb28197d75e157650,0xa067e617805d940eddc2,0x50e01765033f70bc02ec,0xd9408fecaf00bb2819f9,0xfacbc2aeca065f543855,0xb3b2813ef92616765032,0x65f59585dd940cbebab0,0x55160903d76c8aa2c120],#[0x40f9cb2aa8b0481d7975,0xeaa2c1207ce61554582,0x481cf975d9160903b77,0xe6178758240ebcb2aeab,0x154902bf32bc3ac12067,0xb9fcaac8aa481d3d7559,0xb22a9205ee6436455240,0x8197d8759554902e7b2b,0x5d6555240abecbacaaa4,0x49032fb0cbaaa92055fe,0xebb2caaa481f2f925955,0x2a92074f6557655240e9,0x7b79161954902f7720c3,0x8655240bd7c930caa481,0x2f7321432a92056fe5d,0xaf00b24815bd97a19549,0x92067e5d580d9240cfcb,0xd75617649027df24c2ec,0x59640af7c92caba48197,0x3daedc12cb206fa58382,0xeab2c819ed97e0965903,0x65fe117559640eb7c12,0x361d659033df24c3acb2,0x640cfcba301b2c819df9,0xb29c2aed2047f65187d9,0xb02a1e3d64551605423f,0xce59154581509beca70a,0x5160543e74c8aa2c0a87,0xf9c422a8b02a1e7b645,0xcaa2c0a87cee11545815,0x2a177b9655160542ef32,0x2116458150e7dba2c8b0],#[0x60543d7708b22c0a87ae,0x3ccaac8b02a1e7b85591,0x22c0a85de6566458150f,0x1cfb74d9160542bf32f3,0xa7458150b7dcb2e8b02a,0x542fb3273a2c0a85fa64,0xb2ee8b02a13f9989d160,0xc0a86ee6108458150ebc,0x7b9561160542ef32a422,0x458150dbdc2d08b02a17,0x3ed724b2ac0a85de6568,0x70ab02a177b945956054,0xa86de6195498150bbcca,0x9655260542ef32caa4c0,0x8150fb5c92cb302a177b,0x7b08aa6c0a85dee51659,0x9b02a197d87553605436,0x6dbe4985d81509becc2a,0x61f605426ff28c2ec0a8,0x50cefc9b0fb02a19ef92,0x26bb2a8a85dbe4976551,0xa2a1d7b905d954542ebf,0xbe497655150abfc82eca,0x954543abf26bb2a8a875,0xe9fca2ecaa2a1d3c945d,0x3b2a8a865f2617655150,0xa173d949d954542ef321,0x1c8059150dbcc2900b22,0x45436f30bc02c8a867e6,0xdba700b22a19fa87e016,0x2c8a86de5978059150cf,0x9f976e01645436f32bc0],#[0x7459150cfdbb700b22a1,0x42f5b253a2c8a85ee642,0xa2cab22a179d939d1645,0x8a85cfe516599150b9fc,0xd76616645432fb0eb2cc,0xd9150cbfbb30b322a197,0x6df24c2ec8a867edd180,0xfb22a197f7461764543,0x8677e4d87d9150cf7c93,0x25d9745434ff0cb2ae8a,0x150aefc9aecba2a15ef9,0xf0cbb2e8a856fe51765d,0x3a2a18fe76e19745431f,0xdb595829d150cfcbb301,0xe745433daecc14e8a86,0xceebb3073a2a1b5d656,0xcc34e8a869f619659d15,0x2a1d6f92597745431fae,0xd9186dd150c7eb230dba,0x655436f309c02caa863f,0xb7c2704b2aa1b6d84e09,0x22caa85dee418459550d,0x176f9261165542eef22c,0xa8459550bbcc8508b2aa,0x542ebb27422caa85db64,0xc8708b2aa167d96a1165,0xcaa86de6438459550bbc,0xee74e09765436f521c22,0x35d950db6b2f04bb2a19,0x379f25c1aeca86f6e438,0xf06bb2a19de74e0d7654,0xa86d7e57835d950daeb2],#[0x83e017654337ce9c22ec,0xd950ebdc2f00bb2a1ddb,0xd909c12eca8773e0f825,0x4bb2a19ed84e09765433,0x67be13825d950cf74270,0xe0976543adf0bc12eca8,0x50cf7a0704bb2a19ed40,0xc9c12eca867b593825d9,0xb2a19ed94e09765433dc,0x7e03835d950cf74a704b,0xd76543bb721c1aeca867,0xcee42706bb2a1dcf92e0,0xc1aeca8677613835d950,0xa19df84e0d765433bd09,0x57835d950eafc2f06bb2,0x65433ba81c1aeca8757e,0xfc8706bb2a19df40e0d7,0xaeca8677593835d950ce,0x9dc94e0d765433bcc9c1,0x835d950ceeca706bb2a1,0x433bf29c1aeca8677a53,0x708bb2a19bd40e11765,0xca866f593845d950cdfa,0xd94e157654337cc9c22e,0x9d950cfcba3013b2a157,0x37ac8c26eca866f5d184,0xe2b04a19be6461376543,0x877c6117158250ef8b22,0x45c960943be32cb8ac12,0x250ef4c22e4b04a1de96,0x2c8ba2c12873ee1d6458,0xb24a15f994e1d60943b7],#[0x7e65f8059250cfcbb700,0xd964943b7700ba2c9286,0xcfdc830eb24a1cfb805,0xbc02c8b067edd7805916,0x2c16fb90595645827f32,0x6548059160b77c92cab2,0x64582df52e402c8b05be,0x7ccaf00b22c1ebb74e01,0xa4c8b066f6177499160b,0x19f57560474582b7b2bb,0x5831d160cf6bab043a2c,0x582b7f2aba0e8b06775d,0xc830a3a2c19bf985d074,0xe8b065f5d7855d160dbc,0x7d756167458337b0bba4,0x5dd160af7c92cbba2c19,0x33df24c2ee8b047f6418,0x30bba2c19df936177458,0xb04fe6538059560cbeaa,0x94dd565583adf05baaca,0xd560df4a0704baac157d,0xdac9c12eab06fa903825,0x4baac1aef64e09755835,0x67b5d3825d560cf63a70,0xe09755833dce9c12eab0,0x60deca0706baac19ef74,0x21c1aeab06f6903835d5,0xaac1bcf92e0d755837b7,0x7d93835d560d6eb2706b,0xd755833b8e9c1aeab06b,0xcef3a706baac19dd74e0,0xc26eab0677dd3835d560],#[0xc15ef92595749833f720,0x5f82596609fcca700b2c,0x5983adf04baacb3067b6,0x6c0704baec197f845d56,0x2ebb067b613825d760cf,0x9ed90e0975d833dd09c1,0x825d760cf6ca704baec1,0x97bb726b80e0b2e7ba53,0x26e4382cb9fb985c0705,0xb2f73e0f725c165cf6c,0xf85dc9705973df09b92e,0x5c165cf6ba704b82cbd6,0x79ee5c1ae0b2e7b9d382,0x6b82cbbcf92e0d70597,0x2e775d3835c165cee3a7,0x4e0d705973bce9c1ae0b,0x165dafcaf06b82cb9df7,0xce9c22e0b2e6f5d3845c,0x382cbbe7726067059737,0x7d5d1819c165df2c9303,0x6705973eee8c0ce0b2e,0x5d7acb303382cbb75956,0x9b94e0b2e7d65d819c16,0x2cb9ed86dca705973db0,0x5d1829c165cf6cc6e538,0x7059737ae8c24e0b2e7b,0x7eba30d382cbaef7261a,0x96e0b2e3fdd1869c165c,0xb9ed84dcb705973db01b,0x184dc165cdea0309b82c,0x596bdb28406e4b2e6fd0,0xc2301b92cbdcf9360372],#[0xe4b2e7be1180dc965cf6,0xed94a0372596bdf28c06,0xdc965af6cb501b92cb5,0x2bdb29c06e4b2d7b6628,0x207f830c132066019800,0x43e1fe0e586602ca13,0x61698aec54628b12c09,0x7480a3db1dd0e1c6963,0x4d125c92848ca44d21a9,0x9710b2255e295944c9e4,0x26c935419f8c966212f2,0x9f14f127563961c08dc,0x6a894439a16d07482240,0xb9256928492147ba3351,0x3aa9bd4d7267d3209814,0x52528ed458a14502a7d9,0x155aa9e547aa014e2a62,0x56d2b5159cac85612af,0x115fcaf85792bb15ccae,0x285912c7162cb105852c,0xd3168cb4059d2cd165cb,0xb705b52d916bcb585a92,0x2e5171cb885c12df16ec,0xcbb85d92eb174cba05cd,0x12f717acbd05e52f1177,0xcc005fd2fd17dcbe85f,0x15309183cc1860930318,0x89cc4862130f186cc306,0x63931b18ccc6062d3151,0x192cc9064532118fcc78,0x65d32d195cca8651327,0x919bccd8669333198ccc],#[0x868133f19eccf067533,0x4b1a4cd2068d3451a1cd,0xd506a53511a7cd386993,0x35d1adcd686b13571aac,0xcd986c93631b0cd806bd,0x136f1b6cdb06d53691b3,0xccde06ed3751b9cdc86e,0x53811bfcdf86f937b1b,0xc5ce287113871c2ce107,0x7293931c8ce4071d38d1,0x1cece707353991cbce58,0x74d3a51d1ce8874139f,0x11d7ceb87593ab1d4cea,0xe87713b71daced07653b,0xc31e0cf0077d3bd1ddce,0xf307953c91e3cf187893,0x3d51e9cf487a13cf1e6c,0xcf787b93db1eccf607ad,0x13e71f2cf907c53e11ef,0x8cfc07dd3ed1f5cfa87d,0xf53f91fbcfd87e93f31f,0x1d0088013ff1fecff07,0x81940b204d02080d4052,0x20ad050825411207d038,0x83d41d20dd068831417,0x9213d098849423210d08,0xc886142f216d0b085542,0x3b21cd0e086d435219d0,0x11088544121fd0f88794,0x44d225d128891447222d,0xd1588a9453228d14089d,0x145f22ed1708b545922b],#[0x4d1a08cd465231d1888c,0xe5471237d1b88d946b23,0x3dd1e88f147723ad1d08,0x909483240d2008fd47d2,0x246d230915489243d218,0x92d495249d24892148f,0x124fd27893949b24cd26,0xa89514a7252d2909454a,0xb3258d2c095d4ad255d2,0x2f09754b925bd2d89694,0x4c5261d3089814bf25ed,0xd3389994cb264d32098d,0x14d726ad3509a54d1267,0xd3809bd4dd26dd3689b,0x381be1f112459c94e327,0x7c5e0141c0df17820e28,0xe37841be2a4880e06f8,0xf003610285e8be006f8a,0x68a0ef0837c5e0168be1,0xc3e0f1034562f87c1e20,0x7890e8be1f07881a285f,0xc5f17802f1782c61f8ac,0xc0178bc01317c5e06268,0xbe2f0612c62f8bc0178b,0x37841c0d0601bc5e01f0,0x7801828582be1f178018,0x88282057c0120fc206f1,0x5e2f005e2f085e0067,0x8381be2f00de1f005e2f,0xf007e1f005e2f004160a,0x2d87c017864de00e4de2,0xd83c410171bc370f82c4],#[0x403e1f842be2080bc370,0x7e1857c1e2060ca6f10,0x5f1780182a9bc00cf109,0xf10403f1043860f13c21,0xf13c5e03307e2080466,0xc17c215f10404f10430c,0x57c3e0240c470af83c40,0x1506f87c5e0060c0cf18,0xc0140fc5e0082de00906,0x803f1787c01f87c0178b,0xec3e0f10960f10527717,0xc064f106e2f059386205,0x702860430e108180d09,0x6868406840d041c08341,0x103094206820d0418260,0x22020c044a15082a0854,0x183c3078608341]]
def g223H7 := limbs80 #[#[0x88a48062a18014390420,0x1455ca61bea9e330f71,0x2359080000035d400000,0x403a06e530adc4000000,0x1a939b600000219000a9,0xd613f6140019d34c49fd,0xe54449449a4e0522c41c,0x1a2800000001e8251781,0x2998f12fc5b1401100,0x260000010700010e0000,0x8000000000019a000e10,0xb20b57e4]]
set_option maxRecDepth 16000 in
def g223D8 := limbs80 #[#[0xde97254040df17154040,0xf395454040dd97354040,0xeb96458140cf97654040,0x9ef825d9509ed82dd540,0xdf171582509df835d950,0xde5825c650de97258250,0x9ef825d760de5825c460,0xdf97654040f796554040,0xdf7655c440df5655c440,0xdef655c840ded655c840,0xd7d7559440bef8259440,0x9fd8759440cfd7659440,0xd7d75d94409ff8759440,0x9fd87d9440cfd76d9440,0xd7e865d440d7d865d440,0xcfd855d8409ff855d840,0xebd6458140cff855d840,0x9fd8758140bbf8458140,0xfba6458140fb96458140,0xfb88458140efb6458140,0xdf97558140fbb8458140,0xdf97598140dfb7558140,0xbbd84d8140bf98698140,0xd7d7559540bef8259540,0x9ff87595409fd8759540,0x9fd87d9540bf980d9540,0x9fd86dd5409ff865d540,0x9ff805d940dfb805d940,0x9fd85dd9409ff855d940,0xfba5458240fb95458240,0xefb6458240ef96458240,0xdfb8758240df97558240],#[0x9fd8755240d7d7555240,0xdbd7655240f3d6555240,0xbfb8059240dbd7695240,0xbf980d9240cfd7659240,0xbef8259640cfd76d9240,0x9fd8759640d7d7559640,0xbf980d96409ff8759640,0x9ff855da409fd87d9640,0xf795458150b7f8558150,0xefb6458150ef96458150,0xf796558150dfb7458150,0xf795498150f7b8558150,0xbf98698150f796598150,0x9fd87d8150b7d85d8150,0xd7f7655150d7d7655150,0xbf58119150bf98019150,0xbdd8319150bed8219150,0x9fd8719150b7d8519150,0x9ff8759150bfb8059150,0x9fd8799150b7d8599150,0xb7d85d9150bf980d9150,0xbf9809d1509fd87d9150,0xbdd839d150bed829d150,0x9fd86dd150d7d65dd150,0xf7b8059550f788059550,0xb7f8459550f6f8259550,0xbef825d950bfb805d950,0xdfb805d950bdf835d950,0xdef825d9509ff805d950,0x9ff845d950ddf835d950,0xbf9809d950d7f855d950,0xef964582509fd84dd950],#[0xdf97458250efb6458250,0xdf5645c650dfb8758250,0xdf5865c650df7645c650,0xded645ca50df6865c650,0xbfb8059250def645ca50,0xcfd7659250dbd7459250,0x9ff87592509fd8759250,0xcfd76d9250bf980d9250,0x9ff845da509fd87d9250,0xdbd855d060df5855c460,0xbfb8059160d7d845d460,0xefb8059160ef88059160,0xdbf7499160bf98099160,0xbf5811d160afd8699160,0xbdd831d160bed821d160,0xb7d851d160dbd741d160,0x9fd85dd160dbf749d160,0xbef8259560bfb8059560,0xbef825d560d7f7559560,0x9fd84dd560bdf835d560,0xbef8259660bfb8059660,0x9ff855da60d7d7559660,0xdef825d7609ff855d360,0xdf9701c1659ff845d760,0xdef725c165def721c165,0xbdf835c165bef825c165,0xbf5819c165dfb709c165,0xbed829c165def729c165,0xdef72dc165afd869c165,0xdec80dc9659fd84dc165,0xdee80dc965ded80dc965,0x9ff845c365def80dc965],#[0xfbd6454140ff96054140,0xff96558140f7d6554140,0xbfd85d8140ff96598140,0xbff855d940fef8259540,0xff95458240bfd859d940,0xfbf6455240fbd6455240,0xdfd7655240f7d6555240,0xfbe8655240fbd8655240,0xbfd85d9240dfd7559240,0xf7d5458150dfd655d240,0xbff8458150efd6458150,0xffa6458150ff96458150,0xffa7458150ff97458150,0xff98458150ff88458150,0xffb8458150ffa8458150,0xf7d54d8150ff96498150,0xbfd84d8150efd64d8150,0xf7e7655150f7d7655150,0xffb8059150ff88059150,0xfbe7459150fbd7459150,0xf7d6599150f7d6559150,0xf7d655d150bfd8699150,0xbff865d150dfd765d150,0xbfd869d150f7d659d150,0xf7d8459550f7c8459550,0xf7f8459550f7e8459550,0xbfd849d950bff845d950,0xbfd8599160efd6559160,0xbfd859d160bff855d160,0xdfd655d260dfd65dd160,0xbff845c165dff745c165,0xfef8259440bfd849c165],#[0xdfd8759440dfd7659440,0xdfd7654140dfd855d840,0xfbd6458140bfd8654140,0xbff8558140dfd7558140,0xff98458140dfd7658140,0xff97558140ffb8458140,0xffb8558140ff98558140,0xbff8059540dfd75d8140,0xdfd7659540f7d7559540,0xdfd8759540dff7659540,0xdfe8759540bfd8759540,0xbfd80d9540bff8759540,0xdfd765d540bfd87d9540,0xbff865d540dfe765d540,0xdfd865d540dfc865d540,0xdff865d540dfe865d540,0xdff805d940ffb805d940,0xdff855d940dfd855d940,0xff98458240ff96458240,0xff98558240ff96558240,0xbff8559240bfd8655240,0xdfd75d9240dfd7659240,0xfef8259640dff655d240,0xdfd7659640bff8459640,0xbfd84d9640dfd8759640,0xdfd855da40dfd845da40,0xf7d6558150eff6458150,0xbfd8719150f7d8055150,0xdff7459150bff8059150,0xdfd7659150f7d8559150,0xdfd8759150dff7659150,0xdfe8759150bfd8759150],#[0xfbd7499150bff8759150,0xdff7699150dfd7699150,0xbfd80d9150bfd8799150,0xbfd87d9150dff74d9150,0xdfd769d150dfe765d150,0xf7f8059550f7d8059550,0xfef825d950ffb805d950,0xf7f855d950fdf835d950,0xdfc845d950dff805d950,0xdfe845d950dfd845d950,0xff96458250dff845d950,0xffb8059250ff98458250,0xdfd8759250dfd7659250,0xbff8059160dfd845da50,0xefd8059160dff7559160,0xefd7559160eff8059160,0xefc8759160eff7559160,0xefd74d9160dff7599160,0xdfd751d160efd75d9160,0xffb805d160bfd851d160,0xdff755d160dfd755d160,0xdff759d160dfd759d160,0xbfd85dd160dfd75dd160,0xbff8059560dfd85dd160,0xbff8459560fef8259560,0xfef825d560ffb805d560,0xbff845d560fdf835d560,0xdfd84dd560bfd84dd560,0xfef8259660dfe84dd560,0xdfd8759660bff8459660,0xdfd805d360dfd855da60,0xdfd805d760dfd855d360],#[0xdfe845d760dfd845d760,0xbfd841c165dfd741c165,0xfef825c165fef725c165,0xdfd745c165fdf835c165,0xf7f855c165dfe745c165,0xdff749c165fef729c165,0xbfd84dc165bfd869c165,0xdfe84dc165dfd84dc165,0xfee80dc965fed80dc965,0xdfe845c365dfd845c365,0x3780b002080540098000,0xc81fc0718190054812c0,0x83180ba82b409f825808,0x46c10d83f80f083840d3,0xc8164855c14984e012a8,0x41b786a819a863417f85,0x20a87f41ef87781ce871,0x59893023e88cc2218860,0x48a5428d8a18276899c2,0x8b902d68b342c18ad02a,0xce432d8c7830e8bfc2f3,0x3037c8db435d8d483468,0x43c98f003b48e943998e,0x41a90343ff8fd03e68f6,0x739198454910443390a0,0x892ec4ab927048e920c4,0x94304fe93c44e593604c,0x55c54d95005329494519,0xb05a0963c57f95c05629,0xc5eb97785d2970c5b796,0x63a98b461d984860497d,0x8199d8668997464f9918],#[0x29b1c6b99ab069c9a446,0x9c387009bd46e99b786d,0xd7474f9d087349c9c71b,0xa879c9e447839de076a9,0x47ed9f887d49f147b79e,0x834a0ac81fa0508089fe,0x87a1e886aa17c84da108,0x6a32c8bba2c88a2a2548,0xa448904a3ec8efa3908d,0x584951a52093aa4bc91f,0xc89a2a65498ba5f096ea,0xc9efa7a89dea7449c1a6,0xa16a844a09a8109fea7d,0x3ba8e0a30a8a4a21a870,0xaa98ca59a948a4ca90ca,0xaa50a8caa0ca79a9c8a6,0xb4cac9ab08ab8aaa4a9d,0xf0af6abacae5ab80adaa,0x4b1dac60b14ac2cb03ab,0xb52ad24b41acd8b2cac9,0x85ae00b78adbcb61ad60,0xae94b9fae68b94ae2cb,0xaf58bd4af34bc3aee0bb,0xf7cbddaf70bdaaf64bd7,0xa0be6af94be3af88be0a,0x4befafb8becafacbe9af,0xbf8afdcbf5afd0bf2afc,0x1b000bfeaff4bfbafe8,0xab024c07b018c04b00cc,0xb048c10b03cc0db030c0,0x6cc19b060c16b054c13,0x90c22b084c1fb078c1cb],#[0x4c2bb0a8c28b09cc25b0,0xc34b0ccc31b0c0c2eb0b,0x3db0f0c3ab0e4c37b0d8,0x6b114c43b108c40b0fcc,0xb138c4cb12cc49b120c4,0x15cc55b150c52b144c4f,0x80c5eb174c5bb168c58b,0x4c67b198c64b18cc61b1,0xc70b1bcc6db1b0c6ab1a,0x79b1e0c76b1d4c73b1c8,0x2b204c7fb1f8c7cb1ecc,0xb228c88b21cc85b210c8,0x24cc91b240c8eb234c8b,0x70c9ab264c97b258c94b,0x4ca3b288ca0b27cc9db2,0xcacb2acca9b2a0ca6b29,0x835244cb2b2c4cafb2b8,0x203450745e0e20d17878,0x450ee1e2e00d17851780,0x30ce1e2e027851783883,0x1e8f8b8044405042606e,0xf87806a60bc461c3e2e0,0x15c3e110e2198a9a370,0xe20f1054330f83881c66,0x2e0a318438a183c410c3,0x63178783883460bc486e,0xb858e246e145e0e20d14,0x784e163e28966199a138,0x8766185d9a178b818e1c,0xb178b828f10785e2e063,0x8c70645e2e0e10d182e1,0xe0e10d1855178b811386],#[0x915138b83868c81545e2,0x54645e1e2e00da6185e9,0xe2e0a3151917868f8b80,0x6199a178b838434645e1,0x878b8054685e10de2e06,0x158584e2e0e1631e158f,0x2e00c1a17858f8b80546,0xe01c578b80304e326e1e,0x38b809881615030ce1e2,0x126e0e20c1814138f843,0x151857849b838830604e,0x33838854404e1e00ce2,0x305630e0de10c06e0e22,0x6e1e2e00c1b84578388,0x20c1857849b83883060d,0x17128f8b80716e126e0e,0xc0ee10d06e2e01c2e1b,0x88987e2e0180f878b803,0xe1a3e2e01e8f84145783,0x43837868f8b806161526,0x583383884a3e1e2e00c1,0xb818c74403e1e0e21618,0x3e1e2e00c14585433878,0x841d1784398f8b821076,0xb81161071663e1e2e045,0x6e145e2e015145857878,0x16e21517861457838834,0xc1f87883780385e1e0,0x843b831070e06a3e1e2e,0xee1a3e2e0441c600f8b,0x21617868d138b8214685,0x8457891382147e144e0e],#[0xb80304e185e2e015145b,0x60b86c5a3e2e0c41c9b8,0xe00de21b141b87838834,0x518151383886051505e1,0x9b838910605e1a3e2e01,0x450563e1e2e0151a8f84,0x10ee0e20d1b843783885,0x58989784370f8388915e,0x150dc3e10ce0e2262210,0xe2261f8454978b80346,0x84378388545a543e10de,0x3883470ee10de2e00c1b,0x126e0e20d1e940c9b878,0x1c990f8783883461525e,0x78388615c3050de0e1e2,0x60ee1e0e20d145417843,0x26e229180f87809b8830,0x7130f809b88a86c4c3e1,0x809b88306c3e1e026121,0xc60ee1e026e20c183b87,0x1e0e21611138497838b0,0xe2e00c1b843b8b80305e,0x413870f83889870e06e1,0x888e1a504e018e2261c5,0xd0c145460170c9b8387,0x214538388aa345e1e0e2,0x5b8b878034716e1e08d1,0x60605e1e0e20d16940c,0x50de0e218143194378b8,0xe2e01a19878237885c66,0xc9437838860565e1830c,0x8234613c361a6e0e28d1],#[0xde1e0e218170d8a9b87,0x31861e0e218178388604,0x18e01b0e358b838458dc,0xc3787805788501c30de2,0x88345152625e1e0e20d1,0xc315e1e2e00c1c178783,0x20c1b0f84338b8054616,0x870f8388545c3e115e0e,0x7899840566c3e1e21017,0x4198566e1c3e210170f8,0x6665c3e2e0871b870f88,0xe20c14330f8b821d986,0x1b841b0f8b8030603e1e,0x78b8030615c3e1e2e00c,0x644e1c3e0e21618570f8,0xe2e00c18330f878b8054,0x5189b878b8030526e1c3,0x878a184050c03e1e2e01,0x30663e1e286e00c198f,0x4e1e0e2161837878a1b8,0x181b8c57878b80587154,0x783883050644e1e0e216,0x80307e125e2e01517845,0xe1e229151458541b878b,0x1512178f8388a8545e3,0xe215185b8b80304e3e1e,0x38457838830563e125e0,0x60518150d6305e1e0e22,0x4786a3e0e21c55138388,0x218608f8b838454614c5,0x37868f80661c414a3e0e,0x160c15e1e2e0a31d8b1a],#[0x6a3e2e0c41d138388604,0x15186387838834514c58,0x3878b805850563e1e0e2,0x8b80604a301e0e217141,0x5c6150de1e0e218180f,0x32717e0e21e1a96938b8,0xe11a90878b806058da5c,0xf8b8090604c68d62e0c3,0x829060cc62460e2c3e11,0x2127e2e018185e970f8b,0x71060549387830f8870c,0xc043b8b80606a5e0e21,0x7887466564e2e0c3141f,0x1e2e0641f0d942e87813,0x95938b830c5060b65c32,0xc0c34302c3e1e2e01515,0x261180b1430343450d0,0x6308845c20c21180d846,0x1038345630e0c858c206,0x5850e0c3818344230d19,0x43438344098581103841,0x318460304232118105a1,0x60d111436103150e0d0c,0x6250c5b0c9498415452,0x261260d143098383440d,0x10958985809834547256,0x4151218970c316860cc3,0x420e0d08583494326250,0x55898494345160d09143,0x425c30c34970c3250d08,0xc583420d043898303440,0x260d1058943430d06a50],#[0xc260c358984989450e0c,0x4416260a8a84983440e0,0x60e866044e1183498319,0x4244e1180d8984311041,0xa118495104162508549,0x84545056308598c20d0e,0xe8a8450c610e0c389611,0x3094315e124251060310,0x384]]
set_option maxRecDepth 16000 in
def g223H8 := limbs80 #[#[0x18706000061400305,0x40937a0020506041000,0x4882020408208140000e,0x54000050084a05000,0x8010048880c081240228,0x30000102022400300146,0x2040001a3c380041452,0x22cc851404285320010c,0x1c901000450432209000,0xc1881a408020204c000e,0x38a020038b03162004a0,0x80a0c18300144000440,0xc3aac00000010a4553c1,0x312f0dd433800054ef88,0x2bc053b3d9140616b92c,0x21d0000e5200000,0xc8f6bfdcba0003c4f00,0xa81ab85a6430086c1e16,0x17b151534dbac4042493,0x5153483a7022093f1cdc,0x28f3e260000b11eda,0x3f087d432aa9f46a0000,0xb76de927cf1df552c5c4,0x8cec0003c69e66997f72,0xf6591bd8166175a28,0x3765758beb3485207320,0xcb2130e294f290315fb9,0xaa7405d5705a2d20dc4,0xc0008605121eb0e4e3,0x161af0000000e2d7e73c,0x949a000000000014b371,0xcf4f85dd582704cc54a7],#[0x1cf100000000003,0x251c022c00000000,0x425000000,0x48800000000000000000,0x3949282b47b66701a4c,0xb4bb80900,0xa87730303e5589ac2000,0x464281c926651a0001,0x2688a53c00000000,0xede2559a364594a06800,0x91400038fa944763d62e,0x9be4ed29f98cf6cd296b,0xac8d845c000497796f44,0x41e1128406bab2599102,0x28b2a15b2000303606da,0xe000302ff3e4000f3bcd,0xe3e0000b82387856d56a,0x16de400003c851907434,0x1188a1d560411e55b96,0xc63044ac00073a757600,0x1b000028f0347b1adf5e,0xc70814e95517800004b7,0x14c7e4444638dae5a9b8,0x4a8c000b2a8000035af2,0x1487f569849c0044ae,0x2b00000,0x52fc765f2e4f1900,0x3c46a506ceb000,0x4754460cb0000555f6f0,0x2824000000202400035,0x7304000fa5e40ed3109c,0x155e0002c13000098d],#[0x236680b90cfa0ad16a0,0x6089179fac6c3c88,0x8c2000291443312aa000,0xa42b5136a871310001,0x18a00039b800000,0xe420a65c148000c5c800,0x2f1db49399dc8dc81c00,0x28bd0002163e37bc3f4,0xd54264d7d09000397700,0x8252e000000034ea8b8,0x30a10530,0x69644000000000000000,0x380b0000000f4f59a,0x1037a4d8000e222da0,0xb5987000096615b48e00,0x5277155899d270acdc33,0x815280e900246301206,0xe51a438000199809af,0x2a0000000c0480,0x25c4f1c8000862c00,0x2c5ee2f10ea4c154990c,0x16282e67ecf2e2d36757,0x21a72143afab30dca9d4,0x96a800000036f8000,0x67556f094e4198554718,0xe1e910f000388996492,0xc05382d06a4000a1c447,0x824629c0800044a8000,0x63b90c600001951,0x72c9653aedc000000000,0xd0434cbc3b0000000a07,0x35e595c8e00000000001],#[0xd8334000000305fd715c,0xc1fc000d4e0000527245,0x15c000000168fd120a2f,0xa1bf49719a6d93b,0x62ad00020da368c00000,0x146a0000823708,0x3100009c70002d6e0000,0x42c7bda1a4a400000024,0x391b340413aa54f2f,0x5ebcb25f130d851b8000,0xa4d53060ca60000000f,0xaf817d51f8000d1,0xe8d928d0900000000e5e,0xb70002997c52c000d15a,0xb581b0599a0832b0f59,0x83fe55001b4000441c00,0x2ec00082c3e800000000,0x701f71a0000000a,0xbcd3000286100036c800,0xc409590441f1b10d0219,0x69805b53912afdac0002,0xe0003aea259d830b1db5,0xf5b08d7e6fc011820166,0x1381c3609b063047cd86,0x1516119525e7b1599e4,0x2c9d66165abc3458e100,0xd6b0000cfa04bc130b19,0xe7c47700da42c64dc4fc,0x3582f44000009b64,0x1dbeec70ea,0x43428803c00015f2460,0x25bb0000000650c1ba2],#[0xec150c00000eaf5c9200,0x77885a32200008d4055,0x89349fc2c00038f7744b,0x8360193ea19c000a517a,0x36138b6026cc9601358e,0xa385b18402d61148c642,0x9448ad8b6551c3fa5716,0x3c39125406b83260f5f3,0x36c00005d1ce465c,0xc6b1f1c27207d8b7566c,0x30002e070000000e0332,0xf45750e59c90fde5a253,0x3eec298624000f294000,0x44433552b5187b764688,0x51,0xcdfcb10c8685cc583000,0x5f00009250002119d724,0x2710000c9ecc6fd,0x110d806c000440800]]
set_option maxRecDepth 16000 in
def g223D9 := limbs80 #[#[0xd75102f6b90817d5c440,0x8ca13f9d8409faec2057,0x60beae2305ed72942fab,0x5bd74182eeb98c17b5c8,0x7b92cb5f5d460b7ce830,0xd840bfaea207f950102f,0xa07fa60503fcb02817f5,0x2febb2817fdd540bfaea,0xf55240ff2c1205ff7650,0xeb205fd74903df2a481e,0x543fcb02a17f5da40bfa,0x17fdd150efaa8a87fa60,0xfeeca85fd76543beb2aa,0x76942feba4a1fe58250b,0x2c17f5d460bfae8305fd,0xbfee8b06ff645837eb2,0xfd75982feba4c17fdd56,0xbaec17f5d360bfaed305,0x365fdee4b2dff70596fe,0x7ff65103feb28817f5c,0xffb0281ff58140ffaa0a,0x5d540ffecaa07fd65503,0x9207fe76503febb281ff,0x3ffb2481ff59240ffaa,0xff58150ffecb207fd659,0xac8a87fc64543ffb02a1,0x4543ffb22a1ff99150ff,0xa1ff5d950ffce8a87fd7,0xffec9287fd64943ff3b2,0xc74583ff322c1ff59160,0xa2c1ff9d160ffae8b07f,0x60ffaeab07fd65583ffb],#[0xffc70597feb2cc1ffdd5,0xfb82cbff9c165ffae0b2,0x7102c81040520148003f,0x3f61c40ca059026810b0,0x18d8b9056828413108ac,0x48ae4271fb8f1c712359,0x82c99570a584fc266125,0x6cdd66b433e9918c1e5d,0x5e4101fc0f807893ac9c,0x6bd2e2941488a34d12a8,0xb075612a2d4b6a244f32,0x31d186cbf15dd2df167c,0xdda6ce3541a24ce2659,0x63d39e04ecb74a393dc3,0xd70a6837c0e2002fca7c,0x3348be3f11b38b7446e1,0x7ed3b19b64cd65ef2a49,0x38b8f084c4245a3cd0d2,0x868509871601b185c580,0xd871601b1e10b8b0041,0x1600e284878b09014284,0x1c6098f106c2406190f,0x198f086c0206198c362c,0xe2c030cc784304c5807,0x68c0984362c03860817,0x7862e0c43468d0f1601,0x2e2c01070c170e2c0346,0x82634d84660c4415c784,0xc38b0118d361c58060c1,0x647871601830c0c8c70d,0x716018326c6330e2c030,0x1b1958b84262c0426c78],#[0x2c11060a3b0a3c58220e,0x460d8f0e2c030646170e,0x8f0e0c41070d170e2c03,0xc112a61b87062864958b,0xe2c038c4a9b0e0c43470,0x1a5c38b00d1c604c2386,0x38870c0d30dc38310e18,0x4d870621a3054d0c6e0c,0x60c5530c86130e0c4405,0x21e1c18820e1b0c3c580,0xc0346c784362c03062a3,0x40d8c661c58081984362,0xa9057186c2331601c28,0x87062464040d8c661c58,0xd1b1e1c58060c182052b,0x6c38311032361c18868,0xb6319871600c395098c6,0x46070b10361478311820,0x430f1602e30549861e0c,0x1c42429587870620c3c6,0xb026883980c9a2e2c185,0x9a2e1c18868c222e1478,0xc1ca84c69b0e0c43088c,0x23c38b0130d1e1c18930,0x18cc38b02620c268b106,0x91a61c370e2c03088b11,0xc58130c19363c38b00c1,0xa8c982e1c58220e231e1,0x82d0d3230d87105c110,0x851c4221a3c2171604d1,0x28f16088987309a2e2c1,0x2b152844d870621a4c5c],#[0x62183c54b870624c347,0x86a5c38b043286c3c29b,0x992c3c38310c20296889,0xd1e20d4b861e0c49881a,0xe0c43460e3130ec38310,0x3c34a9b061c43472c9b0,0x58700c24b25c3831261a,0xc587026183160c15343c,0x52d131a509871600c5c3,0x95470c206c38310c2429,0x887c618223c2971602a4,0x787062183958d8f08cc1,0xc94263c38b01520ac6c,0x508622a50d13160c28cb,0x8a8e552c61b811e1c441,0x8b061471090c970a3c18,0xa0f0a4c580c12622a50d,0x8c94c431b83161206064,0xc106128c8d0f160c2909,0x64a0f0a4c580]]
set_option maxRecDepth 16000 in
def g223H9 := limbs80 #[#[0xa00014444c0004c0213,0x8210100c120c0b8141e,0x18100400002000f850,0x18642800018040a00020,0xe0082004090280028060,0xa0f03828501702028201,0xc021c0083000002d0000,0x8440409010140a8d0381,0x480c02010a02c18151e,0x70a0008800000100208,0x64044480440000402012,0xa400452280c0c0119808,0x20302c05040282405010,0x10d004305a000405c450,0x44b0808c3e0f0e870120,0x23800000000006434001,0x56927e22922e4b1b16e2,0x8000285b889867fa304c,0x728b6ab367b6c6ce4b,0xd2000496000000000002,0x769521a6000089a00002,0x6b6260667a000100381d,0x578e71c658c05b5de973,0x160858122b0400018616,0xc987e5ec15960bd947e4,0x5c680a00760001179723,0x57e177d6108cb253a082,0x171e30784a5b5cac9bc8,0xf9df6c1d3472dce42800,0x6f800009af8ee0004106,0x7485429dcdf80726a3ed,0x5e09e305716833b9c128],#[0x421089210322d2184878,0x50896822275ee06de4c0,0x6df00a00011fc00059,0x365f4a4257284d85f030,0x7d29bc14a82a7c08dd53,0xe81f1084306feb51ab9a,0xb62ef78d26089248bda6,0x88c62a7da2ac5e2fe6c4,0x174b02af6c37d7c863e,0xdd947e740749ae996b61,0x188f000003eb59,0x93d0a120b3a01c320000,0xda8670004e480341dd3c,0x98d2e4de111e188ad628,0x141eb20001783599b805,0x79a4d0000000259ec16f,0xdb4c0f14a2907088649a,0x20f6c8a21c89cf61f216,0x858b0b47d8653c274945,0xb6ee3eaf40d72c95a749,0x8711806f908e97adc066,0x4c9caa79a0e970a452b9,0xeee1480000000001f780,0x1d2f0000c10ba720003d,0xcb28000a766586000000,0x13d3c131dd03abd73,0x28dd06672b1b6459de60,0x1caf0c08a7e0001a7c88,0x2ee00001fbea0c84e26e,0x9462dc75dc832cc8a27,0x416514c38798000411e4,0x931d41f372565dabd820],#[0x244ab06a4500428e7a98,0x8903e8a8c2eb534fab46,0xca09e333aa0e1a226810,0x9b822437712c65825,0xf96bee45443b092922e0,0x889eca2060238fd21faa,0x49410c4000004b77528f,0x24c044e4b7b1da3d0000,0x300010a2b27120d2138c,0x39140005a0e000000009,0xd85130607a207e8af41c,0xf0000545206d58e40002,0xf421ea6265f8000aa13a,0x32ec9f2d237121e8356b,0xac89875b1563f1be9c3,0xb8e5b0b6848400032eda,0xf13e027800061d69be5a,0x15472654e650a2a63c,0x131af08d40000001a6a0,0x4e7894cf6aed5e40ab4a,0x2092234eb10001ca941e,0x10321445a79ca0005918,0x2bc453168001d1650c20,0xace7e59aa1e16f59a5c3,0x974c0e5a936606a8d84e,0x78e2058a2e5354ff62eb,0x1e5ae1ee43dc864e5205,0x4b0fda7f3358ddc44b97,0x2c0e1c84cf0e7cc21cd4,0xab8ac0001191e0eba872,0x4247b90f8b6ac64c1d1a,0x8ff72052f2a385cbf5ae],#[0x3aa95e2fd437f4423bd2,0x80003547ec7f85f629c2,0xe6b811c255c00c481d85,0x768adec0dc202d98992a,0xe1894a318001e6ae198e,0xfb27a52e60b2389aaa27,0xb0600061227648588089,0xe1ec801dfaa76af56746,0x420549c40002964450c2,0x2492402e2ae323220e4e,0x71e22986342be531768b,0x91fa0cc67b21a801ce,0x1056aa9e27fb64000,0x1971dd9a20539c92784,0x2e058d1cdf134cb80002,0x1a6ce5128b93d,0x236a90eb32a0121ad800,0xb0580200070be63a0acf,0xa000116600001c880014,0x46f26a6f1760003a65d6,0x218209aa4163c2a95462,0xa750a8fb12d9540003,0x269b0a67696615222c80,0x67ae6136adc21aa14658,0x6088118c3dae20000000,0x67457ab46831ca06b11c,0x11a092f4a2e6c4684c3,0x1f878000000]]
def g223D10 := limbs80 #[#[0x50ff543fe40ff503fc40,0xff60ff983fd60ff183fe,0x89c1b036003ff65ff597,0x108829da6a9745110834,0x233218a02060e31618a0,0x8881858e18a01071851,0x3038a180420614434386,0x873050e31a18a0109185,0x68e18a01081631848608,0x8211c51238608861c530,0x51038628061c51060e2]]
def g223H10 := limbs80 #[#[0xc4000200011080edc68f,0x4003064828104009805,0x82d67fdc000d67861709,0x1a4953715b87696b46a7,0xaa80c6e000a64a04aaa2,0x106600000118da2,0x1f24a44a842308b0,0x3c23eb8a1df0060bb1c2,0x1299e24001c37275d2,0x2f8ba001c76f9e000000,0xe052b4200020d67c2614,0x26a48ac6d5b5e1f00843,0x40001c26c90f658b6000,0xb4876433b2000000a8ea,0x28308ca0e001497e5fdb,0x83016b72a7bd33d90e06,0xd14543bb8eea3b84cad5,0x1e4d19d57e688e4849,0x1fb6a7363c000a02eb2,0xca144efa344ae286a40,0x85c586330001c5001000,0x19c9f89b839854e71832,0x38620011ad0a8e47a208,0xe1425bc58001780001a1,0x1d54000293f6fe57,0x4000a797920014af0680,0x23]]
def g223D11 (j : Nat) := if j=0 then 0x3088027f else 0
def g223H11 := limbs80 #[#[0xcc0000000,0xa0000050,0x2b000,0x48000c000054c0000000,0xd78,0xe7002d4004500680000,0x9a00388e340f480,0x8100]]
def g223L : Nat → Packing
  | 6 => (44,5,5,0,0,9,0,g223D6)
  | 7 => (458,4,5,0,0,13,0,g223D7)
  | 8 => (404,3,5,0,0,14,0,g223D8)
  | 9 => (94,2,5,0,0,13,0,g223D9)
  | 10 => (11,1,5,0,0,10,0,g223D10)
  | 11 => (1,0,5,0,0,0,0,g223D11)
  | _ => emptyPacking
def g223I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 13 79 5 11 6 1 g223H7
  | 8 => lookupWord 140 769 7 14 9 1 g223H8
  | 9 => lookupWord 135 619 9 14 9 1 g223H9
  | 10 => lookupWord 31 157 7 12 7 1 g223H10
  | 11 => lookupWord 4 67 0 9 4 1 g223H11
  | _ => fun _ => none
def g223 : Forest := ⟨223,11,fun i => g223Y[i]?.getD (0,0),g223C,g223A,g223L,g223I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_0 : CutRow g223 6 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P6_2 : CutRow g223 6 2 42 := by
  apply polarBlock (data:=fun _ => (word80 [0x80004021180,0x44630020028150a20950,0x20028150a209500041,0x2094486122108000402,0x11804463002004022102,0x9500020028160a20950,0x410209448612210200,0x34020902121001001280,0x44b00932010404030110,0x48200a01040211805453,0xa10402410215200041,0x2094486122100208402,0x21800954010014030110,0x9410300140241100921,0x1001403011009410041,0x2094486122100610402,0x50412400041020b0086,0x12600284040205084431,0x41020b008612600304,0x4020510483102880283,0xa88440028404020508,0x44300064140241044360,0x14102094486125000c1,0x209448612500041020a,0x4861250004102094486,0x12210064140045044340,0x60828160a20b100061,0xc02434126000410402,0x5041260006410a1502c,0x4330006410a1502c4350,0x8000402118044620041,0x4024104122000410402,0x41041220004104024104,0x12100100140205100930])) rfl
  decide +kernel
theorem g223B6 : CutRow g223 6 0 44 := (@joinRow g223 6 0 2 42 g223P6_0 g223P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_0 : CutRow g223 7 0 3 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_3 : CutRow g223 7 3 48 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_51 : CutRow g223 7 51 8 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_59 : CutRow g223 7 59 21 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_80 : CutRow g223 7 80 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x4800a1,0x502c8251004800a1502c,0x82510800040211804464,0x210402410211300800,0x4021180446408000402,0x11804464080004021180,0x44640021040241021130,0x6410a1502c43610800,0x40211804474006410a1,0x502c4341004800824024,0x8250030500190c165842,0x30500190c1658620800,0x4021180447300480080,0x44248250004800804424,0x8250030500190c165862,0x8000402118044730044,0x4030104423000410402,0x5041270006100c02434,0x12700041040205041270,0x30500190c1658420064,0x10a1502c4330004400a1,0x502c4230004400a1502c,0x42300064140301044330,0x6410a1502c43300044,0x40301044230006410a1,0x502c4330082504024102,0x51400021040241021140,0x30400190c1648430064,0x10a1502c4341004400a1,0x502c4230004400a1502c,0x42300020840221020920,0x208402210209200020,0x828160a2092000208402,0x21020920002084022102,0x9200020828160a20920,0x208402210209200020,0x84022102091000410402,0x41041230004104024104,0x12300041040241041220])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_128 : CutRow g223 7 128 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x2080203,0x4a29053002800824022,0x81500041040245041260,0x20820120a209301000,0x2011180847410000080,0x49208274010012094492,0x9520041040241041251,0x410402410412510041,0x402410412510208020a,0x4a290540020828160a2,0x9300028028240a28150,0x6410a1502c43610041,0x4030104126100410402,0x45041260004404024104,0x42610064140241044351,0x410209448612300041,0x4024104123000410402,0x41041230004102094486,0x12301000120945828174,0x410402410412600041,0x4024104126002850402,0x50854710028020b04a2,0x81740021040241021140,0x6410a1502c43610800,0x4021180447400210402,0x410211400208020b04a2,0x90540020828160a20930,0x208000a042290530a04,0x4020520516302001402,0x5201163004400a1502c,0x4230006410a1502c4361,0x6410a1502c43510285,0x4030108545200410209,0x44861241002104024102,0x11400028008240228170,0x6410a1502c437100a1,0x440241021530082030a0,0x58a84374006410a1502c,0x43510200140205201173])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_176 : CutRow g223 7 176 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410402,0x41041220028504020508,0x54510285040205085451,0x2850402050854510044,0xa1502c425002850402,0x5085451004104024104,0x12200285040205085451,0x4400a1502c42500044,0x4020504425000410208,0x44861230006100c02434,0x12500041040241041230,0x208000a042290530141,0x2094486122000c10209,0x448612200048028144a4,0x8260030500190c165842,0x30500190c1658420285,0x4020508545102850402,0x5085441004400a1502c,0x42400041020b00861260,0x41020b008612600305,0x190c16584202850402,0x5085451028504020508,0x54510284040205084441,0x2840402050844410285,0x4020508544100641402,0x41044360006414024104,0x4360004400a1502c4261,0x641402410443610044,0xa1502c4251004400a1,0x502c4251004400a1502c,0x42400041020944861231,0x410209448612310285,0x4030108546200410402,0x41041231004102094486,0x12310041040241041231,0x410402410412200800,0x4021180447400410209,0x44861241080004021180,0x44740041040245041230])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_224 : CutRow g223 7 224 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x808001a,0xc86c0540020028340a2,0x81600028028340a28170,0x30500190c1658431000,0x82502887510000201,0x11808475010800190c16,0x88630041020944861231,0x410209448612310041,0x4034104124100410209,0x44861231004104024504,0x12300048008340248251,0x280283402281500064,0x10a1502c436110000019,0xd269074028504030108,0x54520141020944861261,0xc10209448612611001,0x2814580907400640403,0x1044240006404030104,0x42400100140301100952,0x1001403011009520305,0x190816584202000402,0x5201163010014030110,0x9520300101848160932,0x1001403011009520064,0x14024104436102850402,0x5085451004102084486,0x12410041040301041251,0x410403010412510028,0x2824022814008205402,0x11804575006414030104,0x43611000128045208174,0x10000008250288741000,0x2011180847400410209,0x44861231004102094486,0x12310285040301085462,0x410402410412310208,0x20b0422905400280282,0x40228150006414024104,0x43610285040205085451])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_272 : CutRow g223 7 272 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x200402,0x21020960004102094486,0x12210041020944861220,0x4102094486123100a0,0x828160a20d2000a08281,0x60a20d2000a084022102,0xd2000a0828160a20d20,0xa0840221020d200800,0x4021180446400410209,0x448612310a0104021180,0x546400a0828160a20d20,0xa104024102153000a0,0x840221020d2000410209,0x44861221004102094486,0x12300041020944861220,0x450403010452410041,0x2094486123100410402,0x410412310020028160a2,0x9600041040241041221,0x410209448612200041,0x4024104123100a08281,0x60a20d20028504020508,0x54510285040205085451,0x410201448412300064,0x10824024436101410402,0x4104123100c104024104,0x12310200140301201153,0x414402410416310200,0x4020920127301001403,0x11009520a0104021180,0x54650a01040211805465,0x1001403011009520041,0x20340841241006410a1,0x502c4351004104024104,0x12310064140301044351,0x641082402443610141,0x2094486123101410209,0x4486123100c102094486,0x123100c1020944861231])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_320 : CutRow g223 7 320 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x641403,0x104434100a414030108,0x45410041020944861261,0x10000209458290650100,0x128144b00952004400a1,0x502c4230004400a1502c,0x42400100128144b00952,0x8000402118044740100,0x128340b0095201001281,0x44b00962004400a1502c,0x4240004400a1502c4240,0x4400a1502c42400044,0x40301044230004400a1,0x502c4240004400a1502c,0x4240004400a1502c4240,0x440403010442300044,0xa1502c4240004400c1,0x60344230004400c16034,0x42300084040301084430,0x840403010844300084,0x4030108443000480203,0x40848251006414030104,0x4341006410a1502c4341,0x30500190c1658420044,0xa1502c426100641403,0x1044341006410a1502c,0x43410064140301044341,0x80800a250a8c0540064,0x10816024434100200402,0x21020960006410816024,0x43410020040221020960,0x200402210209600020,0x28160a2096000410209,0x44861231002004022102,0x9600800040221804864,0x410209448612310041,0x209448612310a010018,0x2c8658640020028160a2,0x9600a0100182c865864])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_368 : CutRow g223 7 368 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x208281,0x60a20920004102094486,0x12300041040241041220,0x20828160a209200020,0x828160a2092000410209,0x448612310020828160a2,0x9200020828160a20920,0x410209448612310285,0x4030108546200410402,0x41041231004102094486,0x12310100128144b00962,0x8000402118044740044,0xa1502c424008000018,0x2c864864002004022102,0x960080000182c864864,0x200402210209600041,0x2094486123108000018,0x2c864864004102094486,0x12210041020944861220,0x410402410412200800,0x4022180486308000402,0x1180446400a084022102,0xd200800040211804464,0xa0840221020d200041,0x2094486123108000402,0x11804464004104024104,0x12200800040211804463,0x4400a1502c42610041,0x2094486123101001281,0x44b00962002800824022,0x81500041020944861231,0x410209448612310041,0x2094486124108000402,0x118044740028028340a2,0x81500020040241021160,0x641403010443610041,0x20844861230004400a1,0x502c4241020030c06812,0x12100064140301044341])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P7_416 : CutRow g223 7 416 42 := by
  apply polarBlock (data:=fun _ => (word80 [0x20828160a2,0x9200041020944861231,0x410209448612310800,0x4021180446408080002,0x1088c054080800021088,0xc0540825040241025130,0x410209448612210020,0x828160a2092000208201,0x20a209300808001a0c86,0xc0540020828160a20920,0x410209448612310285,0x4030108545208250402,0x41025140004102094486,0x1231080800a250a8c054,0x20c28160a209200041,0x2094486123100410209,0x44861231080004021180,0x44640825040241025130,0x8250402410251300825,0x4024102513002850403,0x10854410020a28160a2,0x9200825040241025120,0x20a28160a209100825,0x4024102516008250402,0x41025160004102094486,0x12310020028160a20960,0x20028160a209600020,0x28160a2096000200402,0x21020960004102094486,0x12210020028160a20960,0xa0828160a20d2000a0,0x828160a20d2000410209,0x448612310a0104021180,0x54640041020944861221])) rfl
  decide +kernel
theorem g223B7 : CutRow g223 7 0 458 := (@joinRow g223 7 0 176 282 (@joinRow g223 7 0 59 117 (@joinRow g223 7 0 3 56 g223P7_0 (@joinRow g223 7 3 48 8 g223P7_3 g223P7_51)) (@joinRow g223 7 59 21 96 g223P7_59 (@joinRow g223 7 80 48 48 g223P7_80 g223P7_128))) (@joinRow g223 7 176 144 138 (@joinRow g223 7 176 48 96 g223P7_176 (@joinRow g223 7 224 48 48 g223P7_224 g223P7_272)) (@joinRow g223 7 320 48 90 g223P7_320 (@joinRow g223 7 368 48 42 g223P7_368 g223P7_416))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_0 : CutRow g223 8 0 14 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_14 : CutRow g223 8 14 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_62 : CutRow g223 8 62 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_110 : CutRow g223 8 110 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_158 : CutRow g223 8 158 34 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_192 : CutRow g223 8 192 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_240 : CutRow g223 8 240 15 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_255 : CutRow g223 8 255 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x2850403,0x1085452004104024104,0x1231004400a1502c4251,0x410209448612410044,0xa1502c425101040019,0xc164853028504030108,0x54520041040241041230,0x410402410412300044,0xa1502c4240004400a1,0x502c4240082504024102,0x51400021040241021140,0x4400a1502c42510044,0x40301044240006410a1,0x502c4351006410a1502c,0x4351006410a1502c4351,0x6410a1502c43510064,0x140301044351006410a1,0x502c4351006410a1502c,0x4351004400a1502c4251,0x4400a1502c42510064,0x10a1502c435108250402,0x410251400808001a0c86,0xc0650021040241021140,0x210402410211400021,0x40241021140006410a1,0x502c4371006414030104,0x4351006410a1502c4351,0x4400a1502c42400064,0x14030104434003050019,0xc165842004400a1502c,0x4240004400a1502c4240,0x4400a1502c42510044,0xa1502c425103050019,0xc165853004400a1502c,0x42410808001a0c86c065,0x208000a042290640020,0x84022102093000208281,0x60a20930002084022102,0x9300020840221020920])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_303 : CutRow g223 8 303 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400a1,0x502c4251004400a1502c,0x4251004400a1502c4251,0x4400a1502c42510044,0xa1502c4251004400a1,0x502c4251004400a1502c,0x4251004400a1502c4240,0x4400a1502c42400044,0xa1502c424000641403,0x1044351006414030104,0x43510064140301044351,0x641403010443510041,0x2094486124100410209,0x44861241004104024104,0x12310041040241041231,0x410209448612300041,0x2094486124100410402,0x41041241006414030104,0x4351006410a1502c4351,0x410209448612410305,0x190c16585300410209,0x44861241004802030084,0x82610064140301044351,0x641403010443510048,0x203008482510208000a,0x4229064028504030108,0x54520208000a04229064,0x6410a1502c43510064,0x14030104435100641403,0x1044351028504030108,0x5462030500190c165853,0x208000a042290640041,0x2094486124100480082,0x40248251004104024104,0x12410041020944861241,0x410402410412410044,0xa1502c4251004400a1,0x502c4251004102094486,0x12410041040241041241])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_351 : CutRow g223 8 351 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x641403,0x10443510020828160a2,0x9300041020944861241,0x2850403010854520041,0x2094486123100410209,0x44861241006414030104,0x43510825040241025140,0x410209448612310041,0x2094486123100410209,0x448612310020828160a2,0x9300285040301085452,0x20828160a209300020,0x828160a2093000410209,0x448612410020828160a2,0x930004400a1502c4251,0x410209448612410041,0x2094486124102850403,0x1085452004104024104,0x1231004400a1502c4251,0x4400a1502c42510044,0xa1502c425102850403,0x1085452004102094486,0x12310041020944861231,0x410209448612300285,0x4030108545200410209,0x44861231004102094486,0x12410064140301044351,0x410209448612410064,0x140301044351004400a1,0x502c4251006414030104,0x4351004400a1502c4251,0x641403010443510044,0xa1502c424000410209,0x44861241006414030104,0x43510041020944861241,0x4400a1502c42510044,0xa1502c4251004400a1,0x502c4251004400a1502c,0x42510064140301044351])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P8_399 : CutRow g223 8 399 5 := by
  apply polarBlock (data:=fun _ => (word80 [0x4400a1502c42510044,0xa1502c425100410209,0x44861231004102094486,0x12310064140301044351])) rfl
  decide +kernel
theorem g223B8 : CutRow g223 8 0 404 := (@joinRow g223 8 0 192 212 (@joinRow g223 8 0 62 130 (@joinRow g223 8 0 14 48 g223P8_0 g223P8_14) (@joinRow g223 8 62 48 82 g223P8_62 (@joinRow g223 8 110 48 34 g223P8_110 g223P8_158))) (@joinRow g223 8 192 111 101 (@joinRow g223 8 192 48 63 g223P8_192 (@joinRow g223 8 240 15 48 g223P8_240 g223P8_255)) (@joinRow g223 8 303 48 53 g223P8_303 (@joinRow g223 8 351 48 5 g223P8_351 g223P8_399))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_0 : CutRow g223 9 0 14 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_14 : CutRow g223 9 14 39 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P9_53 : CutRow g223 9 53 41 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B9 : CutRow g223 9 0 94 := (@joinRow g223 9 0 14 80 g223P9_0 (@joinRow g223 9 14 39 41 g223P9_14 g223P9_53))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P10_0 : CutRow g223 10 0 11 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B10 : CutRow g223 10 0 11 := g223P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223P11_0 : CutRow g223 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g223B11 : CutRow g223 11 0 1 := g223P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223T : mixedTables g223 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g223 0 0
  · exact mixedEmpty g223 1 0
  · exact mixedEmpty g223 2 0
  · exact mixedEmpty g223 3 0
  · exact mixedEmpty g223 4 0
  · exact mixedEmpty g223 5 0
  · exact g223B6
  · exact g223B7
  · exact g223B8
  · exact g223B9
  · exact g223B10
  · exact g223B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g223G : graphValid g223 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low223 : Lower true (varsX 223) (graphGoal 223) 12 := mixedLower (g:=g223) (i:=0) (hints:=16778819) (before_sound K191 V191) g223G g223T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K223 := extendKnown K191 12 [(223,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V223 : Known true K223 := extend_ok (m:=223) V191 low223 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffee14261209cb86,0xf69000001f00000003ff])),(BitVec.ofNat 152 (word80 [0x52028a142602098384,0x269094a5294a5294a529]))),((BitVec.ofNat 152 (word80 [0xff000ac14f891c329f,0xb8040003e00001f00000])),(BitVec.ofNat 152 (word80 [0x640cca414f8114329f,0xb800739ce739ce739ce7]))),((BitVec.ofNat 152 (word80 [0x1f66cba280825a,0x622007c00003e007c00])),(BitVec.ofNat 152 (word80 [0x78171e464b2280825a,0x202318c6318c6318c63]))),((BitVec.ofNat 152 (word80 [0xffffe44b1363d60d92,0x11800f800007c00f801f])),(BitVec.ofNat 152 (word80 [0x801804431160960812,0x10002108421084210842]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x10ab09d24965c,0xc850000000f8000fffe0])),(BitVec.ofNat 152 (word80 [0x200108809d001400,0xc8414a5294a5294a5294]))),((BitVec.ofNat 152 (word80 [0x2954164680021,0x2cfbf00000fffff00000])),(BitVec.ofNat 152 (word80 [0x4000900000680020,0x4b08421084210842108]))),((BitVec.ofNat 152 (word80 [0x19700c0c937420,0x430dffffff0000000000])),(BitVec.ofNat 152 (word80 [0x800120000c004400,0x410d0842108421084210]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(4,0,235,0,9),(128,0,111,0,9),(1,0,238,0,8),(2,0,237,0,8),(8,0,231,0,8),(32,0,207,0,8),(64,0,175,0,8),(0,2,45,192,7),(9,0,230,0,7),(34,0,205,0,7),(68,0,171,0,7),(6,0,233,0,6),(10,0,229,0,6),(12,0,227,0,6),(33,0,206,0,6),(40,0,199,0,6),(64,2,45,128,6),(66,0,173,0,6),(96,0,143,0,6),(38,0,201,0,5),(44,0,195,0,5),(65,0,174,0,5),(68,2,41,128,5),(70,0,169,0,5),(72,0,167,0,5),(73,0,166,0,4)]
def g239A : List (List Nat) := [[]]
def g239D5 (j : Nat) := if j=0 then 0x3b418754d814c950 else 0
def g239D6 := limbs80 #[#[0x40a64a87d054d814c950,0xa1f095450d32543e82a7,0x51534c950ba4caa86992,0x1543ea2e8a9a62a85d2e,0x1b9b02992a1f519454d3,0xa64a86f861d814c950fe,0xf897450d32543f86e740,0x534c950fa4ba2a6992a1,0x43e930ea9a64a87d2651,0xa6e6992a1f4954dcd325,0x6a85f2653734c950ee4b,0x97355143543e32e8a9a8,0x54d50eacba6e6a9aa1f1,0xb58a1ccc3c005d665373,0x30b82bfdf2f376b9dc2d,0x8d069acbe53238ec5e2,0x5ac2b4f84415d8d84c6f,0x8182178468215469e10c,0x609de11a0]]
def g239H6 (j : Nat) := if j=0 then 0xe else 0
def g239D7 := limbs80 #[#[0xf49534c950f51534c550,0xbc5839c532bc7835c532,0xfe1814c950f71544c550,0xfc9434c950fe2814c950,0xf69544c950fcb734c950,0xf395450d50f595350d50,0xf5b7354d50b798550d50,0xf3b7455150b7b8454d50,0xfc5535c532f555454d31,0xde5755c532fc7835c532,0xf8d5450d32fc5539c532,0xf4d5454d32bcd8550d32,0xf1d5454d43bcf8454d32,0xfe9744c950ff1744c550,0xfd97350d50fe9874c950,0xbf98750d50fb97450d50,0xf798454d50f797454d50,0xdf9745cd50f79545cd50,0xdf974dcd50f7954dcd50,0xbfb835d150bf984dcd50,0xfcd8454d32fd58454d31,0x44b07f0c01341d01b000,0xd143250434790db1902c,0xf73c0724db1a33085c4a,0x4d89a53324b470885051,0x8a053f27b4f09d53926f,0xe11a93520a354528750,0x43a464d38472ca7e519e,0x3845840d48e117128109,0x5a7a319e0e165a41ca52,0xc2e1692d185f0b8540d0,0x15511570b1b84d0516c6],#[0x2f1949a46784d05422de,0xc4b8780bc618a715e1e0,0x545181202e0e1a418569,0xe65e1e018159c938384,0xc88e1e0651ca78780644,0x1330112384c0504c7180,0x966152b2384c050548e1,0x14159b86205040d48e1a,0x1a46223845051866e188,0x1917878220688e114181,0x31c]]
def g239H7 := limbs80 #[#[0x10,0xc2000000,0x0,0x0,0x138000000000000000,0x0,0x1,0x81ac00154000,0x0,0x0,0x248000,0x142000000,0x0,0x2400000000c000000000,0x5a9d6110000001,0x0,0xf7eb52600000,0x3cc000000000000,0x62800000000002640,0x3a00,0xe700]]
def g239D8 := limbs80 #[#[0x932543f918aa1fc4c550,0x9a63de55150ef2a6a87e,0x32fcce2997e5714cbeaa,0x7f950503e6a9a65f350d,0xfba2a1df55150bfaeaa0,0xcd50ff2e6a87f943542f,0x98ffb74543fcba2a1fed,0xbf6b8a65fb4c951feaa8,0x754d43fdaea997ed544c,0xa8a9dfd7550fdeaa287f,0x54ffeba2a17fdd153efa,0x84788ba0ea130007fd74,0x3fa41406730d51882be4,0xbf97a0e65adb245ccabd,0xeaa148274cb992119e1b,0x92360c264abf77d6df58,0x30b06148a454709627ca,0xa41e12033434a48d85a1,0x212c38148c08c90d3830,0x82988f94608c1853100b,0x14106e15320446c24612,0x41861a4a08c298753844,0x382410563c34d870081c,0x2587029903151c1c192c,0x32f20383c2970482a395,0xc460c26472a9d1c2c382,0x9d2a305830a42a4274a8,0x526458c5520ec38148e,0x43191d3614b824100b0e,0x86429602c940a30c7a23,0x81584a0ca64616450517,0xc6311f088c09878e8d84],#[0xc961c12088f86460243,0x81cc29c38094818c0f0e,0x1d283918701]]
def g239H8 := limbs80 #[#[0xe840000000000000a453,0x0,0x2d20000000000f7755,0x0,0x0,0xf9451000000008500000,0x203,0x6580000549d2800,0x22c00000000011716000,0x248842e21650000244,0xe3c0000000,0x186000000000000213,0x550000025b,0xb30000019e0000000000,0x18e0000000000d6a29,0xca1a700000,0xd34a4000000000000000,0xf7266001c200000,0x1e3,0xa7f6081c0000000]]
def g239D9 := limbs80 #[#[0x32fd8c7f531fe943f950,0xfd31ff543fd40ff443ed,0x3fd54ff54ffd43ff547,0xa54240f6692a11454180,0x8484948d0423fe3919eb,0x83cd2c10904523430102,0x4ca5309034301240819,0x8c4c301070d01309080a,0x10924202aa3214c10903,0x4c244078c3d04c10a234,0x930242b03214c109038c,0x510]]
def g239H9 := limbs80 #[#[0x1c00000900010,0x7600000004a0100,0x7700003ba00,0x1da6e00001e4,0x180,0xb0d00000c3800007e000,0xf000000000000028800f,0x16,0x1cc00004200,0x80001638880000000000,0x25400000066a260085,0x5400748000000,0x0,0x119f6000,0x1f922000]]
def g239D10 (j : Nat) := if j=0 then 0xc940402ff else 0
def g239H10 := limbs80 #[#[0x35400186a9f640000002,0x321080000c0000000000,0x1900000000000ee700,0x3cc00000384000]]
def g239L : Nat → Packing
  | 5 => (1,5,5,0,0,0,0,g239D5)
  | 6 => (21,4,5,0,0,9,0,g239D6)
  | 7 => (42,3,5,0,0,11,0,g239D7)
  | 8 => (31,2,5,0,0,11,0,g239D8)
  | 9 => (13,1,5,0,0,9,0,g239D9)
  | 10 => (1,0,5,0,0,0,0,g239D10)
  | _ => emptyPacking
def g239I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g239H6
  | 7 => lookupWord 5 179 1 9 5 0 g239H7
  | 8 => lookupWord 10 157 2 10 6 0 g239H8
  | 9 => lookupWord 7 127 1 9 5 0 g239H9
  | 10 => lookupWord 3 37 2 8 4 0 g239H10
  | _ => fun _ => none
def g239 : Forest := ⟨239,10,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P5_0 : CutRow g239 5 0 1 := by
  apply polarBlock (data:=fun _ => 0x1000220025808231) rfl
  decide +kernel
theorem g239B5 : CutRow g239 5 0 1 := g239P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P6_0 : CutRow g239 6 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P6_5 : CutRow g239 6 5 16 := by
  apply polarBlock (data:=fun _ => (word80 [0x48020300848230,0x480203008482300048,0x2030084822000480203,0x848220004802030084,0x82300048020300848230,0x480203008482200048,0x2030084822000480203,0x848220004802030084,0x82200048020300848220,0x400420110c024401000,0x22010980825310002201,0x980825200880112884c,0x842000880112884c8420])) rfl
  decide +kernel
theorem g239B6 : CutRow g239 6 0 21 := (@joinRow g239 6 0 5 16 g239P6_0 g239P6_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_0 : CutRow g239 7 0 4 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_4 : CutRow g239 7 4 22 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P7_26 : CutRow g239 7 26 16 := by
  apply polarBlock (data:=fun _ => (word80 [0x28011288468140,0x280112884681400048,0x2030084825000480203,0x848250004802030084,0x82500048020300848240,0x480203008482500048,0x2030084824000480203,0x848240004802030084,0x82400048020300848250,0x480203008482400048,0x2030084824000480203,0x848240004802030084,0x82400088020300888440])) rfl
  decide +kernel
theorem g239B7 : CutRow g239 7 0 42 := (@joinRow g239 7 0 4 38 g239P7_0 (@joinRow g239 7 4 22 16 g239P7_4 g239P7_26))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_0 : CutRow g239 8 0 10 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_10 : CutRow g239 8 10 19 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P8_29 : CutRow g239 8 29 2 := by
  apply polarBlock (data:=fun _ => (word80 [0x2801128846,0x81600048020300848261])) rfl
  decide +kernel
theorem g239B8 : CutRow g239 8 0 31 := (@joinRow g239 8 0 10 21 g239P8_0 (@joinRow g239 8 10 19 2 g239P8_10 g239P8_29))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_0 : CutRow g239 9 0 5 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P9_5 : CutRow g239 9 5 8 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B9 : CutRow g239 9 0 13 := (@joinRow g239 9 0 5 8 g239P9_0 g239P9_5)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P10_0 : CutRow g239 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B10 : CutRow g239 10 0 1 := g239P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : mixedTables g239 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g239 0 0
  · exact mixedEmpty g239 1 0
  · exact mixedEmpty g239 2 0
  · exact mixedEmpty g239 3 0
  · exact mixedEmpty g239 4 0
  · exact g239B5
  · exact g239B6
  · exact g239B7
  · exact g239B8
  · exact g239B9
  · exact g239B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K223) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 11 := mixedLower (g:=g239) (i:=0) (hints:=16778595) (before_sound K223 V223) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K223 11 [(239,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V223 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x828c2cd2734a2424d0,0xfe0000001fc07f])),(BitVec.ofNat 152 (word80 [0x82840c92520a2020d2,0x24489122448912244891]))),((BitVec.ofNat 152 (word80 [0x42bbc498503613c030,0x7f000007f0003f80])),(BitVec.ofNat 152 (word80 [0x4289c4985036124000,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0xdcc73d801410da3100,0x3f800003f80fe00000])),(BitVec.ofNat 152 (word80 [0xcc822d801410922100,0x60c183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8532339ea8cc988c00,0x1fc00000000000003fff])),(BitVec.ofNat 152 (word80 [0x532330028c0888c05,0x4a952a54a952a54a952a]))),((BitVec.ofNat 152 (word80 [0x10a98a6d2c92ec42a0,0x1fc000fffc000])),(BitVec.ofNat 152 (word80 [0x1029806c28804c4229,0x93264c993264c993264c]))),((BitVec.ofNat 152 (word80 [0x6154172348210167df,0xe0000001fffff0000000])),(BitVec.ofNat 152 (word80 [0x2154120300000104d6,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x100000648101001028,0x10204081020408102040]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10),(4,0,243,0,10),(32,0,215,0,10),(2,0,245,0,9),(64,0,183,0,9),(128,0,119,0,9),(16,0,231,0,8),(34,0,213,0,8),(0,16,100,131,7),(0,32,146,69,7),(130,0,117,0,7),(1,32,146,68,6),(2,16,100,129,6),(4,32,146,65,6),(18,0,229,0,6),(48,0,199,0,6),(64,32,146,5,6),(66,0,181,0,6),(128,16,100,3,6),(144,0,103,0,6),(80,0,167,0,5),(98,0,149,0,5),(130,16,100,1,5),(146,0,101,0,5),(160,0,87,0,5),(192,0,55,0,5),(194,0,53,0,4)]
def g247A : List (List Nat) := [[]]
def g247D6 := limbs80 #[#[0x6559229fa960c8359564,0xe8359564d8ddd79160d,0xb036803a1f75e]]
def g247D7 := limbs80 #[#[0xb2ac8a8f8de456559151,0xa7c3f87595645478790e,0x1d6559153f0e49acab22,0x359387eeab2ee2b270f2,0xec1906b2ac9a3d855947,0xacab25ade458359564d4,0x1df985cc7359753f0741,0x8559131f1fc2acab2263,0xc797eecc2ac898debe49,0x8acab2663cbf76e15644,0x998f8fe156559331f5bc,0xf9261564cc6f6f22c2ac,0x59564f1fc3acab22a37a,0xc7eebc0acab278fdd581,0x6b2ac9e3f7520d65593,0x278fdd58359564b5f4b9,0x5e0d65593c7eeb41acab,0xc00b5f4bf06b2ac9e3f7,0xdb362544444de2ac6f0c,0xa5894a4c91a408ea227b,0xa88a0a7c9da709aa6497,0x5889e1f030c5a6a94a3,0x8020306591e1f0040a23,0xe1700598c2e88a2c8f0f,0x1080a1954f87c0161489,0x9285e1f005c718ab385e,0x348319b49e10b0989541,0x4f07842c2c4f8585f0f8,0x3c41608cda]]
def g247H7 (j : Nat) := if j=0 then 0xe4000000002403e else 0
def g247D8 := limbs80 #[#[0xcbf7659131ed56358531,0xe3d6559151e756558551,0x9f7815d953e3d6559153,0xabf865cd64bbb805cd64,0xabd869cd64d9f739cd64,0xbaf825d564e3f7559564,0xef56558531abf865d564,0xebd6559331ebd6559131,0xef56358551bf78159731,0xbf5819cd51bf7815cd51,0xdbf8759151dbc8759151,0xbf7815d951f778159551,0xef78159561df7815d951,0xf5c8359553dbc8759153,0xebd65dc564dbf8759253,0xdbf75dc564dbd75dc564,0xebd651cd64bbd85dc564,0xebd65dcd64bbd851cd64,0xebd8159564bbd85dcd64,0xebc8359564ebf8159564,0xebe8359564ebd8359564,0xbbf815d564ebf8359564,0xbf7815cd65ddd731cd65,0xddf739cd65aff865cd65,0xfbd8559131afd869cd65,0xfbd8559331fbf8559131,0xff78159731fbf8559331,0xfbd85dc564fbf8759151,0x4c1160e00a2064036000,0x62602321fc1d61b018a1,0x39a36c33e3202e22ac28,0x144e64b047243c4063c8],#[0xe6586325f45a658054a5,0x7da7a47567306fa6d469,0x849569288e28ac866818,0x6a98a6aa3ca0e9e09aa9,0xd238b87805c6ad2accac,0x8384287e412e1e04e140,0x1716e0e1871c105c5b8b,0x51814428b87805865110,0x4387142c708c4e2e1e0a,0x484e1e0100f10a29b8c,0x84406e1e013101387804,0xe3a4e0c50d144b0b8f83,0x6e1e0121710278780544,0xe1c6161d908b8780485c,0xc1717871858364c322e0,0x17838b8444585c2e1e00,0x7804295447e2e1e01117,0x6484610e1e01819211b8,0xe1a5111c5b838b869444,0xc584787802861716e0e2,0x83105864362e1e016145,0x8460e2e146161a88a787,0x216e1e010278780405c4,0x838593142471831a3a6c,0x314408e0e1101810c4b3,0x1e0101718628ca09b878,0x10161b8780405c41982e,0xa278780405841982e1e0,0x64649a41966c216e0e10,0xe1e017191d985b87811c,0x18c4f0b838458905c224,0x9a412c2e0e1172065269],#[0x6320930b878058646194,0xb84585282609c5a4e1e0,0x584c4e2e0e116149b138,0xc4e226e0e1161b878050,0x5614e4817886787805c5,0x464c1615913922885158,0x1930d311a88515c361]]
def g247H8 := limbs80 #[#[0x50658d0b935e82271408,0xf0d26150c89890d5df34,0x3a00208468cfdcc614,0x39d33b0ae38e007bf34]]
def g247D9 := limbs80 #[#[0xd534c7fab0a63af59564,0x1a63f758d31fbca698fd,0x31bfaea98fbd644c7ef3,0xdff764c6febb2637fdd5,0xeb2663f758f31fbaa798,0x8551bfaed98dfd75cc7d,0xa8dff73547bea9aa3fd5,0x6febb2a3df59551f7ac8,0xf59561dfac6b0dff7654,0xc6a9fdd6354effb8aa7b,0x54fbeb2aa7ef59153fbc,0x77f5c653bfeeca9dfd76,0xfaed29fbd6494feeb1ca,0x7198effbaac77fdc563b,0xac9ef5c564bfaeb31dfd,0x4f7ae6b27bc73593dfb8,0xbd75593dfb9ac9ef9cd6,0xb9acb7fdc565f7eeab27,0xd51ffacb98ffd654c6ff,0x8ffd73547ff31aa3ff58,0xfeb8acbff5d951ffce6a,0x5cd65ff8e6b2fff71597,0x8007ff73597ff39acbff,0xa808c87806004b83381b,0x21269120fd8e90d48c00,0x1e39bd9a598a16b15694,0x9d285270a5523d221a06,0xab26311afd2e1ac9ab1a,0xbbcba8393b7f367352b3,0x6844943142040f3f73d4,0x8d0d4f54d9cc1ca9c8ac,0xdcddb2593574558d40d2],#[0x82c2218f0e0483e085ec,0x498219218905c5870171,0xe02e362c29301717161,0x5c7c58700e24283118b,0x878b0e0243054590961c,0x161c05c5498b0e02e2a4,0x987016170e2c04870a23,0x60c2587c58700c262e24,0x305498b0e02c2c345923,0x25a260c5845118b0e026,0x9218884078b0e02c3972,0xba521830962a262c3821,0xe1e04b8b096268c48688,0x1c8972d8b06114391085,0x2c380b8c18b25c18b091,0x852e59262c18450e301e,0x8a261c09460d13161c05,0x89870161b144c380b0b,0x700c1c205c5870161911,0x16262c380b0b101a5c58,0x6c5130e02e2c4c587017,0x3161c05c54442261c05c,0xc184b8b93062c23098d1,0xe02c2e2c38071215262,0x5894c1f0e02c406498b,0xc380b8c621232f14861c,0x102e261c040b084a110,0x1844909a110c380b0d87,0xc7830c5204924d8e2a4c,0x747130e2c05882499202,0x9171a262c38228c1a29,0xd262c1863161d262c38],#[0x2c298b0f13161c030b8d,0xc61d83161225864b1306,0x80b62c26871983161225,0x64b912d8b0611441723,0x97323842e5b161c08cc9,0x213c58309620292c5830,0x2319884b160c25c7328e,0x6c5830963]]
def g247H9 := limbs80 #[#[0x27246b302ca1c0001001,0x1a169de839798d532a5,0xdb69ad35725aa0000070,0x11f0001c59cee3231cad,0x82c927ed00280574009,0x5e366e40033773c862,0xbc00d340012000ad4900,0x70005af31a6c0094800b,0x30109b9592c13002e28,0x28edc99127fc3c6aee0]]
def g247D10 := limbs80 #[#[0x61ff547ff31ff4c7bd64,0xfe63ff58ffe53ff54ffd,0xfa10cc4b1985400ff597,0x890a48c58601bc1b0ba4,0x38a11871a59080e18a03,0x2464650e012188896480,0x228162175860e48a180a,0x50d71218221881850e11,0x1461d30c690c88586024,0x68c51208a11e48e2860]]
def g247H10 := limbs80 #[#[0x88003c6030624520300,0x4640000000003b6003d4,0x3ea6283a6d00000000,0x2ad003b0002d1f03af,0xd965acdf12b3ec7a7486,0x135003df,0x156c8e6876c00a9161,0x9bad8dc84d108000017b,0x4e000778009f0e9e07e0,0x9aca700026d5f4371213,0x2cf9920000000000000,0x155ce00145c2400cce2c,0xaf800633fd4400000000,0xdc8c400]]
def g247D11 (j : Nat) := if j=0 then 0x1483080437f else 0
def g247H11 := limbs80 #[#[0xe9008200b80000004000,0xf6000000000045001300,0xe10054f700000000]]
def g247L : Nat → Packing
  | 6 => (3,5,5,0,0,5,0,g247D6)
  | 7 => (28,4,5,0,0,10,0,g247D7)
  | 8 => (56,3,5,0,0,12,0,g247D8)
  | 9 => (63,2,5,0,0,12,0,g247D9)
  | 10 => (10,1,5,0,0,9,0,g247D10)
  | 11 => (1,0,5,0,0,0,0,g247D11)
  | _ => emptyPacking
def g247I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 11 0 6 2 0 g247H7
  | 8 => lookupWord 7 31 5 9 5 0 g247H8
  | 9 => lookupWord 14 71 6 10 6 0 g247H9
  | 10 => lookupWord 15 101 4 10 6 0 g247H10
  | 11 => lookupWord 2 29 0 8 4 0 g247H11
  | _ => fun _ => none
def g247 : Forest := ⟨247,11,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_0 : CutRow g247 6 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P6_1 : CutRow g247 6 1 2 := by
  apply polarBlock (data:=fun _ => (word80 [0x60000148a2,0x5110020002090ca21252])) rfl
  decide +kernel
theorem g247B6 : CutRow g247 6 0 3 := (@joinRow g247 6 0 1 2 g247P6_0 g247P6_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_0 : CutRow g247 7 0 11 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P7_11 : CutRow g247 7 11 17 := by
  apply polarBlock (data:=fun _ => (word80 [0x210110c846,0x113000210110c8461130,0x840112084c44520825,0x4024102513000210110,0xc846113000210110c846,0x113000210110c8461130,0x210110c84611300021,0x110c846113008000100,0x90c04473080004020980,0x427300840112084c4462,0x2200a0d02a21500442,0x1824064827104420182,0x406482710800010090c0,0x447300840112084c4462])) rfl
  decide +kernel
theorem g247B7 : CutRow g247 7 0 28 := (@joinRow g247 7 0 11 17 g247P7_0 g247P7_11)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_0 : CutRow g247 8 0 13 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_13 : CutRow g247 8 13 36 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_49 : CutRow g247 8 49 4 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P8_53 : CutRow g247 8 53 3 := by
  apply polarBlock (data:=fun _ => (word80 [0x210110,0xc846113000210110c846,0x1130002200a0d02a2130])) rfl
  decide +kernel
theorem g247B8 : CutRow g247 8 0 56 := (@joinRow g247 8 0 49 7 (@joinRow g247 8 0 13 36 g247P8_0 g247P8_13) (@joinRow g247 8 49 4 3 g247P8_49 g247P8_53))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_0 : CutRow g247 9 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_1 : CutRow g247 9 1 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_49 : CutRow g247 9 49 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P9_50 : CutRow g247 9 50 13 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B9 : CutRow g247 9 0 63 := (@joinRow g247 9 0 49 14 (@joinRow g247 9 0 1 48 g247P9_0 g247P9_1) (@joinRow g247 9 49 1 13 g247P9_49 g247P9_50))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_0 : CutRow g247 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P10_1 : CutRow g247 10 1 9 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B10 : CutRow g247 10 0 10 := (@joinRow g247 10 0 1 9 g247P10_0 g247P10_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247P11_0 : CutRow g247 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g247B11 : CutRow g247 11 0 1 := g247P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247T : mixedTables g247 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g247 0 0
  · exact mixedEmpty g247 1 0
  · exact mixedEmpty g247 2 0
  · exact mixedEmpty g247 3 0
  · exact mixedEmpty g247 4 0
  · exact mixedEmpty g247 5 0
  · exact g247B6
  · exact g247B7
  · exact g247B8
  · exact g247B9
  · exact g247B10
  · exact g247B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 12 := mixedLower (g:=g247) (i:=0) (hints:=16778564) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 12 [(247,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xb45c75c5441000000,0xff00000000ff00ffff])),(BitVec.ofNat 152 (word80 [0x41431c1441212121,0x21212121212121212121]))),((BitVec.ofNat 152 (word80 [0x40ab06a9e949000000,0xff000000ff0000ff0000])),(BitVec.ofNat 152 (word80 [0x40a30608c9010b0b0b,0xb0b0b0b0b0b0b0b0b0b]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x210085aeaa20000ff,0xff00ff000000ff])),(BitVec.ofNat 152 (word80 [0x2100042e882060606,0x6060606060606060606]))),((BitVec.ofNat 152 (word80 [0x4a78b000a4be00ff00,0xffff00])),(BitVec.ofNat 152 (word80 [0xa18b00020be545454,0x54545454545454545454]))),((BitVec.ofNat 152 (word80 [0xa522fe2403b0000000,0xff0000ffff000000])),(BitVec.ofNat 152 (word80 [0x8522ac200330989898,0x98989898989898989898]))),((BitVec.ofNat 152 (word80 [0xbc0950031552ff0000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0x280850011440606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x919621a01a05ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x910400a00200808080,0x80808080808080808080]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(8,0,243,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(2,0,249,0,9),(16,0,235,0,9)]
def g251A : List (List Nat) := [[],[96,65]]
def g251D10 (j : Nat) := if j=0 then 0x659ab8c1ffd31 else 0
def g251D11 (j : Nat) := if j=0 then 0x3544383ff else 0
def g251H11 (j : Nat) := if j=0 then 0x1 else 0
def g251L : Nat → Packing
  | 10 => (1,1,3,0,0,0,0,g251D10)
  | 11 => (1,0,3,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 11 => lookupWord 1 2 0 4 0 0 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : CutRow g251 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : CutRow g251 10 0 1 := g251P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : CutRow g251 11 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : CutRow g251 11 0 1 := g251P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : mixedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g251 0 0
  · exact mixedEmpty g251 1 0
  · exact mixedEmpty g251 2 0
  · exact mixedEmpty g251 3 0
  · exact mixedEmpty g251 4 0
  · exact mixedEmpty g251 5 0
  · exact mixedEmpty g251 6 0
  · exact mixedEmpty g251 7 0
  · exact mixedEmpty g251 8 0
  · exact mixedEmpty g251 9 0
  · exact g251B10
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := mixedLower (g:=g251) (i:=0) (hints:=16777283) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe6810d09140de7c42,0x4000003f00000003ffff])),(BitVec.ofNat 152 (word80 [0x810101040c66440,0x49249249249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x72213a6e2a3522a,0x40000fc0000fc0fc0000])),(BitVec.ofNat 152 (word80 [0x2c042013a48283522a,0x430c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff049c85c8831692b0,0x8003f00003f03f00003f])),(BitVec.ofNat 152 (word80 [0x49040081c883101230,0x82082082082082082082]))),((BitVec.ofNat 152 (word80 [0xf86cd3deac000027,0x80fc0000000000000fc0])),(BitVec.ofNat 152 (word80 [0x70606cc3ceac000027,0x96596596596596596596]))),((BitVec.ofNat 152 (word80 [0x112a6c083f8928e4,0xfc003ffff000])),(BitVec.ofNat 152 (word80 [0x80110a6c0028080884,0x24924924924924924924]))),((BitVec.ofNat 152 (word80 [0x2e552b025400c55c,0xbf000000ffffc0000000])),(BitVec.ofNat 152 (word80 [0x2a55000254008440,0x18618618618618618618]))),((BitVec.ofNat 152 (word80 [0x191c1206588680781,0x7fffffff000000000000])),(BitVec.ofNat 152 (word80 [0x9180200100280180,0x20820820820820820820]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(32,0,221,0,10)]
def g253A : List (List Nat) := [[]]
def g253D10 (j : Nat) := if j=0 then 0xff else 0
def g253L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g253D10)
  | _ => emptyPacking
def g253I (_ _ : Nat) : Option (Nat × Nat) := none
def g253 : Forest := ⟨253,10,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : CutRow g253 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : CutRow g253 10 0 1 := g253P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : mixedTables g253 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g253 0 0
  · exact mixedEmpty g253 1 0
  · exact mixedEmpty g253 2 0
  · exact mixedEmpty g253 3 0
  · exact mixedEmpty g253 4 0
  · exact mixedEmpty g253 5 0
  · exact mixedEmpty g253 6 0
  · exact mixedEmpty g253 7 0
  · exact mixedEmpty g253 8 0
  · exact mixedEmpty g253 9 0
  · exact g253B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 11 := mixedLower (g:=g253) (i:=0) (hints:=33555715) (before_sound K251 V251) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K251 11 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V251 low253 (by decide +kernel)
def g254Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffb2416914c07c274e,0xc8000000fc0000fc003f])),(BitVec.ofNat 152 (word80 [0xa20416904403c2642,0x48145145145145145145]))),((BitVec.ofNat 152 (word80 [0x4808bb623f143349,0xa00003f00003f000fc0])),(BitVec.ofNat 152 (word80 [0x330800bb003e143309,0xa0c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0x39b32f0c22138523,0x3000fc0000fc003f000])),(BitVec.ofNat 152 (word80 [0x5c39b12b0422118103,0x20c30c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xff949c4c97ae4e9988,0x1203f00000000000003f])),(BitVec.ofNat 152 (word80 [0x6014980492ae429988,0x1269a69a69a69a69a69a]))),((BitVec.ofNat 152 (word80 [0x652c2fb48934e42,0x2200000003f00003ffc0])),(BitVec.ofNat 152 (word80 [0x800642407b40824c40,0xb2cb2cb2cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x8a90580d3a05810,0xbdfc000003fffffc0000])),(BitVec.ofNat 152 (word80 [0x8048081000010,0xb1410410410410410410]))),((BitVec.ofNat 152 (word80 [0x674430492480a0b5,0x54fffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x4204004900800024,0x4820820820820820820]))),(0x0,0x0)]
def g254C : List ColumnInfo := [(4,0,250,0,10)]
def g254A : List (List Nat) := [[],[50]]
def g254D10 (j : Nat) := if j=0 then 0xff else 0
def g254L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g254D10)
  | _ => emptyPacking
def g254I (_ _ : Nat) : Option (Nat × Nat) := none
def g254 : Forest := ⟨254,10,fun i => g254Y[i]?.getD (0,0),g254C,g254A,g254L,g254I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254P10_0 : CutRow g254 10 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g254B10 : CutRow g254 10 0 1 := g254P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254T : mixedTables g254 10 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g254 0 0
  · exact mixedEmpty g254 1 0
  · exact mixedEmpty g254 2 0
  · exact mixedEmpty g254 3 0
  · exact mixedEmpty g254 4 0
  · exact mixedEmpty g254 5 0
  · exact mixedEmpty g254 6 0
  · exact mixedEmpty g254 7 0
  · exact mixedEmpty g254 8 0
  · exact mixedEmpty g254 9 0
  · exact g254B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g254G : graphValid g254 (boundsBefore K253) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low254 : Lower true (varsX 254) (graphGoal 254) 11 := mixedLower (g:=g254) (i:=0) (hints:=287397184) (before_sound K253 V253) g254G g254T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K254 := extendKnown K253 11 [(254,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V254 : Known true K254 := extend_ok (m:=254) V253 low254 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f8000000000007f8,0x7fff8120589b6023bc4])),(BitVec.ofNat 152 (word80 [0x90909090909090909,0x90908120488b6001904]))),((BitVec.ofNat 152 (word80 [0xf800000007f8000007,0xf80000d80612078dbc9b])),(BitVec.ofNat 152 (word80 [0x585858585858585858,0x5858585804100285b899]))),((BitVec.ofNat 152 (word80 [0x7f80007f800,0x51818043830c00f])),(BitVec.ofNat 152 (word80 [0x383838383838383838,0x38383c1808041010400f]))),((BitVec.ofNat 152 (word80 [0x7f80007f80000,0x7fa382000404100c7])),(BitVec.ofNat 152 (word80 [0x303030303030303030,0x303030080000000000c3]))),((BitVec.ofNat 152 (word80 [7,0xfff800e44067807e0f23])),(BitVec.ofNat 152 (word80 [0xa2a2a2a2a2a2a2a2a2,0xa2a2a0a40067007a0222]))),((BitVec.ofNat 152 (word80 [0x7f8000007fffff8,0x3000078007ff038])),(BitVec.ofNat 152 (word80 [0xc4c4c4c4c4c4c4c4c4,0xc4c4c3000030006fa030]))),((BitVec.ofNat 152 (word80 [0x7fffffff8000000,0x427807fff800000])),(BitVec.ofNat 152 (word80 [0x30303030303030303,0x3030026804bed000000]))),((BitVec.ofNat 152 (word80 [0xfff800000000000000,0xfff8000000030])),(BitVec.ofNat 152 (word80 [0x40404040404040404,0x4040001730000000000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12),(8,0,247,0,12),(32,0,223,0,12),(1,0,254,0,11),(2,0,253,0,11),(16,0,239,0,11),(64,0,191,0,11),(128,0,127,0,11),(34,0,221,0,10),(96,0,159,0,9),(130,0,125,0,9),(144,0,111,0,9),(0,2,45,208,8),(0,16,108,131,8),(0,32,146,77,8),(3,0,252,0,8),(17,0,238,0,8),(18,0,237,0,8),(33,0,222,0,8),(48,0,207,0,8),(65,0,190,0,8),(66,0,189,0,8),(80,0,175,0,8),(129,0,126,0,8),(160,0,95,0,8),(192,0,63,0,8),(1,16,108,130,7),(1,32,146,76,7),(2,16,108,129,7),(4,32,146,73,7),(8,32,146,69,7),(16,2,45,192,7),(50,0,205,0,7),(64,2,45,144,7),(64,32,146,13,7),(128,2,45,80,7),(128,16,108,3,7),(146,0,109,0,7),(3,16,108,128,6),(5,32,146,72,6),(19,0,236,0,6),(49,0,206,0,6),(65,32,146,12,6),(80,2,45,128,6),(82,0,173,0,6),(97,0,158,0,6),(128,4,27,96,6),(129,16,108,2,6),(130,16,108,1,6),(144,2,45,64,6),(145,0,110,0,6),(192,2,45,16,6),(194,0,61,0,6),(51,0,204,0,5),(131,16,108,0,5),(147,0,108,0,5),(161,0,94,0,5),(208,2,45,0,5),(210,0,45,0,5),(224,4,27,0,4)]
def g255A : List (List Nat) := [[]]
def g255D7 := limbs80 #[#[0x83b0e71975e91915c160,0x570bc73c16d176641755,0x845c2d4e71bb05d79460,0x5d5709d6bc26dba05d5,0xe41755c335a507b269b9,0x85945d975cd6981ec9a6,0x91e61230602b1d70386e]]
set_option maxRecDepth 16000 in
def g255D8 := limbs80 #[#[0xe0884d6bb269b905d570,0x65d570502eb5d934cbaa,0x2ebd2322b82c175aec9a,0x6c79a6e85755c160da7,0x570582e3cdb742baae0b,0xd02eab22c171e6dba45d,0x7976e51905d560b8f76e,0x58363cbb341c8aeab074,0xecbaac1b1e5d9a0e5175,0x4685875d560b8ef62d22,0xcbbd8b48c3aeab0593fb,0xae1d4eec175e51815c2,0xb945d570e27b0cbaf28c,0xc3f44cb2eaa0cd7bb069,0xb51f6daa95d9805d74b7,0x5d975c8ff4cbb321c0ae,0x42ca2ecbad577b165190,0xe6d9755057058363bc37,0x60f8f36cbab22b82c1f1,0x82eab07c79b65d5945c1,0x17664175583e3cd8aecc,0xaf36dd02eac22e1f1e6d,0xaa05c7db0e19915d975b,0x5d975503c3ed472cbb2e,0xecd02eaa0ac1e1faa396,0x757b976817550560f8f2,0x41583a3fcbb4cbaa82b0,0xbaeaa0ac1c5f6a3975d5,0xfba61f915d560e2fd51c,0x834bfdd30fca2eab0697,0xbaac1adb507a2661755,0xe9d985d560d6ba83d1b3],#[0xbea0b4f4c2eab0697d41,0xac1a5f6c5a7a61755834,0x985d560d2ff62d3d30ba,0xa34f4c2eab0697db469e,0x75e6dba05d5415c34bfd,0x570baf760d32eaa0ae1,0xbaac2b85d6fb2699755,0xe63a05d5615c3abccc74,0xea7b6cbaf28c0ae1d5e,0xb02b8753fb65d7946057,0xa05d5815c3cbcc3740ba,0xf760d32eac0ae175e6db,0xb85d6fb26997560570ba,0xd5845c2ebdd834cbab08,0x2c3720baae175bec9a65,0xc7fa65d9905d541baf76,0x55074bfd370ec82eaa0e,0x2ecbaa83a5f69b87e417,0xa0e1d965d541b8fb61cb,0x7cb7d170ecb2eaa0e97f,0xbaac3a5f68387e597550,0xd9905d564d8fd74bb320,0xedd2edca300baec7eba5,0xebd1fe59a15d9805d72b,0x660175cafd52d0aecc02,0x348bb300badd77b16917,0x5faa5a45d9805d7a3fcb,0x175ceda83d132dc02eb9,0xc82ecbae57dba5d990e1,0x1ba4641765d7a3fc3328,0xdaef01d0b28bb2ebb1fe,0x40005c7db0e19945d975],#[0xf10cd0a908505b83d02,0x139e49b0186962939115,0x52ebac2298a8525ba322,0x39ab8cb73b5ab41b33b1,0xd0bcdbcabc7bc4bc1bae,0x5be2bdfbdcbd9bd6bd3b,0xbf7bf4bf1beebebbe8be,0xcc09c06c03c00bfdbfa,0x1c1ec1bc18c15c12c0fc,0xc33c30c2dc2ac27c24c2,0x48c45c42c3fc3cc39c36,0x345ac57c54c51c4ec4bc,0x722617f8bf12e37c104e,0x6c2e09fe08a09fc27c18,0x6c4f810690bfc11e19dc,0xca914f81f040d8de198c,0x6ae210ff81f042c0c498,0xc1608818df81f04150c4,0x8c048277c0e8bf04178,0x4150e2ac4a490f8008be,0x16060b0256464c5f81f0,0x7f047143b17e0096f82,0xf824c19c3171450fc0f,0x358670bdc4f0de0fa17c,0x9c2f717c1f42f81f0483,0xf4461ff03e099814d0e1,0xccf44c3470be0117f823,0x6c666c5f81063e0dc61c,0x87f81f047723f0519868,0xc6c3f823a54e86534a66,0x7e07c11c9124de89f020,0xf058c0b85ee2961d0506],#[0xb031181e510b62a56f81,0x62b0319c224419c22762,0x788258249cf11a109513,0x22ae820aa1f45a209243]]
def g255H8 := limbs80 #[#[0xb4000000012000000032,0x16027414]]
set_option maxRecDepth 16000 in
def g255D9 := limbs80 #[#[0x7450110f6c5d17150110,0xfac5914158110e6e61d,0x97558110f3c5d9715811,0x10d5e65d7558110f1e5d,0xd5415c110f6c5d1415c1,0x110e6e611745c110f5c5,0x5d7845c110e5e5d5845c,0xc110f5c685755c110e5e,0xee19755c110e5e619755,0x50510d5ee59755c110e5,0x5de5d7550510e6d61d74,0x65c510e6d611745c510d,0x8efe91985d110e3d6197,0x765d510c5fe5d7561110,0xacfe91985d510e1f619,0xe985d510a5fe9d985d51,0x408efe91985d910a5f69,0xd7815c140e6e5d3815c1,0x140d6e5d3915c140e5e5,0xe19745c140e6e619745c,0xc140f4e691755c140e6e,0xee19755c140e5e619755,0x5d540b4fe9d945d540e5,0x5fe9d985d540e1f61976,0x85d940a5f69e985d540a,0xe5e5d7815c1608fde859,0x645c160f2e5d1645c160,0xe5e5d7845c160f1e5d5,0x975e0560f1e699755c16,0x60c5f65d75e0560e1f5d,0xd975e1160e1f61d75591,0x560c5f65d75e1160e1f5],#[0xe9d905d560f1e5d9905d,0xd560adbe89985d560b5e,0xfe9d985d560ad7e8d985,0x60570a5f69e985d560a5,0x5e687905d570d4f5d794,0x5d570d5e653905d570b,0xb5e69b905d570b5e6939,0x945d570b5ee81915d570,0xb5ee81965d570b5ee81,0x9645c541b5be89965d57,0x41b6d69d645c541f2d5d,0x19765c541e6d619745c5,0x141f0f5d97559141e3d6,0x619765d541e4fe1d7559,0xd541a5fe9d865d541e1f,0xf69b875d541a5f683875,0xe01618fde85985d941a5,0x1f5d975e0161e3d5d971,0x45c561f2d5d1645c561e,0xe3d5db845c561b3d69d6,0x75e1161b3de91765c561,0x1f1d5d9915d561e1f5d9,0xd985d561adbe89985d56,0x64a5f69e985d561a5fe9,0xd975e0564e1f5d975e01,0x564f0f5d9945d564e1f5,0xe81765d564b4fe9d945d,0xd564adde85985d564b1f,0xfe9d985d564adbe89985,0x60175a5f69e985d564a5,0x5f69b9760175d1fe5976,0x6605759dbe8996e01759],#[0xd1fe597660575e1fe197,0x9761175d1fe597661175,0x595f69b976117595f683,0x3865d975b5de85945d97,0x75b1f687865d975b1f68,0x997558110b1f693865d9,0x110f5e65d7558110f9e6,0x699755c110f5e659755c,0xd510f5ee99755c110f5e,0xbe89965d510f1fe59765,0x5c140f6e5d1615c140bd,0x6e659745c140f5e5d561,0x55c140f5e685755c140f,0xf5e659755c140f5ee857,0x755c140f5e699755c140,0xf6d5d17158540f5ee99,0x97558540f3d5d9715854,0x40f1fe59765d540f1f5d,0xa1765d540e5f6a1765d5,0x940bdbe89965d540e5fa,0x69e985d940a7fe9d985d,0xc160f6e5d1415c160a7f,0xe5d5815c160f5e5d5415,0x5c160b7ee9d815c160f5,0x5e5d5915c160beee9191,0x45c160f6e611745c160f,0xb7ee9d845c160f5e5d58,0x755c160f5e5d5945c160,0xf5ee91755c160f5ee85,0x97150560f6d5d1715056,0x60f1f5d97550560f3d5d,0x5d7550560e5f61d75505],#[0x560f3d5d9815c560d5fe,0x5d975605609efe91985c,0x560e5f61d7560560f1f,0xfe5d8760560d3fe5d766,0x59160f9e6817559160c7,0xfde85985d160f1f61d75,0x561160f1f5d975611609,0xd3fe5d7661160e5f61d7,0x905d560c7fe5d8761160,0xbde683915d560ddee51,0xb915d560f1f5db915d56,0x60b9f69b915d560d9f65,0xa3915d560e5f61f915d5,0x560bde683945d560adf6,0x69b945d560f1f5db945d,0xd560e5f61f945d560b9f,0xf685765d560adf6a3945,0x5d560f1f691765d560f1,0x5fe85875d560e5f68587,0x75d560e5f691875d560e,0xbbde85945d960e5fe918,0x9461d60aefe919161d60,0xf5ee817550570afde85,0x17558570f5ee81755857,0x70d5fe617558570d5f66,0x9f985857097fe9d98585,0x570cef61b946057097f6,0x6197560570f5ee817560,0x1170f5ee817559170e5f,0xf6197561170f5ee81756,0x5d570f5e61b905d570e5,0x5f65b915d570e5fe1b91],#[0x45d570b5f69b915d570d,0xb5fe85865d570b5f69b9,0x905d541b5fe85965d570,0x1e5fe1f905d541e5fe1d,0x9965d541f1fe59765d54,0x41e5fe1d965d541bdbe8,0x81765c561e5fe1f965d5,0x561f1f5d9905d561f3d6,0x5db905d561b5fe9d905d,0xd561f1f5d9945d561f1f,0xf681765d561f1f5db945,0x5d564f1f5d9905d564f1,0x1f5db905d564b5fe9d90,0x160175f1f681765d564f,0xe5f5db8460175d5fe5f9,0x9460175e5fe5f8460175,0x5d5f5db9460175d5fe5f,0x576601759df69b946017,0x75d5f5d990e0575d5faa,0x8986e05759dfe9990e05,0x175d5faa57661175edbe,0xe8176e1175d5f5d990e1,0xd9759dfe8196e1175b5f,0xf651905d975d5f645905,0x5d975b5fe91905d975d5,0x1fe19915d975f1fe1990,0x161975f1fe19945d975f,0x9df6839161975ddbe4b9,0x9261975ddbe539261975,0x6ddbe939261975ddbe87,0x17550560afde85846017,0x70f9f6997550560fde68],#[0x997560570f5f69975505,0x541f5f6997561170f5f6,0x6857660175f5f5d9905d,0x560f5f6917660175f5f,0xf6a17550560f5f61d755,0x5d560edfaa17550560ed,0x5fe85875d560f5f68587,0x75d560f5f691875d560f,0xf5fe997550570f5fe918,0x7561170f5fe997560570,0xf5f61b915d570f5fe99,0x5865d570f5f685865d57,0x41bdfe99905d541f5fe8,0x9b905d541f5f5db905d5,0x541bdfe81965d541bdf6,0x683965d541fdbe89965d,0x175f5f68576e0175bdf,0xf69990e0575f5f69176e,0xe1175f5f68176e1175dd,0x5f691905d975ddf68196,0x170000f5fe91905d975f,0x6800a500fe016401980,0xa05840a5012e021a03c4,0x4a046608480f101a802f,0x17a02c905640a3013582,0xa0e641be835706620c54,0x5a0868104c1f683cc076,0x27d04e3098e128423d84,0x16542bc85620a781480,0x4c0c6a18642f985dc0b8,0x37d86da0d681a3833b86,0xc1e583bd075e0e841c84],#[0x7510a820b83ff07e20f8,0x48a88f911a622dc44b08,0x826984c0096912a424ec,0x5d148c28a850709f7139,0x57c0ae1158a2a905418a,0x2e9c5c08b6516922cc8,0x7c18b630ac6028be9179,0x68b8cf119aa32e464e8c,0x837046d28d891ab234b8,0x961cfe397871c0e121bd,0x7a00f151de83b247540e,0x405c7f38fc11f043d70,0xfb21b442d083f905e207,0x8d0117a22b244e088e10,0x495091c120d23ce4704,0x3d26384bd8960929624e,0x9f613cb27404dfc9af13,0x452e4a49947228845070,0x8e2ada5530a95950529b,0xb2d96352c1e5768ad795,0xe5c78b8116e12d805a2c,0x1b2ff45f28bd217742e7,0xc8818d6313861d8c2598,0x46724cd41982329a64b0,0x9434e66970d1d9a1a33d,0xda69b2736206b94d5d1a,0x6ff0ded9bba37146da4,0xdb394c71d8e2a9c34383,0xed91d7d3aa47488e7e1c,0x67970f229e1a3bf2774c,0x3b3e167b44f531e8f3ce,0xff51fc93f5a7e1cfb09f],#[0x682a103c2057406c8054,0x8742c2849d08820ef41a,0x116221043e887110cf21,0x8b4515aa29944f08935,0xf745e88bc517722eb45d,0x183230346008bf517d22,0x8c55189230f46188c25,0x2746488c8518f231b463,0x2b1233346608cb519523,0x7c0f061c0ac5f03c1070,0x3c14f0bc0087c10bc701,0x670322bc2f03c10ac70,0x8e13c50d82af03c10cc7,0x14b0bc5e1036f03c10cc,0xcc5a320ff0bc0f042f19,0xf04330bc606fc0f042f0,0x8f03c10cc2f1407f0bc0,0x4310a85f03c10bc39101,0x9c6f03c10c4840fc0f0,0x71bc0f050f2c18e1217b,0x1242a0901805ec249bc5,0x6f142fc3c2a05fc0687c,0xc4e0fc212fc0f052119c,0x2fc0f05211bc0f04330b,0xe0fc2f03c147c6e0fc21,0x4e0c0df0b47f03c11e0a,0x3c10c48f0033f0528138,0x4221818e134216783f0,0xf04230885e1383d1fc0f,0x4e0fc1f00a60887e0fc0,0x83d1b47f0bc0f047f178,0xc05f0bc00cbc12705e13],#[0xf049c0ac40cfc00cbc10,0x782dc6f0bc0f049c1bc0,0xc60ac2371bc2f03c10c8,0x42f1c3040fc0f042a0b,0xf04371818e143071bc0f,0xf03c10a470a81871bc0,0x83f03c10c070904e1602,0xfc0f042209050a818d0b,0xf03c11fc0f04220c84e0,0x10c42a1785e0f46d1fc2,0x4bf0bc0f04261c0af03c,0xa85f002af04361017a18,0xf03c10a8808fc0f042f0,0x10c42a142f40fc5f1217,0x87f03c10c42a100af03c,0xa8506514d16c2f03c10d,0xf04300a8412fc0f04300,0x6f1119f17c0f042a23c0,0x41d1fc0f04350a840cc8,0x1e1fc5f1386e0f47f0,0xf042d1bc5f1386e0f47f,0x6e0fc0f047f17c403bc0,0x44f03c10bc6f17c403b8,0x483f03c10c42a15c2f1b,0xbc2a1418f03c10bc2a1,0x771bc1f001b2423f03c1,0xc10d82a142408fc5f121,0x423f03c10bc2a16c4f03,0x8fc5f1117b1bc0f041b2,0xc5fc5f12c6f04271c240,0x60650af0bc0f042f1b07,0x49a1ac6f0bc042bc1268],#[0x2bc10bc571bc2f020af0,0xb0b84f03c10bc7f0bc08,0x7d1bc0447c10bc508859,0x431818d0b84f03c10bc,0x33f04a813c00bfc12b,0x2f03c11fc00bfc12b04f,0xc0f04341c0cd1b47e17c,0xfc0f0434202609343f0b,0x41f0984063c50d82ad0,0xf1404f03c109a1f17c0f,0xc10991f13c2f03c187c2,0xbb0bc0457c10bc7f03,0x1b4221bc0f04310a8606,0xb08c5e138606f47f041d,0xc1f001b0d04e1bc0f041,0xec24afc4f0343f05162f,0x3c10cc36102a08c1805,0x40a8521bc0f04300a85f,0x19f03c10bc7083c0f042,0xb47f03c106c6f10330a8,0x178606f47f041d1b85e1,0x106c7e1bc0f042406c5e,0xc10889e17c4e1bc02afc,0x4609023f17c426743f03,0x4271a0e86035f03c10b,0xf04330a85f17c4b1b87f,0x5093c0f042a0cc5063c0,0x3c10a47d17c0f04390a8,0x4240a840920e86020f0,0x187c382fc0f061923c0f,0x4865c3f03c10889e0830,0xc0f04310a8509023f17c],#[0xa8811bc0f04300a8511b,0x1d2612785e13c0f04330,0x61fc5e1036f03c10cc2a,0x391d14e12c2f03c10cc3,0x3918c943f84f07c006c,0x42a0e44e13c1f002a16,0x10c4361bc109e390fc0f,0xc0f04310d88b1bc2f03c,0x3c2f0436181b46058b1b,0x14c8f03c10a8871a85f0,0xdfc10c039142485d10e,0x53082af0032f04361fc0,0x2471a170e7c1f001b338,0x4580a8706310325c4440,0x4af0497183385fc0f0,0xdc643746e0e0cf088bf,0x10c0371c46f0bc0f0430,0x39f042a182a16458f03c,0xc59f03c10c0ae1058f00,0x4371c330c90e61342e0,0xf0427182443b42167c0f,0x2f03c10c06e12c68e747,0x6f0bc0f04371406e0fc,0xbc6887c0f0865f042f18,0xf042a1f86463c0f04650,0x6f06141a9551fc5f0036,0x1af0bc185c7b13c0f083,0x3c0f04330d87c52c4f00,0xbc0f05140988b15c246,0xf03c10a836161704247f,0x361ec5f03c2f04361610,0x2a2386b1518f03c10c8],#[0xa8a715c430836f03c116,0xc5c430a17717c0f04580,0x887c0f0bc11951a1c330,0x6267c2f03c11942f1847,0x42f18980cfc0f04650bc,0x5510bc60cc82f03c119,0x12bc12502b20980cfc0f,0x2f041a928646415f0bc0,0xc50dbc0f042a2786f03c,0x3c10a8331f44454c7267,0xbc0f061427c5d1036f0,0xf04331836857c5d1099f,0xf042f0a870db44f03c2,0xc0f04360a864ad16d17c,0xbc0f0b83f064b2019d17,0x67c0f042a0d87131c4e1,0xd17c0f042a0d8645b102,0x626614f0bc0f04361899,0x2a1899d17c0f0bc10d8,0x4580a882adc5f03c116,0x1602a28380dac4317c0f,0xc02f90919f16c4f03c1,0x729bc5b13c0f04580a87,0x89f149a287c0f04580a8,0x6c5b12420dbc0f04580a,0x1885e0ec4f03c1160a46,0xf03c11602a18382848de,0x2467c0f042a0d862849a,0x436183bf03c10a836164,0x3c1160a46642f002af0,0x243b2688ce1884e0ec5f,0x71218e0c36f03c10cc34],#[0x4d0a18f03c10bc391fc5,0xc5713420dbc0f043325c,0x436f0148f0433191b0d1,0xe43271742f03c10d8971,0xd0bc0717c10d8846dc40,0x5f0bc0f06191e1916094,0x86b13c0f0bc12f14086c,0xbc12c9ac5f1471719d1f,0x71471317d1f83b17c0f0,0x1898f03c18942f14a1c6,0x10c4ad1498f0436f002a,0x40bc4e516c2d1bc025fc,0x2313ac2f0155f04361c3,0xd86d1bc2f0383f043118,0xf0bc12587d1bc2f03c10,0x6181f6659486917f0344,0x330d86d1b45263c0f043,0x3c10a836134530bc0f04,0x1c98d17c0f04320d86f0,0xa209982cc2f03c10c836,0x805dc4f142ff03c18602,0x2fb16c4f0117f06180a8,0x63c10e47f03c106c3910,0xf042a0d8523c49e0fc00,0x3b1bc0f05480c460efc0,0x1871383f02c6f0431278,0x2c6f0191f042f188f126,0x16c6647c0f04580bc616,0x1c96331458f07c089433,0xc3f0591f00331b07927c,0x6c3647c1f00580cc6162,0x51c5067c2f0036f060a2],#[0xb0d190dbc0f042229c30,0x6f03c10d46656c525423,0x19f07c01602a1c5813b8,0x6c5e13c0f042a26c30bd,0x3c10c436222008d1925,0xf03c10cca06096a1242f,0x61a18251c3717420db84,0xc10d4725b85f03c10883,0x4580d8603858e1bc00bf,0x17c0f043623850abc0f0,0x8bc10d448609406742e,0xc10d45f0022f043613c0,0x3c0f04220d44063c008b,0x5918b15c6f0343f04302,0x71844e0b87f03c1b14b1,0xf05122649137438384c,0xc10a8709061863c5f13c,0x3c10e070e2450dbc00cf,0x41b8e471344571b44f0,0xf042a480586255a25c0f,0x671bc0063c10d86093c0,0x45d13c0267c18602a205,0x84c111c3d17c10ec60cf,0xe46a0836f03c10cc341,0x18643025c4a0bc0f042f,0x2a2093239c5e0ac3f03c,0x45066c5b1033f03c1460,0x7c00e46463c1f00340e,0x6fc10763912c4b0d18f,0xd115c3e0b87f03c1b10b,0x87d1bc10747133468384,0xf09f04274e447113906f],#[0x2533c25c4d1bc109c2e1,0xc5f1428619b17c0f0bc1,0x6514350be4761951141c,0x55160c3318332264760e,0x15c060c238288225c0c4,0x82d8313849184e32449d,0x514a91644c60bc5325c0,0xc241584449824388a154,0x1c422]]
def g255H9 := limbs80 #[#[0x3272a90411e9800600,0x198000000000af000000,0x0,0x2970006060006080,0x318000000000004190,0x314800d680000002a000,0x3cd18c00,0x50000003120000000000,0x433000000001,0x306b1602600000000,0xec000000000000000000,0xcefb7c6be300069f0010,0x8800000000001e1a,0xd500000010a00130000,0x2a1c36016cf32400,0x21f4913e001270005380,0x79584184400000094,0x20400000000b5800,0x1022f6992a5e1e0000,0x42e00000000547c89e70,0x0,0x1400000e420008200000,0xd73cfc0059458ac,0x78e00398c2bb1c130,0x2e580000000000,0x360000d00019e6418f00,0x43a6,0x2614c9e5a00313000000,0x40000000000000091200,0x16008]]
set_option maxRecDepth 16000 in
def g255D10 := limbs80 #[#[0x77f28c3a21d79755c110,0xbcbaae0a076e5d170502,0xfaecbaac1d79755c160e,0xdc82eab865f61d755838,0xae8b8a8397f865d570eb,0xbb2e2b0e5fe1d75507b6,0xecbaac9c7d765d561e7a,0xbb00bacfde45875938fa,0xbb2eb57f9761175abfc,0x30cbaf1fe19765d6aff2,0xa0221ff17150110bb7c9,0x80887de5d540443f72e8,0x2217fb9650110bfccb2,0x886fee1d404437f30ea,0x2217fb9750110bfccba8,0x887fc5c560443fe282b0,0x217fb9458110f7cb22c0,0x87be5d960443ef2eab02,0x1bfb8758110dfcc3ac08,0x5fee5d60442ff32eb022,0xdf9745c110ff8a0ae088,0xfee11704437f308b8221,0xf9865c110bfdca2e0886,0xee59704437f70cb8221b,0x57450510fdab2282885f,0x61d41443eeaeaa0a21fb,0x9750510dfbc3a82886fd,0xd171442fef2ea0a217f5,0x45c510dfac22e28877d5,0x971443beaecb8a21bf78,0x59110dfbc32e2886fd61,0x6444377f08b22217f791],#[0xd1109fecc2c8886bf619,0x44433fb0eba221bbd845,0x110dbebab08884ff6617,0x4427ff2ec22213ff9661,0x109fecb708886df5d784,0x43eeb22baa213fd97e11,0xdbec32ea8875f5d9754,0x36fb30baa21b7f865d51,0xbfbc8aec886dfa617544,0x7fb30bb221afd865d910,0xffcbb0c884ffe5186442,0xfb2fc32213fd94e19109,0xe4a30e885efe51874427,0xf28c3a21bbf9461d10dd,0xca70e884ffe59874427f,0x2b82813fd96e1d109fe,0x32e0a05fee45705037f7,0x8b8a81bfb865c140dfcc,0xf02a06ef5d381503b7ae,0xc0a813fd96e0540dbeba,0xe8a06ef619745027fb2f,0xaa81f3d945d540ddfc32,0xaa06df61975503afaecb,0xa81b7d985d540dbfc32e,0xa06bf619765036fd30ba,0x813ff91619409fecc2ec,0x4ff647865027ff2ec32,0x13ff9161d409fecbf0ca,0x4ff647875027ff2cc3a8,0xbfb815c1609fecb70ea0,0xbe59170582ff722b82c1,0xfb845c160efcba2e0b07],#[0xf59141582ff720a0ac1b,0xd64e0560e7ebb2e2b07a,0x5d7815827fb29c0ac1af,0x97e0560d7ebb702b06df,0xd564583d7ae8b22c13fd,0x759160d7ec3ac8b079f5,0xd64582dfb2eb22c1aff8,0xe11609fec8f08b05bfe5,0x845835faedc22c1b7d75,0xd560fbcc82eab04ff65f,0x5583afb0ebaac1e7d965,0x960dbf4c2eab06df6617,0x5827ff22c3ac16ff945d,0x609fec8f0eb04ffe5187,0xc3b7ae8a0ae13fd94e1d,0xebebaac2b875f5d5415,0x3afaeac0ae17bf946057,0x9feca702b867f5d3815c,0xb7ae8b22e13fd96e0570,0xbebaac8b86efe11645c3,0xfb23c22e1d7d7561170e,0xec8aeab84ff65b845c27,0xb28baae1d7f915d570eb,0xc32eab875fe51755c3af,0x2cbaae1d7d965d570ebe,0xa70cb84ff647865c3aff,0x8b8a833fd96e01419fec,0x2e2a0f7d5d971507f6ac,0xb2283f3d7559141dfac3,0xc8a0eef61d64507d7aec,0x22837bd9759141ddfc3a,0xaa0eef61974506f7f2eb],#[0xa83b7d865d541ebebb2e,0xa0ebf619765076fb30ba,0x833ff90619419fecc2ec,0xcff643865067ff2ec32,0x33fd96e1d419fec870ea,0xebf593805877eae3c02c,0xb7d75e01619feca700b0,0xff65f805875faedc02c3,0xf5745c561f7ab22e2b0c,0xf5d1645877ef08b8ac3d,0xd8759161f3ebaac8b0fa,0x65d645875ff0eb22c3af,0x90e1161b7fcbac8b0dbf,0xdb845876faebc22c33fd,0x15d5619fecbf08b0ebf5,0x1755876fb30baac3f759,0x61d61b7fca2ecb0edfa6,0x875867ff28c3ac33ff90,0x91719feca70eb0cff643,0x45c79faecb22e3dbd745,0x164affca2ecb8d7f65d6,0x59377ae9c02c93fd91e0,0x64d7ebb700b26df5d780,0x927fb21c0ac93fd97e01,0x4dbebaf02b26ef5d3815,0x27fb2fc0ac9afd76e056,0xdbecc2eab27cf6517559,0xdff20bb2c9b7e985d564,0xfbc8b0eb25bfe4576592,0xe922c3ac93ff9061d64b,0xfc8b0eb26fde45875937,0xb23c3ac93fd90e1d649f],#[0xc2300baddfe45805d67f,0x28c02ebb7f8460175dbe,0xb300baf5f5d9805d6eff,0x3c02ebd7f9760175bbfc,0x700baedf613805d6efb2,0xc02ebd7d76e0175bbeca,0x2baddfe41815d6efb2d,0xaebb7f8460575dbec23,0x2baf5f5d9815d6eff28c,0xaebb7f8660575dbec330,0xbaddf643815d6eff2cc0,0xeb77d94e0575dbec2702,0xaedf61b815d7afaedc0a,0xb77f9061175bbecb702b,0xf5f5d9845d6eff22c22e,0xd7f9761175bbfcb308ba,0xdf647845d6efb21c22eb,0x7d96e1175ebebb708bad,0xf645765d7afb20bb2eb7,0xf9061975ebeca2ecbaf5,0xe49865d6eff22c32eb77,0x90e1975bbfca30cbafdb,0x53865d6efb23c32eb77d,0x4e01769fec8f00bb5df6,0x3815da7fb21c0aed3fd9,0xe1176bfbc8b08bb4ff65,0x604427fb23c22ed3fd90,0xc110ffccbac0887fe651,0x5443efb2cbaa21ff9965,0x140ffcb0ae0a07dfe597,0x503feae2b0a81ff9965c,0x40fbebaac2a07ef5d161],#[0x37fb0eb0a81efd76585,0xbfecbac2a06ffe1d615,0x3bfaecb8a817ff975854,0xfbfc8aeaa07df6457550,0xeff2cbaa81f7d965d540,0xfecc2eca05ffe4576503,0xf282b82c1bfe985d940d,0xcc8ae0b07fe60570583f,0x328b82c1ff9845c160ff,0xba282b07fd5c541583ff,0xeca0ac1f7d7550560fde,0x3a82b06ff61d41583dfa,0xea0ac17fd9750560dffc,0x282b05ff66141582fff2,0xb8ac1ff5815c560bffcc,0x2b05ff66171583bfae8,0xac1bfd8460560f7eb23,0x2b07df5d581582fff28c,0xac1bfd8760560f7ebb30,0xb07bf61d64582fff2ec0,0xc17fd985d160fdec22e8,0x7df5d584582fff22c22,0x1bfd8761160f7ebb308b,0x7dfe4575582fff2ec22c,0xefd915d960fbfca2eab0,0xffe4587583dfb28bb2c1,0xfd9161d60bffca30eb05,0xf651875837ff22c3ac1b,0xd7458570dffca30eb06f,0x661615c37ff08b0ae1df,0x8660570bffcc2c2b85ff,0x19845c3bfb0cba2e1bfd],#[0x5d541bffc8b0cb86ff6,0x975507eff20baa83f7d9,0x5d561fbfcb2eaa0fdf65,0x75587eff20baac3f7d90,0xd961fbfca2eab0fdf651,0x5593bfb20bb2e3efd905,0x964fbfc82eab27df6417,0x5d7eff22c02ebefd905d,0x75fbfc8b0cbafdfe5180,0xdb7fb02c02edf7f94619,0xbffca300bb6ff611805,0x3ffb22c3ac1ffd875056,0xffeca30eb07ffe458758,0xffb22c32e1fff9461d60,0xfeca300bb7ffe45865c3,0x700570001fff9460176f,0x9600fc01a1029403cc05,0x7740dd419c82f4053a0,0x2852e09f612d822f8408,0xb5434806540c3017282c,0x10021ef03c007440e101,0x209361218234044a084f,0xbbc5550a5c142e27484c,0x18002f345c88b5516442,0x10d7d1a9434146528c45,0xb4c7500e6d1c6237f86e,0x20463f787cc8f541e303,0xa1161224a43808569068,0xb24946925a244e47648c,0x28444f509c3134a260a4,0xb15a82ab45454a63948b,0xcd0b7c16aa2cdc58c8af],#[0x31086120bfd17b52ee05,0x819d4331e6504c8298d2,0xcf0d7b9abb35106930d0,0x393c7164e059ba236de6,0x29e093b9a75fce9d1cec,0xde8f9a9f023d7a7a28f2,0x417081850129fe93f5a7,0xda1ff43aa85f909ca0fd,0xd9d19122e6455489b911,0x494a91a521223df47588,0x1a5fe4b4e956528ea4e1,0xf253c2273f4e069a8d32,0x5268a32d4432853501c9,0xbaa69545aa7a14daa970,0xf55f32b8f5694abf155,0x5b74b56968f2ce25916b,0xe2f405e1abb45738ae23,0x2c583ab0305fd6bebd7b,0x63ccc6858ae312061c8c,0x9333f6618cb1d9413234,0x1e9a1f340b67b0ce959b,0x6ba6d6a5ab2351f697ed,0x236f66d86da1db25b60f,0x1c1c1a37ef6f78de01ba,0x7380e611c9b38e87158e,0x8bafe7584e9f5d253a05,0x205e0c3be57752edb5d9,0x7ba2f655eacbd1d79c2f,0xa3f0f7d82fa15f293e0d,0x24a026c0117f86fe1dfa,0x83d7069a0b0c12581af0,0x8c383868f0b9e13f4227],#[0x51628044a088a510121e,0x8cd1188e2f3c5b48b151,0x847948ec31cde370469b,0x482464c896909120563e,0x94e128424eec9aa92dd2,0xb4bff973f2d6a58acab5,0x7966cbcd5299e532b662,0x9efb3cbe770ce8a9c553,0xdd0dfa13541327ff4fb9,0xaaa920d1d8a327455e88,0xa91550ce9ee5385a66f4,0x85622ab4f55aea9354e1,0xfb6bcfd75aae3d5b1eb3,0xb2c36472c6bd889b0775,0xb5abab4fd68e6cfa59af,0x1aae09dbd7b7136d12d7,0xbb9975d6e93dcf4b95f7,0xbdf64be1b7afef3d5e23,0x40b05ee078c0557f4efc,0xc4c9887f0ed618cc2598,0x563f3c75d8da718962c4,0x6b32af6522c9bb928722,0xce2f9b4b342663fcbe39,0xee8b8d0c3a0733ebe789,0x8a74fb69b1d2d9a4c347,0xd717ad1b580eab3d4cba,0x7eba9d747ae775cbeb91,0x11c0e08d89d777aed75d,0xa3f0382488c3017e2f19,0x382361c3e0de361307c2,0x5e07046c4f18200be170,0x3822a2430c20bc438d8],#[0xc11512c20c71789860bf,0x704aa106389c50ce0f81,0xc85f8b42e261b07c015,0xb93c6e2f102fc0e08607,0x7150245fc5e231b81c10,0x488dc603f0f85c0e0894,0xb81c11c8e02e370f81c1,0x38470382392386150570,0x1781c11c8d890c8612bc,0xc2a3f03824f0c33420c6,0xf0382121c380ce1e1b0b,0x1c0e08a8402f181c181a,0x971467c461f038219243,0x8bc4e186781c10c0e2a0,0x8c4278bc4a361f822723,0x8dc681f0b81c1450ac6,0x8039e08dc70e71b85c0e,0x2703822b180a308230b,0x50ac60270b802be08dc6,0x804be0898681f0b81c14,0xe301385c0e08dc71470b,0xe1e10e370b81c118101c,0x60a40f85c062f04663c7,0xe08d8681f0b81c1450ac,0x381c1158c040b05381c2,0x8616138a361570382332,0x1f09c51b05385c0e08cc,0x4663a1607c2e0705142b,0xe08cc8c27144dc2e070,0x382331c29c5c20db85c,0xc0e08bc662e106c14e17,0x3178c31e170382361785],#[0x38231178c07e1703823,0x47c207381c11c8b47e17,0x107950303b1b85c0e08c,0x424e289a2f476370b81c,0xe2861f846370b81c10b9,0x7c207f038221178e2f0,0x233178fc2e0704343316,0x57068a21183703617038,0xdc2e07044c331785c00,0x233178bc2e012f82210d,0x382f81c1130ac5e17038,0xac6c1b1785c0e0c2842,0x7c0e08ac7a383f81c112,0x1703830a0f8e0fc1f086,0x85c007f0614211f06c6e,0xa2f0a8dc0c1f0446389b,0x88b84e17028d83e08907,0x85c0e088c702f0382261,0xc192f81c1198d46a2e0f,0x884702f038226158bc2,0x81c1199145a3e0f85c0e,0xe08a06628398418a2e0f,0xc8dc2e070446281785c0,0x81c1188c2461703830f1,0xe1703821f120ec6c1f0b,0x1083e0704622a198f83,0x80c10854c6c1f0382392,0x2c31426360f81c1150c4,0x18a1714554763703828f,0x21707c0e088862329848,0xe2442d1f0983e0704444,0x31238546a3f0307c10f8],#[0x87c8236100f83e170382,0xe241a8c05a3e0f85c0e0,0x170382311b07c2e07043,0x85c0c1f0442241b0746e,0x28998fc2e003f822123,0x288468570b81c110c3c6,0x810ae087c7e170215c16,0xe151f81c10f8e05e1087,0x707c2a3f038221201b83,0x806f0b8147e08a060681,0x140a266370b800fe088c,0x2fc1158dc2e00cb8230,0x76370b81c1179010e170,0x8d8dc2e07046438ac460,0x60e02b85c0e08dc6158,0x1880cc6e131f81c10807,0xb81c1108c05610c381c,0xc383e0f85c0e08704637,0xe08dc56360f85c0e0c2,0x2d07c0e08c0542b1b85c,0x42e260c48c6157038239,0x31b07c01570460406321,0x1421531b81c11b8e18a1,0x1a130b83a3f038222203,0x4684a3e1707c0e088881,0x841180f83e170382301c,0x18d460251f07c2e07043,0x81c1180d83e1703821c1,0xe17028dc1118f46c1f0b,0xe0f46e17038237170785,0x8237141983e151f81c10,0xe17038347108ec6e1703],#[0x88dc2e00438230170785,0x2fc1158c0ae105381c11,0xa70385c11b0c14e1700,0x828391b70b81c1259216,0xb11e1b85c0e08bc70be1,0x178e83c370385c1328c2,0x3824a250c14e170289c1,0x6188814c1f143236e170,0xf85c0e087c483703822,0x38231180fc0e08c4542e,0x3e170382311815c20a70,0x1e0dc2e070496261a898,0x46c3c198583e00ab8236,0x2e08d850c8528bc0e170,0xf85c025f044c385381c,0xc40b0af81c2e08bc7830,0x150d86e1703821c118d,0x5381c1180c07a2f03823,0x45c1f0b81c1180c4be10,0x8cd0dc4e2d1f81c11511,0xe09e220f8b47e0704544,0x50642fc4e2f03822a1c5,0x47c5e261b0747e07041c,0xe251f0d83e07041c5090,0x385c00cf044c309047c5,0x76260f85c0a3f043e384,0xf8ec5c1f0a8fc0e0870,0xf821c1f0786e17028fc1,0x12f045e2e1b07c2e051,0xd05c6e07044a2f1f85c,0x46e288f062ae07046c5c,0x51385c0e08bc60c55585],#[0xb450571985c0e08d87e3,0xc0e087c702f038226158,0xf0b81c1158c0dc1e1f85,0xc45e17004dc1179183c3,0x151b8183c3f0438385a8,0x30821560e8dc0e08d88e,0x84b0817c61970382361c,0x68ac40660f0fc2e07043,0xd6361f8945e170382392,0x1d8a8324703823615100,0xc6e2b1307c0e08d8304c,0x6182683e070454361885,0x38217298cc5e0063823,0x1b2c32c6a17138a2f157,0xf1724a0f8bc46370780,0x8bf178818e07045440be,0x30746e17030fc10614c6,0x3e1703828b0e0c0d02b1,0x108bc6e1703821a128b8,0xb81c1128cc50570b81c1,0x5e3f098dc0857045e370,0xe08bc71130a8dc0c2704,0x3828a0d0c192370b8184,0x6e17038211178bc2a370,0x178ac6e170309c105868,0xb81c18586870270b81c1,0x2e1f038225198ec6c270,0x8318463703822f210c4,0x85c251f8022e086c8075,0x9180f84e1703822f1c41,0xbc5a351f09c2e0704343,0xc0e088c582f0b81c1160],#[0x3140bc2e070442251785,0xb81c1118b05e1703822,0x382361a87c2e0704742f,0x2e050f82241c0bc2e00b,0xa98fc0e08da2a561b09c,0xc2e070468386185c5a18,0x8db85c0e08d071309287,0x4743703821f1b0805a1,0xc0e08543e307c17c2e07,0x41b85c0e092c4c370a8f,0x7c6c2c1185c018f046c3,0xc3e17038231200bc0e08,0x70b804be089868e4582b,0xbc51670b808ae08ac683,0xc0e0c545e3e1b81c10f8,0xf082bc0e08bc60c03985,0xa86c370b81c11207c605,0xc1e006c80421b81c1188,0x707801b204885c261a8f,0x19e08986122168f84c3,0x18db85c0e08d0708f0b8,0x8b84e17028fc10d0e056,0xfc10d0fc20af03823115,0x22b82261b0d84e17028,0xc19e17038236168dc2e,0x5c1130d46e122b81c113,0x3703821a118dc2a37021,0xc58b0b703828b130bc2c,0x1186185c41531e87c0e0,0xd32c7a1f0b81c10b152b,0x7e105b81c1130c23e20a,0x130cc3c370b81c1180cc],#[0x383161b0cc70b7038223,0x7e17038230198c236170,0x158f86e1703821c118ec,0x3821b180c86e0704602a,0x7c2e1b81c10d9084c370,0x1433c2e07045e388d094,0xa2c3617801fe08d850fe,0x7e070434442f85c0e086,0x13830b0d0c0c0261b854,0xc4e1703830b0d0fc2e03,0x330dc2a3f03821c1e2c,0xd860230f842be0704484,0xc1198e0ce17028fc1160,0x50f82221f04c418d0f81,0x22e07046c30c70ec5e0,0x17198b43e0704604860a,0x8bc4a1f0382222e300ec,0xe07044450cc24874c91b,0x84430904612e2f128787,0xe088c5440606bc0e084,0x31c1150a240c11511c,0x132210f81c1120a8862f,0xa678bc40c707802a2046,0x3c5e231b83c00c06caa1,0x2c2381c11b0a871208c1,0xec51170211c10d8f872,0x1c1178e45e07046c3913,0x38208dc0e08a872360b8,0x8a851861e10c6e070436,0xfc084704543d138018e0,0x2d1381c11b0609121170,0x8bc0e08e46c20e187c6e],#[0x18e08e46c1703822f1c,0xaa2437c1e00e47a250f8,0x8a882186381c11c8a182,0x636144613225170fc0e0,0x2f038239151382e07046,0x81c11c8a8809a1e8846a,0xe0704401b182644a2e1f,0xb0a46e00638236143022,0x83c01c860ac170382331,0x1b0607a250e0545630db,0xb81c10c943b630e783c0,0x11c8e1761e0b8bc4198a,0x382391f040ae18d381c,0xc0c3f0436531017c3c17,0x7046248904609e2f128d,0x21d26300ec13138746e0,0x78f09207178987a306f8,0x30222b04c51851b81c11,0x1c48230971788c3e0704,0x5440908a88e0704462a,0x10f8e230991031c0e089,0x1f820d2b0d87e170287c,0x362418c50261a87c2e06,0x100c61e1f8b44e070b82,0x246198b87e170289c10d,0x30c3010f0e17c2e07063,0x81c10e0f86e17030fc11,0xe17045636201986c3f0b,0x38414e08cc80821509c0,0xe170466361f8b841b70,0x251fc1e006c72361029c,0x46c323c85c0e08a87231],#[0xe17046c3b1b85c0e08c,0xb0bc0e0928b630530bc,0xc1459655868541983a37,0x210c080368d83e151381,0xc1c430b44e00a98fc13d,0x6e430930588688e2b46,0x10e12592a91b85c0e08c,0x4090a8328d83e122f81c,0x48541946e131e89c0e0a,0x200da360f85c0257043e,0x6e0f84c7c2f03825524,0xe09c2e0704602b1b8e10,0x6e31204890e0704622a1,0xe0f00366d0b8030e08e4,0x9024b1121841231a8e39,0x6128439e0704b02a2031,0xac4c1f0b81c12c87c963,0x960f85c02cf046048401,0x4859e170382371866841,0x2408629c0e1704ca2f1c,0xb10364a91c29c0e17047,0x6c44501ec5e070b82331,0x1b10102385b81c2e0850,0x45e38418b14e070b8232,0x10d19472399781c2e088,0x3826517904719f0385c,0xc2e09945e391d849819f,0xf0385c1328bc74a0cf81,0x3c019f0b8294178e9419,0x2f1843c0e17043465182,0x705282f2067c0e1704a2,0x5c14a1947160a289c0e1],#[0x1253824a1590210d7038,0x85c0e08ac4c30541fc0e,0x22f03844ae0a5056492b,0x48bc2e070456361c6c34,0x52291381c2e08ac6c385,0x63f0454470385c1158bc,0xb82141993448af146dc0,0x2e08cc90a91f8a36e070,0x628491c2944e28db81c,0x361e2a21e28db81c263f,0x92c4c40668bc0e105382,0x24b1312160861b81c2e0,0x30cc51c8c88986e070b8,0x21c0e08a86c370385c11,0x8811f81c20a7046c4c5a,0xc2945e070b8236213216,0x60870385c18a0d874c91,0x1189c51b7038258150e1,0xb81c1198d0ae07045436,0x1178e480ac5189c51b70,0x6282b1c2d146270b81c,0x47e0c504c3b1381c2a3f,0x8db81c2e08cca62f0b81,0x1c2e08cc88a31468c4e2,0x70b82362629c51b3138,0x85c11b0f14620e464c5e,0xe070462361e331462f03,0xb85c0e0a5c384d188bc2,0x2e025f8231242a0c62d1,0xabc11b0c2f228d28dc,0x45e070b82331b0e23e17,0x62033c0e142f82361929],#[0xc474ca5217c0e1704643,0x251790c4a370b81c18b8,0x9605e3c1cb0c61af0383,0x3c0928cc86310b81c192,0x494b0331e0e58619278,0x8e36e070444630c85c1e,0x151018cab152b8511b0e,0x543b0f0b421b7078058,0x1188d871008d2bc0e08c,0xb81c11992952c61b81c,0xc1850cc7618518a36c27,0x70382221b0ac51b70b81,0xd874b10b81c1150d864b,0xc1110e140ce1785c0e08,0x7044436178b87a1f006d,0x10922707801b1c8c45e0,0x44278987a30e783c00d9,0x8f14a28db85c0e08cc68,0x2301e28c4e1703822f1c,0x31687c2e07063]]
set_option maxRecDepth 16000 in
def g255H10 := limbs80 #[#[0x3761100220211220010,0x2000020810010101300,0x173010011016000832,0x800024fb308c23021140,0x3ba8d8640000920000f6,0x2a094c00142a65900004,0xd8381840000009,0x7bf2240000000000000,0xb710000e040df,0x800018c8000000436800,0xe5566eb02247126,0x0,0x3d0c000e5541c40000,0x25c8,0x1c7b0000b04000,0x0,0x80000000000000000000,0x6c000000703adc32fba2,0x51000000000000000038,0xb600023c75620002,0x5330000001a630000000,0x39a400000000004ee000,0xa80800,0x2d764ec32d800009800,0x4605a8000000000c2380,0x19daf65402ba80008,0xd300000000000000000,0x85d00038b8,0x4cfda378000000000018,0x18c80000001915c3,0x3066bf5fc39c85000000,0x478000000000000619c8],#[0x388c0000001,0xe4f0000,0xc1863c377883c000000,0x473000000000044ec44,0xdb2000000000204a00,0x0,0xa08000000000000010a0,0xd470000000000c3f3,0x2506000a528000000,0xe00000039e4000000000,0x40000001c0057069ea18,0x42851317,0x700c000000000502c0,0x5ae1d5a0000,0x30634cb0000000,0x118c000520c049526000,0xf000000009f8be000000,0x50000000000329f48825,0x720000000001c1c582aa,0x12d70000000000a,0xe1f00000000000000000,0x1059a2d0002378001,0x38d40000b8c000000446,0x7000000000000000014b,0xcb2c906e0001c6600021,0x405c00181600000038,0x81be9b0001a800000000,0x5adc0000000000000,0x400000041be01e53e000,0x2000588400000000059d,0x3d9a00000000000000f,0x709800146900000],#[0x1b0e0005af00000,0x26e0000001ddc0000000,0x169cf6aca48001,0x2000000000147a000000,0x5660963d2,0xe800030120fc000cfc00,0x3cc00000041000034,0x3b6a1680000,0x61800016a40000000,0x896000659f828514000,0x8650000000000621800,0x2412c4d0628be800000,0x872eb9000000000000,0x20400000000000000000,0x63495300018f167c0001,0x3d5000000000025db,0x200000000020fe000361,0x4fe0007a8d5a,0x182f0005158000ec000,0xc3b00000000,0x8200000000000,0xcd40000000000,0x2d32000c86c890000000,0x8f8000000,0xae0ae29826b7a2000000,0x78,0x1de1c0100000034ec0,0x11380025340007248,0x6168000,0x43c000000000,0x141ba89000000,0xf0600],#[0x28a40,0x91600000000000000000,0x12f90000001,0x3617e4001ae188000000,0x4e5728fa1d200068aaab,0xc14a485d42f00039b60f,0xa42d81da,0x58710000000024260,0xc87c3872bd6120000000,0x1aeb67aaa84001,0xf88450280000002d8000,0x5880000000002df,0x401ac0903900,0x183384ee2500000,0x34448d8e1e0,0x625c00000050a8000,0x69500050e8001a51,0x125a556000a24000,0x362800,0x5116847d5281000000,0x59f10a000000097a0,0x190c8398]]
set_option maxRecDepth 16000 in
def g255D11 := limbs80 #[#[0x50110d7d765d75f5d570,0x443fe5c110ff960443fe,0xbfd84443fd5c510ff541,0x61910f7d75442ffe1110,0x442ff61d10bff86442ff,0xbff81503fe5c140bff87,0x61940f7d75503ef5d140,0x502ff61d40bff86502ff,0xbff81583fe5c160bff87,0x5d560bff84583bf59160,0x582ff61d60efd76583df,0xdfd745c2ffe0570bff87,0xe0141bff865c2ffe1170,0x507ef59141ff571506ff,0xbfd86507df5d541fbd74,0xe1d41bfd87506ffe1941,0x587fd5c561bff80586ff,0xf7d75586ffe1161efd64,0xe1d61bfd87587bf5d961,0x5937f5d971dfd745c6ff,0xfbd74592ffe0564bff80,0x61d64efd76593df5d564,0x5d7df60175bff87592ff,0xf7f815d7df60575f7f80,0x61975f7f845d7df61175,0x5daffe0176f7f865d7df,0xffd64442ffe1176bff81,0x5d910ffd84443ff5d110,0x503ff61d10ffd86443ff,0xffd81503ff5c540ffd61,0x61d40ffd86503ff5d940,0x583ff5c560ffd41583ff],#[0xffd84583ff5d160ffd81,0x58570ffd415c3ff61d60,0x5c3ff59170ffd815c3ff,0xffd80507ff61970ffd84,0x60161ffd86507ff5d941,0x587ff61161ffd74587ff,0xffd80593ff59171ffd87,0x60176ffd87593ff60564,0x3ff61176ffd815dbff,0xf01a605000f2027004e0,0x3b20d302ee0aa024207,0x57614a04e2125044e0fe,0x6a1c706de1a0063a1750,0xe238089220f07f61ec07,0x2a30a4628209c225f093,0x100bda2e50b562c00ac2,0x50d7e34c0cea32b0c763,0xf623c90ec639e0e1a37,0x11642e107240b0fe63e8,0xfa4a9125e48211c245b1,0x6520143a4f9139e4d012,0x58715ce564154a54114c,0x417c25dd16fe5ac1662,0x719c665c190262f18766,0x1bba6d51b166b21a7268,0xd7674e1cf27271c4e702,0x2a7bb1ea67961e0a7711,0x982e206a8051fc67de1f,0x241d085f1b1713020f04,0x4a078219c5c4c3c046c1,0x718703c4116130b0304e,0xc0f85144684c0c2c1392],#[0x3f140f1a111f0b0304d8,0x4c2c045c18333288c5c,0xa0f0b0304ac288110f46,0x6844583c2c0c133303d1,0xb00e7043c811100f070,0x844783c0c1362c1b1d17,0xb0b0304c4c421823c5c6,0x10f2054503c1c16120d1,0xaf0428a26c7c546c2c0c,0xc10f205c3c18160f0b00,0xb0304d8926c6c547c2c0,0x33c1102217185c411f0,0xf0b03042c9070644c2c,0x858347c0c12f1b103442,0xb0304c0c42182490c6c4,0x205850401c12151a0f0,0x42cb07043746c2c0c11,0x1cc85c40131a0c730b03,0xb051c9c6c447c2c0c110,0x13114205c5313161b030,0x170b04d88070544c2c0c,0xc2c0c130142058520f01,0x61a0f011f04a8a070445,0x583c0c2c147250863131,0x1e1a0f030b04b1914c4c,0xc0c2c1141c645c531711,0x5130b0304ac5c8c5c447,0x7c68336c2c0c10b20181,0x17231b13091703045c71,0x3049462fc5c446c2c0c1,0x7c3c2c0c1251c190f0b0,0x160f0b011b0610bcac60],#[0xc607c3c2c0c1251c5844,0xf30601d0b1b0f0304948,0x5110785034684c2c0c12,0x25180d1b0b0304946161,0xf030b04447c6c3c2c0c1,0x53a43c2c0c115231b0d1,0xc30561b0b0304289070,0x16158445c2c0c1362b17,0xd140f0b0304bc548c31f,0x395c5c3848647c0c12c1,0x64551f0b0304e4942182,0xc3861fc2c0c10a2e130c,0xd1f0b030454734191505,0x8c6c3c2c0c10b0a1f170,0x1620670d18e70b030428,0x4d85882bc7c443c2c0c1,0x26c10b200f1d130b030,0x1e1b0304d8b164386c2c,0xc0c136290862130ce615,0x3042ca39c316194785c2,0x1162064580c121b089b0,0xf0304a2bc4c347c2c0c,0xc1182209186317121c89,0x30304e4a02c6c5c443c0,0x139182119150c621ca82,0xab0304d8b4645c344c0c,0x3618220919110c621d14,0xd1b0700a4443c645c0c1,0xc118210c246317121c6,0xb030464802c5c4c346c,0xc244c0c1191ccf17110f,0x4100f0b030498648c3c5],#[0x74683160fc0c12b36211,0xf2325143c2f030498e4,0x304e48111045c221c0c1,0xfc10f232465183e0f0b0,0x2b043c7c9151446c2c01,0x1fc0c11c385d17088700,0x55108544c715904683c2,0x4c11043182b0b0304dc9,0xc11100f44c2c0c124282,0x10411d18920f0b0304e4,0x14c21cc0c11024206643,0x45c402f0b030470c8816,0x4c7838644c0c2c11a513,0x1a0f030b0528a9411451,0xc0c2c13914291050db16,0xf030b052ca441547450f,0x2c136142914521b10e60,0xb045094510474416c0c,0xc1252f1c645f13151f03,0xd1b0b0304d8c8617c2c0,0xc136245d5714561e0c8,0x304d88170f45c60ac2c,0xc2c0c136245e0c591b0b,0xb030b045ca321710c60b,0xc11123206450bf17111,0xb030494cc7100fc221c,0x11c2c046c11a23250c67,0xc53087f0304548c81615,0x14515c30bc2c0c13a243,0x585445170b03048cb093,0x8719150ac2c0c11f3420,0x116242610582b0304acd],#[0x458909141043c2c01cc,0xc1161c24544513086b03,0xb030464a1944c21a0bc0,0xc139245c5314cf110f0,0x304e49341915c30ac2c,0x6459130c2f0b]]
set_option maxRecDepth 16000 in
def g255H11 := limbs80 #[#[0x4038481a37030340a15,0x543a0002846000009c4a,0x34043500804380012820,0xd01c8e020c805ea01028,0xb0a8189c120f0f0081f0,0x58f00005d08b000ac0c4,0x808000a8100202c98bc2,0x181d01a0858310280,0x260082ed24f1e9400820,0x771a03c4800018241802,0x14777a9a400fab50044e,0x9524436a582372265810,0x4b7655e6d13e72dc001,0x828905b42e45b0a4e000,0x2b4ef0e1862b6ae2d67,0xc84b859ae24f065a4f00,0x77caff31b17fb360002e,0xc22000000394ee713694,0xd34f48d2b8c03bc472cf,0x9b0173ea819a90da087e,0x4834328163cecee19881,0x491c732f58992a40fa49,0x46eb723c48c6c43643f3,0x550819e9087e208223b2,0x80b5421dab725173799a,0x89b854f438e460bff292,0x800018924dc4ab96f6bd,0x20000001536ea8f36c8c,0xcb183163029362d628,0x7833aa8726e20001a940,0xd8c00023e4ccb6776,0xa7ec1d459f450d2fd5c8],#[0xbec1117dc2141ddc8000,0x661bb30ca9ac9965642,0x58713a61f11610080166,0xcb3b083ad727eaec09ec,0x4ed2e147fc0b34a31ec4,0xe37f2e0bde8154d5c143,0xa3d55f6a5d76bc1ae6fa,0xc51488c48778cf322750,0x1e0529ff47ad5c4e,0x31eaf97344a4662e12d8,0x248e3800097e000005f8,0xa95e9a0002d9625864b4,0x906c3d3054932a352a49,0xc0002a3ca6ed54122cda,0x20005223a18d5d810860,0x7b64a00076fa0b40cc85,0xe13420a5394728a092,0xd78000a99158395eaec0,0xedec4c75e41e40000002,0xb434000f0fdc7f2b5a57,0x9a1478ad9e228a415560,0x5a16c0000000001e5049,0xd6b4c50ca275ddc000b8,0x20dd2f68e6dda215e436,0xd9bc5135f7dde322b402,0x3014975a01f834b66,0xf5c2b1c7b8c025611efe,0x3a1b2a05c1f96c524581,0x5b1da16370d04ffa322f,0x2cb224cea6b6742423e1,0xcc3c56000ba7c61690ac,0x87b1a83bb199040452f2],#[0x6c91d8a279111e2f191d,0x4b05a5d9e2b5a93626be,0xcd56287b120a39cba155,0x9b701513fa0e44a69512,0x4bea98439b566541d654,0xe5ce74b5a839d0758e0b,0xe1a52026694a2b563ba7,0x24e753c1fe009e73948,0xe8885e0427b21e3bd189,0xd5a34000cb319605a310,0x6751f23720600bd73d58,0x31a11443182579bfebf7,0xd26f1e431f7054f86bac,0xd07d68ce0800000bbc36,0x88106b419c111bec2188,0x8ddd09f444578fb53916,0x1d778d625968ab5ee553,0x55b50c876b09b590d138,0x317aa2e053d21c]]
def g255D12 := limbs80 #[#[0xffac1ff503fe8877d75,0x64ffae3ff587fea0ffd7,0x1061f001ff5dbfeba7fd,0x53b2fc34ee32ea921a64,0x20920a345890c3c0824,0x70a041247c78b1820385,0xd001c2824908f1a2050,0x5881c1c085049291e245,0xc6861424281052925e34,0x4158f161840d0a041243,0x50209212345870a04114,0x850208b20b47890c3058,0x4861c342810490b1a243,0x662c]]
def g255H12 := limbs80 #[#[0x8f002003b1c182047084,0x29dc31d400010c0032,0x1d5fa5d049e79e12c,0x65486a01d000e0b85c00,0x3e47901a6002c575,0x1e23ba82c000000,0x68f91bac2001a5000c04,0x52911e2ca0c000000b4,0xdecb600000033c8e0000,0x5c00071b0191800051d,0xb80c2268768001d54ec,0x15800054e41ad680000,0x1edd0b1a0000063c0000,0x63947e300006e4eb264f,0xc001534cd000f6a82400,0x4dd062e5225100012a22,0x10ca4c0e0000006f8003,0xddb21df01d9b0c8b1c8d,0xa52b22d097abc44000ae,0xda17ccbe72c91f991140,0xfaa0036c4a100153b038,0x7d0b5c5d226f19e8a800,0x10724956b50]]
def g255D13 (j : Nat) := if j=0 then 0x7185103080048ff else 0
def g255H13 := limbs80 #[#[0x6db57491fc540030da87,0x61536]]
def g255L : Nat → Packing
  | 7 => (7,6,6,0,0,6,0,g255D7)
  | 8 => (81,5,6,0,0,12,0,g255D8)
  | 9 => (278,4,6,0,0,15,0,g255D9)
  | 10 => (405,3,6,0,0,15,0,g255D10)
  | 11 => (109,2,6,0,0,14,0,g255D11)
  | 12 => (11,1,6,0,0,10,0,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupWord 1 19 0 7 3 0 g255H8
  | 9 => lookupWord 20 211 3 11 7 0 g255H9
  | 10 => lookupWord 69 701 4 13 9 0 g255H10
  | 11 => lookupWord 101 439 9 13 9 0 g255H11
  | 12 => lookupWord 27 149 6 11 7 0 g255H12
  | 13 => lookupWord 2 13 3 8 4 0 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : CutRow g255 7 0 7 := by
  apply polarBlock (data:=fun _ => (word80 [0x20002090ca2,0x12630800010090c04463,0x800010090c044630800,0x10090c0447300400209,0x44861250020002090ca2,0x12720040020944861250])) rfl
  decide +kernel
theorem g255B7 : CutRow g255 7 0 7 := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : CutRow g255 8 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_1 : CutRow g255 8 1 21 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_22 : CutRow g255 8 22 7 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_29 : CutRow g255 8 29 48 := by
  apply polarBlock (data:=fun _ => (word80 [0x410209,0x448612410020828160a2,0x9200825040241025140,0x8250402410251400200,0x2090ca2128300440401,0x8104425108250110c846,0x51400041020944861241,0x220281c0a221600825,0x4024102514001040029,0x141a485300208100a042,0x92000a4110180484552,0x840112084c44720020,0x828160a2093000410102,0x4104124100840112084c,0x44720140311208540b52,0x800010090c044840064,0x1181c064434008000100,0x90c04484014031120854,0xb520140311208540b52,0x140311208540b820040,0x2094486126100400209,0x44861261010011824070,0x9520044040301044240,0x800010090c044840100,0x11120854095201001281,0x44b009520082028340a8,0x24620082020300882462,0x820203008824620082,0x2030088246200820203,0x882462008802018088,0x846200200100a0420970,0xa08100a0420d200041,0x2094486124100410209,0x44861241044201824064,0x82710041010241041241,0x4420182406482810442,0x1824064828000a41112,0x84c458100840112084c,0x44620021040241021140])) rfl
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_77 : CutRow g255 8 77 4 := by
  apply polarBlock (data:=fun _ => (word80 [0x285,0x1824068546200208281,0x60a20920028501824068,0x54620825040241021140])) rfl
  decide +kernel
theorem g255B8 : CutRow g255 8 0 81 := (@joinRow g255 8 0 22 59 (@joinRow g255 8 0 1 21 g255P8_0 g255P8_1) (@joinRow g255 8 22 7 52 g255P8_22 (@joinRow g255 8 29 48 4 g255P8_29 g255P8_77)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : CutRow g255 9 0 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_48 : CutRow g255 9 48 48 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_96 : CutRow g255 9 96 11 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_107 : CutRow g255 9 107 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_155 : CutRow g255 9 155 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_203 : CutRow g255 9 203 41 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_244 : CutRow g255 9 244 8 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_252 : CutRow g255 9 252 26 := by
  apply polarBlock (data:=fun _ => (word80 [0x820281c0a82462,0x820201808824620041,0x2094486124100410209,0x44861241004102094486,0x12410020828160a20930,0x20828160a209300104,0x29141a485300208281,0x60a2092000a411018048,0x45520020828160a20930,0x20828160a209300022,0x281c0a2218000820201,0x80882472008202018088,0x24720041020944861241,0x4400a1502c42510104,0x190c16485301040029,0x141a485300820281c0a8,0x24720082020180882472,0x820201808824720082,0x2018088247200a41101,0x8048455200a411018048,0x45520082020180882482])) rfl
  decide +kernel
theorem g255B9 : CutRow g255 9 0 278 := (@joinRow g255 9 0 155 123 (@joinRow g255 9 0 96 59 (@joinRow g255 9 0 48 48 g255P9_0 g255P9_48) (@joinRow g255 9 96 11 48 g255P9_96 g255P9_107)) (@joinRow g255 9 155 89 34 (@joinRow g255 9 155 48 41 g255P9_155 g255P9_203) (@joinRow g255 9 244 8 26 g255P9_244 g255P9_252)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : CutRow g255 10 0 20 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_20 : CutRow g255 10 20 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_68 : CutRow g255 10 68 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_116 : CutRow g255 10 116 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_164 : CutRow g255 10 164 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_212 : CutRow g255 10 212 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_260 : CutRow g255 10 260 42 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_302 : CutRow g255 10 302 48 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_350 : CutRow g255 10 350 46 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_396 : CutRow g255 10 396 9 := by
  apply polarBlock (data:=fun _ => (word80 [0x82,0x281c0a8245200820201,0x80882452008202018088,0x24520082020180882452,0x820281c0a824520082,0x2018088245200820201,0x80882452008202018088,0x24520082020180882452])) rfl
  decide +kernel
theorem g255B10 : CutRow g255 10 0 405 := (@joinRow g255 10 0 212 193 (@joinRow g255 10 0 68 144 (@joinRow g255 10 0 20 48 g255P10_0 g255P10_20) (@joinRow g255 10 68 48 96 g255P10_68 (@joinRow g255 10 116 48 48 g255P10_116 g255P10_164))) (@joinRow g255 10 212 90 103 (@joinRow g255 10 212 48 42 g255P10_212 g255P10_260) (@joinRow g255 10 302 48 55 g255P10_302 (@joinRow g255 10 350 46 9 g255P10_350 g255P10_396))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : CutRow g255 11 0 2 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_2 : CutRow g255 11 2 48 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_50 : CutRow g255 11 50 21 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_71 : CutRow g255 11 71 38 := by
  apply checkedRow
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : CutRow g255 11 0 109 := (@joinRow g255 11 0 50 59 (@joinRow g255 11 0 2 48 g255P11_0 g255P11_2) (@joinRow g255 11 50 21 38 g255P11_50 g255P11_71))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : CutRow g255 12 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_1 : CutRow g255 12 1 10 := by
  apply checkedRow
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : CutRow g255 12 0 11 := (@joinRow g255 12 0 1 10 g255P12_0 g255P12_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : CutRow g255 13 0 1 := by
  apply checkedRow
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : CutRow g255 13 0 1 := g255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : mixedTables g255 13 := by
  intro k hk
  interval_cases k
  · exact mixedEmpty g255 0 0
  · exact mixedEmpty g255 1 0
  · exact mixedEmpty g255 2 0
  · exact mixedEmpty g255 3 0
  · exact mixedEmpty g255 4 0
  · exact mixedEmpty g255 5 0
  · exact mixedEmpty g255 6 0
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K254) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact mixedRoot (g:=g255) (top:=13) (i:=0) (before_sound K254 V254) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_32506

open PEqualNP.Outside.L_meta_32506 in
theorem PEqualNP.Outside.L_meta_32506 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 1, 4, 0, 5, 2, 5, 3, 5, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
