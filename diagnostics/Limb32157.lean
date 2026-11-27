import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_32157.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_32157
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffffffe,0xfffafffffffefffffff0,0xfefefefeeeccaa00ffff,0xffffffffffffffffffff,0xfffefffafffffffeffff,0xfff0fefefefeeeccaa00]))
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 2 &&& x 7) ||| (x 3 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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

def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,2]⟩,⟨.or,[3,5]⟩,⟨.or,[4,5]⟩,⟨.or,[0,7]⟩,⟨.or,[2,3]⟩,⟨.or,[4,7]⟩,⟨.or,[12,13]⟩,⟨.or,[5,7]⟩,⟨.and,[10,1]⟩,⟨.and,[11,9]⟩,⟨.and,[14,6]⟩,⟨.and,[15,8]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 2, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 2, 0] : List Nat).getD i.val 0))

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
def g137Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0)]
def g137C : List ColumnInfo := []
def g137A : List (List Nat) := [[],[115],[48],[48,112],[112,48],[112]]
def g137D3 (j : Nat) := if j=0 then 0x7 else 0
def g137L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g137D3)
  | _ => emptyPacking
def g137I (_ _ : Nat) : Option (Nat × Nat) := none
def g137 : Forest := ⟨137,3,fun i => g137Y[i]?.getD (0,0),g137C,g137A,g137L,g137I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g137P3_0 : block g137 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g137B3 : block g137 3 0 1=true := g137P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g137T : checkedTables g137 3 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g137B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g137G : graphValid g137 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low137 : Lower true (varsX 137) (graphGoal 137) 4 := lower_forest (g:=g137) (i:=0) (hints:=3) (before_sound [] baseKnown) g137G g137T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K137 := extendKnown [] 4 [(137,[]),(161,[83,67]),(164,[32,16,83,67]),(196,[32,16,99,67,84]),(200,[48,16,33,98,66,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V137 : Known true K137 := extend_ok (m:=137) baseKnown low137 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe6de3fff03fff1ffe6,0xde3fff03fff1ffe6de3f])),(BitVec.ofNat 152 (word80 [0x648490a2850240206,0x48490a28502402064849]))),((BitVec.ofNat 152 (word80 [0x19e9c0fffc07fe3f19,0xe9c0fffc07fe3f19e9c0])),(BitVec.ofNat 152 (word80 [0x50e8db2c3161408450,0xe8db2c3161408450e8db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b04185892808,0xa7b6b04185892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x891524c08206003089,0x1524c082060030891524]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := []
def g43A : List (List Nat) := [[],[80,49]]
def g43D3 (j : Nat) := if j=0 then 0xf else 0
def g43L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g43D3)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,3,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P3_0 : block g43 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B3 : block g43 3 0 1=true := g43P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 3 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K137) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K137 V137) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K137 4 [(43,[]),(45,[33]),(51,[16,67]),(54,[16,32,67]),(77,[96,16,33,50,83]),(86,[96,32,50,67,84]),(89,[96,16,33,67,50,83]),(90,[96,32,66,84]),(101,[32,16,99,67]),(105,[48,81,33,96,66,64]),(108,[32,49,81,65,100]),(114,[64,81,32,99]),(116,[32,65,83,99]),(170,[112,32,66,100]),(178,[80,65,32,115,33,99]),(209,[96,16,33,67,50,117]),(210,[96,32,115,66,84,83]),(226,[112,32,99,66]),(240,[112,65,32,83,99,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V137 low43 (by decide +kernel)
def g141Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0)]
def g141C : List ColumnInfo := [(4,0,137,0,4)]
def g141A : List (List Nat) := [[],[48]]
def g141D4 (j : Nat) := if j=0 then 0x1f else 0
def g141L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g141D4)
  | _ => emptyPacking
def g141I (_ _ : Nat) : Option (Nat × Nat) := none
def g141 : Forest := ⟨141,4,fun i => g141Y[i]?.getD (0,0),g141C,g141A,g141L,g141I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g141P4_0 : block g141 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g141B4 : block g141 4 0 1=true := g141P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g141T : checkedTables g141 4 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g141B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g141G : graphValid g141 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low141 : Lower true (varsX 141) (graphGoal 141) 5 := lower_forest (g:=g141) (i:=0) (hints:=1795) (before_sound K43 V43) g141G g141T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K141 := extendKnown K43 5 [(141,[]),(163,[33,115,67,84]),(166,[32,16,115,67,84]),(172,[32,16,49,81,65]),(197,[32,99,67,84]),(212,[32,16,65,115,83,101]),(216,[48,16,66,113,33,82,101]),(225,[98,83,66]),(232,[48,16,82,97,65])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V141 : Known true K141 := extend_ok (m:=141) V43 low141 (by decide +kernel)
def g165Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g165C : List ColumnInfo := [(1,0,164,0,4)]
def g165A : List (List Nat) := [[],[117],[32],[32,117]]
def g165D4 (j : Nat) := if j=0 then 0x1f else 0
def g165L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g165D4)
  | _ => emptyPacking
def g165I (_ _ : Nat) : Option (Nat × Nat) := none
def g165 : Forest := ⟨165,4,fun i => g165Y[i]?.getD (0,0),g165C,g165A,g165L,g165I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165P4_0 : block g165 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g165B4 : block g165 4 0 1=true := g165P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165T : checkedTables g165 4 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g165B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g165G : graphValid g165 (boundsBefore K141) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low165 : Lower true (varsX 165) (graphGoal 165) 5 := lower_forest (g:=g165) (i:=0) (hints:=1285) (before_sound K141 V141) g165G g165T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K165 := extendKnown K141 5 [(165,[]),(169,[48,82,32]),(201,[98,50,83]),(204,[32,16,49,101]),(228,[80,16,98,49,67,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V165 : Known true K165 := extend_ok (m:=165) V141 low165 (by decide +kernel)
def g47Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf8003ffe00fff803ff,0xfffffffffffb5d61e03f])),(BitVec.ofNat 152 (word80 [0x501a80941a02905828,0x540940a414940616249]))),((BitVec.ofNat 152 (word80 [0xffffc00000fffffc01,0xffe001ffe008a3d3c1c0])),(BitVec.ofNat 152 (word80 [0x61530ad8ac2b22914c,0x2986d84c8668a351c6db]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000001,0xfffffe000004e42dde00])),(BitVec.ofNat 152 (word80 [0x819c0ce13033c4e270,0x4e04e06f0b84e429c6db]))),((BitVec.ofNat 152 (word80 [1,0xfffffffffff22feda007])),(BitVec.ofNat 152 (word80 [0x5e02f01c0bc070381,0x701701700c022f8c8db6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffffffe,0xdfa9e5ff8])),(BitVec.ofNat 152 (word80 [0x600300000c0000001,0x80180180100018861924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g47C : List ColumnInfo := [(2,0,45,0,4)]
def g47A : List (List Nat) := [[],[33]]
def g47D4 (j : Nat) := if j=0 then 0x3f else 0
def g47L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g47D4)
  | _ => emptyPacking
def g47I (_ _ : Nat) : Option (Nat × Nat) := none
def g47 : Forest := ⟨47,4,fun i => g47Y[i]?.getD (0,0),g47C,g47A,g47L,g47I⟩
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
theorem g47T : checkedTables g47 4 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g47B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g47G : graphValid g47 (boundsBefore K165) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low47 : Lower true (varsX 47) (graphGoal 47) 5 := lower_forest (g:=g47) (i:=0) (hints:=1363) (before_sound K165 V165) g47G g47T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K47 := extendKnown K165 5 [(47,[]),(55,[16,67]),(93,[48,33,65,101]),(94,[64,33,49,101]),(124,[32,49,64,81,97])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V47 : Known true K47 := extend_ok (m:=47) V165 low47 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc07ffff800ff,0xfffc07fffff27a560f0f])),(BitVec.ofNat 152 (word80 [0x822810810004504a01,0x4008102201300a525555]))),((BitVec.ofNat 152 (word80 [0xc003ffff80ffffff00,0x1fffffff001dadf9f0f0])),(BitVec.ofNat 152 (word80 [0xb005000201600c05,0x8050000404102c993333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc000000ffffffff,0xe00007fffe67e88e000f])),(BitVec.ofNat 152 (word80 [0x24c2a61a34a98510a6,0x156165485047e08caaaa]))),((BitVec.ofNat 152 (word80 [0xffffffff,0xfffff800002697f400f0])),(BitVec.ofNat 152 (word80 [0x3703382c58ce0660c8,0x1982467098269364cccc]))),((BitVec.ofNat 152 (word80 [0xffffffffff00000000,0x19d530dff00])),(BitVec.ofNat 152 (word80 [0x3803c03060f00780f0,0x1e038780e08d51048888]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := []
def g59A : List (List Nat) := [[],[16,67]]
def g59D4 (j : Nat) := if j=0 then 0x1f else 0
def g59L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g59D4)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,4,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P4_0 : block g59 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B4 : block g59 4 0 1=true := g59P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 4 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g59B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K47) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 5 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K47 V47) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K47 5 [(59,[]),(91,[48,65,101]),(107,[80,49,100]),(110,[80,97,32,49,67]),(115,[80,65,48,97,49]),(121,[96,16,33,67,83]),(122,[96,32,84]),(186,[112,32,98]),(211,[112,65,48,101,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V47 low59 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(1,0,108,0,4),(4,0,105,0,4),(8,0,101,0,4),(32,0,77,0,4),(64,0,45,0,4)]
def g109A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g109D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g109D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g109H5 (j : Nat) := if j=0 then 0x0 else 0
def g109D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g109H6 := limbs80 #[#[0x2a000000000000,0x600003b5c00000000000,0x80000002,0x25f804c0000480c40]]
def g109L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g109D4)
  | 5 => (2,1,3,0,0,4,0,g109D5)
  | 6 => (1,0,3,0,0,0,0,g109D6)
  | _ => emptyPacking
def g109I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g109H5
  | 6 => lookupShort 2 53 0 6 1 3 g109H6
  | _ => fun _ => none
def g109 : Forest := ⟨109,6,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
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
theorem g109P5_0 : block g109 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B5 : block g109 5 0 2=true := g109P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P6_0 : block g109 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B6 : block g109 6 0 1=true := g109P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 6 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g109B4
  · exact g109B5
  · exact g109B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 7 := lower_forest (g:=g109) (i:=0) (hints:=33555715) (before_sound K59 V59) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K59 7 [(109,[]),(118,[16,67]),(242,[16,114,67,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V59 low109 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(0,2,137,16,5)]
def g155A : List (List Nat) := [[],[115],[65],[65,115],[48],[48,112],[48,65],[48,65,112],[112,48],[112],[112,65,48],[112,65]]
def g155D5 (j : Nat) := if j=0 then 0x3f else 0
def g155L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g155D5)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,5,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P5_0 : block g155 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B5 : block g155 5 0 1=true := g155P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 5 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g155B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 6 := lower_forest (g:=g155) (i:=0) (hints:=65603) (before_sound K109 V109) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K109 6 [(155,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V109 low155 (by decide +kernel)
def g167Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff81ffffff00,0x3ff01ff80feae3c40e07])),(BitVec.ofNat 152 (word80 [0xa0a8d4253452502a1a,0x84a342916288e2c49249]))),((BitVec.ofNat 152 (word80 [0xffffe0001ff03ffff,0xc0001ffff0054bb40038])),(BitVec.ofNat 152 (word80 [0xc930993658649a4c93,0x26c5932244c54bb6db6d]))),((BitVec.ofNat 152 (word80 [0xffffffffe0003ffff,0xffffe00000196c9871c0])),(BitVec.ofNat 152 (word80 [0x1c0e0386078e0701c,0x70603c387086c989249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffffffffe47e6381ff])),(BitVec.ofNat 152 (word80 [0x20100400080008020,0x8000400000000012492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x1b91bffe00])),(BitVec.ofNat 152 (word80 [0xc02018001000300c0,0x30081804081311224924]))),(0x0,0x0)]
def g167C : List ColumnInfo := [(1,0,166,0,5)]
def g167A : List (List Nat) := [[],[32]]
def g167D5 (j : Nat) := if j=0 then 0x3f else 0
def g167L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g167D5)
  | _ => emptyPacking
def g167I (_ _ : Nat) : Option (Nat × Nat) := none
def g167 : Forest := ⟨167,5,fun i => g167Y[i]?.getD (0,0),g167C,g167A,g167L,g167I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167P5_0 : block g167 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g167B5 : block g167 5 0 1=true := g167P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167T : checkedTables g167 5 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g167B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g167G : graphValid g167 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low167 : Lower true (varsX 167) (graphGoal 167) 6 := lower_forest (g:=g167) (i:=0) (hints:=1365) (before_sound K155 V155) g167G g167T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K167 := extendKnown K155 6 [(167,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V167 : Known true K167 := extend_ok (m:=167) V155 low167 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ff0fffffc03f,0xfff0fffff5560300f0ff])),(BitVec.ofNat 152 (word80 [0x2028280a2020028281,0x40220020900603111111]))),((BitVec.ofNat 152 (word80 [0xffffc000ff0ffffc0,0x1fff0ff014b579000f00])),(BitVec.ofNat 152 (word80 [0x48b0322c41428b2325,0x9140284214b551bbbbbb]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xe0000fff2bb5260f000f])),(BitVec.ofNat 152 (word80 [0x82c140b005842c0406,0x58442802b9120666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x30180c08608300808,0x6000304034828444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0203000800c03030,0x18088c084420c4888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(0,2,137,32,5),(2,0,169,0,5),(8,0,163,0,5),(1,0,170,0,4),(32,2,137,0,4),(128,0,43,0,4)]
def g171A : List (List Nat) := [[],[112]]
def g171D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g171D5 (j : Nat) := if j=0 then 0xc8404fd40 else 0
def g171H5 (j : Nat) := if j=0 then 0xc else 0
def g171D6 (j : Nat) := if j=0 then 0x2b2a0bf else 0
def g171H6 (j : Nat) := if j=0 then 0x0 else 0
def g171L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g171D4)
  | 5 => (1,1,3,0,0,0,0,g171D5)
  | 6 => (1,0,3,0,0,0,0,g171D6)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g171H5
  | 6 => lookupShort 1 2 0 2 0 0 g171H6
  | _ => fun _ => none
def g171 : Forest := ⟨171,6,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P4_0 : block g171 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B4 : block g171 4 0 1=true := g171P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P5_0 : block g171 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B5 : block g171 5 0 1=true := g171P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171P6_0 : block g171 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g171B6 : block g171 6 0 1=true := g171P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171T : checkedTables g171 6 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g171B4
  · exact g171B5
  · exact g171B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K167) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K167 V167) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K167 7 [(171,[]),(217,[48,65,33,101]),(230,[32,99,67]),(244,[32,65,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V167 low171 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5),(4,0,169,0,5),(8,0,165,0,5),(32,0,141,0,5)]
def g173A : List (List Nat) := [[],[80,50]]
def g173D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g173L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g173D6)
  | _ => emptyPacking
def g173I (_ _ : Nat) : Option (Nat × Nat) := none
def g173 : Forest := ⟨173,6,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P6_0 : block g173 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B6 : block g173 6 0 1=true := g173P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173T : checkedTables g173 6 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K171 V171) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K171 7 [(173,[]),(205,[96,32,50,83]),(229,[32,99,67]),(233,[48,82,96,66,64]),(236,[32,16,49,81,65,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V171 low173 (by decide +kernel)
def g174Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ff001ff80ffc07ff0,0x3ffffe03ff4b12b0007])),(BitVec.ofNat 152 (word80 [0x42a8d4251a148b42a9,0xaa4a8a458a64b1235b6d]))),((BitVec.ofNat 152 (word80 [0x7ffffe0000ffffffff,0xfc00ffffc068db9401f8])),(BitVec.ofNat 152 (word80 [0x4c098362c191204c1,0x306c0c891340d3841249]))),((BitVec.ofNat 152 (word80 [0x7fffffffff00007fff,0xffff0000000ff00e8e00])),(BitVec.ofNat 152 (word80 [0x1702e0b8305e1c1701,0xc0702f0e1c0df00cb6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x800000000000007fff,0xffffffffff99af6d703f])),(BitVec.ofNat 152 (word80 [0x180300c04060201802,0x80300000190c082492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6754f2ffc0])),(BitVec.ofNat 152 (word80 [0x600c0100008000600c,0x300c010202200724924]))),(0x0,0x0)]
def g174C : List ColumnInfo := [(2,0,172,0,5)]
def g174A : List (List Nat) := [[],[49,117]]
def g174D5 (j : Nat) := if j=0 then 0x3f else 0
def g174L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g174D5)
  | _ => emptyPacking
def g174I (_ _ : Nat) : Option (Nat × Nat) := none
def g174 : Forest := ⟨174,5,fun i => g174Y[i]?.getD (0,0),g174C,g174A,g174L,g174I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g174P5_0 : block g174 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g174B5 : block g174 5 0 1=true := g174P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g174T : checkedTables g174 5 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g174B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g174G : graphValid g174 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low174 : Lower true (varsX 174) (graphGoal 174) 6 := lower_forest (g:=g174) (i:=0) (hints:=537949520) (before_sound K173 V173) g174G g174T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K174 := extendKnown K173 6 [(174,[]),(227,[32,99,67]),(248,[65,50,82,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V174 : Known true K174 := extend_ok (m:=174) V173 low174 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ffffffff003ff,0xff87ffc374d9420f83e0])),(BitVec.ofNat 152 (word80 [0xa8540a09002a0a814,0x910008a645802318c63]))),((BitVec.ofNat 152 (word80 [0xffffe00ff87ffffc01,0xfff87ffcd352b6007c1f])),(BitVec.ofNat 152 (word80 [0x830190c02120c43118,0x8201210050123694a529]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11c00001f])),(BitVec.ofNat 152 (word80 [0x2c16050ac24b08c221,0x2c224a00afc1096b5ad6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe9f07fe0])),(BitVec.ofNat 152 (word80 [0x30180603040c010040,0x30000c100105c8421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc020180c00700e0381,0xc04470211aa2118c6318]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(0,16,161,2,5),(16,0,163,0,5),(1,0,178,0,4),(2,16,161,0,4),(128,0,51,0,4)]
def g179A : List (List Nat) := [[],[112]]
def g179D4 (j : Nat) := if j=0 then 0x4fd5130 else 0
def g179D5 := limbs80 #[#[0x480e140fd40ff30fd30,0x4088]]
def g179H5 (j : Nat) := if j=0 then 0xc else 0
def g179D6 (j : Nat) := if j=0 then 0x18989f else 0
def g179H6 (j : Nat) := if j=0 then 0x17000001110080 else 0
def g179L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g179D4)
  | 5 => (3,1,3,0,0,5,0,g179D5)
  | 6 => (1,0,3,0,0,0,0,g179D6)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 2 0 0 g179H5
  | 6 => lookupShort 1 11 0 5 2 1 g179H6
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
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g179B4
  · exact g179B5
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K174) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=65605) (before_sound K174 V174) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K174 7 [(179,[]),(182,[32]),(214,[32,65,101]),(218,[48,65,32,101]),(234,[48,81,32,65,116,100]),(241,[97,33,50,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V174 low179 (by decide +kernel)
def g63Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffffffffff,0xfcd8034dfabc9c007c1f])),(BitVec.ofNat 152 (word80 [0x80a0a80a1280a14810,0xa4d003043a28985294a5]))),((BitVec.ofNat 152 (word80 [0xfffffc00003ffffc00,0x1a55e33360f780f83e0])),(BitVec.ofNat 152 (word80 [0x53000db00099003,0x31a11e21200c58318c63]))),((BitVec.ofNat 152 (word80 [0x3fffffffffc0000000,0x233e3a455ec53f00000])),(BitVec.ofNat 152 (word80 [0x2c9c02c9c02cde025,0xc231c3a454ac52f7bdef]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffff,0xfac58e65c5f6a400001f])),(BitVec.ofNat 152 (word80 [0x2b0e02b0e02b0e0146,0x2058c61c5d625ad6b5a]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x245795afe62520003e0])),(BitVec.ofNat 152 (word80 [0x33f0033f0033f00278,0x244615ade6203ce739c]))),(0x73aa5b8895b2bfffc00,(BitVec.ofNat 152 (word80 [0x3c0003c0003c000380,0xa2018815321084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g63C : List ColumnInfo := [(4,0,59,0,5),(8,0,55,0,5),(16,0,47,0,5),(1,8,54,0,4),(2,16,45,0,4)]
def g63A : List (List Nat) := [[],[16,67]]
def g63D5 (j : Nat) := if j=0 then 0x1ef52 else 0
def g63D6 (j : Nat) := if j=0 then 0x222317f else 0
def g63H6 (j : Nat) := if j=0 then 0x0 else 0
def g63L : Nat → Packing
  | 5 => (1,1,3,0,0,0,0,g63D5)
  | 6 => (1,0,3,0,0,0,0,g63D6)
  | _ => emptyPacking
def g63I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g63H6
  | _ => fun _ => none
def g63 : Forest := ⟨63,6,fun i => g63Y[i]?.getD (0,0),g63C,g63A,g63L,g63I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P5_0 : block g63 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B5 : block g63 5 0 1=true := g63P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63P6_0 : block g63 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g63B6 : block g63 6 0 1=true := g63P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63T : checkedTables g63 6 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g63B5
  · exact g63B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g63G : graphValid g63 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low63 : Lower true (varsX 63) (graphGoal 63) 7 := lower_forest (g:=g63) (i:=0) (hints:=66883) (before_sound K179 V179) g63G g63T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K63 := extendKnown K179 7 [(63,[]),(95,[48,65,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V63 : Known true K63 := extend_ok (m:=63) V179 low63 (by decide +kernel)
def g111Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xd929fa398962400003ff])),(BitVec.ofNat 152 (word80 [0x828a02a50252814905,0x1929722181221294a529]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0xd6a26ca31ed00007c00])),(BitVec.ofNat 152 (word80 [0x14cc14c61b63099219,0x8d6826ca11e916b5ad6b]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x35b423e5c8d801ff8000])),(BitVec.ofNat 152 (word80 [0x2700270013800de02e,0x3424236148c806318c63]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xca58e5684e4ffe00001f])),(BitVec.ofNat 152 (word80 [0x3800b8005c002e0030,0x25085484c4c4c6318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4579a17773c000fffe0])),(BitVec.ofNat 152 (word80 [0x10c0086004300040,0x1288142614294a5294]))),(0x33aa5dc49781bff00000,(BitVec.ofNat 152 (word80 [0xc01f000f8007c00380,0x18a58849301b18c6318]))),(0x0,0x0),(0x0,0x0)]
def g111C : List ColumnInfo := [(2,0,109,0,7)]
def g111A : List (List Nat) := [[],[32,99]]
def g111D7 (j : Nat) := if j=0 then 0x7f else 0
def g111L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g111D7)
  | _ => emptyPacking
def g111I (_ _ : Nat) : Option (Nat × Nat) := none
def g111 : Forest := ⟨111,7,fun i => g111Y[i]?.getD (0,0),g111C,g111A,g111L,g111I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111P7_0 : block g111 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g111B7 : block g111 7 0 1=true := g111P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111T : checkedTables g111 7 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g111B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g111G : graphValid g111 (boundsBefore K63) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low111 : Lower true (varsX 111) (graphGoal 111) 8 := lower_forest (g:=g111) (i:=0) (hints:=33555795) (before_sound K63 V63) g111G g111T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K111 := extendKnown K63 8 [(111,[]),(119,[16,67]),(125,[48,65,101]),(126,[64,49,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V111 : Known true K111 := extend_ok (m:=111) V63 low111 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffff001ffffff,0xcc256358d06fc0007c1f])),(BitVec.ofNat 152 (word80 [0xa500a500240ca04481,0xc216100906794a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000ffffffffffe00,0x2c70bcab38d1000f83e0])),(BitVec.ofNat 152 (word80 [0xc602c6014808c00901,0x8c20b4aa10911294a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000001ffffff,0xf8eb829aa38a41f0001f])),(BitVec.ofNat 152 (word80 [0x53005580b00a9014,0x20ca821a22884a5294a5]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x231964366e4dbe0003e0])),(BitVec.ofNat 152 (word80 [0x64006601200ce026,0x211900146a4c8c6318c6]))),(0x24569b45573c000ffc00,(BitVec.ofNat 152 (word80 [0x878087801c10f0038,0x20560a454708294a5294]))),(0x13aa5dc49781bff00000,(BitVec.ofNat 152 (word80 [0xf800f800e01f001c0,0x12205dc09501318c6318]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(32,0,91,0,5),(9,0,114,0,4),(18,0,105,0,4),(33,0,90,0,4),(34,0,89,0,4),(72,0,51,0,4),(80,0,43,0,4)]
def g123A : List (List Nat) := [[],[97,83],[16,67],[16,96,83,67],[48,65,101],[48,81,96,65,64],[64,49,101],[64,81,99],[80,49,100],[80,65,48,97,49],[96,16,67,83],[96,84]]
def g123D5 (j : Nat) := if j=0 then 0xafd9110 else 0
def g123D6 (j : Nat) := if j=0 then 0x683fa61fd10 else 0
def g123H6 (j : Nat) := if j=0 then 0x4 else 0
def g123D7 (j : Nat) := if j=0 then 0x34ad11bf else 0
def g123H7 := limbs80 #[#[0x2,0x9c00000000140000000,0x14030e500c4000000000,0x84000000003300]]
def g123L : Nat → Packing
  | 5 => (1,2,3,0,0,0,0,g123D5)
  | 6 => (2,1,3,0,0,4,0,g123D6)
  | 7 => (1,0,3,0,0,0,0,g123D7)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g123H6
  | 7 => lookupShort 2 47 1 7 1 4 g123H7
  | _ => fun _ => none
def g123 : Forest := ⟨123,7,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 1=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 2=true := g123P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 1=true := g123P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 7 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g123B5
  · exact g123B6
  · exact g123B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K111) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 8 := lower_forest (g:=g123) (i:=0) (hints:=50397251) (before_sound K111 V111) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K111 8 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V111 low123 (by decide +kernel)
def g159Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffffffffffffff,0xb94049bf55b28003f03f])),(BitVec.ofNat 152 (word80 [0x814150284a050a4214,0xb8404097451205145145]))),((BitVec.ofNat 152 (word80 [0xfffff80000ffffe000,0x36bb4666c1ae40000fc0])),(BitVec.ofNat 152 (word80 [0x100a62036c404c8066,0x3633462401ae134d34d3]))),((BitVec.ofNat 152 (word80 [0x3fffffffff00000000,0x66c749abd8b00fc0000])),(BitVec.ofNat 152 (word80 [0x59380b270166f04b8,0x26c449abd8b0f3cf3cf]))),((BitVec.ofNat 152 (word80 [0x3fffffffffffffffff,0x58b1cca8bed4bf00003f])),(BitVec.ofNat 152 (word80 [0x61c00c380187008c0,0xa10c28bac48a28a28a]))),((BitVec.ofNat 152 (word80 [0xc00000000000000000,0x48af2b5fcc4a40000fc0])),(BitVec.ofNat 152 (word80 [0x27e004fc009f800f00,0x488c295bcc406cb2cb2c]))),(0x0,0x0),(0x0,0x0),(0xe754b7112b657ffff000,(BitVec.ofNat 152 (word80 [0x3800070000e0001000,0x4510b300002070c30c30]))),(0x0,0x0)]
def g159C : List ColumnInfo := [(0,2,141,16,6)]
def g159A : List (List Nat) := [[],[65],[48],[48,65]]
def g159D6 (j : Nat) := if j=0 then 0x7f else 0
def g159L : Nat → Packing
  | 6 => (1,0,1,0,0,0,0,g159D6)
  | _ => emptyPacking
def g159I (_ _ : Nat) : Option (Nat × Nat) := none
def g159 : Forest := ⟨159,6,fun i => g159Y[i]?.getD (0,0),g159C,g159A,g159L,g159I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159P6_0 : block g159 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g159B6 : block g159 6 0 1=true := g159P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159T : checkedTables g159 6 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g159B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g159G : graphValid g159 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low159 : Lower true (varsX 159) (graphGoal 159) 7 := lower_forest (g:=g159) (i:=0) (hints:=67395) (before_sound K123 V123) g159G g159T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K159 := extendKnown K123 7 [(159,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V159 : Known true K159 := extend_ok (m:=159) V123 low159 (by decide +kernel)
def g175Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ffffffffffffff,0xfe28e884bd89000f00ff])),(BitVec.ofNat 152 (word80 [0x20581400a804a01481,0x4e08a0808c0911111111]))),((BitVec.ofNat 152 (word80 [0xfffc00fffc000fffc0,0x7d10ea50cb300000f00])),(BitVec.ofNat 152 (word80 [0x4290a6853236c89906,0x67d10ea50c91bbbbbbbb]))),((BitVec.ofNat 152 (word80 [0xfffffff00000,0x1cf2190dad100f0f000])),(BitVec.ofNat 152 (word80 [0x84e13809c02700de0b,0x814b2180da9133333333]))),((BitVec.ofNat 152 (word80 [0xffffffffffff,0xf2153f483bb80f00000f])),(BitVec.ofNat 152 (word80 [0x701c02e00b802e00c,0x151d4033b066666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x116d0a38776f000fff0])),(BitVec.ofNat 152 (word80 [0x3000c0030010,0x45000016644444444]))),(0x0,0x0),(0xce9177e4005ffff0000,(BitVec.ofNat 152 (word80 [0x80200c003000c0020,0xa0023e000088888888]))),(0x0,0x0)]
def g175C : List ColumnInfo := [(2,0,173,0,7),(4,0,171,0,7),(0,2,141,32,6),(1,0,174,0,6),(8,0,167,0,6),(3,0,172,0,5),(4,2,137,32,5),(6,0,169,0,5),(9,0,166,0,5),(10,0,165,0,5),(32,0,141,0,5),(32,2,141,0,5),(128,0,47,0,5),(5,0,170,0,4),(36,0,137,0,4),(130,0,45,0,4),(132,0,43,0,4)]
def g175A : List (List Nat) := [[]]
def g175D4 := limbs80 #[#[0x5412050d504814350120,0x4826558520d055048161,0x5946550d75d05205c341,0xd05501955450d7019543,0xd077259741d8f4154176,0x8e63585d76d07505db53,0xd8b19c5ad8b1ac39e272,0x18737614eb750a5d43c2,0x993855321c6d5417e149,0xe0b8b82a161ee77542e1,0x8560a5980926030b82d2,0x2921191109000e1de165,0x7a726a625a524a423a31,0x224928a82,0x4]]
def g175D5 := limbs80 #[#[0x545205412050d2050120,0x99520595205852055120,0x5414050d40d5120d0520,0x5514354d431954359540,0x50d50d4d439954359543,0xd8d50d05505855054550,0xd4f415974158341d8954,0x59353d07505935050f50,0x9ebb3e9ecee733758354,0xae9f2f7cbd5e6f176b9d,0x2f579bc7e2ed73b8fb9d,0x1dc9a4ae04514303f1f,0x9d0425eea02d7502eaa0,0x50c2cae2165610b2a885,0xd029ea814d540b1b9858,0x4556ec1a976214ba90bd,0x4aaa80e370055ba8b099,0x5ae039f73196b8122dd8,0x2ca55b702a4aa17650cb,0xe0b0373305b918ed94a7,0x6a0d7658abaacfd8d662,0x980764e2aa26fd8d57ec,0x1575780ba2ef5c5704ec,0xb7275cb2391551c1aecf,0x72687b83435d9b1eeac8,0x41bb2a465d1236e8743,0x3ebb91e6dc0f16e48137,0x4eb91a85c0d8eca7c465,0xbb2a27dc9046e0835653,0x90000dce012e0c0b727d,0x98ca2d09e2386c1603e0,0x3174591525092a461083],#[0xc220839fe7a9d8701a46,0x72ccaf2aca4a7c96a428,0xf362d232cc730cbf2ecb,0x1bf6f9bccef3ace738cd,0x1c7719c5711c3709c170,0x7d0f3fcef364c329c972,0x52159256f57d4f4fd2f4,0xc51570610251030683b1,0x827811c5848190440280,0x3602c0400708480c5876,0x100b21008009d08b0,0x401010099086c3283282,0x341a42bd42d41008000,0xa6c2000000000000000,0x168200000000003415a,0x0,0x290d216d8400]]
def g175H5 := limbs80 #[#[0x3e300000009402680033,0x688388280233e9269601,0x24133372000400]]
def g175D6 := limbs80 #[#[0xd055454d515414350120,0xf9f7efef6eedf54d4f50,0xa5003fbf7efebe7dfcfb,0x309584255109d0429500,0x96572581c3633550c5d4,0x2d5401d89955422d810,0x5406e650b5942d640bd5,0x3cd04cf651359459541d,0x5438d8ce1433c584f151,0x21438cd060f6434d50d1,0x4d33537c54dcd6484552,0x3594995428d4ca1532c5,0x528194a360285808f652,0xd6493d91636528994a16,0xe8d60a3d8daf6263d818,0x831ac530f42805400358,0x1a424f8390ce2fca9260,0xb3699936097057d434b5,0x488ee2a866087c1da715,0xbeac2a8a5a8e9f26f95e,0x60d1f2ac5300bc6ddb36,0xd7f2bc2eb79be237bdb3,0xe11b0d58ac0011040483,0xc963d241108e442062c0,0xac902901ca03aa430220,0xa89364226cdd0f72a1de,0x1c6c8d5b60a5e564bb55,0x8a3249365344d284bf4a,0x8b5e031d9c238e11f69,0x44807429f90ac84735ac,0x31d639bc21d64c4d023c,0x617420ba136c0d6aa511],#[0x3988f2c2b55288788920,0x2e213603cd84017a4200,0x63f20917810d681c7312,0x6c81180863c0887de482,0x3005aaa19cc467889120,0x90]]
def g175H6 := limbs80 #[#[0x9f2d50401c00441c0018,0x31380335ac8387831ca9,0xd78035d03606167e2,0x3651c8c4ac010b626300,0x1255b44,0x108018400a1803520000,0x1b09c240186d50d0733d,0x5a029e4936a000003f61,0x44638a006816e460a877,0xd4881d045f27c00a6844,0x28a6e00033408017699d,0xe96540011a4100000011,0x1152]]
def g175D7 := limbs80 #[#[0x3951b41520910fff7df7,0xd53d43f50d50d4024314,0x64f39281200f54d54f53,0x821ddcbbbada09080736,0xc004dac50e808428b308,0xd084ade031fe416e8248,0x65006002a010f8812d,0x480cd2032803200a0055,0x3]]
def g175H7 := limbs80 #[#[0x800401000,0x348029b56c0005804880,0x0,0x36d18033e30020807080,0x6a0006000000000061,0x50000000000000055ef,0x200000,0x0,0x64806ada004b00,0x57000000110000000000,0x2e8900000000006d00,0x18000000,0x7444002680670000,0x48418000000047800000,0x8000003b000050536280,0x798000006f8057,0x0,0x2d806e000000,0x16004cd880002b8000,0x12f200000000000000,0x3900000200,0x3807a80]]
def g175D8 (j : Nat) := if j=0 then 0x5a02013f else 0
def g175H8 := limbs80 #[#[0xc0000000034000000143,0x12c0c2603a3799c00004,0x201c000a0001]]
def g175L : Nat → Packing
  | 4 => (19,4,5,786447,68,8,1025,g175D4)
  | 5 => (71,3,5,1703969,86,10,1044,g175D5)
  | 6 => (55,2,5,917515,68,10,1056,g175D6)
  | 7 => (14,1,5,262145,32,8,1040,g175D7)
  | 8 => (1,0,5,0,0,0,0,g175D8)
  | _ => emptyPacking
def g175I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 4 29 3 7 5 0 g175H5
  | 6 => lookupShort 17 97 6 9 7 0 g175H6
  | 7 => lookupShort 13 211 3 8 6 0 g175H7
  | 8 => lookupShort 3 37 2 6 4 0 g175H8
  | _ => fun _ => none
def g175 : Forest := ⟨175,8,fun i => g175Y[i]?.getD (0,0),g175C,g175A,g175L,g175I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P4_0 : block g175 4 0 19=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B4 : block g175 4 0 19=true := g175P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_0 : block g175 5 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P5_3 : block g175 5 3 68=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B5 : block g175 5 0 71=true := (@block_merge g175 5 0 3 68 g175P5_0 g175P5_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_0 : block g175 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P6_13 : block g175 6 13 42=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B6 : block g175 6 0 55=true := (@block_merge g175 6 0 13 42 g175P6_0 g175P6_13)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_0 : block g175 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P7_6 : block g175 7 6 8=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B7 : block g175 7 0 14=true := (@block_merge g175 7 0 6 8 g175P7_0 g175P7_6)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175P8_0 : block g175 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g175B8 : block g175 8 0 1=true := g175P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175T : checkedTables g175 8 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g175B4
  · exact g175B5
  · exact g175B6
  · exact g175B7
  · exact g175B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g175G : graphValid g175 (boundsBefore K159) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low175 : Lower true (varsX 175) (graphGoal 175) 9 := lower_forest (g:=g175) (i:=0) (hints:=1363) (before_sound K159 V159) g175G g175T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K175 := extendKnown K159 9 [(175,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V175 : Known true K175 := extend_ok (m:=175) V159 low175 (by decide +kernel)
def g183Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffe0003fff801,0xc71d31124cb001f003e0])),(BitVec.ofNat 152 (word80 [0x589402540da81290ad,0xc11d30124c80c6318c63]))),((BitVec.ofNat 152 (word80 [0xfc00fffffffffffffe,0xf8051a6f0d5800007c1f])),(BitVec.ofNat 152 (word80 [0x902640988131032048,0xf8041a6204525294a529]))),((BitVec.ofNat 152 (word80 [0xfffffffc000000,0x39c4f6938a803e0f8000])),(BitVec.ofNat 152 (word80 [0xe13804e009c01bc170,0x2944b6138880c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffe,0x428bea0bd9e80000001f])),(BitVec.ofNat 152 (word80 [0x1c097012e025c0180,0x28be009d9adad6b5ad6]))),((BitVec.ofNat 152 (word80 [0xffff00000000000000,0x22fa117cb687c00fffe0])),(BitVec.ofNat 152 (word80 [0x18003000600200,0x2a0010c120108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [1,0x9d26ecc07137fff00000])),(BitVec.ofNat 152 (word80 [0x200e001c003800400,0x140248c02136318c6318]))),(0x0,0x0)]
def g183C : List ColumnInfo := [(1,0,182,0,7)]
def g183A : List (List Nat) := [[],[32]]
def g183D7 (j : Nat) := if j=0 then 0x7f else 0
def g183L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g183D7)
  | _ => emptyPacking
def g183I (_ _ : Nat) : Option (Nat × Nat) := none
def g183 : Forest := ⟨183,7,fun i => g183Y[i]?.getD (0,0),g183C,g183A,g183L,g183I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183P7_0 : block g183 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g183B7 : block g183 7 0 1=true := g183P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183T : checkedTables g183 7 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g183B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g183G : graphValid g183 (boundsBefore K175) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low183 : Lower true (varsX 183) (graphGoal 183) 8 := lower_forest (g:=g183) (i:=0) (hints:=66885) (before_sound K175 V175) g183G g183T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K183 := extendKnown K175 8 [(183,[]),(222,[32,65,48,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V183 : Known true K183 := extend_ok (m:=183) V175 low183 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ffffffc03fffff72,0x2a8a85666c003f03f03f])),(BitVec.ofNat 152 (word80 [0x2800a0008080220032,0xa000506285145145145]))),((BitVec.ofNat 152 (word80 [0xfc000fffffffff00bd,0x54871b85180000fc0fc0])),(BitVec.ofNat 152 (word80 [0x3102c405001004023c,0x148311011934d34d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff000003fffffad,0x8dc8d210e40fc000003f])),(BitVec.ofNat 152 (word80 [0x405301560b05482885,0x588d210c4a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000080,0x4b45b7ecd00000000fc0])),(BitVec.ofNat 152 (word80 [0x826409981226704c80,0x4b44a6ecc2cb2cb2cb2c]))),((BitVec.ofNat 152 (word80 [0x91,0x75382c5b43f000fff000])),(BitVec.ofNat 152 (word80 [0x7801e01c07807081,0x61282850408208208208]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x3800e002038008048,0x90560028130c30c30c30]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(8,0,179,0,7)]
def g187A : List (List Nat) := [[],[112]]
def g187D7 (j : Nat) := if j=0 then 0x7f else 0
def g187L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g187D7)
  | _ => emptyPacking
def g187I (_ _ : Nat) : Option (Nat × Nat) := none
def g187 : Forest := ⟨187,7,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 1=true := g187P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 7 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g187B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K183) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 8 := lower_forest (g:=g187) (i:=0) (hints:=65603) (before_sound K183 V183) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K183 8 [(187,[]),(219,[48,65,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V183 low187 (by decide +kernel)
def g190Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffffff,0xd927e638c872c00003ff])),(BitVec.ofNat 152 (word80 [0x28802a40252014805,0x1927622080229294a529]))),((BitVec.ofNat 152 (word80 [0x1ffff00007fffc00,0x3ed8320ba06d800ffc00])),(BitVec.ofNat 152 (word80 [0x14c014c01b60099019,0xba50320b006186318c63]))),((BitVec.ofNat 152 (word80 [0x1ffffffff8000000,0x73433e14bd881f00000])),(BitVec.ofNat 152 (word80 [0x6702a7015380ade0ae,0x63433214bd88e739ce7]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffffff,0xc858f56c4e4f4000001f])),(BitVec.ofNat 152 (word80 [0xb81338099c04ce0130,0x58954c4e4d6d6b5ad6]))),((BitVec.ofNat 152 (word80 [0xffe000000000000000,0x4578a17773c3e007fe0])),(BitVec.ofNat 152 (word80 [0xc003c001e000f001c0,0x4008814631c08421084]))),(0x0,0x0),(0x33aa5dc49781bfff8000,(BitVec.ofNat 152 (word80 [0x1c000e0007000200,0x18a44c09400318c6318]))),(0x0,0x0)]
def g190C : List ColumnInfo := [(8,0,182,0,7)]
def g190A : List (List Nat) := [[]]
def g190D7 (j : Nat) := if j=0 then 0x7f else 0
def g190L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g190D7)
  | _ => emptyPacking
def g190I (_ _ : Nat) : Option (Nat × Nat) := none
def g190 : Forest := ⟨190,7,fun i => g190Y[i]?.getD (0,0),g190C,g190A,g190L,g190I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190P7_0 : block g190 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g190B7 : block g190 7 0 1=true := g190P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190T : checkedTables g190 7 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g190B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g190G : graphValid g190 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low190 : Lower true (varsX 190) (graphGoal 190) 8 := lower_forest (g:=g190) (i:=0) (hints:=538015040) (before_sound K187 V187) g190G g190T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K190 := extendKnown K187 8 [(190,[]),(215,[48,65,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V190 : Known true K190 := extend_ok (m:=190) V187 low190 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffffffe01fffffff6,0x35e8a471480001f003ff])),(BitVec.ofNat 152 (word80 [0x42850a044c48282242,0x25a0a401482108421084]))),((BitVec.ofNat 152 (word80 [0xe0007ffffe01fff003,0xc488afcaa60000007c00])),(BitVec.ofNat 152 (word80 [0x93164c28888d304463,0xc488afc824ad6b5ad6b5]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff80000001fffffb,0xca4c91a45a003e0f801f])),(BitVec.ofNat 152 (word80 [0x1800b01010028000,0x404c11a41218c6318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000008,0x14f4491bb307c0007fe0])),(BitVec.ofNat 152 (word80 [0x42010c00000430088,0x10540012935294a5294a]))),((BitVec.ofNat 152 (word80 [9,0x1713a28774f8000f8000])),(BitVec.ofNat 152 (word80 [0x7c01f00e0e07c0709,0x1712a003646318c6318c]))),((BitVec.ofNat 152 (word80 [4,0xe9177e4005fffff00000])),(BitVec.ofNat 152 (word80 [0x180060010101800804,0x88014a40008421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(2,0,233,0,7),(64,0,171,0,7),(0,2,201,32,6),(8,0,227,0,6),(32,0,201,0,5),(32,2,201,0,5),(128,0,107,0,5)]
def g235A : List (List Nat) := [[]]
def g235D5 := limbs80 #[#[0x67abb6a598db77454b31,0x29f6e0b2a656ddd15254,0x25fba2c5a9cbf745953,0xf624c3]]
def g235D6 := limbs80 #[#[0x6bf53d4b3154d5254532,0x6c88acb3f7efdfbefef,0x22a62aa432a476a532a5,0xd2c75ec896c696ca12ca,0x510d8a0743c012c596c4,0x4a08eb2926a3e15ed9d5,0x13c0899100c449cacce0,0x902f236d81d24561130,0x2908000548402008f8]]
def g235H6 := limbs80 #[#[0xc000540000089,0x0,0x100000000000000,0x8]]
def g235D7 := limbs80 #[#[0xf52fea97f4cbeaa3f731,0x38291a0b007fd4ffaa7f,0xc338e5430d950a25849,0xa69530e3baca540ce935,0x8350ec33a4d430c]]
def g235H7 := limbs80 #[#[0x3202586303aaed580c50,0x7009c80395]]
def g235D8 (j : Nat) := if j=0 then 0x688817f else 0
def g235H8 := limbs80 #[#[0x181da00000e000000000,0x8000000000000000000,0x0,0x5]]
def g235L : Nat → Packing
  | 5 => (6,3,3,0,0,5,0,g235D5)
  | 6 => (14,2,3,458759,51,8,1037,g235D6)
  | 7 => (7,1,3,0,0,8,0,g235D7)
  | 8 => (1,0,3,0,0,0,0,g235D8)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 53 0 5 3 0 g235H6
  | 7 => lookupShort 3 23 4 6 4 0 g235H7
  | 8 => lookupShort 1 59 0 5 3 0 g235H8
  | _ => fun _ => none
def g235 : Forest := ⟨235,8,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P5_0 : block g235 5 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B5 : block g235 5 0 6=true := g235P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_0 : block g235 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_2 : block g235 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 14=true := (@block_merge g235 6 0 2 12 g235P6_0 g235P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_2 : block g235 7 2 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 7=true := (@block_merge g235 7 0 2 5 g235P7_0 g235P7_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 1=true := g235P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 8 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K190) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 9 := lower_forest (g:=g235) (i:=0) (hints:=50331731) (before_sound K190 V190) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K190 9 [(235,[]),(249,[48,65,33,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V190 low235 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x44510a204404101144,0xcc00e249249249249249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(BitVec.ofNat 152 (word80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a39,0x31110186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3861514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044104,0x42ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,7),(4,0,233,0,7),(8,0,229,0,7),(32,0,205,0,7),(64,0,173,0,7),(128,0,109,0,7),(5,0,232,0,5),(9,0,228,0,5),(12,0,225,0,5),(33,0,204,0,5),(36,0,201,0,5),(40,0,197,0,5),(65,0,172,0,5),(68,0,169,0,5),(72,0,165,0,5),(96,0,141,0,5),(37,0,200,0,4),(41,0,196,0,4),(73,0,164,0,4),(76,0,161,0,4),(100,0,137,0,4),(129,0,108,0,4),(132,0,105,0,4),(136,0,101,0,4),(160,0,77,0,4),(192,0,45,0,4)]
def g237A : List (List Nat) := [[],[98,83],[32,99],[32,48,80,96],[48,101],[48,82,96,32],[80,50],[80,98,48,50],[96,32,50,83],[96,82]]
def g237D4 := limbs80 #[#[0x10c7060f915c87254110,0x30d095539259171d49]]
def g237D5 := limbs80 #[#[0x6137654c2061d6454c20,0x5d164d4c205d163d4c20,0x61d6510910e0974d4c20,0xe0d6510910e096510910,0x59573109105957010910,0x54950481106197510910,0x4c9214c11061d6548110,0x54d514c11054d214c110,0xd51514c110551514c110,0x5d1534c110595534c110,0x61d654c91061d644c910,0x54921501104c92150110,0x95151501102115150110,0xd895150110d4d5150110,0xe095150110dcd5150110,0xe0d655011020d6550110,0x5d621501105522150110,0x5c872541105487154110,0x54d32541105493254110,0x54d51541105495154110,0x1c95254110dcd5154110,0x98952541105895254110,0xd915254110d8d5254110,0x21562541101c96254110,0xdc96254110d4d6254110,0x54a32541102156454110,0x54a42541106063254110,0x54a51541106064254110,0x593525411058f5254110,0x5d3715411060b5354110,0x5c47054910a077454110,0x61070549105d87054910],#[0xe01765491020d7654910,0xe0d7654910e057654910,0x60b645491061f6354910,0x61b7454910dd36454910,0xe0964589105d47558910,0x1cd72595105c87259510,0xe017259510dcd7259510,0x60b735951020b7359510,0x615218c110549218c110,0xe0d518c110551518c110,0x607528c110e0d658c110,0x5515190110607548c110,0x5895290110e095190110,0x61d6590910e055490110,0x5957190910e116590910,0xe0d65989105974290910,0x4c951c81105c550c8110,0x5cd51c811054d51c8110,0xe1953c811060552c8110,0xe0d65d01105cd51d0110,0x61d64d491061d63d4910,0x59170d4910e0964d4910,0x54d525412059171d4910,0x1c97154120d8d5254120,0x54a31541205497154120,0x61b735452054a5154120,0x60271595205c47159520,0x5c9521855061d658c520,0xe056218950e0d6118550,0x60770549506047054950,0x5907358550dcc6258550,0x99373585505937358550],#[0x607629495061f6294550,0x61972985506017298550,0x551515061020172d8550,0x59153542105d56450610,0x60564542105d16454210,0x6056454610e0d7154210,0x603725461061d6454610,0x6037154a1061b7454610,0xdd16454e1061d6454e10,0xe0954542206037355210,0x6137654e2061b7454620,0x61f54586206037255220,0xe0974d46205d164d4620,0xe0974d4e205d164d4e20,0x770de17c1f60b7358750,0x2ae4dc7c8f51ba1f43d8,0x695d27a2f3d26d4ce967,0xd53aa734da9ad33a5d4b,0x9ab2d63ac6d78ae5572a,0xba974ae65cab656aad1d,0xf87b0ee1bc2f7a2f25d8,0xf31d636c6b8cf1762bc4,0x46e78ce99cb3665ccb58,0x6d8da5b33556a6d35a5b,0xeb1d53a6745e35c5b78,0x91ec3cc794f25e33c377,0x5c986475d82ff07d0f,0xb145e0d86a2a6c32d526,0x5d91e70ec8ef836394b9,0x2ca1b31740d0acbb29ce,0x17850d8ac286cc5d4369,0x192ba084a5d03e82ca1d],#[0xa850e444a32ca269d931,0xd149daeaa63b935196ba,0x70ea83b93561dc9aac95,0x2d7517a6aa0bd550c59a,0xd9caa0d88e6086130a41,0x8cbbe0c712b283509541,0x10794b2630a992184aca,0x70eae21975868438fc0e,0x21546610cbad475d565c,0x6a2b1132ce14c4132ecf,0x944adcc9e82c64f13822,0x88a23046f45623777c1,0xb0c493f632438491dc46,0xfd863388a91a3e61895f,0xa7fc1953f618d622a46c,0x94a8644a533265683932,0xcb10324589194294cc9,0x72472f9833840c916bee,0xfb833040c9182364cb90,0xa74c1919ce448cfb265e,0x9e1c648f1032464fb633,0x48200f282a03951434ca,0x730124f94082dc98418e,0x9970756ba83ac5d4181,0xe25ca2e8fe4c2817260a,0x9e82e4d6c5324b887935,0xd8fc47307ae5843d76c1,0x6e88a0794440bcc1f315,0xd0834105c9a392645198,0x35fc2202de1509770a82,0xb417e49b0c724d6bf844,0x4da44b2ad4c1746a05c9],#[0x32ebe03984861ba2482e,0xbf844b6839a683e61281,0xf5fc2262f21130153096,0x27902513cab229c07944,0x4a226b270f01648a21ca,0xf2d0a7596853dcac4a2e,0xf5858b62b24693e4218e,0xf05c9c710e4e308f2518,0x4912e46409b2122c5648,0x48082722024b910062b2,0xb0ce2b1650423c90194e,0x6d936f87c1b83f619c9f,0x303ca3b20645ba1f06da,0x49b6dc5d42730e807947,0x42648f25300b939482b2,0xf253413919505c9cb876,0xb93806bcb4b076426c8,0xc5ec23e19641dd9f0ef0,0x3f14e49f41730f8be847,0x4e0dbb0b0409987f29c9,0x728f64d948423ca4194e,0x33947b88c93d0d649e83,0x3ca4e325cde45f2702,0x780d0160240380400400,0x238410760d21702a04c0,0xc630be16c2b85309e12c,0xf9082003e0780e31b634,0x5c2a8530a213c26049c8,0x330640c41802f05c0b21,0x674ce41c03706c0d41a0,0x790b20e4007e0f81e63b,0x2ca514929051ca3144c8],#[0xa91512a053ca714d2985,0x1592b055cab1552a854c,0x12c057caf15d2b856cad,0xd059cb31652c858cb116,0x5bcb716d2d85acb51692,0x3bbf76eebdd3b99722e1,0xff7eefbdf3bdf7aef3de,0x86f0be13c1f82f03e03b,0xf1be33c5f8af13e23c3f,0xbe53c9f92f23e43c7f8e,0x73cdf9af33e63cbf96f2,0xd1fa2f43e83cff9ef3be,0xfaaf53ea3d3fa6f4be93,0x2f63ec3d7faef5beb3d5,0x73ee3dbfb6f6bed3d9fb,0xf03dffbef7bef3ddfbaf,0x3e3fc6f8bf13e1fc2f83,0x160608b33e5fcaf93f2,0x2c2e021000304159101,0x70e800ae081210690480,0xf2200000000d410000,0xc8580a682404000,0x8b080006d04000000000,0xb210080017e25000000,0xb21000000000,0x8030100000000000000,0xc04000000b6100004058,0x0,0x0,0x0,0x0,0x26c20128328200]]
def g237H5 (j : Nat) := if j=0 then 0x1c else 0
def g237D6 := limbs80 #[#[0x54c20591530816354c20,0x837454c20dc15308176,0xd4d610815358420dd953,0x58c205d5630817458c20,0x8373594205cd6508275,0x5d35308164d4c2058f53,0x8110544204412108110,0x44170109105944244175,0x5d84244175109105cc42,0x48110541204436510910,0x44175481105952044151,0x4c930441214c1105d920,0x4c11054930441514c110,0x441654c1105513044153,0xd4930441754c1105d130,0x4c91059132443544c110,0x443704c9105d93244165,0x54540441505011048540,0x50110589404415250110,0x44251501108854044165,0xd4540443505011099540,0x50110d89404435250110,0x44165509105494244365,0xd954244363509105d542,0x541101c5504404254110,0x44142541104c95044072,0x54950441515411050d50,0x54110551504415354110,0x44165541105915044162,0x5cd5044172541105c550,0x541105d9504417454110,0x44251541109095044232],#[0x98950442545411094950,0x541109c9504426454110,0x4434354110d095044274,0xd89504435354110d4950,0x54110d91504436354110,0x4437454110dcd5044371,0x5955244164549101c152,0x54910989524417654910,0x4436354910d895244354,0xdc1524436554910d9152,0x54910dcd524437154910,0x4416554d10dd95244374,0xdc9534417654d105c153,0x589101d5624437654d10,0x44175589105956244164,0xdcd62442755891099562,0x595101c9654437558910,0x44272595105cd6544172,0xdcd654437259510dc165,0x8c11054630441218c110,0x441658c1105523044152,0xd4a30441758c1105d230,0x8c91054a32443548c110,0x441758c9105c63244165,0x54a4044151901105da32,0x9011058a404415490110,0x44352901105d64044165,0x596424415290910d5240,0x909105d6424417190910,0x4436590910d0a4244176,0x59250441629411055250,0x949105c6524416594910],#[0x44173989105966244365,0x5432044132c81104c720,0xc811054b2044151c8110,0x44171c81105972044153,0xd432044265c81105d720,0xd01105434044353c8110,0x44171d01105974044151,0x5935044162d41105cf40,0xd491058f5244171d4110,0x44171d49105c35244164,0xd8b5244176d49105d352,0xd4d10d935244363d4910,0x44172d4d105c35344165,0x5d36244363d4d105db53,0xd8d105cb6344175d8910,0x481654c5205cb6544175,0x4c55048072541201c550,0x54120549504815154120,0x48161541205515048153,0x5d15048173541205c550,0x54120905504823154120,0x48261541209495048251,0xd855048353541209c550,0x54120d91504836354120,0x4816554520dc95048371,0xd8d5148361545205d951,0x54520dc1514836554520,0x4816554d20dd95148373,0xdd9534837454d20dc553,0x59520995614816558520,0x48173595205c56548071,0xdc56548370595209c565],#[0x8c520546314837359520,0x48165945205da3148165,0x5c3514816598520d9651,0xd4520d875148176d4520,0x48176d4d205c35348363,0x5486154175d8d205c763,0x18550588615416118550,0x54174185505c86154164,0x54d51541711895058862,0x54950dc1515436354550,0x543705495058d5254070,0x54961540735855018961,0x58550589615415358550,0x54352585509916154262,0xdc1615436258550d4d61,0x945505c2515437358550,0x5436494550d8a5154361,0x54a6154362949505c652,0x985505ca615416298550,0x5417198950d866154352,0x5cf6154172d855058b61,0xd855094b6154174d8550,0x54173d89505c76254274,0x5d530841534c2105d362,0x5061054541843544c210,0x84175506105914184154,0x54950841515421050550,0x54210551508415354210,0x84172542105c55084164,0xd495084174542105cd50,0x54210dcd508435354210,0x8415454610dd95084374],#[0xd5151841655461059151,0x54610dc9518437054610,0x8437154a10dc15284374,0xdd1538417654e1059153,0x552105d9548437654e10,0x8437655210dcd5484371,0x5c5648435458e10d4961,0x592105d5648417359210,0x84373596105c56584275,0x58b5184154d4610dd165,0xd46105c35184164d4610,0x84171d4a105c35284172,0x5c35484170d4e1059353,0x542205cf5484171d5210,0x88153542205495088151,0x5c550881615422055150,0x542205d1508817354220,0x8815454620dd95088353,0x5d951881645462058551,0x54620dd1518837254620,0x8817654e20dc55288376,0x5c1548837654e20dd153,0x55220dc5548817655220,0x8837655220dcd5488372,0xd4961881545862054961,0x58e20551638835458620,0x88174596205c56588354,0xdd1658837359620dc565,0xd462058b5188154d4620,0x88174d46205c35188164,0x5d35388170d4e2059353,0x587505c961d417058750],#[0xd4372587509d161d4272,0x5c562d437458750dcd61,0x58b509c562d417358b50,0x8df7458b50dcd62d4371,0x9ee7a9de6f97e3f8f63b,0xaeeb7abe9fa5e7e9f67c,0xb7adcb6edab5aceafabd,0xc7afcbeaf6bd2f3bcaee,0xcef37cdb33cbf2ecaf1f,0xd7b5dd735bd6357cfb3d,0xddb75dd370dbb6ddb367,0xe5f96e3f8edf37ade778,0xeb7aceafa7e7b9de6f9a,0xf37ccf2fbceebb6ed7ae,0xfc3ecfabdcf6bd6f53ce,0x62ea106ab9843f8fd3f2,0x64ba045b2e61172ba841,0x973021213c384572ea11,0x97eb288a92a620b09907,0x444f0e969eaa0bce7068,0x5e7eb19220ac44701c19,0xb180706688fa0985fec6,0xb3e18c2b3936c6cb01c1,0x253deac94782b151dfac,0xc9507ab2521fac7487ab,0xb25d91ac97346b25c5ea,0xac8034cb180d1ac97746,0x3b1b660aa4e740b280d1,0xd306d62ac2b8caf06d98,0x1c1e1dfac77c2ac1398,0x8170f1044b26483b0192,0x526c2468a3071a2ec0c6],#[0x4407073b03c3c552ae71,0x19a8a9065e3021278ba8,0x86c87041b52bb06952ec,0x21c17c00701b0e1b1fc1,0xabde2e2af07c2874570,0x2b760baabea2a4af3fc,0xbaadcf304b7a8a92dcfb,0x2a4b415c3ac0530eb060,0xfc1acc8704b352b2ad1d,0xd2a6adb6a92b41f0eb31,0xb6992c0fb0aad78baab6,0x2aea6b0aaa9ac2daa4b0,0xe78baac0ff06b078b9ac,0xc4f30aae76baabacaa6a,0xb13dc1ac5dae6b1b6c0a,0xac8970cb270b9ac9df0e,0xeb83cc12e0fb02b816c3,0x3accef06b33dc12cc5b0,0x2b516c3ad8f304b617c,0xa907ada841e17c1ad5e3,0xaca1e78ba07ad2a61eb6,0xfc2878fb0a1e78ba87a6,0xd2a6203fc1082d264203,0x78ba082aea820aaaa082,0xe5aca1f70ba07de2ea20,0x73ec089c5f0e2170ba87,0x885b0e2724c309ceb062,0x2270ba088ef0422b4c08,0x88da2e8233fc088e5aca,0xc283ac18a0fb022816c3,0x2895e7022516c38a0930,0x6249bc08905f0a2554b],#[0xc2099c7062679c089a5f,0x2ea889ab2a22daa48817,0xfc1224ff0a883ec2a21e,0xaea889aaaa226d706893,0x60baa29e2ea8978ba226,0xd82ea8f3ec0a3c5f0e8a,0xb3fc0a2c5b0e8f24c323,0x40fb029016c3a2da2e88,0x8c54b2a345b0e9024c32,0x8b85f088e55c3a325f06,0x82f3ec08d8930c2e3fc0,0x90b47708321fc18ca82a,0xca2d9ab28b6daa42db69,0xb28cebaa83378ba8b66e,0xaa82f3ec28cde2ea339a,0xfc10be6ec42f33c20be8,0xe6e62faba98beaaa62f3,0xaf2a0bebaa82f3fc18bd,0xebf082fae420beaea82f,0x478ba8d1e6ea2f78ba8b,0xdccb08373ec28d1e6ea3,0x3817c38c182ea3016c38,0xe182ea3832c20e0fb02,0xa3933c20c45b0e3824c3,0x20c8ef063224c28e552e,0x43225c08ca6f023233c,0x420ca5f063296418c897,0xb083554438ca4f083292,0xfc125a6ac49624c10e8c,0xe2ea96abaa25aaaa8963,0x24c325d82ea9798b125d,0x182ea9c3ec0a705f0e97],#[0x954baa645b0e9c24c327,0x7582ea983fc0a60970a9,0x9a24c327582ea9d3ec0a,0xa6d570e9a97c1a689704,0x8b970b9ae5e2e2b978c0,0xa2e9bae6ba60baae4cf0,0xeba14c3ae97aeabaa0a,0xaa2f54acabc66aa2f057,0x708bb1fc1aed3acabd62,0x4c11881f0ebb42baaec7,0x6f0a4a51b912a12c4471,0x7c11447f064c1bc292c,0xa6ac446aaa91193f0651,0x6aaa9918ff04469bb111,0x51e6e6469bb191a6ac64,0x543ec11526ac454aaa91,0x106aaa44179ba1526ac8,0x462aaa9188ef064d3ec1,0x998aaaa6623ec1189e4e,0xa44378ba188fb066278b,0xc290e5ec643a6a990ea2,0x2a4523ec0948930c4330,0xec0900930c5230c294aa,0x930c4030c2900eb06403,0xa8a91105d0e4016c3900,0xeb684533ec094c930c44,0xb24c314cc30a53a8a914,0x1c5d0e5b16c396c930c5,0x47ab4091eab024798b11,0x11e26c447a93111ea2c4,0x64788b191ea6e447a839,0x211e22c84731c191e26c],#[0xc4553ec095586e84789b,0xb1174930c5530c295662,0x6c65d88b197626c45d88,0x9b217622c85d30c19762,0x60e44a31c292986e85d8,0x89a992a22a64a99b912a,0x897084a55ba12897064a,0x73ac195e270a4a884292,0x893085f55ba17cc30a5,0x423ac1909dae4423ec09,0x964ff024e3342108cb08,0x64597b1914ff02453ec0,0x3970930c5c1743915c6e,0xe64896b19205d0e5c16c,0xb9920c70448aac0921c6,0xee66024c1180c3045ea7,0x6c218cff024f24c21825,0xa6e85669ba124ff02491,0x25c112cc70a4b24c3159,0xeb065889c292e210a4b,0x3fc094093046130c296,0x68fb025a3dc1140f1045,0x643ec0991a6e85a3ac19,0xa985b06647940991e302,0xea768ba294ff02a555c3,0x23005704c052b1301570,0xabf1bc2af942e4be52b,0xc28b05b082c54b20b06f,0xf0e2906c38a487042916,0x7c38a81b0e2a1fc18a81,0x1f0a2b07c20ad57002b0,0x3dc02454aca9374a924c],#[0x81b0e921fc1a4942ec91,0x407c2a545f009407c3a4,0x553aca1555b285152ca1,0x131fc184c8704134fb28,0x8601f0e1306c384d0aea,0xc1660c00581b0e1842ba,0xa0ec1f0a1743430590b0,0xe3c1fc18f01b0e3e9ca,0xc30f45f003d06c38fc1f,0xecaa052b2a81d2a4a007,0xbb27a36caa38cb2a8d4,0x1b0e9f1dc227c7f069f5,0x17c02841b0ea407c3a7c,0x4eb066578b89941f0aa2,0xf78b89bd52ec6532c219,0xbd54ec6f54bb1bde4e26,0x6f79409bde3026f14c09,0x9bc5b086f16c19bd56c4,0x7055431bd56ca6f54b2,0x11b06b0a6b36c19a45b0,0x27106c39b13ee66c20c,0xc3998c3006a06c31c453,0xb0e6d49ba1b483046d07,0x1c119c1b0c7214c09c81,0x7f066820c11b87f06672,0xbc21a03706681dc21a0,0x1f026853c09a1570068,0x807c19a13f06684e419a,0xcc1b067306c01cd0f0a6,0xa853b2aa54acaa906c21,0x30c8304aa1fc1aa08704,0x6c355b1b0d52c6c355b1],#[0x230d56c8c354b230c5f0,0xc6c452b1b114ec4c417c,0xb23114ac8c415c1b114e,0xb0ec14eb9b046b0ac753,0x8ba3088704c206c3b201,0x1b0ec907c3b081b0ec24,0x4e41b183706c615c0b14,0x81f08c607c1b193f06c6,0xb1fc19ec87047b21c11e,0xfd0eea7d20c11f50eea7,0x791ec19e41b0a7f06c21,0x9f87f067c23c09f10aea,0xaac06c1a010eea7e22c0,0xaaac7f06ab21c12ad3ac,0xe27507c23401f0acf42b,0xc31dc53027716c01dde2,0x7067489c01d07f067406,0xfc19d81f047655c01da0,0x5f00cc17c232c1b04784,0x7c13360706ca4fb1b30,0x81f0ad107c23453f06cd,0x579b8a153f06d207c134,0x153ee68571c021dc6e68,0x8597b9a1658e6859bb8a,0xa0542e48124c22149306,0x68223c0a089700824fb9,0x22087f06824fb9a0938e,0x28424c02107708821c4,0xc1a113ee68451b92108b,0xb06864fb9a1938e6861e,0x7c021c97008306c22181,0x3f00874ec021c1b04879],#[0x4f4121d3b04874e4121d,0x25acb3e07c234d3f0487,0xf16c3d00930d403ac1d0,0x1a4ac94555c34fc5f093,0x4b3bc1d2e4ac9469ab0d,0x51e4ac94798b151e4ac9,0xd4c92b253222c34f89bb,0x25224ac94896b1d20970,0xc94d88b254226ed4888b,0xb25245b095125c35364a,0xb074a92c0d2a4ae94a92,0x5c3538f7054e92c2d2a4,0x93075324c154c5b07522,0xa0aa504ff014124c254c,0x8730d4286b2d0642c941,0x817c051122eb431dc350,0x6522c95916c05645b095,0x547cb25501b0d5942b2d,0x55df2c9571bc35506b0d,0xb5590c0d5526e9551ac3,0x3d55230f557d42d55f30,0xc5711bc25581b0d5a494,0xc05c942e56f54b25c552,0x2c96e42b2dc922c97217,0xcc2dc122e9701ac35b9f,0x8b036524c0595230f707,0x88b2d6e62c55b06c3d94,0x1530d5b54b2d6d52ed5b,0xc48b257142c55c16c057,0x750acb7448b25d10acb5,0x5d48c3d762b075d49ba5,0x5781b0d5f16c057d250f],#[0x97554b25d81b096007c2,0x599230f7506c3dd522e,0x16206c3d987b076624c,0xb258c5b016348b25885b,0xb076407c1d841b0d6348,0x8bad9d22c97948b25e01,0x770b6848bada0770b674,0x1cc0da87707691dc0da4,0x41b096c1fc1dac73076a,0x322c201c8f080606c1db,0xe22ca0392b200e5ac60,0x354b280d52c80354bb0,0x80526e8014fba001530c,0xa044943805230e018ac1,0x20141f080206c30110ac,0xe0e48ba0393ae80d06c,0xb283c47040f48c38381b,0xf00091fc28213aea0842,0x6c20307b080a1fc20265,0x6b080c1bc202e27000b0,0xa8a935ea700d9a8c0364,0x4930ce0a8a93829aa6d7,0x2a8a938aa2a4d824c338,0x90c70adca8a9370930ce,0xe798a939cc30ae4a8a93,0x376a2a4dda8a935666e4,0x4e53bc1b74f704dd7639,0x9b66a2a4ea3cc1396a2a,0xe6d93dc1b6666c6d9a8a,0xc1b66a306d9a9b9b66a2,0x306eba8a9baea10ed9a9,0x7b9b6aa304da76ba3acf],#[0xa6e8db3dc13789302e8a,0x7c3b50f704df24c0ba5,0x81b0f021fc1c094aed01,0xe10c13c41f0b0307c3c0,0xbd3ee6ef22c0bbc6b0ae,0xf023c0bb01b0cf206c3b,0xbcc3706ed1fc1bb48b02,0x30722c0c148f030406c1,0x241d56c70760a9c1d56c,0xf0a1ac2c245f090755b,0xbabe50eeaf807c1c201b,0x304f542bac188f030643,0x6c33d84304f606c33d44,0x1b08f706c0bdc7f06f40,0x7c24301f030c17c242c,0x9dee4fe07c0c381f0b0d,0xa24c23fa66e4fe55b8bf,0xf47f06fb25c03ed4ae2f,0xfc06c1bfd4ee2fd24c03,0x4001b030021c13f09700,0x57e88a95fa6ac37a06c2,0xb5fcef077f55ba5fa26a,0xc77c98b15ec970d7f55b,0xb260a26ed7c88b25f25a,0xac97d3dc15f4970d8088,0x4c0e0c970d813dc16064,0x4ee58524c260c9307832,0x16c06221ea98586aa615,0xc1b0d8949ba619f2c984,0xa07c261d3f07871fc1e1,0x8552c9a354b168c1b098,0xa248ba689f2c9a006c3e],#[0x65c97019511c16901b0f,0x19823c0e588b039724c0,0x362c1b0f9822c0e60930,0x98e07c26301b0d8d06c,0xc3e9522e9a554b26981b,0x3019a21c16644705a706,0x7b963c1b0f9a1ec1e689,0xf3019206c36445b01917,0x76c064942ed928cb2648,0xd430d9250b2e48430392,0x6c364d22c99316c064,0x501f079051c16401f039,0x9d1fc1e6c1b079406c0e,0xe7c87059c06c26781b09,0x51960a94641b079f06c0,0x24645b071960a9c645b0,0xa5294fb9c6206c71716c,0xc14aa1aa52a55b24a582,0xb0f2b50b94ac8b092a22,0x5c1c414ae51006c3cb01,0x1f0f115ab943d4f0f109,0x7c3c4887051216c044c,0xdc6e7277039c9c5b0114,0x457b9c915ee71f5bb947,0x747b071d4fb9c74250f2,0x210743c7475091d1cc24,0xc993ee72251b94893ee7,0x72557b9c8206c7204fb9,0x4a13ec91e4eb24795ee,0xc9284f324a13ac92871c,0xa94cd26e9231ec1c8d3e,0x2e1325ab94bc8b053386],#[0x3c0cc0230f325ab94c98,0x6b0b3151b24c5db01312,0x6c3ce497013550c34c5,0x957013654404d8970136,0x707c14dc1f093607c1cd,0xe81f073807c14e01f093,0x1c1ac2ce87b073a24c04,0xc685b091c16c1c705b03,0x51c30c0c70c50d1a30c0,0x146cc3091c30c1c72a6c,0x11620c0cb946c52d2dc,0xc3c5487031578c04585b,0xf073b0dc1ced46c53451,0x7c1ced3f073b4e41cec7,0x1f093c07c0cf01f093b0,0x1fc1ea01f073d07c0cf4,0x88b03aa1dc26a47109a9,0xd06c26b01b07ac1ec1ea,0xb88b03ab06c26b41b05a,0xb11dc26bc1b07ae06c16,0x6c81b07b220c16c49301,0x9b306c0ecc9701b006c2,0x1b07b406c0ed01b0,0x1b005a01200360090012,0x840d3030c0ac024007e0,0x413804b011604380fe03,0x18605ec16e0584159052,0xec076c1ca06e41a70654,0xf08d0227086820d07f41,0xa9029709f0269095023,0xbf02ed0b942d40b142b6,0x9034c0ce83280c5830b0],#[0xc3a40e503880de43710d,0x3e50f6c3cb0f0c3ba0eb,0x1c105040b100c3f60fb8,0x116044610e843210a84,0x125c48f121c47f11b846,0x3204c012e04af129c49f,0x344fe13d84ee13984d71,0xc552152853c149c51b14,0x593162c57d15d456d157,0xce17105bc16c85a3166c,0x5188461918105eb178c5,0x19e066a1988653191063,0xad46ab1a8c69b1a38686,0x106fc1bd06ea1b606ca1,0xc73f1cdc72f1c687101c,0x7801de07701d847591d2,0xc01ed07ac1e787961e30,0x51fd87e81f787d31f2c7,0x20e883220a4821204880,0x1dc86f219885e213c847,0xc88a3226c893221c87f2,0x88ea236c8d3231c8bf22,0x93f24c491e243090223d,0x9a263097d25749542530,0xc27789d1270c9b026889,0x28a0a202834a0527e49e,0x9b8a60294ca4628e0a30,0x3cac72accaa42a30a7a2,0x8b162c18af92ba8add2b,0xb6e2d84b572d10b372ca,0xb72ea8b9e2e44b832dec,0x2fc8bea2f70bcd2efcb],#[0x30c8c253074c153034c0,0x1e4c6d3168c513124c3f,0xdccaf329cc9d3238c863,0xccf733a0ce0334ccbf32,0xd3e34bcd263468d0e33f,0x8635f4d7535a0d5a3548,0xd36f8db036a0d9b3638d,0x3820df537b0de03758dc,0x900e3438b0e24386ce12,0x58e8b39d4e683974e523,0x8ed33b10eb93aacea33a,0xf173c2cefc3bd0eec3b7,0x533d2cf3f3cdcf2b3c7c,0x93e2cf803ddcf633d6cf,0x3f58fc73ed4faa3e84f9,0xa501e40450033fd0fe9,0x9d05c414504841010314,0x90b2427908641ed07141,0xfa43c90e643790d0430,0x3b44b9126446510a4409,0x445b1164456514f45191,0x46a51a14651189460517,0x7951dd47551cd46fd1b1,0x9121c483520147d51ed4,0x125c493524548dd22c48,0x2a54a7528b49f927649a,0xe94b752cc4b092b74ab5,0x64c793164c293024bdd2,0x4d753554d213404cd532,0xe4938a4dfd3774db5365,0x453c34eed3b34ead39d4,0x540b4ff53f54f9d3df4f],#[0x44850e543150a541d505,0x8851fd47551a145f5151,0x852f54b152a549f52454,0x54114f753bd4e253594c,0x50153854c151c545150c,0x3157b55cd569556d54f5,0x55cb56c95aa568959456,0x632587961258195f8579,0x7859c1668595964e5919,0x35a8969a5a496885a016,0x5b856d95b456c95aed6b,0xc5d70f5c156fd5bd56e9,0xa17605d417425cd972a5,0x57a55e757905e0977a5d,0x7e15f657d15efd7b55eb,0x1c603d8075ff17f35fad,0x612183d60d582d60958,0x61f987661b5861616185,0x2c18a7627d897623d887,0xb18e3636d8cf63058b96,0x1920646190663f98f663,0x960656194d651593964b,0xa2665d98a660197365a1,0xc67459c566f59b266a99,0x682d9ff67d19ec67919d,0x901a3468b1a24686da13,0xcda6a6989a596941a486,0x1aa06a61a906a11a7c69,0xad46b31ac46ae5ab16aa,0xb6c0dafb6bc9aea6b89,0x46d1db3e6cc9b296c7db,0x6e39b866dedb736da1b5],#[0xf41bc86f01bb56eb5b98,0x45c036fddbe86f81bd86,0x1c507109c3470a1c2070,0xc897201c7771bdc60716,0xd67335cc572c1ca5725d,0x67439cff73d1cec7391c,0x7525d3c74c5d287481d1,0x601d7875c1d687565d51,0xc1da87681d987641d887,0x1dee7799dd77731dbe76,0xe3d78c1e287871e0f780,0x7f79dde6b7975e507915,0x37b01ead7a89e957a35e,0x7c19efe7bc9eea7b6ded,0xd09f347c99f1e7c59f0e,0xe9f727da9f617d51f4a7,0x1faa7e6df937e2df827d,0xfe87f55fcc7f11fbc7ed,0x3280aa01b804dffe7fd9,0x88182058814204780fe0,0x8246089820607881c206,0x33a0c582f60b0829209b,0x60f983c20e8837a0d68,0x213784a611a844610984,0x17185a615f855e148850,0xa3866e192862a18285ea,0x987461c987021b886c21,0x884e20087ce1eb878e1d,0x92e24388ee23288aa222,0xee27389ae263896e2538,0xa2a68a7a2968a3628489,0x2f38bae2d28afe2b68ab],#[0x2b8c8a3168c323048bee,0x38dae3578d2e3438cde3,0x8e9639c8e423848df237,0xfbe3e78f6a3c78ee63ad,0xe242c907e412901e3fc8,0x648391e2470918645590,0x4d9932e4bf92c649e924,0x3694a651e942e4f693a2,0xa967a58595da563953e5,0x97a65e197565c796e25a,0x8b6622986a60797fe5f7,0x9265b994a64a990a6359,0xa6959a3267f99de66f99,0x6ca9b026b69aba6a69a7,0xfc9bca6ea9b8a6da9b4a,0xf9c9671d9c5670c9c126,0x9d7a7559d267409ce272,0xe3a7869dfa7769dba766,0x227c09ee27ab9e8e7969,0xe7f29faa7e29f667d19f,0x830a09e81ca0428089ff,0x6da18a85aa122840a0e2,0x4a272894a232880a1e28,0xa35e8cba30e8b7a2be8a,0x45e908a4028f8a3a28df,0x46948a502934a4b2920a,0xa97ea5d696da59695da5,0x9b0a69e99ea65a98ea61,0xe9a7869d5a7369c1a6e2,0xca852a0ca8129fba7ce9,0xa93aa42a8d6a2da892a1,0xa0ea7ba9cea66a97aa56],#[0xd2aacaa92a9baa4ea8ba,0x6addab56acdab12abcaa,0xb12ac16afdabd6aedab9,0x60ad4ab3dacd6b2dac82,0x8ae6ab90ae1ab77adbeb,0xaf6ebd0af22bc0aedaba,0x76c12b02abfcafc6be9,0x92c5cb152c46b0e6c2bb,0x2cb0b28ac94b21ac78b1,0xcf7b396cd0b322cc0b2e,0x4eb4fed37b48ad13b3fe,0x7b5e6d71b5a6d61b55ad,0xb6dada7b67ed97b63ed8,0x7eedf3b7a6de1b736dbe,0xbae26b87ae16b832e03b,0xae56b93ae46b8fae36b8,0xe94ba1ee7bb9bae66b97,0xe4bb62ed0bb0aeb3ba82,0x3bc6ef13bc1aefebbbee,0xbd3ef47bcfef33bcaef2,0xe0ef7bbdcef6bbd8ef57,0xeefaebe9af9cbe52f8bb,0x2fe4bf72fd4bf32fc3be,0x15c037005bff6ff5bfb,0x1018200500803029c087,0x40b0480e410888806150,0x68104c1810c3c2a024a0,0x41818a04001e0d058902,0xa88c8c00ba96034121e0,0x62c1484a1a2c8a488360,0x40c00ac1489173083364,0xaa3c1d0d192112838ca],#[0xfc85bf216fc848611885,0x16fc85bf216fc85bf216,0x5e421ebc879cb4cc9bf2,0xa22002f2136586192361,0xf58400790abac4605b2,0xd0a49439250ee91521eb,0x87790956844d232691aa,0xcd040e682a43161eb0f5,0x9886b411fc92881bc8c1,0x2ce04009a47310a4a14,0x724a1c928724a1d2167,0x22846424e0403683896d,0x5019d420000b01603,0x90800066c20001001a08,0x8d3106c201d8311,0xb8137020000010000000,0xd823216d865c08000001,0x8400023611a08036c22c,0x120200808381000000cd,0x800937044c348300166c,0xb0803b813c454e05b6d8,0x8d0d0100009a08056c21,0x3a82000080d42c52c0ad,0x803361d410000660c120,0x16c080203a820000788,0x9c086c280d2100a42642,0x1009a08000401dc08d06,0xd4100000000803b8,0xa0d38100d41001a09381,0x186053cb1370c480990e,0xc3f6863d856194020134,0x8d053618d2c4db08026],#[0x10f60800c86683ec,0xb1190c3033419a0c3020,0x100cf262b70299e4c754,0xc14d210d04f114d0618,0xcd05014f2c43419a09b,0x100cb0990cd06361001a,0x26836c0805b022e06d8,0xb10040101ab0cd040000,0x4045c0805584c853c,0x100170201561cf862000,0x13a416b81009909908b8,0x619a080004026838c080,0x3a82808072d0db02019,0x5a8200000100a025d188,0x1cee18f682c0580f70c,0xb018702c0436100eb0b,0x4194100941270200001b,0x20187e82000000941009,0x381a8589808040336160,0xc584b613c44c07b0b10,0x501602c0402000e04018,0xc8a15a0c16078b1b0140,0xc08000004a08063038c0,0xc050100b011a08045855,0x400022c2c0403ac20000,0x4c8400000000003610d8,0x8800b6160200000e04c8,0x2b0621a08016c32831c,0xd84c0b748480b0140400,0xc051c080004a0805218,0x80301004040000006820,0x2d84b610000008d8580],#[0xc8401012d8400b610,0x14072c2016026424e040,0x302c075040101a604020,0xc4000000b4100cb0d90d,0x406b22d41070200011f4,0x1f4180004b0201a74200,0xd90d6447ac8c5e0a8384,0x8b1000061aa183841590,0x8d310000202000000009,0x35040000000136100,0x49b0990990e3d8200404,0x22c30c0800f48401a28,0x40400007a424040000,0x4000000039610060201,0x80007504020000c,0xd41b60400020100000,0xc364200bc21000020201,0x31616020000c0402c87a,0x6c84018080003019a0a0,0x10000d41602000000c0,0x80004020001a820000,0xc0400020000016420001,0x8200000080004b020000,0x328756100d9080501f74,0x3dc504808052100a433,0x321db420000000001484,0x11b0c6c2642012e06361,0x581b604020100e342000,0x12c0804001db05486,0xc3484020080801381a42,0x12e0400032,0x3816034c0d6c20000000],#[0x201283d61b2441c31001,0x100941ad87ac2c040368,0x95304db589808d0402b6,0x4a080238100,0x7ac2808053034c08,0x809b810000008000,0x961c10066c32a6080200,0x1001a0801c2200,0x3a820140400000200000,0x2008080000040068,0x8440001cd851c0804000,0x8000000040101003,0x80000020000341,0x80006da12e0c5341,0x4020100000000000000,0xc031f476200800000000,0x2100d90804000100000f,0x100cc362b2100b21b,0x443680ec840003643642,0x1ab0b01603b4100da0ce,0x1d684c84bfd90c9643b4,0x10d869991ed043616020,0x629305116c3ee04b6132,0x371820c35b1ad0580c65,0xb0ca0a7e018e0d0c6562,0xad8402507981f7035,0x8000658401808054b620,0x40396100006020100,0x80000000002028080000,0x20001404000002000080,0x75040,0x400020001b4100da08],#[0x160364200015a08000,0x200c058080070c400000,0x41009410060200000128,0x201f3420000474201009,0x2c840201a8201a8,0x40200010080000000004,0x100404035040350,0x590ed0400020000,0x10000000000da08,0x20000,0xbbb2080002ac25b0d584,0xc0a0280b38100d343ac0,0x403581a42000080dc45a,0x587581d605808016c2c0,0x2c0cb032cd040001ac0d,0x9d904000000017114b03,0x22d133814658200ed58b,0x6040000029080738100a,0x99c08045a100000000d,0x202010000404031a6,0x8000000000000000000,0xcda1ccec5283561941da,0xda08045a160364201cc0,0xb21000000d4100000000,0x8020200010000000000,0x2000000000100cb,0x2c840000]]
def g237H6 := limbs80 #[#[0x104058010880d0003c1,0x58430111871480041410,0x1115c4ccb0d10050402c,0x80014041c00c4440183,0xc00101524c7c50460910,0xc17400583841010d001,0x20305039441f9dac0,0x4704942f800082c444d,0x28958019a405012f2238,0x309a000006d0000056ce,0x419400040f0000000,0x2a0000000c24c0088128,0x94077025055646500020,0x82ba080cc7443040b10b,0x11095a0c830684969513,0x1000bc01509191c4407c,0x364ac21528a11a50725c,0x8a4204444821e090145,0xbb613631f54480788c9d,0x6000000000010a3827a4,0x9c000c15303502e30a,0x527c1b4c5d4000,0x8c02f000000012930320,0xa326d2f506e000373b8c,0x4744b0019cd4f43b605,0xc1ac000c1804328e32,0x8800e0794230000c2c80,0xc104000000022241b301,0xcd006c087121,0x78259829444282f64670,0x80000001039c16000001,0xc09d0112dc16f204c13],#[0x7448cb21f000000041d7,0xf000027d41dc00012fb0,0x1028000341e00ff06,0xa03c00054cf228,0xc000423908fc0ac0000,0xc0008101601000105c58,0x69fc293415402b0bc82a,0x460003416010c00002c0,0x6e26c0000003234425e0,0x52f080bc0b903a803746,0x20500000221,0xf6111001208841cc2260,0xa0a0898c000022601b41,0x901a119c0405094c8,0x57c28a05983040000000,0x3903400051d7052d0200,0x1092029f10981ec01,0x2ed09484e505582d1007,0x680028024000000204f8,0x61230000000014c00081,0x1760380000000c0a,0x502644580500000000,0xc046909c803800000980,0xd1bc0000000000000200,0x6873a526f04c,0x25cd82400096b008d0,0x508441c405fd03c11300,0x17000073ec258095884,0x7c91180638cb92000001,0x6c19f28c000000000000,0x4267154000173d010b03,0x7c0000000324c8a473f],#[0x38000000105100000008,0x314a5c0c01c02a90baa1,0x1098426e209000,0x76000140a02fc00008dc,0x30000000428500f41a60,0x84000042d4000c11702,0x140200000000000000,0x9c000000212a00000000,0xf0ac0134000000203148,0x153808881e103000044a,0xa0d1a00af02a00150003,0x42dc00002cd21a807b4,0x805a37741f8000847502,0xad90de46e81c207f,0x4000c18b02d00005100,0x3e000160b000203de0,0x9004000885,0x22889504802190370000,0xe420e03be1d508bd0b31,0xd1310010208034809321,0xf00644049311c27d2a8,0x630b6000311701aa2121,0x170982760a941e806144]]
def g237D7 := limbs80 #[#[0xd48105941054c1054810,0x5842054c2054420d4c10,0xd4420984205942058c20,0x81105885058450d4c20,0x4c110481101491010910,0x5411050910501104c910,0x595105891054d1054910,0x90910901108c9108c110,0x99510989109491094110,0xd4910d4110d0110c8110,0xd9510d8d10d8910d4d10,0x54520541204c52014520,0x8c520595205852054d20,0x99520985209452094120,0xd8520d4d20d4520d4120,0x1895018550d9520d8d20,0x58950585505495054550,0x98950985509495094550,0x4c210d8950d8550d4950,0x54a10546105421050610,0x58e10586105521054e10,0xd4610c82105961059210,0x54220d5210d4e10d4a10,0x5522054e2054a2054620,0xd46205962058e2058620,0x58750d5220d4e20d4a20,0xdadf6eafd7a7f3758b50,0xbebf5d9fbfdfafb7bbbd,0xfef777b7dadfefb7bbbd,0xbfcfdfebf1f7fb7bfd7d,0x1741e32e63dd4847ffbf,0x5c6ac9340dccd84ba8f1],#[0xaec00c594020b1005152,0x415d8198b2830776000,0xdd8082bb013165027ac6,0x103b90205760862ca101,0xbb1229751f02a23c1dcc,0x481514902629095c5202,0x754852e691e54923c992,0x6da644e05449c0909329,0xea4d2594994ba136d532,0xa5d0e40a89c81213852,0x84ac0909529753892ca7,0xa5b11582512b02a25608,0x11e81513c96ca552594a,0x29753c92ca78a5d0f24b,0x62e4ee25c75cd292b8a5,0xe25e0944bc0a897057,0x45d7d48baea91783712f,0x7d4cbaea9974b622e92c,0xb95b9974b632e92c65d,0x4b1202b742e96c85d259,0xa629754052e881259102,0x5713a0aec50adc0a12b8,0x203ae640a5c0802bb1d2,0xae27c15d88073a900d75,0x44a5c0882bb1f67423e4,0x9d088aba111d73224ae2,0xc02bb182b70300aec445,0xbb215752424ae2841dd8,0xa05764e4ae29ca5c1382,0x74523ae6881dd4d03b99,0x262ca64f58cc82baa905,0xc6a0a5c1403bb1905763],#[0x815c9502bb283165507e,0xc0da5b81b1f73360aeaa,0x9fb99b3c73360ee46c1d,0xad67952ac0ae4ac1dccd,0x29759692cb2db54e594b,0x39a92c5357d4a6aea94d,0x56e735258e6afa9cd5d5,0x9312dda695ba4d49649a,0xe99271cb24e2b709c72c,0x2b9cb2572970ae62cb38,0xb14f2b709e62cb5ce99,0x4f31659e74c93ce5927a,0x964b052e1601dda782bb,0xa00aed60c596c1d32583,0x2cb40e99281cb2503d63,0x64a5c2c83bb500576a06,0x5dac98b2d93a64b272c9,0xd03bb510576a272c9441,0xb8d40576b472c968a5c2,0x53a75a872eb50e5cea1c,0x610a0ee9541dcea83b95,0xa62ca14f98c29eb18545,0xc62d1584583bb0505760,0xc15d8598b28b3e63167a,0xd43a2ba8747530e8aa61,0x15b8064753148aa62919,0x2863a640c72c818f58c3,0x3d63180eec1815d8318b,0x61862ca30e99061cb20c,0x7cea20f5d441eba08057,0x224c5c4483b989077112,0x5549719b98931731266e],#[0x9725b0ae05765c46e4b9,0xc392e5f525cf4a4b9e54,0xae5f535cbaa6b9edc973,0x9756856e8b92d91725b1,0x5852e0b015d9990b9382,0x6a2d41dd9782bb2c1d73,0xec15d9c94b83905766ab,0x5c9d14b83a0776600aea,0x902babc0571780aece88,0xb9b20771640ee0c92dc1,0xb5d52b692c36c15c5e83,0x63b6bea76d754edafa95,0x896ed6cadd2da4b25b49,0xe18c1ddae02bb5c4561b,0xc596e95b85d0576c652,0x96f1eb1de3165c852e19,0x94b8650776bc0aed78c5,0x25f2372be0aed94c5972,0x2970cc0eed7c15daf9cb,0x4c40ee7881dc7102bb66,0x82e23915d06a2b90d077,0x2f91d86214b8442b7080,0x1d8630fb9c21c73848ac,0xe482b94922728c42e519,0x2ba4905739266a724c54,0x455f7082b8e104adc208,0xd73901aeb150d8a294b8,0x7e82c4fc99c5f92b8bf0,0xce8fc55d1f8f39bf1d73,0x2815ce502b8ca43628e2,0xdd3383b9e70772ce0ae9,0x3ba680773d00ee3a01],#[0xbb014d65029aec013594,0x28950249ae60935c8126,0x75249aca49f548942a89,0x90aa2922d41244a8242d,0xa690b5d5226b2a47d524,0xe2995244b2a48b534912,0x509c5a91389522712844,0x45a91c89523916a84e25,0x81589502b16a8722550e,0x89512a9aca561544ac5a,0x22b12645625c4ac5a895,0x12ca562588ac5a915895,0x87a2d48f44a91e8a652b,0x15452c4a8258b543d12a,0x4b96baa54d654ad2a896,0x6b11763522ec2a45e154,0x972f742e9ac85cbdc8ba,0x9322f16e25e25c4ba6b2,0x2f12845e2108bc519178,0x4a45e2548bc5a1178a42,0x5e21c8bc5311789622f1,0x50cbc5b9178a722f12e4,0xbc4b99789532f16865e2,0xb2178a542f12a85e2dcc,0x789742f10e85e2990bc4,0x544112a4822dd0bc53a1,0xc5ae4993589330a92689,0xca513590a16ba264d644,0xb5d4ea6b29d7d523a9a,0xd8816ba904f65209aca4,0x27b1964d632cfaa458b5,0xb162d752c9eca593594b],#[0x4f653e9aca7df548f96b,0x305aec44b5d8f96ba9f,0xae260bdc0c45b818887,0x461f588c17b898867131,0x3d8cc26b1984f6230fcc,0xc31aa186154305ee661,0x6b2982f74309ec861359,0x182d76309aec613d94c2,0xd6542fac484bdd8c273b,0x4e5aec84b5d50a7b2a14,0xac69d3d89396b8a72d70,0x9d3591396b9a74f634e9,0x590d16bb272d744e9ec8,0xd27329a4d65345ee8693,0x3a9a4f73349ae668bdd4,0x24f75349cea6935d4d26,0x723312e064b5d5126b2a,0x65ae4a135d8ca6b2992f,0xe06dcdccd97b91b8b703,0xd39c8da6b91b4c72369e,0xc91a7b99b4d73369ee46,0xc4a0cd8b549712a92cb5,0x94d89529b12e33625466,0x89549b12e736254e6c4b,0x598d2a9321546644ba4d,0x5ee539358a716bacc4d6,0x9393592731aa4e61549c,0xb5caba6b1574d659c5ee,0xa916ba574d64aec2a95c,0x6b2cf2f719f16e13d3d4,0x508970a05ae36135da7a,0xd76a09acb40bdd2826b2],#[0xa69aa94cb5d2ca6b2594,0xee744bdc68c4b8514f54,0x68b5c6d26bb514d65a25,0x5ceaa6b9554d71aa5ae7,0x326bb054d650a9ae9553,0xb2862f740c9ac81a2dc0,0x92d74189ac83135d8326,0x525c5ee2b935cc4a6b88,0xd1462ba24c5726b2ae7d,0xa2ba254574520ae89415,0xa21c574530ae89615d14,0xc9745b8ae8a715d12e2b,0x44b9ae89535d16e4ba25,0xa2e89745d12a8ba2dcd7,0x4d655a5ae2e22545a45b,0x6585aeacd35959c2a8b3,0xcc2be1585797b82f2d7,0x6bd8d4d7b0a9af4f615f,0x3d957a6b2af2f735e9ec,0x97a73b2f2d765e9aecbd,0x7b2b54d656b0ac2d4bdd,0xb92d70725aecd4b5d5aa,0xd73729ec6e5854dca7b0,0x629ccac53595896bb392,0xee2c0b5d5b26b2b62f75,0xc13595817ba307d72605,0xdc1916ba3a2d71749aec,0x92638b24f70645ee2ca2,0xb9b24f71649ce2c935c5,0xb8951b65ae2dd3dcd926,0x53b712e56e254adc4b8d,0x912e96e2552dc4b9db89],#[0xc9718d52e30aa5c2f72b,0xd35dae26b2dc2f74b89a,0x931b0aa632d72c69ac58,0x27a9604d52c05ae98d35,0x2dd2f71ba9ea98135530,0x2f74bc9ac978b5c7226b,0x4ca9ac99535daf26b2de,0x12e17d3d530a6aa612d7,0xb7cbdcefbfb95f2f71bf,0xb5cf316b8e64d76be9ac,0x3126b9e24d72c49ae388,0x7b1406152805ee10135d,0x444f6380c2a700bdca02,0xf64885ae5113d8a230a9,0x7c9ac4f98549f16ba444,0x6e108b5d1f26b23e2d72,0x9318a131a9426152851,0xdca127b1424e62849ac5,0x126b1c2635384c2a708b,0xb9c2737384e0e7093d8e,0x24f64849cc9093592117,0x628cc6a519854a317ba4,0xc9ec918b5ca327b1464d,0xc525358a4b0a9492d748,0x5358e4b0a9c92d72929c,0x4a4a6a9492d74925ae72,0xa6a9c94e72929ae52539,0x8414e74929ae92535ce4,0x637082c2e1053d8e097b,0x18ac0ed058d8e0b0b1c1,0x5ae2fd858e430b1482d7,0x70d358e197b8c38b7086],#[0xb5c6397ba432f73869ec,0x6516ba4a2d73945ae328,0x6ba4a4d73949ce32935c,0xe74e72ce9ae59d35c33a,0xd70d09ce99d35d33a6b9,0xd09ae7a139c7426b8e84,0x4400cc02200440004d74,0x802bc09601f406401600,0x4f812704400f703780c,0x7101ad065817f05a0155,0xc821d08301fb07a01d70,0xc2ac0a4827d098824d08,0x3310c7430f0bd02e20b1,0xa50e243730da435d0d08,0x8101c3ed0f843cd0ec43,0x11f8465114844610cc41,0x46c4fe13784c712c0495,0x3c57d15a855c15245321,0x45e717545c016c45a316,0x65f194c64318cc61a180,0xeb1b606bd1aa868e19d4,0xf1db47551ce47211c186,0x1fc47d51f087ae1e6877,0x1fc86a216083c20a480d,0x448f423548c122b48912,0x897f25b095c250092424,0x9ec275c9c426b899b263,0x622950a402898a1327ec,0xf2b30ab52aaca9329dca,0x2cb8b232c60b042bc8ad,0xe0cb782db4b562d28b3e,0x10bf32f60bc42ec4b952],#[0x4c703154c4330d0c1f30,0xcde3328cb33288c8f321,0x5134f4d263448cfe33a8,0xb36c0d9535f4d6d357cd,0x388ce0837c0de5373cdb,0xa90e9139e4e613914e31,0x20f2b3c38ef33b60ec03,0x8fb03e6cf883dc0f5c3d,0x3140710073fc8fde3f2,0xc042a508e41cd05f412d,0x644f512244350f2435d0,0x47691bf469918d45c515,0x9e525e490d22a48391f3,0x192eb4b5d2c34aa12944,0x135c4d4133b4cbd3214c,0x3d14ef53ad4e6538b4dd,0x1e50394024fdd3eb4f7d,0x251fd46a515d44450c54,0x54014e953594b9529549,0x5995575511534547950e,0xa15d856f55aa565d57a5,0x962e5885616582d5f457,0x6ab5a5d68259b165058e,0x115c056f55ba56d95b05,0x35d7d7515d197305c717,0x5f5d7cb5ecd79b5e0977,0x17d84860c581960157ef,0x698bd62bd8a5622d8766,0x994864ad91363e18ee63,0x9ba66a598d65c995c654,0x2068359f767999da6739,0x56a31a796985a4e68e1a],#[0x6c45af96b85acd6ac5aa,0xe59b826dadb566cf9b26,0x1bf06f79bce6ef1ba66,0x1c647149c4270a5c1770,0xcd67305cac7255c8071d,0x4974f1d237449d0273b9,0xf76b9d9c7631d76757dd,0x787de0b77c9de17741db,0xa75e8479cde627905e30,0x71f077bbdeda7b15eb37,0x5f737d85f4f7cfdf297c,0xfef7f61fc27eb5f9b7e1,0x6d815603a809e01d8011,0xf83760ca82c209882120,0x855613f8496113840a0e,0x6f61b3868618d85ea169,0x2227883620087961cf8,0x229f8a36278899a25389,0x3178c0e2ef8b6a2c38ad,0x8f8df23698d3a33c8c9a,0x38fbe3db8f0e3af8e7e3,0x915a44590b241f903e40,0x3124b0926a48591d6465,0xb251b943e4fd93b24d59,0x658495de567954653a94,0x5f397725cb96d65a5965,0x649942636989261c982a,0x99ae66a89a5e68699da6,0x9ca27139c0e6ef9b7a6c,0xe3277b9dae75a9d2e740,0x927d19f127b49e867979,0x283aa0b681ca02a7fc9f],#[0x89aa242878a1a285ea11,0x1a3ca8e8a34a8bea2b6,0xda55e944a4c291ea4429,0xa7229b2a68298ba5fa96,0x8f6a2ea852a00a7c69dc,0xfeaaaaa4ea7fa99ea53a,0x2b1bac26af5ab9ead4aa,0xb88add6b65ad46b3eacb,0x8afcebe1af2ebb3ae7a,0xbb1a6c57b10ac2cb06ac,0xb3aecd3b2e6ca0b23ec7,0x54ed45b4e2d1eb436cfb,0x5adbfb6aad98b5fed68b,0xae2fb87ae0cb7d6de3b7,0xe8eb9fee73b9a2e55b90,0xf9bbc2eddbb0eeb0ba86,0x3bd86f4dbcd2f20bc26e,0xbeeefacbe76f91be16f7,0x7700abfe6fe9bf6afc8,0x4f07dc19b058c10702ac,0xf0ebc38f0ccc2d70a3c2,0x148c4e3129c45f105c3c,0xb0c68718fc5fb170c567,0x8c81b1f8c7a31d6c70f1,0xc983251c91b23bc8a721,0xb0b2afca8b292c9ff272,0x47305cbcb2e7cb732cfc,0xb364cd5b345ccd3323cc,0x3decf2b3bcce97394cdf,0x52d10f432d08740acfd7,0xfd2f34a7d24747bd1974,0xd4d3522d4474fbd39b4c],#[0x6d359ed623572d57354a,0xbf623d8275f7d78b5c9d,0x368ad9e3667d94b640d8,0x702dbe36e2db2b6b5da8,0x80ddb775bdd27734dc7f,0x3df937d1deeb7a7de637,0xe13783ae09f80ee0037f,0x2d3893e22787ae1c385f,0x6b907e3cf8e0e34b8bee,0x3972e58b952e50b930e4,0x9d2e7139b7e68b98fe61,0x49e8d3a1ee8279f5e793,0x9ea27a7fe9d7a6ce96fa,0xebbbadaeb17abaea8fa9,0xd5fb46ecd7b25ec43b00,0xfbb4ee83b95edffb6ee,0x3c29f053c00ef93bd1ef,0xc81f1cbc63f15fc4cf0f,0xe2f34bcc1f2d7ca3f23f,0x941848444057d07f3cfc,0x304c041020881c145c58,0xc246602950204600008,0x36085214850d91089104,0x690ae182e888f151194,0x858e11170a8c3c283b0f,0x21d210e90b020d2e311a,0x304980123ad8874843a4,0x7c20893e10445e222217,0x8c7d08883e84449f110e,0x3a31672063ce40c61e91,0x31dfc824dfc887bf910f,0x4464e89074857388f390],#[0xa1837d9640f1920e90af,0x8c244d58a1837d964d58,0x7a425fc04889ce09917,0x4bd11e8d219c44bc4691,0x33219e04801281273826,0x107f1187094322817728,0x718e09917484bd50a228,0x632f09319f0235023f44,0x604abf010da2bb327722,0x873def2459ef68146b6,0x324181123830ff043df8,0xcf1138063e4867811c5,0xee0226f9c2887811ef01,0x48a04744674473b5144d,0x22484f22641f192219e0,0x9ee38884e8927fa9225b,0x175a2326f86224f71c44,0x3049ee38897091ef1622,0x277902325c124bc1246f,0x992e092175a232779023,0x25c24718e638c5883d31,0xc2a2de21237982779023,0x8cc96d9121f6c309875c,0x45a690ce88e7fe1110fc,0xf7012a7e24d34876223c,0xb64496ca04c70109ab04,0x6ce248c8a3ad8b7e9a44,0x4d22203dde4c67dba84d,0x7090ee123b9049a690c7,0xc024203203720400640b,0x1c71a0321e04600c01df,0x29c46baf49126a10ef21],#[0x1e046f00e474869d5499,0x3bc2460148e90d3aa932,0x8242039dc435b8888f30,0x21adc444bc824ba124bc,0x59f9125911a606981cee,0xdde4497804800f79e122,0x23207bcf0912cfc89001,0xf226d7022674c3325e01,0x6b81123975992f211a5a,0x9736648e204c837f4913,0x12f0092f2090b2e6cc85,0x859d12474876788f6b81,0x748723a433f0233f0231,0x467e04630b3a248e90e4,0x931a1dfa4443bf4887e0,0x39f444273e895c498eb8,0x955d2275bc2641714121,0xde602275380320e77a44,0x92aba44ee364c8b59a44,0x9bcc044ea700641cef48,0xd0efd2221dfa4453d748,0xe0467e046bf30110fc08,0x69818efc0441df80887,0x984903f049480ee904a4,0x18f2219e114e821a4087,0x235304203a42406406d0,0xc633ec467d88cfb11d9e,0x6134c421d9e233ec471a,0x3680ccbc925e123be1c,0x32457848ce88cf5a065b,0x1232f2477c31c26ba124,0xf009080dc8127ae0225e],#[0x907c8436023018030077,0x80876ce24a7c0931bf09,0x901b90267b331d3e0493,0xbbc892f009001d911901,0xf8663cb4378048c81803,0xc088c0496bc89b5c0899,0x1ed70225e01253e049b5,0xa8438e44c71c898e3913,0xb781321c440117e00c6b,0xe44c737d6910028f2624,0x5a7c0900200af86384c9,0xd433902978e032291384,0x125f70487205203203d8,0x1dc824ae118d3c898ee4,0x3101ee34112e41227913,0xca26d702217c121f6ea1,0xd11d44d0b944b671268a,0x3c22db843daec8819924,0x8bb0623c22ec18877843,0x2d55ca2066479e218ccc,0xaec50cc86cc88c3235d4,0x1b631a8a1cf050e707a1,0x8e689be42b322cf8620f,0x33430b70c6877a1ac090,0xa628531424f588cc887,0x847c647ab594498a14c5,0x76523c9538932cc50a62,0xe70c51c131ee84512ca4,0x30c7b4e288b11431a8a1,0x11ec47a284bf921d88bb,0xa1970c545c31d42c49c3,0x17c2871a858f7f0439c1],#[0x77508642c2c4016fac11,0xc927190cf3b121e6192,0x486191b4f0458d4510f3,0xc6a3d6a21e0467623a86,0x21b7262cc314ac21d752,0x7610c69c310043d210f9,0xee8937c0a2588b7ac0a2,0xc50c93232e0c59c98966,0xd42c64c8a70687dc316c,0x9a855b6c49e6c5b31438,0x921afa724524c8d60f43,0x7ac5053c855e4544c927,0x846434d1040f305c9f0c,0x1322d8a14e61d126833c,0xc73343ed431d7915791,0x91af5087a0a25b48e575,0x1f74863b88aa64664319,0xb381ef50b2c33c859a43,0x785e18f628556c31b381,0x81448cc8c02b8626b7cc,0x3842af2224c8e6050d79,0x621ea21d911d4c8e7284,0x818e78c874a4731c8758,0x6471e447623dc854843e,0x20d04e88c9d1220240ab,0x1887a42ac89bd898e299,0xf089016fd218d01b1156,0x629d21729820090bad8e,0x66a13c034057b843ef2,0x428658588b2d883d6286,0x3ec18b2f086b413591af,0x88dc0826e0acf08c2f84],#[0x594cb1c9422f22d8d3c1,0xd38c7872865a42c65b6c,0xf6c32750d60686b85436,0x435cd08a64745b12dba1,0xe10e6ca19e116dc21c9d,0x10ef0869816c6b374355,0xd0c3b62a2d8a2ee87d83,0x8745b1516c5be0431c8,0x89e05b1b7a718e7085bb,0x639c21760c47844bd608,0x2d8d66e871b0b8093db0,0xc717743ec18abb60c790,0x988b12b1f60c4e022e06,0x194143282865051c230e,0x8ad9154324b645283486,0xe11005a3b12fd2889995,0x21ecb3d107910e63c219,0xa14a0b016fc85bf216c4,0x8a149426d58aac306864,0x1d601635a0d43245ca14,0x51a631d74c636d844f7a,0xd8f18f232b1db647968,0x4a15b6476d91c6646000,0x23e606b00b1ee10a450a,0xcc2c45e988e110d6841e,0xf1086b422c8b550ac323,0x1a958a4a130160235a16,0x1bc2475613c22cc2c4b4,0x14a087c62404c06ac356,0x21818d314708e6a84dc3,0xadb1ce50a3906310be11,0x1c21b69c633e3236d869],#[0x35702bd422991aff0439,0xbf0a1c690c6a07a1ce14,0xa5430a96c73850f66287,0xde10c2f429ba15538c63,0x7d0d40f431c8d0fb0621,0x28a07a26f810c72343c3,0x84c04beec22516c56c18,0xc18a3847bf0430bd0a72,0xc244b9a189e10e39063e,0x8614db064406b4c633cb,0xb16f0851991ad610d2e6,0xb43378460e06be3c91be,0x63a489604b80d38312e7,0x467c11cbd828e8c49ef2,0x70e7ef08a80bc03406c6,0xec504cdd88e224ef6240,0x2bc225cd09a3c63cc6c5,0x3e6ec5484b323bc22934,0x3f00c9c23cd87682be84,0xe610f4f8431e021cacc1,0xc2100401007708558314,0xd431e421a02ab60c6016,0xc8a10f210ee08ea962d8,0xc71c23df3087bc428e11,0x15a44648a1820980c69c,0xf810f7410c7fac111b6b,0x27806c0480af088fc11e,0x1ca0878c5b1486711072,0xec87318871e6237038e1,0x1b]]
def g237H7 := limbs80 #[#[0x205020003010a020000,0xd0402000f05010b0702,0x30a0300010501040002,0x9120004070e0f010200,0x4010006000902080c01,0x110500000a0404000504,0x401000d030300010201,0x3020e00000205090218,0x30000080a000a02,0x61708081001000a0c00,0x3010e0006000e000d00,0x5020005010901060101,0xc13020701040f00091d,0x10501010001030f0d1b,0x50106000f0306070e02,0xa070a02060002000601,0x312040f013700000000,0xc01071e000100000412,0x1202030000000c080301,0x1500010003030900013f,0x7040203,0x7050a001200030a0600,0x9090502470201030102,0x103030402000100021b,0x905020e010100021320,0x2020b01150302000100,0xb010910020001050104,0x3020009010c010c0505,0xe0f0306060704011f00,0x1010004090b17022501,0x30000060800002d0005,0x705080a07060601],#[0x501110a0000180800,0x32d0d02031d13000600,0x1401010020042f01040c,0x40f0500000a19040d00,0xf0b020d0a00050c0b0e,0x2b0d020e000001040001,0x100050102000301000c,0x8160518000c01020f00,0xb0504000406110a1b00,0x93300070109091100,0x121200020e0c021d0a01,0x20a0012010108000a0a,0x9b061243060000070203,0x703080c07010005030d,0x111050723000d060729,0x3011406090c0c010003,0x3a00000000203f20208,0x8040dd21100e7400001,0x2063b08b0086dc447b05,0x0,0x31800010567013800a08,0xb182880000025e021dc0,0xc02940a5511a280b,0x1d831900006045f0074,0xe00000000081bb401960,0x22d8000101728029ca1,0x2130422802e783d70000,0xd00000000206c991959,0x882678c67009b0000183,0x81511b51cdd80000511,0x9f6064b009a485b80146,0x4891a04f28345000060],#[0xe4e0de403850148000,0xd4434080c000188d8,0x5c9cc079d009e0,0x8c6bc04c400,0x8703cb406d8000,0x1b18720350,0xc41b7c02e80000000000,0x37500000063f739202f,0x24c000000000000220e8,0xc0000190d61447800012,0x80000000000008195607,0x139460074,0xc00680000044a00000,0x959c071505b173b000,0x2d49aed000000000000,0xc9d034188af417266427,0x2c0e01230881eb000060,0x816d80491010b03a181e,0x1d00000408c001a983d6,0x920000608fe071706b48,0x45a224d340,0x22e901bb89a2805580ff,0xb0c0607060c889042118,0x70000001bb64a0000040,0x33301f0000000001120,0x681821e0000000000000,0x1905a80f40000000000,0x180380000000,0x202840000412b,0x14519300000000000000,0xf0106c0d2ec93c03a492,0x4d400004203a0043228],#[0x301e4204380dcc6564,0x6af6c00000000000000,0x615a40d4c054a0000000,0x2d20000406d47283385b,0x36803300000000000008,0x200c5126a00003222e06,0x303034f205e00004ecf,0x8b044b50363297d41e90,0x40,0x91121cff446d00000000,0x5d241275038000022125,0x42042b81b70000000020,0x9f301cb03df188dc01,0x40a1400000000c02b,0xe64da4c6415035103770,0x494000c9331b900,0x18a834a000000000000,0x355160000000000003,0x380003101a0000000000,0x10dd0544a16f408,0x2d0000040a4a21420000,0xe000000000000000009,0xa68000006,0x6700000000,0x409f800000000e5e20,0xf01a580002008b029900,0x81d841326031e20ad839,0x40200000000000000000,0x103ca00000553e63350,0xc4350078c0000c1fb000,0x1c6044080001905901c3,0x4059546b400004],#[0x6000040fa800b401ee00,0x19055000000f9906f,0xb2831a4098e822464f60,0x420248004681c8000040,0x9c9f40ab1466e203f813,0x15b6e08db04f4821f,0xd60000944b0000104c60,0xc00000000c143c024704,0x50e016d31b000544074,0x458000024fe10fec12c8,0x6a22b50fa000001,0x8ed8211000022562000,0x17d838b0153000000001,0x9743de088940bf4a2350,0x807e32304abfd000020f,0x1dba06ee05ea00000065,0x5880cec067002898303c,0xc00fc0784817620,0x2575ca4c093c000,0x92f071ba1a8002fa0b08,0xa08b7546f8925cc87520,0x20b6400018893c82,0x2100000000000000000,0x11269000000000015b8,0xb030f811f00000000000,0x8556635c818541d1610b,0x1d602ff2504000000000,0xb01f8c0adf73c903de41,0xa35c000000000562f08a,0x24a5e87b1355e,0x9c06a3211c0000525300,0x1217c0000c1f1c0a],#[0xbb8000160a40209c0b3,0x485700000000003c18,0x4810d40af00401085400,0x18103519400003032,0x3900001814090d5c2290,0xa0000306ba000015b940,0x203cc0000811,0x413b60ef0134082ff,0x7290c7805ea0ffe21720,0x4000198c180596228d25,0x34b04932340019da013,0x34c0e2a06cc000000000,0x4a000000000033a80,0xd9801380eda2195833,0x294028201072255827ae,0x5c00012898000040c7d0,0xd50000111294c67803,0x23d0729002a0000,0x98000000d8b64b204390,0xf092391bf4809904dd00,0x1c3030b41cf000ff01c,0x514006481ed0000207fa,0x1c04fc04bc00000045e0,0xc230721ba32819,0x303c0c16b,0xd60000c8c90000002e20,0x199110552c114542,0xec0069e000080778000,0x890e,0x103a000,0x4d0af401dc0000000,0x102330000020a872b1],#[0x1837e00a9c49940,0x1242985f5800,0x3b0000,0x2045231ba00000,0xf0000060cac000000,0x4620000000000000000,0x409600c6817ceee06,0xd0004a05b810c2821a00,0x81054622f42d882c7803,0xa8b0000202e403470104,0x1e0404000060c50042f8,0x1027b007e0076823,0x264816960000819a0000,0x40a3c0000000040982,0x8483e60d9c0000000000,0x220d8051a6340224a132,0x83158405f0c9912b7,0xc431a80000cd17800000,0x23a4c02d40a,0x14ba08f0000000000000,0x209000001013d4,0x1990d000000790000000,0x1036d9c9f8e778000,0xb1945b190ee000044124,0xa06b2067e80ced89c00,0x5b80003219a01d601a,0x31000000001076588d3,0x9d83050188000004470a,0x40000a09a00003085004,0x229088f407118086220,0x20710000182fe48be8,0x9c09764f6c06d4000000],#[0x18be0017a428200d7017,0x278017d0000087c2056b,0x700001209dc21e800017,0xc23ca444c0000000000f,0x9480000030610894d13,0x4200000007b082400004,0x30430c87e00002077b11,0x2260000416240fae081,0x31724d80883c19464332,0x1057070ca16ed11164,0x103fd000,0x42840acc41b060bbab46,0x6c81b6814f0000208382,0x4be0000c0798000200,0x28812388000080330000,0x205b80000a0300c6de,0x30000000000000000000,0x108f,0x40200000000268b40000,0x20026394a0000000012,0xe24a4000102adc087800,0x4c88e02113e012c0014,0x60047c80000000003a6c,0xa0000003dc413b274d00,0x11e2121a80bb4475e12c,0xd800001008940078879f,0xbc496a00aa810a907d0c,0x10010a000019,0x133020400ca6351a0000,0x1a36244608000323548,0xa649d0301508c2241000,0x43000000013ad4c2c08b],#[0x2e00d13377c000000006,0x91afe113f73618265dc,0x82b200000000100de000,0x685b9e1c0ef000011854,0x28255800008221000011,0x223d4406c00009022e11,0x40f3050200000000,0x3b00000084c000000000,0x10c412d4635804de84,0xa139c1ecc0470000,0x5a65020000048470809c,0xc0c8a832cb8054809920,0x90b8c81541237a04851b,0x2aa40fda08ed8139015a,0x10000000006641800018,0x30798000000002a1ec01,0x207e913da0000208e,0x601cf0273003700000,0x30000000004424000000,0xa0478c5fc4acf03d083f,0x7f200000000000030604,0x43229881800000000000,0xe0cc80001018a0176641,0x5ef052603cf402b,0x414832800000000a32b0,0xb28798150c0918055320,0x14560096cc8aa07a9133,0xe0a063400000c3e60812,0xfe03b400000000000020,0x49568000108520000847,0x3ee402510d5c06840000,0x62201300006445701070],#[0x2019839da82098000306,0xed00000090b800000093,0x20e6301c1801500004,0x880ef809dc20f6000000,0xa06602158415c000080c,0x355c982000000cd7062e,0xd4000001ce020d800031,0x404382219b07f0000205,0x130844f8021182100000,0x724001243f502de004e0,0x899a000046328037a80,0x3309872847a0cdb0000,0x4740c20000101b80003,0xbe495e7394280ac22840,0x8004c267921d0125418d,0xa240000649bf02b89994,0x252c0a30000107d18,0x2008020760000681cc00,0x2e001f2813b00005047,0x3c608f40000000042070,0xccd2800011118a87a41,0x407364c08432d0158000,0x4c0000041e2690900001,0x3c00000000816d640e52,0x4104000000000d89ce44,0x4440261301d8000091bd,0x725186a0ce203ae88b3c,0x298c9c1a30000227b3c8,0x59a494dc17c1085e03d,0xabb90c5ac0b30,0x600f0000083da000000,0x18000000000],#[0x23f00000000000018255,0x560000c16b404d800010,0x1114100000000184,0x85a704cd80b3a4c18000,0x5a8000211fb828388298,0xa483e800002188000080,0x82888131282ed43d5828,0x4cf30508064e87cd03b9,0x3f00bc18da8c61e41e72,0x210ca0374233f086ae42,0xc2ee633305a2119788cc,0xf8043f609d00000098d1,0x10885045380130143a80,0x1c06c1ca100000000,0xfe211fd01ad5199a09c0,0xa000000001828e81aba0,0x40896c16f80ed0428044,0x279808e8000000b1899b,0x90393800000000020c71,0xc14d8cc9321,0xb8000181ca40c40000,0x64203780118000000006,0x41,0x6e50f12c4000,0x9a341ac601200000,0xa400000000407f2090c0,0x40b41202a49c3c200a87,0x8298c201,0x84495920983377e83e90,0x181f6401600bb495de80,0x8196c0417055,0x11500e5c],#[0x18000207ef809c000000,0x446b80002213f00d0847,0x834d,0x102b9000044b4602960,0xc1f7a049800,0x2055680fd00000818,0x94426440000a145cc720,0xe8111c23400000b9bdc8,0x12b6,0x59204430000000000000,0xa9011a88d4009a90b220,0x4203a33620000419f206,0x22612f220240000080e6,0x560000000000001809f0,0xd9051c80800003008483,0x83b81620d5960cbe014,0xf2a000c03ba0084a01d0,0x7402bc00008090c1d9a0,0x7e8000082eb404,0x5d8456202c403a98219,0x34000050f90e75c00000,0x3209e0168c07f8038e21,0xf0a4084127000c32087,0x10800000000000006,0x7000020306408810e900,0x29f40b86438a117d896,0x5c6844d006ae02d20245,0x250a000040e0800030,0xe10840000000008fe000,0x684980001b854c092,0xc0362094d42c000000,0xd98d884800000054b000],#[0x5758994c067c0be9038,0x1,0x58000000720000000000,0x1c13800000001204c016,0xa8a00000624a004481d9,0x6890c07c82,0x720f40000c15f0000000,0xe73d235b009e80750232,0x10b20816000000002,0x2011360a400534000000,0x2ce40dc00000000103e,0x29e000025e3a0d787383,0x78000110b18023686b14,0xa0455034802325c9de0c,0x3049a0010e10c35c9e,0xa084d0ce6f0069903db1,0x79263d0fb80bc1643a82,0x2500000c44920eb6823,0x3bb000000001,0x246cd07da8216000000,0x4e816058a837a000,0x8f0c93d4058c00000000,0x885680061070b0,0x1809fa33ec88f8000000,0x22b401458227000e60a9,0x4230d43e880f1c0e06,0x7c0cd8000100da000000,0x4223d247408f,0x51407001b604a040000,0x32062504170223406130,0x8000107480000d4c3400,0x8680cd1600e200cd0202],#[0x2081b80000002a19b920,0x13aa000060cda04a302,0x113003ac847700059087,0x3739d125504ce0e717,0x6f300000018e5cdd00,0x48129002e0000000,0x8e4486f8000107a20000,0x9e80a5000020efc00008,0x2079c01a200002095021,0x438d06a0b94400000000,0x310035806ca8399015c4,0xc01ac08d4075e007f50,0x816b41cb000021014000,0x1112700a38000221cd,0xfc0690023e8c69a44680,0x60f56079a0000421fa0d,0x9b1c43b40000000008e7,0xbf40f662288000180410,0x80000000000001005702,0x41b908cb603e,0xc2a767f90d2000000000,0x8a00000234c0d0000,0xd0b5204b400000000000,0x3d0cc87200f901a682a3,0x92112048a06e4d6080d0,0xbfc027402,0xa242071ea32301d2e2d1,0x42fc000102bbc452e,0xf0000401f80000000000,0x206d000186ac7036508e,0x0,0x1800000000d19d000000],#[0xc83ec0001914b0000008,0x233443dd034e4024,0x75820a40bb8436a822f0,0x20174c11080185072482,0x752000050f580003069,0xabf0242a32fc87860962,0x4207550686817a8c85a0,0x89fe0f4f20d3c274d4c,0x360c217ae4ea004c0000,0x728313119ca090604fe0,0x908660361846440bf744,0x94000102050038622b,0x6060554000081ef800d2,0x2000000c0342e1835f0c,0xfa01860000207688b8,0x7ba000001be80efa232d,0xf47281b9d281b9c669a4,0x28b4803e201b00805800,0x45480002169000000000,0xf3801200000000083fa0,0x4000001c48000305df01,0xe13680002042,0x1076382c0811600000,0xcce5210320a008900200,0x901,0x42d000064a1000000000,0x2e7f605b08,0x80000b3db00000000000,0x30178a42180ab0301,0xa05f05450,0xf0000000010518816000,0x44e000024780000082d],#[0x0,0x4c00c802b00000000000,0x80000065c88ddc450a06,0x1213c00000924,0xc1f500002221400000,0x391a6000000000000000,0x41360000000040c84230,0x1870197000000003,0x78000000000000102b00,0xc84a60dc5864e998f416,0x20b8400010395,0xc9000000000000,0x40aee227800,0xc1280e40000808c8000,0xc4000000000000001a90,0xe4220603a000000000c1,0xa33b41ea4086b067801e,0x190e780808443a2201,0xaa07ea0000a13e800000,0xe0bdd0353111bd10a242,0x8870,0x3d000000744000083dd0,0x7205780ed80000056990,0x4232099f416f0e6ff111,0x6d600000000402a6,0x10489007c810c00,0x91bea09770000a893000,0x40001f3e634403fa01fc,0xcc6a84ad800008,0x5068f83abc1ad8000000,0x40a7,0xaf0083c0000014a0],#[0x7c84864ab8061f82f100,0x22b0936800022014815,0x5e583b980b3803d7236d,0xdc60a7a1e6000044abf0,0x806560100025c59b5807,0x8f58000100144025,0xf2c450000000001032c0,0xf206ec54f80000000181,0x11a5843a00000000002b,0x7340000000000000029c,0x305a883834108c0,0xc0c48000000000000000,0xbb0002c230204a188db,0xcf0271420b2854000011,0x80000000080d70000205,0x82c0000000080e188d4,0x18b12,0x20017815800,0x2074000040206318e000,0x1e5aa4dd1a4c03ad07b1,0x1a09c81c2000004,0x80000000001510000000,0x969000000000000a421a,0x40df6091606e88318c,0x81a1c114c03ec000000,0x10286404be0478000,0x10501111c01b180000,0x8d02680000ba04000000,0x839b0d3563080000421,0x3c8885d2067800000000,0x40e780ea308220,0xc0000000080180000000],#[0x164000008f600004470,0x3e81104000018c8c1bc0,0xa4ca2800002182000049,0x4061000030787006,0x4790152c12d804f3078e,0x1706729190406e0816a4,0x4103002f942d20000480,0x0,0x5bc87200003078000000,0xd82e6000050d3e0622a3,0x3218039180ff810f1032,0x231803b5420c00003,0x6a818c035f10eb000000,0x15ea41c922bd0427c94,0x74046f80cf5119800ca,0x28a11e0003a0c980000c,0xa0256024a00000000232,0x15510020081dc6088,0x8d8a60301ed024788778,0x9000040a70212a88c7c0,0x12170000001d40000801,0x1088b,0x3c1104831c847c000000,0xe28bc049a280918ab481,0x139a078f233200001915,0x20d108c042d06d283160,0xd0102e04ec6367036780,0x61c0000000020e06029,0xd67040fa897091c44948,0x64421800019295805760,0x206f80000c10,0x8107e0a35081e0000],#[0xbb04030808c23f107380,0x200fa0000c10dc007505,0x40f80001818280188000,0x6308840000083aac0416,0xc00000000217d800008c,0x827201168cce8211a81b,0x74780010000689030582,0x55040588b5e076e109b0,0x4801e0356106a0000402,0x845f033ea1f6c14b,0xbe0093ea22005c110c60,0xda98481aae444f084a11,0x14540000519e080cb01d,0x21202311a2e000000002,0xc8026c000003fbc17a42,0xc17d80002626e2046201,0x3ec00000000142bb02d3,0x1a34a00da0000000000,0x1100c00500000000,0x198c200000000,0x89b100000,0x40000000000000000000,0x816c817b0000000010b9,0x3ff4bc1415b463100000,0x9102f00000c023c20437,0x864400000835c5032108,0x21f40ba823bf3b3a8088,0x7800004e70e510e83e18,0xe841f81ff40633048580,0x40ca0000340c,0x41124,0x3378e0000000000],#[0x46e604680000b077000,0x2830000083d2088802f3,0x1,0xe01bec39c00002908c00,0x2180000a0758050a071,0x2e6be219c289101d3a,0x902120000247be014f00,0xaac0cd000030068900,0x144760b0c0001,0x44000000004453405300,0xa04a8018802e24157603,0x10f80e39407702e5102c,0x493bc49f803c402d59,0x882e800004072c000000,0x13129264002200001464,0x3e80001107748c3206fc,0xb800014664000040ada2,0x601e40000a889c09,0x20e4c0793a1e8,0x181dd00006029000000,0x1b08289845f8000000,0x471e4618990f8c850000,0x2469726a40000c1cd2,0x30000403680001819100,0x8322c02e000000001809,0x16a00000000000030036,0x36413209450000608de2,0x1067083400000000608,0x4bf809b621ae03f001b7,0x7e0000405b4000000001,0xcc5ca08e400b629,0x5af4bc5000000000000],#[0x8320805800001,0x0,0x41cdc464d46cc01a6000,0x33d810a0000232114099,0xd2000010aa0089355c5a,0x164a901994901c0c2504,0x22a203160000409a0688,0x1a0590031a0000893a6,0x85ceca0551027d88bc86,0x88aa80340112c0000836,0x3ffa065c12420a440247,0x80eb80764088000012,0x610d8000083ae0000000,0xfcb33214280c83c]]
def g237D8 := limbs80 #[#[0x88210541204405008010,0xfdebfbdbbb7af9fd4250,0x451611199185646fffed,0x99441651298c49631498,0x839888d6224984916120,0x20355941563055881b50,0xe140388c0e13038c80e0,0x88d56238940e15038900,0x5d94d56535d8cd56335d,0x265585a150684c1a3206,0x5611559595646558d956,0x522504854115651558c5,0x541d76545595176345d8,0x75591d56375589d56178,0x5255d855562255849565,0x156285586176257d495d,0x4825520558a556195596,0x9c80e52039d4c255309d,0x239d40e55039d00e5403,0x64239508e442398c8e53,0x8e75239948e55239148e,0x594e7533954ce6623958,0x69d45a55169505a66539,0x5469d4da55369d49a552,0x655319d44655119d51a5,0xc5253149d41255049d4c,0x9d452651495452451498,0x549d4d25534998525614,0x55279d45e55179995256,0x1e55479d4de55379d49e,0x585646159945655159d5,0x59949655259d85666159],#[0x9d896662595896462,0x9107d06605203c02800e,0xf0fd0ef0da0cc0b30a60,0x18a17916114e13c12310,0x121fc1ea1d61c51b41a2,0xa29428426e25a2422282,0x31f3072f52e52d82bf2a,0x9d38b37936c35a342334,0xe4114013f43db3c43ad3,0x49c48847646645143541,0x4952b5174f94de4c44b4,0xe5d25b359e58957455d5,0x68666e65463861f6085e,0x4872d70c6f36dd6c06a7,0xb7e77c97b27937777597,0x89b88886b85083181b7f,0x4292e9199018eb8d58bb,0xe9f79d69bd9a49819689,0xaa8a92a73a5ba3ca21a0,0x7eb5cb42b1aaffadeac8,0xdc16bfdbe7bc7bb6b95b,0x22a900054a44910c46c2,0x6521088b1208226840a,0x1c6993030b96088e186,0xdb242cc24bf660958048,0xc0a5984872ec90b3092c,0xf38148053e91132010f9,0x3e89132ea21bd2084029,0x5f80679704b530923c23,0x15e808c6053f010f5c09,0x5bfa092fe8243b015fa0,0x410efc88e63811348e04],#[0x8225c8896f90244806df,0xfb8221e846b00ac035f4,0xb8890ff08901053af02a,0x2048900cf8823e208804,0xac035f48225fe2243f,0x20a7ce284d7f8891806b,0xf224bf02352419a411f9,0xf7f388944f7045480633,0x772fc0935e1125f2e044,0xfc0497e02439c04b3888,0x6318114f3ca213df8092,0x73fd9031ce02537c0098,0xa4fc009697c22603b7a2,0x733a27a7e11290394e8,0x78dd04295f40221fc048,0x2c1ea408cb6048dc484f,0xf5c9096f1982142fb402,0xdcef04145e1125f2e044,0x5efa2630bdf44f72412,0x5e378214564243f8c213,0x40cdf882b6a20f1b9213,0x9a134adfc016dc2487f6,0x252e5369a533f60442e2,0x35cc3484a07d00894fc2,0x2427bf3844afc410dd98,0x416f9581141b92129c99,0xe8a2e4825b9de08286fc,0xa76e03c34b93d13185c9,0xb094fee014286f83821f,0x3111483818fc38584e70,0x64c895f6920eda483df2,0xd2418f6f20c]]
def g237H8 := limbs80 #[#[0x36008000c1a000a00816,0xe050293c0000130d81e,0x3402091b8043a0201804,0x48101010118082a2d000,0x403008c8350888cd0050,0x20000000020600800460,0x4006e80c1a430086c0,0x482800100002a020406,0x2c42002f00c1e2f18,0x1058000206022b83809,0x2540b09078110001002,0x241a220380002051d818,0x1004ca0107804e63d018,0x503070aa120000032000,0x2010201409000b03e0,0x4f600030082c00098000,0x18b00f0081c40b01980,0x13014020a0409c0e0404,0x9068040016020299600,0xa9f0081c7820000b936,0x38000d218180e0000828,0x304c8a32008248c10052,0x251d81a060d80c20110,0xe07009403c0c01048380,0x2c87078d400cb1b8080,0x83c520f0b0e800104c80,0xd94c20121800816a012,0x58600e2900808325c,0xe15189584c950887800,0x7c9401198045062180ec,0x1810021b1e804007c059,0x10501056ca921a0b8651],#[0x41b0f01c023500854580,0x80e1d17b248c12331481,0x810140000b48019c1803,0x60a0004d0581034ae01,0xe1a04c844e239a4a600,0x8205c010649b1280400,0x203e00008443a2204010,0xb050600380486260a8,0x10350047203c44220,0x233002c403a12609a034,0x146000003a5018a0000,0x85ed82c13b2a82388afb,0x860308601340805a0001,0x80dfa88610f02493bb88,0xcc11af403000000a22e,0x181199430a84b13e6,0x85e609e4020b8ae80642,0x31c808e0541a1e5,0x38a8219a83ac0001016c,0x299e013481aa81291a4d,0x122d3d8549008d0512,0x26a855a0000bb7bb8a7,0x416000d017502f00001,0xcc58556a4e110720000,0xc3ad1704ac43a624cc,0x2958b5152504827a203d,0x94100d3c2deebb710afc,0x5e4bb6a02d581e71968,0x8343853f04c880fd819a,0x84c2860a351321b08b49,0x84fd055d830c4a448328,0x912b130c860400000001],#[0x569985743b684ba03f6,0x29c0000850e02f40000,0x832e089c0357b402,0x23f21a200013b2403ba,0x80fa38a4012f81be0065,0x1802381ce90878464,0x83348475a5d8,0x34084ee935c8846,0x811b039e01eb063c0000,0xc4de000004be0001ba0b,0x42020d00000,0x85b885c0000144a382de,0x1a8366000025010b56,0x1df811633a710990ae3,0x80aa00000000854c0b55,0x4b581e112e185370bfe,0x8566025600000099,0x859200420df0841292d8,0x1e5ba843501858522be,0x26ea1ed8adb81fe80b8,0x931a0000088e034b83c7,0xe1192c703f51d7a033e,0xa19d24e4000121ce28e2,0x24c29d7d804f00ee05a1,0x10790399acbc000183b1,0x85c8828f236185c581d7,0xc8039304591303a1c5,0x4b30a728dee00000000,0x93b209dd024800011c6e,0x217f80480000142080b7,0x823a0000000181408267,0x2be80ca824c818e1063],#[0x4e5038c047caa03,0x84f2934b83650461801c,0x809d020603ce016323ba,0x83e6443a84a78a82054b,0x1091a0668cc60b520597,0x36ca18103ed00e894eb,0xb8ada45502e58115003d,0x102948449aa3e,0x2ef053d843c00009c70,0x826da10482cf8347,0x104885cc000082b9a396,0x101a80000a1e1a5e6,0x8b5802e7833d84060000,0x8889b5ca1a71535bd18,0x3fc000001ac013a83d4,0xb020000000102ff85c3,0xd80b1e9d5681cb82f9,0xad1b015a000090a8902a,0x303603b4042f806002cc,0x9c4b821780660561203b,0x2b484d880d200019016,0x831b02d9a2c420cf141f,0x93a70cbf84bc04940000,0xc2ea4b885e18646908d,0x124847305250aed,0x24af089bbb8e020001a0,0x36a82c3832000a429fd,0x4545846204b022b92841,0xac1d8251050182a8,0x129ff0156017d8326,0xf983100492000194c8,0xa09600000000000101fc],#[0x3c0013613289053931f,0x1985aaa7103e1,0x825800011ae9850c0000,0x8383063f83af857c14e7,0x85820ade09e28ad602ca,0x1480a710b4784249b4b,0x183528d42046e035a,0x8498853a906aa4e2a27e,0x6410281022701b60001,0xdc8000912ce806885d6,0x90a3034484b681908096,0xa214863ac1e9860c80c6,0x484134fa42484cd20c5,0x4e228480adda568944e,0x812a862221af83f092cc,0xed84d7045185fac4cf,0x4a48c1c2316000e4c7b,0x81b401d482dc849101ef,0x57181f5bbdc040a80ba,0x839138bd137b841808e5,0x1b0e8e18032380812107,0xe34d88048b94a934de,0x3e983770434284482fb,0x9870843b04b9811d0611,0xaf6140e05ee861f0131,0x4fa826085a680378332,0x80040894829000d6007b,0x917106ebbd70284a610,0x8123925e102f20c29047,0x105b887580314b42806a,0x35182567a6068113032c,0x83c292b7b3fdbad2],#[0x83bf091b886a22088ad4,0x9da05f2b8af062800fe,0x807cc3d33b6f028c0001,0x82e984ae00012c9404ec,0x24ce93d21593016a84dc,0x82720302027e037b109c,0x840f002783a884d48389,0x85d121f7823382a581b2,0x8575235b813e0627bb27,0x2c5c13e48e0e833aa27c,0x104f983f292cb0092,0x10476000123ed802c,0x829f00f493db059e0000,0xb10243004b92e80000,0x83fa10c701c383bcb3d2,0x8a1a0000c4d0000084f4,0x8879d4610fb22c20dc4,0x4c704d2bb6c925c0487,0x51e92a9014e843e8165,0x214313bd04d184548559,0x1a52000011c378479,0x8054112c847a00000c2a,0xa1d59c3d04080af40361,0x1202cbbc905108440,0x2da84e600520000,0x103b713640000,0x856f830a821582e1044e,0x1369827193f785140000,0x82b68dd2000014132c01,0x203085a5062a00010316,0x44cd2ad800000001ab44,0x1342884aa453a1b3a2b7],#[0x14a6885d039b22c9a18b,0x38c022cb8bd8b2038b66,0x63804808aea21e785af,0x56820305958bb121c8,0x191f9091f218c832b,0x44a037d13210d18842c,0x822b8d3f944200018106,0x42a940388ed824a0c9f,0x13c5006da90c015d0562,0xa3b7830e80bd8649884f,0xbbb40aee827921a8825a,0x84ca818900210235a0c8,0xb0a1035c0000a6148359,0x20d58274944400018bd3,0x81580dd494a4839620d6,0x14ab8ab24a42914845b,0x44d280ae000185238863,0x22003c80001841a0000,0x934504439aef02c60362,0x20c91ef80a601f68a20,0x83f9085981c980d10378,0x8433046b22c7134d003f,0x8d9d06311406017b2d19,0x8528b2f3890c802f8198,0x936e81e33b7d8b050527,0x22cc031f13b08039252f,0x81c093a8a19215a7a8e7,0x82d2807f9b08058c8372,0x1a20ea0bb0229,0x404d82b3018004220000,0x943f34cc05d323cc0914,0x4fe8dc7885781770063],#[0x2bfe8371051d85f704db,0x23ce938a0000932e207e,0x185a328e9a2bab4a0,0x8297838f01020e220000,0x8502a8e4136b82558552,0x100be2135a4981858,0x122b021124ab84389598,0x5de220a83da1103955b,0x14198da505fd21c60001,0x577809e12d3013c01d0,0x16925038167885b82ac,0x857391eb0dc20001909f,0x30682c82c68000083e5,0x12fd017180cc00000001,0x95833703e200004504,0x8a198b4c01b189cd810c,0x5be0132130b80240411,0x3a20645022fad749308,0x842914fcbb76064b84c1,0x8071b51a81ae1bd80001,0x8cc2000a000001508121,0x13b784a00600249f,0x181a7848c15940016,0x3040000bbae0001aa18,0x808a1b0b02221cc21923,0x1aeb104a954c0338185d,0x618023da565c5a20001,0x819524a9856b8ba70624,0x180460000852b,0x986e00000110000102ea,0xa0d24c73807400012c8c,0x23c905dba1ca9027001e],#[0x5ac0044105984aa,0xa3940000000001600000,0x1d80000000110e80001,0x12c200001bb1810b8085,0x61ba04c000000000001,0x1a5052d804d8b4a,0x81a30348019f9860850a,0x91f785c690441001105c,0x132b0019a39d85bd80d5,0xbbaa8de2000080280230,0x5348033018680e005b6,0x88e22b410318a48e82e3,0x861c9aec00018e09b032,0x41e00008b0000000001,0xa846000000000001a4a7,0xadff02ba0001886c81ec,0x821a0471b8360dff80a0,0x8ad2000000000000,0x1c338193824f0427049e,0xa39a000000019035059c,0xc4c5988402954901e8,0xf2000000c082532d1f,0x103950af929da04a2,0x1a53813d8017f9122,0x45d81b9044c112581f2,0xa530021314f89c2d4d81,0x80b583b285b2143738cc,0x84a8828692ee00000000,0x181c7b8be051baadb,0x101dd13c8885e,0x84458dae01f923ea0000,0x57805f40001a5b40001],#[0x93fa000005f18509,0x85473b84056c0050,0x1814481bc0000820e,0x8b1c0000000000010314,0x82af857e841c821800b3,0x9d400000239902a18384,0x8324046d03fe10f9bbac,0x100e40001818d44e4,0x2518000012b000000000,0x848980dd012783eb0599,0x235f015e83df852f8507,0x8078805f93d592eb03d2,0x415a19503d0336992ed,0x24405ea018538b2839d,0x38b0104f800390411311,0x830980148632a48a862e,0x93c683b8000183c50504,0x836f054321d2b8a1bb72,0x24fcb36a014210640001,0x203f01da044702090cbc,0x903e8afe00000001848f,0x851701f1849a80911350,0x2d10246943da60c140c,0x10825d0153802b1ca5,0x2aa81cd25243b29,0xa8ef2004000082d724de,0x1a1a4000182688088,0x108b827c20a200010436,0x12f1046881d28c2db325,0x8288140b858081978554,0x1c48034862d840d202a,0x2630105b8b600004b2f],#[0x2038000025f784f70b44,0x106184c40ae112da00f6,0x28a0000a90913af010e,0x210f807710939b0605d8,0x28290f7245a0d4082a3,0x85398d9b059a00008087,0x852003ef01fa0533060e,0x5ce806e849690338276,0x840084f1a0ca8551855e,0x91f402a604668621847e,0x59092bb00da82f743c4,0x8ad8858ea27a805d84ce,0x37e8637057a260f2bfa,0x85dd24d10851061782f3,0x37544e105b48609,0x804120b8843185fea082,0x80a8239e13fd06140204,0x4ea012c000111f0,0x35f825e0000138c8854,0x2c61249d02b100ac0001,0x21ea826480a205f8,0x800000019c1f954602ec,0x811f92d1b08a00000000,0x8b7d005903cd816fc554,0x85bba2c1834f85440001,0x85e380732dc3045604e0,0x80f00867a2302c8992e3,0x22338612403f0354b51d,0x80cea0cd03aac0f9a5a9,0x106803d9b1fdac1a0000,0x930488528634838180eb,0x93b980e6854e14502c29],#[0x8154045e2278a1bf0237,0x387901224ac848224d7,0x38a85d43201000782bd,0x864d0848a8e00606029b,0x4df1d8703dd14d69af7,0x809b8588813982259b0c,0x4d7f959712fa0518bb2d,0xad9b104d91f283310404,0x2fc3b8a03a7c4480240,0x5a80312029841ec058b,0x85cb05e8022c821f0369,0x82856401731c79ad6c,0x8c1a85aa888b84e8a2bd,0x8531231383ca05b00001,0x834c000194040293849d,0x1817981820c28021c,0x959c0000bb8104520000,0x8586a007019da4c8014c,0x8100086410101089003a,0x810901bb83d600000001]]
def g237D9 := limbs80 #[#[0x284409004108220087f,0x42ba39a1189006a1282a,0x82488a20610204c43bcb,0x801000096003a00129a8,0x900180012000900085,0xc0]]
def g237H9 := limbs80 #[#[0x3404060880801c3005,0x1030420800403450412,0x10100159a00404c4400c,0x800015815002803c0080,0x21e72d30001821033030,0x9132740020043441c10c,0x9506d901621444f1007c,0x80009d40000c95303695,0x26340a0000816701950a,0x68199217e509f1820001,0x9000313900012451d4b4,0x85c085275119212,0x9912000000000002181,0x55e000200f00030318,0x4420000000311c00,0x0,0x135994000845c0004114,0x520000000203880d00,0x407400,0x2530001009000124f,0x5d048000000000000000,0x12130002252557c000c0,0xc90404d0000000000,0x2a45f506101280000000,0x547f4500964001444f0,0x406000091c4000d13c00,0x20903245240000002051,0xb117fd0e475c00010664,0x304c8124000842c000c9,0x210000009,0x5c81a800000020520000,0xcc104000819d02711484],#[0x302c0000075c92117,0x24670000000000124a,0x220d000321200001830,0xc000a1a474b417701000,0x5d372174157073c1a,0x8000ba05a90b145d5d74,0x196091a721590a50,0x41c237a418c000000000,0x206f81080000000000,0x78000000000080700000,0xd136000301f004874001,0x812c000c00,0x1aa58400000200000000,0xbc034000c05685a00010,0x200b0000000c47f37,0x800081c800084b4000,0x240400000008,0x8011015a0545d0604600,0x11686100000000000c1f,0x5bc079211000067041ef,0x3c4ef05f000301b00038,0xc94727d491807180cd04,0x1100160001751000007d,0xfc360000000001fe97ac,0x776c1415780d1d04f00,0x3e010202b5110000000,0x3b817000059c57830615,0x7c9400000000000c0810,0x146826a919400041de24,0x4e800081d00290003466,0x136104a826b1d3b97b8,0x9777d046579818216609],#[0x53d1c00000003135597,0x4b80dc00000000004469,0x2874061f21800f72,0x41e000000000eb44,0x1e100004fc41059e0000,0xf106e000300e00000860,0x22c16100a884316700,0x2160000000c18b1865d3,0x267991d80000003,0xd803054244bc00041900,0x204000011c000110526,0x14510001004,0x6b180000387500e40690,0x2087997c00049,0xd20c0000001555000,0x347700000000000,0x1543000101400000,0x886400044fb079c08c00,0x115c20c0000003025,0xe1f400011160570,0x110981a1006444b02f00,0x10a55c024e955a25b159,0x2d9d3e571c13b13781d9,0xc0c300581b000000010,0xc4e0249000007c019400,0x98873900025128d64000,0x6c00000000000000000c,0x303581e8000c1]]
def g237D10 (j : Nat) := if j=0 then 0x3f else 0
def g237H10 := limbs80 #[#[0xa94398840022420c9061,0x9000a988b33110928094,0x910b000e2924cbaaee59,0x3e0a014a104085380a28,0x143062004060062b3,0x38d2a94d044cc4000280,0xa8000000023d04000131,0x4200070e24c2249001b,0x100009869148000004c0,0xa2460086b99e0ca40009,0x1a360e00000144612]]
def g237L : Nat → Packing
  | 4 => (2,6,5,0,0,3,0,g237D4)
  | 5 => (194,5,5,5636253,120,11,1043,g237D5)
  | 6 => (1106,4,5,6029749,121,14,1095,g237D6)
  | 7 => (807,3,5,2293865,103,14,1085,g237D7)
  | 8 => (136,2,5,655370,68,12,1056,g237D8)
  | 9 => (10,1,5,65537,0,8,1035,g237D9)
  | 10 => (1,0,5,0,0,0,0,g237D10)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupShort 1 2 0 3 1 0 g237H5
  | 6 => lookupShort 84 461 6 14 8 4 g237H6
  | 7 => lookupShort 480 2851 8 17 11 4 g237H7
  | 8 => lookupShort 361 1657 9 16 10 4 g237H8
  | 9 => lookupShort 76 491 6 14 8 4 g237H9
  | 10 => lookupShort 15 79 5 10 4 4 g237H10
  | _ => fun _ => none
def g237 : Forest := ⟨237,10,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P4_0 : block g237 4 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B4 : block g237 4 0 2=true := g237P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 194=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 194=true := g237P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_2 : block g237 6 2 52=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_54 : block g237 6 54 512=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_566 : block g237 6 566 512=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_1078 : block g237 6 1078 28=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 1106=true := (@block_merge g237 6 0 54 1052 (@block_merge g237 6 0 2 52 g237P6_0 g237P6_2) (@block_merge g237 6 54 512 540 g237P6_54 (@block_merge g237 6 566 512 28 g237P6_566 g237P6_1078)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_7 : block g237 7 7 333=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_340 : block g237 7 340 467=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 807=true := (@block_merge g237 7 0 7 800 g237P7_0 (@block_merge g237 7 7 333 467 g237P7_7 g237P7_340))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_13 : block g237 8 13 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_64 : block g237 8 64 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 136=true := (@block_merge g237 8 0 13 123 g237P8_0 (@block_merge g237 8 13 51 72 g237P8_13 g237P8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 10=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P10_0 : block g237 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B10 : block g237 10 0 1=true := g237P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 10 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g237B4
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
  · exact g237B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 11 := lower_forest (g:=g237) (i:=0) (hints:=33555715) (before_sound K235 V235) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K235 11 [(237,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V235 low237 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffffffc03fffff0063,0xcc9bf88108003f000fc0])),(BitVec.ofNat 152 (word80 [0x514144898902822622,0x4c99e801085145145145]))),((BitVec.ofNat 152 (word80 [0x1fffffc03fffff3c,0x588a27543c000003f03f])),(BitVec.ofNat 152 (word80 [0x618981111193044434,0x580a2510394514514514]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe00000003fffffbc,0xa08cda0be40000fc003f])),(BitVec.ofNat 152 (word80 [0x21016020220280008,0x8084d20bc638e38e38e3]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000081,0x4f0597e4d00fc003ffc0])),(BitVec.ofNat 152 (word80 [0x840218000004300881,0x30412c440a28a28a28a]))),((BitVec.ofNat 152 (word80 [0x91,0x75782c5b43f000fc0000])),(BitVec.ofNat 152 (word80 [0xf803e01c1c07c07091,0x75582c4000c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x4e,0x937660389bffff000000])),(BitVec.ofNat 152 (word80 [0x1c0020203800804c,0x80220038930c30c30c30]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(2,0,241,0,7),(64,0,179,0,7),(0,16,161,66,6),(16,0,227,0,6),(32,0,211,0,5),(128,0,115,0,5)]
def g243A : List (List Nat) := [[],[97,117]]
def g243D5 (j : Nat) := if j=0 then 0x4fb7059653 else 0
def g243D6 := limbs80 #[#[0xed8153bd58453be58053,0x59653fed8153d7d4e53b,0x401413142f3185b400bf,0x1002628]]
def g243H6 (j : Nat) := if j=0 then 0x8 else 0
def g243D7 := limbs80 #[#[0x47888807f94ffaa7fc53,0x6a1474365a981d90ea61,0x190e]]
def g243H7 := limbs80 #[#[0x23880000000001024029,0x1400100000]]
def g243D8 (j : Nat) := if j=0 then 0x468817f else 0
def g243H8 (j : Nat) := if j=0 then 0x98014e else 0
def g243L : Nat → Packing
  | 5 => (1,3,3,0,0,0,0,g243D5)
  | 6 => (6,2,3,0,0,6,0,g243D6)
  | 7 => (3,1,3,0,0,7,0,g243D7)
  | 8 => (1,0,3,0,0,0,0,g243D8)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g243H6
  | 7 => lookupShort 1 29 0 6 3 1 g243H7
  | 8 => lookupShort 1 7 0 5 2 1 g243H8
  | _ => fun _ => none
def g243 : Forest := ⟨243,8,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
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
theorem g243P6_0 : block g243 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_4 : block g243 6 4 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 6=true := (@block_merge g243 6 0 4 2 g243P6_0 g243P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 3=true := g243P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 1=true := g243P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 8 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 9 := lower_forest (g:=g243) (i:=0) (hints:=67174469) (before_sound K237 V237) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K237 9 [(243,[]),(250,[48,65,32,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V237 low243 (by decide +kernel)
def g246Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff83fffff208e8,0x1ef36c00000000003fff])),(BitVec.ofNat 152 (word80 [0x90a4810809040200a0,0x1ec16c52a54a952a54a9]))),((BitVec.ofNat 152 (word80 [0xffffc1ffe06f688,0x5ccc20003f80fffc000])),(BitVec.ofNat 152 (word80 [0x2c00a004008227088,0x50c40060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff000001ffffbd84e,0xb1211a000007f000007f])),(BitVec.ofNat 152 (word80 [0x3082c10905001d84e,0x2120128d1a3468d1a346]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x491ab301fc00001fff80])),(BitVec.ofNat 152 (word80 [0x240130000260480454,0x12932850a142850a14]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774fe0007ffe00000])),(BitVec.ofNat 152 (word80 [0x3801c0210380880611,0x8083243060c183060c18]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00e00421c01048902,0x7a4000c183060c183060]))),(0x0,0x0)]
def g246C : List ColumnInfo := [(2,0,244,0,7),(4,0,242,0,7),(16,0,230,0,7),(32,0,214,0,7),(64,0,182,0,7),(128,0,118,0,7),(0,2,196,48,6),(0,16,164,66,6),(2,16,164,64,5),(18,0,228,0,5),(32,2,196,16,5),(34,0,212,0,5),(64,16,164,2,5),(6,0,240,0,4),(20,0,226,0,4),(36,0,210,0,4),(48,0,196,0,4),(66,0,164,0,4),(66,16,164,0,4),(68,0,178,0,4),(130,0,116,0,4),(132,0,114,0,4),(160,0,86,0,4),(192,0,54,0,4)]
def g246A : List (List Nat) := [[],[114],[65,101],[65,114,101]]
def g246D5 := limbs80 #[#[0x50d514c7c55514354531,0x4c795d915354531b5585,0x1d771591318f7815d954,0x104085b546031d]]
def g246D6 := limbs80 #[#[0x50d31d9510d911055110,0x591315513154d3154531,0x54540d9531d913159531,0x5815150d51d854358543,0x7efb77b7d7e7f1fd8d51,0xa993ebe7eef577bbbdbe,0x2ba085750aee200dd4f4,0x96aa1354321ee8b8d896,0x478aa0f7711cec849590,0x90a9ba8d1751beca3759,0xdc4e5ba9d77138aec67d,0x15d523ba9db753b0ea79,0x1dd9c9b9bc57450ee88,0xb83c002bab4b7560ae9,0x713417caa4d1f0c85422,0x9ac35dacd509b47204f2,0x822b08803e1e0e76fb55,0x90e0403043c16773395c,0x381195900690130a869,0x280801d22d410000a420,0xc076833415a080000040,0x20080802020000,0x2ac20000c0580c5840]]
def g246H6 := limbs80 #[#[0x60000048000000001100,0x25c1000250092000008,0x1900]]
def g246D7 := limbs80 #[#[0xeed5150d404c53048110,0xceca0ec806c53fff7def,0xcec8cac8d2a6d286daa2,0x62a80ec34ec78ecacaca,0xe2c4e2a322a2a282a2a2,0xa287a2c1a2cae2c8e2a8,0x80d01a0026c362c362c7,0x6414e4334b5270861984,0xe729a96397a5a1525092,0xc3e6f966418a6097d1d,0x90c68008860954a28107,0x23083402f2c4464c2964,0x91422227064c51e02603,0x47a4645a5fc494a17203,0xbfb34270fec309978c1,0x4adf80392dc028f1425,0xbfb92113dff38009d4d8,0xe90bbc263be223eaf108,0x171ea2301fca44dca439,0x5235c3090dcc24af0620,0x6121396128e84a22fcb9,0xe068772]]
def g246H7 := limbs80 #[#[0x18a28bc2a44530020,0x8c3c43026e8414000000,0x4320c405a,0x8010249e86800000000,0x5800000018ee24028348,0x4219e139fc3a2e00001c,0x41c0023685c228ae0c0,0xfa138b78e000380020e0,0xa808e8021f906930,0x221c6a060]]
def g246D8 := limbs80 #[#[0xd31fea07f4c3fa41fd10,0x4210a830007f50ffaa3f,0xa16502422204a1e40e45,0x16592188818b1e584930,0xc39648a004a2650a1292,0x32071959238a01412473,0x1258602a230]]
def g246H8 := limbs80 #[#[0xb624800000a503b00440,0x190b02000000058c00d5,0xa00001ee216007209391,0x980198e7811878e00e50,0x30030a005cc34002ec06,0x60b4600000002000c,0x987a5044151589aac000,0x32f0f84800014e0055e1,0x71]]
def g246D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g246H9 := limbs80 #[#[0x26000000000000000235,0x8800000,0x25000003200000000,0x40000580c00000,0xd088a0000010b8f80]]
def g246L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g246D5)
  | 6 => (33,3,5,917521,69,9,1038,g246D6)
  | 7 => (26,2,5,327687,51,10,1064,g246D7)
  | 8 => (7,1,5,0,0,9,0,g246D8)
  | 9 => (1,0,5,0,0,0,0,g246D9)
  | _ => emptyPacking
def g246I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 2 37 0 7 3 2 g246H6
  | 7 => lookupShort 11 71 5 10 6 2 g246H7
  | 8 => lookupShort 11 67 4 9 5 2 g246H8
  | 9 => lookupShort 3 59 1 7 3 2 g246H9
  | _ => fun _ => none
def g246 : Forest := ⟨246,9,fun i => g246Y[i]?.getD (0,0),g246C,g246A,g246L,g246I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P5_0 : block g246 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B5 : block g246 5 0 5=true := g246P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_0 : block g246 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P6_2 : block g246 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B6 : block g246 6 0 33=true := (@block_merge g246 6 0 2 31 g246P6_0 g246P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_0 : block g246 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_1 : block g246 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P7_12 : block g246 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B7 : block g246 7 0 26=true := (@block_merge g246 7 0 1 25 g246P7_0 (@block_merge g246 7 1 11 14 g246P7_1 g246P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P8_0 : block g246 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B8 : block g246 8 0 7=true := g246P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246P9_0 : block g246 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g246B9 : block g246 9 0 1=true := g246P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246T : checkedTables g246 9 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g246B5
  · exact g246B6
  · exact g246B7
  · exact g246B8
  · exact g246B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g246G : graphValid g246 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low246 : Lower true (varsX 246) (graphGoal 246) 10 := lower_forest (g:=g246) (i:=0) (hints:=571540800) (before_sound K243 V243) g246G g246T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K246 := extendKnown K243 10 [(246,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V246 : Known true K246 := extend_ok (m:=246) V243 low246 (by decide +kernel)
def g127Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffb82290128b5bfaaa,0x81c33d000000001fc07f])),(BitVec.ofNat 152 (word80 [0xa282090128a49baaa,0x8180384a952a54a952a5]))),((BitVec.ofNat 152 (word80 [0xe496fb8690d322a,0x83ed80000000fe03f80])),(BitVec.ofNat 152 (word80 [0x330e406e38290d122a,0x1a50468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0x7da4e45e5005fb50,0x730a800003fff0000000])),(BitVec.ofNat 152 (word80 [0x5c1c24e41e4001eb10,0x730a801e3c78f1e3c78f]))),((BitVec.ofNat 152 (word80 [0xffd6d70c3e074a4d0d,0x44e78001fc000000007f])),(BitVec.ofNat 152 (word80 [0x6054d70c2c01024505,0x4067803468d1a3468d1a]))),((BitVec.ofNat 152 (word80 [0x4032db8fc2a26263,0xe2348efe000000003f80])),(BitVec.ofNat 152 (word80 [0x8040329187c2226041,0x62248c3870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x48a924e0bcb285c1,0x784475000007ffffc000])),(BitVec.ofNat 152 (word80 [0x408900c014b20441,0x84405a142850a142850]))),((BitVec.ofNat 152 (word80 [0x2754920534ad14b5,0x8f8813fffff800000000])),(BitVec.ofNat 152 (word80 [0x23000200348c10a0,0x8c8013c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g127C : List ColumnInfo := [(1,0,126,0,8),(2,0,125,0,8),(4,0,123,0,8),(8,0,119,0,8),(16,0,111,0,8),(9,0,118,0,7),(18,0,109,0,7),(32,0,95,0,7),(64,0,63,0,7),(0,1,86,40,6),(0,2,77,48,6),(0,8,54,65,6),(0,16,45,66,6),(1,8,54,64,5),(3,0,124,0,5),(5,0,122,0,5),(8,1,86,32,5),(12,0,115,0,5),(17,0,110,0,5),(20,0,107,0,5),(32,1,86,8,5),(32,2,77,16,5),(33,0,94,0,5),(34,0,93,0,5),(36,0,91,0,5),(64,8,54,1,5),(64,16,45,2,5),(68,0,59,0,5),(80,0,47,0,5),(37,0,90,0,4),(38,0,89,0,4),(40,1,86,0,4),(48,2,77,0,4),(65,0,54,0,4),(65,8,54,0,4),(66,16,45,0,4)]
def g127A : List (List Nat) := [[],[16,67],[48,65,101],[64,49,101]]
def g127D5 (j : Nat) := if j=0 then 0x306e98e1c8259465 else 0
def g127D6 := limbs80 #[#[0x59465609651948259465,0x441655c865e1d6519782,0x61b7154372d89505cb62,0xdcd60dcd6158187d9552,0x59585dd1605977358154,0x60372597725c1651c970,0x8fc7b61f64d418758b50,0xe67c3f86ecdd75ae74ee,0xcb962b70e26e1c1c6f39,0x243928872502658c1c91,0x92039261f24b4e4551c2,0x4c02b8703f304ae4881c,0x5c389f8710f2e17e1c2b,0xafc90dd9218b243ae5c5,0x7c9be78370530d9e0d,0xa2928272625242322212,0x5341311f0efeeed8c2b2,0x4e1585d5c5b5a595816d,0x985a128,0x290b0100000000000,0x80a02e02008000400]]
def g127H6 (j : Nat) := if j=0 then 0x0 else 0
def g127D7 := limbs80 #[#[0x58110541105c86559465,0x5d9105d5105c91059510,0x50920dd910dc910d8910,0x58120551205492054120,0x5d920595205912058520,0xdd120dc520d9520d8920,0xdc9405d5405954058140,0x5d950595505855055150,0xdc950dc550d9550d8950,0x995525d9525cd5259552,0x54960dc152d95529d952,0x59560589605856055160,0xdd160dcd60dc960dc560,0xdc965dc1655c1651c965,0x5d35058b50583505da65,0x59752d9350d8b505db50,0xd8b525db525cf525c352,0x97e1f5cb605976054b60,0xb7edeb6e7f9fa7d9ee77,0xcff3bc7efebf6fbbdeef,0xf6fbbe7f9bdfb7bddf5f,0xc1870f0a141c380ff3fa,0x9323025e1bb141b04285,0x17067c7c11f2702685c1,0x4987c13c2702ed1c2b9,0x4bc0413b0b0ecb2c31f,0xfc380b70402c41007aca,0x903dac20ddc302aee409,0x9330a24dc305a2e422bb,0x7041a5ba84670410cc30,0xa28cc10a37041cdc3063,0xebb88fd6c4334a10c330],#[0xb1165708419c110d2843,0x8d670a2d8c28b330c5a9,0x630a530b2946308532b2,0x4499c11196ea39bc08e,0x64cc29baee461ac09567,0xcc322570874dc11a6704,0x11e6f0270cc323a6e480,0x9aae2e4dc11f6b02859c,0xaecf4cc3ba8aeceaab93,0x4f28413c330ef8cc3bd8,0xccc1309ee6b4dc13ca70,0xb2b19ee6baeb2ab9ee6a,0xac9acaca6aa32330ac62,0x6704bccc2b33304ceeb2,0xeb12eb2c4c704bf0412f,0x17041458acb18cc3c492,0x9c124770094cc32ac705,0x1297300a52c327cf0491,0x87300a29c126330ea58c,0x7050b3c13fa6c5012c2a,0x4d683935bf0402ec100a,0xa839365f06d59c135a6e,0xc037650ed0cc136a6e4d,0x3704e284138a700de8,0xb614c2383705e09c0f8,0x260480880f81cc35863,0x708a0f01c43505e8b515,0xbe1742d8578a614024e4,0x9c636a6b4d299d32a610,0xa438851062013e0790e8,0xee9bd322584a08f51aa2,0xb015c2b0550a814aa8a4],#[0x5883035ecba16d2d0590,0xb5969ed1d9eb3164ac7,0xa8740e61c2b7d6e6dadb,0x818fe1f2bd679af11dbb,0x516a284488710b60f414,0xba4d48d90b1ea3946a8c,0x864fa9e538a6d4cd97d2,0x56aab753ea0d35a4f452,0x5b6f68ecad8db0b5f6ba,0xc20d50c010701052e85c,0x84480a86700080d8601e,0x1413410721f84c041006,0x20102cc4e270f83c0e37,0x613b0f0508c188110c1a,0x2c8675080000003b0e,0x8791000059080400000,0x614d24549141cc25005a,0x190afb19118080007b0e,0x19a100000056c211b1,0x90d72626023e42000000,0xa421b0800052158a11,0x25cd880290ea0804c843,0x280800000000000521a4,0x2100da0ed07683db0f6c,0x40401010040401013213,0xf586e1100002736200,0x80803783147c62270201,0x80800e213015702,0x7c45196c434100a42000,0x2e684001e44013417702,0x8c869229412d87662180,0xd89361000000008044c8],#[0x3014d86b4]]
def g127H7 := limbs80 #[#[0x40000069e40004898204,0x3a80e0025000147b3b2,0xd6d8d731bae000004100,0x30053239e201140000f0,0xf3403]]
def g127D8 := limbs80 #[#[0x59560549505012044065,0xfcfdfef777d8352d4265,0x6500dcdbfffefdfdfbfb,0x615013d96017381dc9cd,0xd4497512dc8497218580,0x8580a15022dd8497612d,0x427d889d52275088b712,0x97622dd4897522dd0897,0x4c97532dc8e16032dd88,0x5d90b7442dc90b7142dd,0x925ca4971985824b7642,0x7362dc98b71625da4974,0xcb7564d95916562dd19b,0xd6d165b25d2c972b25c6,0x5995556552dcd4b70525,0x3a7d8a8970a2dd949765,0x972025c00976a5596897,0x20b7277dc9dc7272dc1c,0x5484976825ce0972825c,0x29d94656519d88656219,0x6429550a76129584a551,0xe55239d94a56529d90a5,0x89276149585255149594,0x9d912564495512762495,0x499d8a656299d9525654,0x55469589a55269585a76,0x56565595cd6552b9595a,0xdc1e570799d9657659d9,0x704c0250009dc9e57279,0x1231080ed0d30b708d06,0xd91be1a218816e15513e,0xe27726424b2302171fe1],#[0x33f3273092e82ce2ae28,0xf53dc3bf3a038937035a,0xd49147845743e42740f3,0x5385235014ed4d64bf4a,0xf5e95ce5b259257054e,0x66c66a167e65e64c6326,0x7ab79476874371e6fc6d,0x5f84582e81c80a7e47d0,0x28ea8d48ba8a688b8748,0x98e97496194292a91390,0x2ca189fe9e69cc9b79a5,0xdac1aa9a88a70a58a42a,0xb82b66b52b31b1eb00ad,0x50914bfdbe7bd3bb1b95,0xa80421504010a0c07088,0x90e86874118480f02161,0x588032200461d0b44821,0xfc5408312c1c2c6451b0,0x117130d104320c4c3c01,0x91b19579847111e1c232,0xf88a3aedef44103ae0e0,0x63822987f79308532a32,0xd8126bec104fb1f0226e,0xbbf04b98c18cb3e11317,0x73b611557e2442ef8898,0x41127f601b88f9751114,0xae2269ad045217c92ad7,0xf9f86826bc831872620b,0xa0446d8f8112fb8048a1,0x222b79031af54b88abd6,0xc3410175c44684c206f8,0x64631e46922dfe012273],#[0xe258397c731bf8a60f1f,0xd70633ff006138e33111,0xc6fc21bc40a38c288b5,0x411ffd0a24f6e504bf81,0xa279f596411cdfa05075,0x33b949a36d52996fff02,0xb1498dcf02c54664f094,0x151a0f429af6912373c0,0xce1185579749d0a36b80,0x1627aef80210af690a31,0x7639a380abb1cd1effd8,0x46d2630bbbb3e962b015,0x40842b0658289fc08a15,0x4b3c29137a428c18abbc,0x871293ce24d8c219f0e8,0x6ba43272189a2e90cfb,0x9498e0fe124e10b42e91,0xfdae25a5848bf0161153,0x762583d12d7c4675e894,0x83e243f5e896696912cf,0x244b87a25af218cebe24,0x48858e0c73ac88a461d7,0x73e524599ac7108cb5eb,0x907190c30592ecabb90d,0x8d18016c9d2d883802d,0xca47dc4b1f78314cf78b,0x2]]
def g127H8 := limbs80 #[#[0x24c31030142104000,0x57031061115514104011,0x2e104102093005,0x32a00000,0xd6800000000000000000,0x667000000182150db1c9,0xf4915b15800000972bb,0x78000000590000000000,0x9c00066589194c000004,0x4c000001d6c00042c83,0x423001118006da00000,0x886594000008280000,0xf613c00000000000000,0x205edcd3bec00000,0xb4004760340000000000,0x271000000000000010,0x800c1100902e50416000,0x7e718db0a5d00183c30,0x7b8000000000000,0x4c000422000000000000,0x13e9b8055,0xb8000000000053500113,0xfa00000000000000fd90,0xbc9070000005c8002,0x82510800bf604c00000,0x11393e04700,0x4b5000000000000000,0x8004068ba2dde0000000,0xd4aa0c92b8d900000228,0x3310008311b80,0x0,0x1db00000000375800000],#[0x80000001240000000000,0x16dc87bb5001769d,0xefc00007000000000,0x4bb00000000000,0xda0000000339c,0x0,0x2ec8b9000000,0x40000000000000000000,0xd800000000280000007d,0x30b0000,0x1398000001a8d8e27000,0x77a00000273f5a6ee00,0x0,0x31c800000000000,0x69c000000018fc00000,0x9000000dda0000000000,0x1201e0011b9007599b79,0x10d000458415117,0x8ce80031d06000107c00,0xde001b00004cd8800023,0x7b0004ee001f9000e,0x91296d00159a1600052a,0x800cbe000000008528f,0xb692a00e00000006e0,0x0,0x620012b800000,0xecd627500004937a1900,0x1f740cdb8000004975,0x6cf7e80061d000000,0xf62d0001e60013d,0x1b27731040020880,0x8d913000953370000790],#[0x1,0xc5e00166be109a00,0x44000000000000000000,0x6a000e0800000000b44,0x1000000,0x3296283801ac0000000,0x2f000000061603b20000,0x23b75e000000004631e0,0x474003db0d000325,0x10800]]
def g127D9 := limbs80 #[#[0xb60583505414048110ff,0x422b1500995651975254,0x8407ecdcc1b096846b5a,0x78e3a18d158a082c2291,0x75e203840664f221248,0xd900cef300ee71021f90,0x803bee700ee003bff001,0x3ff300494033fc60091]]
def g127H9 := limbs80 #[#[0x51010141050001002,0x22011400100430100000,0x80f83d62d840400f0b71,0x430f,0xc00000000000000e84b8,0x10e4000004867b,0x1480000000000000,0x8d80046c0000030c8,0x65400000000000,0x2864bd8bc0000000,0x996b02d0000,0x5624aa0000000008a000,0xa6a00000000000002b4,0x168418000012d33800,0xa4e51001746ed0000,0x1e2ef6c0001c9264000,0x4060001800000084800,0x442cf0000000000000,0x640032d800001754000,0x30aec00910e800000,0x10680006f00,0x58c00000000cd00,0x2d30001778900049a000,0x900005800000c472cc00,0x1b90800634c580000024,0x57000033e220000,0x1263e2000,0x716b40000000000000,0xaf8006270000000,0x250,0x22b800,0x52b0000000000000],#[0x2670000000,0xdca00000000c188a8,0x1980009c00000,0x0,0x348a4187bfc3f40000,0x1f000000,0xd8000000000000000000,0x31d5528d02073b60000,0x238000354006,0x1ca298006cdaad35800,0x3ce000000dbd2c00000,0x2028000d20,0x7c002e972e000,0x7ad60022780000000000,0x12000000003a711c0006,0x640000000112bbc,0x800000000cb000425000,0xcbe000000000019b,0xc632aa00000000,0x56200102000000000000,0x1d6c0a00083018c0b800,0x553cb31a9d880000,0x104f043977e230004ac0,0x3d00000000894bccc074,0x1cc200000000001eac05,0x372e4000087a59b40076,0x42b3,0x25800c040038b800000,0xac2e0018400000000150,0x13000000004cd07e0011,0x531880040f6d88ec6fa,0x8000007d40000de0f0c4],#[0x90000000014aed9fb,0x802000007de0000,0x800001838005e6001940,0x29880000000142,0x3200000000000d7edf00,0x7,0x40000000000000000000,0xa74cc5194a9f00000178,0x82da]]
def g127D10 (j : Nat) := if j=0 then 0x430a1ff else 0
def g127H10 := limbs80 #[#[0xf100b6000000a40081,0xa58800c46700,0xc6d491e600eb0000,0x6056002300000000,0x920000a8000080f40021,0x54900c3007500,0x73004a00530000000000,0x55000000c24700000b,0x100]]
def g127L : Nat → Packing
  | 5 => (1,5,6,0,0,0,0,g127D5)
  | 6 => (28,4,6,720914,69,8,1029,g127D6)
  | 7 => (126,3,6,1835079,87,11,1065,g127D7)
  | 8 => (115,2,6,655372,68,12,1081,g127D8)
  | 9 => (12,1,6,65537,0,8,1045,g127D9)
  | 10 => (1,0,6,0,0,0,0,g127D10)
  | _ => emptyPacking
def g127I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 1 2 0 2 0 0 g127H6
  | 7 => lookupShort 7 47 3 7 5 0 g127H7
  | 8 => lookupShort 51 521 4 11 7 2 g127H8
  | 9 => lookupShort 50 509 4 11 7 2 g127H9
  | 10 => lookupShort 8 83 2 8 4 2 g127H10
  | _ => fun _ => none
def g127 : Forest := ⟨127,10,fun i => g127Y[i]?.getD (0,0),g127C,g127A,g127L,g127I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P5_0 : block g127 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B5 : block g127 5 0 1=true := g127P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_0 : block g127 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P6_2 : block g127 6 2 26=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B6 : block g127 6 0 28=true := (@block_merge g127 6 0 2 26 g127P6_0 g127P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_0 : block g127 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_1 : block g127 7 1 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P7_21 : block g127 7 21 105=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B7 : block g127 7 0 126=true := (@block_merge g127 7 0 1 125 g127P7_0 (@block_merge g127 7 1 20 105 g127P7_1 g127P7_21))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_0 : block g127 8 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_5 : block g127 8 5 67=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P8_72 : block g127 8 72 43=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B8 : block g127 8 0 115=true := (@block_merge g127 8 0 5 110 g127P8_0 (@block_merge g127 8 5 67 43 g127P8_5 g127P8_72))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P9_0 : block g127 9 0 12=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B9 : block g127 9 0 12=true := g127P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127P10_0 : block g127 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g127B10 : block g127 10 0 1=true := g127P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127T : checkedTables g127 10 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g127B5
  · exact g127B6
  · exact g127B7
  · exact g127B8
  · exact g127B9
  · exact g127B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g127G : graphValid g127 (boundsBefore K246) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low127 : Lower true (varsX 127) (graphGoal 127) 11 := lower_forest (g:=g127) (i:=0) (hints:=33621315) (before_sound K246 V246) g127G g127T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K127 := extendKnown K246 11 [(127,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V127 : Known true K127 := extend_ok (m:=127) V246 low127 (by decide +kernel)
def g191Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdc920712d36aa096a,0x350c800003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x504100102d348a0168,0x250c050a142850a14285]))),((BitVec.ofNat 152 (word80 [0x170978870930258ed,0xea4d000000000fe03f80])),(BitVec.ofNat 152 (word80 [0x9970078870120058ec,0x84c23468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0x2e54e9fbee00a2a44,0x970001fc07f0000000])),(BitVec.ofNat 152 (word80 [0xe0e14e9f3ca00a2a40,0x170f1e3c78f1e3c78f]))),((BitVec.ofNat 152 (word80 [0xfeb671b1740f94ce22,0x501300fe00000000007f])),(BitVec.ofNat 152 (word80 [0x2b471a1500b140e02,0x50131a3468d1a3468d1a]))),((BitVec.ofNat 152 (word80 [0x2012d631f855287d9,0xea838000000000003f80])),(BitVec.ofNat 152 (word80 [0x20128630f85528711,0xe283dcb972e5cb972e5c]))),((BitVec.ofNat 152 (word80 [0x24592a2c119793013,0x1f2ff000007ffffc000])),(BitVec.ofNat 152 (word80 [0x20490208009710003,0x809020408102040810]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x13a484c0a6855d794,0x62c7ffffff800000000])),(BitVec.ofNat 152 (word80 [0x10a0040024000d094,0x22060c183060c183060]))),(0x0,0x0)]
def g191C : List ColumnInfo := [(16,0,175,0,9)]
def g191A : List (List Nat) := [[]]
def g191D9 (j : Nat) := if j=0 then 0xff else 0
def g191L : Nat → Packing
  | 9 => (1,0,1,0,0,0,0,g191D9)
  | _ => emptyPacking
def g191I (_ _ : Nat) : Option (Nat × Nat) := none
def g191 : Forest := ⟨191,9,fun i => g191Y[i]?.getD (0,0),g191C,g191A,g191L,g191I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191P9_0 : block g191 9 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g191B9 : block g191 9 0 1=true := g191P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191T : checkedTables g191 9 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g191B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g191G : graphValid g191 (boundsBefore K127) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low191 : Lower true (varsX 191) (graphGoal 191) 10 := lower_forest (g:=g191) (i:=0) (hints:=66883) (before_sound K127 V127) g191G g191T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K191 := extendKnown K127 10 [(191,[]),(223,[48,65,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V191 : Known true K191 := extend_ok (m:=191) V127 low191 (by decide +kernel)
def g239Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff447e3a2404775d0,0xa300000003f000000fff])),(BitVec.ofNat 152 (word80 [0x828006e382404365c0,0xa1009249249249249249]))),((BitVec.ofNat 152 (word80 [0x52349162fda1b6,0x99b4000000000003f000])),(BitVec.ofNat 152 (word80 [0xcc052349060fda1b6,0x9996baebaebaebaebaeb]))),((BitVec.ofNat 152 (word80 [0xcae3482c928cd59,0x10980000fc003ffc0000])),(BitVec.ofNat 152 (word80 [0x1704a23482c120c458,0x108830c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffe6b1325eaa878214,0x43c0003f000fc000003f])),(BitVec.ofNat 152 (word80 [0x1804a11054aa848210,0x42806186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x10b84759f40b063,0x28600fc0000000ffffc0])),(BitVec.ofNat 152 (word80 [0x20000900651e001001,0x614514514514514514]))),((BitVec.ofNat 152 (word80 [0x22c1b057070590e,0xe557f000000fff000000])),(BitVec.ofNat 152 (word80 [0xc0020c0b0110501906,0xa1518618618618618618]))),((BitVec.ofNat 152 (word80 [0x19d049c814980680,0x9c8ffffffff000000000])),(BitVec.ofNat 152 (word80 [0x1950000800080000,0xc060820820820820820]))),(0x0,0x0)]
def g239C : List ColumnInfo := [(2,0,237,0,11)]
def g239A : List (List Nat) := [[],[32,99]]
def g239D11 (j : Nat) := if j=0 then 0xff else 0
def g239L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g239D11)
  | _ => emptyPacking
def g239I (_ _ : Nat) : Option (Nat × Nat) := none
def g239 : Forest := ⟨239,11,fun i => g239Y[i]?.getD (0,0),g239C,g239A,g239L,g239I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239P11_0 : block g239 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g239B11 : block g239 11 0 1=true := g239P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239T : checkedTables g239 11 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g239B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g239G : graphValid g239 (boundsBefore K191) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low239 : Lower true (varsX 239) (graphGoal 239) 12 := lower_forest (g:=g239) (i:=0) (hints:=33555795) (before_sound K191 V191) g239G g239T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K239 := extendKnown K191 12 [(239,[]),(253,[48,65,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V239 : Known true K239 := extend_ok (m:=239) V191 low239 (by decide +kernel)
def g247Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x8239cac1809be2565,0xc1c00001fc0000003f80])),(BitVec.ofNat 152 (word80 [0x60039c801809be0565,0xc1c58b162c58b162c58b]))),((BitVec.ofNat 152 (word80 [0xf228e900d5dee50361,0x334000000000001fc07f])),(BitVec.ofNat 152 (word80 [0x4020e900955e650261,0x1154a952a54a952a54a9]))),((BitVec.ofNat 152 (word80 [0x6578d00b634198d95,0x84000fe0007ffe00000])),(BitVec.ofNat 152 (word80 [0x82518d00b424180d85,0x183060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf3594ce7aac1d05148,0x6900000003f80000007f])),(BitVec.ofNat 152 (word80 [0x25904e72281901108,0x6823468d1a3468d1a346]))),((BitVec.ofNat 152 (word80 [0x84814f63a0146632,0xd6807f0000000fffff80])),(BitVec.ofNat 152 (word80 [0x84004d4280006010,0x60a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x116669158062bf0a8,0x15ff800003fff0000000])),(BitVec.ofNat 152 (word80 [0x1066010480023e020,0x15cc183060c183060c18]))),((BitVec.ofNat 152 (word80 [0xce93272055b22080f,0xc3ffffffc0000000000])),(BitVec.ofNat 152 (word80 [0xc280222015200000a,0x83060c183060c183060]))),(0x0,0x0)]
def g247C : List ColumnInfo := [(1,0,246,0,10)]
def g247A : List (List Nat) := [[]]
def g247D10 (j : Nat) := if j=0 then 0xff else 0
def g247L : Nat → Packing
  | 10 => (1,0,1,0,0,0,0,g247D10)
  | _ => emptyPacking
def g247I (_ _ : Nat) : Option (Nat × Nat) := none
def g247 : Forest := ⟨247,10,fun i => g247Y[i]?.getD (0,0),g247C,g247A,g247L,g247I⟩
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
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g247B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g247G : graphValid g247 (boundsBefore K239) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low247 : Lower true (varsX 247) (graphGoal 247) 11 := lower_forest (g:=g247) (i:=0) (hints:=33621317) (before_sound K239 V239) g247G g247T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K247 := extendKnown K239 11 [(247,[]),(254,[48,65,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V247 : Known true K247 := extend_ok (m:=247) V239 low247 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfc997ec41a50fb0101,0xa0400001fc00001fc07f])),(BitVec.ofNat 152 (word80 [0x20893cc00a40330101,0x80450a142850a142850a]))),((BitVec.ofNat 152 (word80 [0x110a4924f27512f92,0x4b40000000000fe03f80])),(BitVec.ofNat 152 (word80 [0x3010a4904e07512a10,0x4954a952a54a952a54a9]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfa455007280e7c8aa8,0x770000fe0007f000007f])),(BitVec.ofNat 152 (word80 [0x804040072002488aa8,0x7602850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x1863475d5e08813a5,0x1680000003f800003f80])),(BitVec.ofNat 152 (word80 [0xc186102511e08811a1,0x16a3468d1a3468d1a346]))),((BitVec.ofNat 152 (word80 [0x6ac2a2b1d80b64f2,0x44007f0000000fffc000])),(BitVec.ofNat 152 (word80 [0x624202b1980844a2,0x40a142850a142850a14]))),((BitVec.ofNat 152 (word80 [0x8b2348ac0b05f026,0x99ff800003fff0000000])),(BitVec.ofNat 152 (word80 [0x922488c08056006,0x894c183060c183060c18]))),((BitVec.ofNat 152 (word80 [0x674893902a5804849,0x8cfffffffc0000000000])),(BitVec.ofNat 152 (word80 [0x61481300025800040,0xb060c183060c183060]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,9),(2,0,249,0,9),(8,0,243,0,9),(16,0,235,0,9),(32,0,219,0,8),(64,0,187,0,8),(128,0,123,0,8),(0,2,201,48,7),(0,16,169,66,7),(9,0,242,0,7),(10,0,241,0,7),(17,0,234,0,7),(18,0,233,0,7),(33,0,218,0,7),(34,0,217,0,7),(72,0,179,0,7),(80,0,171,0,7),(1,2,200,48,6),(2,16,169,64,6),(3,0,248,0,6),(8,16,161,66,6),(16,2,201,32,6),(24,0,227,0,6),(32,2,201,16,6),(32,16,137,66,6),(64,2,137,48,6),(64,16,169,2,6),(96,0,155,0,6),(10,16,161,64,5),(17,2,200,32,5),(19,0,232,0,5),(26,0,225,0,5),(33,2,200,16,5),(34,16,137,64,5),(35,0,216,0,5),(40,0,211,0,5),(48,0,201,0,5),(48,2,201,0,5),(50,0,201,0,5),(65,0,186,0,5),(66,0,169,0,5),(66,16,169,0,5),(72,16,161,2,5),(80,2,137,32,5),(96,2,137,16,5),(96,16,137,2,5),(129,0,122,0,5),(130,0,121,0,5),(136,0,115,0,5),(144,0,107,0,5),(160,0,91,0,5),(192,0,59,0,5),(11,0,240,0,4),(25,0,226,0,4),(41,0,210,0,4),(42,0,209,0,4),(49,0,200,0,4),(49,2,200,0,4),(73,0,178,0,4),(74,0,161,0,4),(74,16,161,0,4),(81,0,170,0,4),(98,16,137,0,4),(112,0,137,0,4),(112,2,137,0,4),(137,0,114,0,4),(161,0,90,0,4),(162,0,89,0,4),(200,0,51,0,4),(208,0,43,0,4)]
def g251A : List (List Nat) := [[],[48,65,101]]
def g251D5 := limbs80 #[#[0x54550441862195154110,0x480a8589515411068886,0x55142541202615450950,0xd89405d594d896050386,0x29d6254560541a6e4975,0xdc96054076e4d7158150,0x5459625980d5151e8964,0x25980d51516889660354,0x3d03b6a774d4d43581a4,0x93532a61d2cc94e458e1,0x53192ac4d623aa6552aa,0x2c87dd06b0c28da1722b,0x2b68e1dc34764acdb1f7,0xb59765b8ca4bb6912d94,0x4060808003dd5532d96c,0x3868c16284880e1828]]
def g251D6 := limbs80 #[#[0x64886541106188654110,0x58951541102195154110,0xa1951541106195154110,0xdd95154110dc95154110,0x5895254110e495154110,0x21965541102616254110,0xe4975d89105977254110,0x55142541202614254120,0x5895154120e194254120,0xa1962541205516254120,0xe4187551206617655120,0x59154581205895158120,0x59162581205516258120,0x5d164581205d16258120,0x64b64581205898158120,0xa1b805d120617805d120,0x66175d9120657845d920,0xd9562509405956250940,0x5d542581405894258140,0xd494258140a594258140,0x5d564581405956458140,0x99564581406156458140,0xa556458140a156458140,0x2597558140e496458140,0x59353581405935258140,0x65362581405d76258140,0x24987595402597559540,0xe518759540e418759540,0xe41835d940618865d540,0xe4976d4940617805d940,0x5d565d894066176d4d40,0x5d580d8940e4975d8940],#[0xe49761d9505d584d8940,0x5d9821d950e61761d950,0xdd9545095021d5450950,0xa1f80509506537650950,0x5d876545505db8150d50,0x25d62545506487654550,0xe4165551505db8354550,0x55142581506507658150,0xdc942581505894258150,0x58951581501d95158150,0x1d95458150e095158150,0xe4954581505915458150,0x595625815025d6258150,0xe096258150dd16258150,0x99564581505956458150,0xe4d71581501d97158150,0x55362581501d97458150,0x5937258150dcb6258150,0x59782581505538258150,0x6508758950e0b7258550,0x64b74589509d97258950,0xa1f8059150a178059150,0x1db835c5501d9655c550,0x610825d9505db835c550,0xe09815d950209815d950,0xe17805d950e0b805d950,0xe17825d950647825d950,0xe57825d950e43825d950,0x9d981d51505d981d5150,0x25980d5151e4964dc950,0xe49751d560a5980d5151,0xdd35350d6065f5350d60],#[0x59564551606577450d60,0x64382551609956455160,0x657745916065f8355160,0xe43825d5605d7845c560,0xe4954dc96066374d4d60,0x66265dd1605d581dcd60,0x5cf805c96466275dd160,0x651809d564e53805c964,0x618865ca5465d809d564,0x654865ca54640865ca54,0x649645ca54615645ca54,0x661655ca54615655ca54,0xe416250b405956250b40,0x64b6550b4064a8650b40,0x64886543406188654340,0x59542543405894254340,0x5c962543402616254340,0xe616254340e116254340,0x21965543406556454340,0xe1362543405957254340,0x61b84543405978454340,0xa1b845434065b8454340,0x5cb8058b40a5b8454340,0x64b655cb4064a865cb40,0x662865cb41e4182d9740,0xe87b83f83b663655cb41,0x92e91f8fa8ee8de8be87,0x7396b96795b94f93e93b,0xea3b9ea9dc9ae9ab97a9,0xa73a6ea6ba67a5ba4fa3,0xd9aceabaaaea7ca7aa79,0xbb1eb1bb0eaeaadcadaa],#[0xb6ab5cb5ab4eb3ab2eb2,0x1bbd8bccbcabaab9ab8e,0xec6bc5bc3ec3bc3ac2fc,0xcbacaecaac9ec7ac73c6,0x2ed1ed1bceacdaccecca,0x2daad8ed6ad5cd3ad36d,0xe5ae4ee3ae1ee1be0fdb,0xef0becae9ce9ae8ee6a,0x918980ff8af4af2af1af,0x925053ab096916219304,0x40180ea645c30d26e986,0xdd821834c0c9ba8034c5,0xbb4404c1a20728d3044f,0xadfa204bac3013669009,0xc0cd205252a026ef0c0,0x48045618059b4416bfa2,0x5d83d29502229a60d09d,0xab4c1f7b860fbcc307e3,0x41da60e8bcb0835e983d,0x1644d409b36944ee30c2,0x38c625d0669728394f93,0xe946e632e2eb7a51a5ad,0xf4c280fa0149cba8eac,0xe5ca61e05d110bc25854,0x2006d48f9c6907cfb443,0xb12e25d49249304e0ba2,0x65cc09b524cd1a22698c,0x632e62b7a23298ba99cc,0xcb1a72bc0ba95e05d4a2,0x2a985494ace88a662ea5,0x117a16a0b49b5258d3a2,0x694eda340477d75225ad],#[0x4f447a6fa2403fd11f8d,0x80ba23c14d31f3d614f9,0x367fca1b41248d94b446,0x49c39e58dddf2c6af396,0xe10e4bf4c7473a43a03d,0xaf453e9ca89ec8b2cf3f,0x16d65a2824c50e159685,0xa7b6b2d3866928c33494,0x154aee9e917f454d1d95,0x65eaac32f508da5ab4fd,0x2b0d3acda2a546d2d63f,0x77d7598a0bb4c84ea672,0xafb4b25695e8268af413,0x3a986692c08f415c47a0,0x691499b44a5239254545,0x6348bcb5a25e9a3b2fb2,0x38964515a53a86455141,0x59b8b2add16593e0930a,0xa310b691616b44b4cfa2,0x6518d6f44c74594619cc,0x8ac8ae97a2654bd1324c,0x8c9a45566d12ab2e895a,0x4e5ad13032691759748b,0xb250c6912cef449945a5,0x69598fb40cc23a94994b,0xef44dc69a46d3ad13699,0x953864506d4a3a9689b0,0x685ad03439e1918c34c8,0x23d3fe819e52cad2a5a5,0xdd934f7449035a57a7cc,0x2b52d499a07949d13c4b,0x4ef984177d4a1836a5ac],#[0x75adbb39d7dd9c9df448,0x4b83ee51c2cf0ae55776,0xe81bdf728e3039371055,0x772cec0ba96f2dd3379f,0xc6fa4743bd1ba4ae59de,0x7f7ac2c49168224df450,0x1440fe8a008744fc39a9,0xe8a1222c9067ba28a05d,0x7f450ac9a08265d04082,0xa0ba28b05d14612e8a14,0xb107d05945e5a1def30f,0xb3da3691ed2b44f60fa0,0xe9a518f412b0b967c84c,0xdb0d2647a097aac34b2b,0xf13968e41d0c6bbea645,0x2c02c001fe8a42232d1,0x81b03105208c0e817023,0xc8540a012c2304207c0e,0x788e91c2364660c41782,0x13424e47c8a1092023e4,0xc3065c8b29592a25249e,0x8e6fcdb9ae34c674ca98,0x7fcfb9ef3ce77ceb9cf3,0xd21a3a4628950d20f40e,0x52824f49c93325d4a892,0xd1592af95b2ae544a594,0x612c057caf15d2b856ca,0x2d059cb31652c858cb11,0x5bcb716d2d85acb5169,0xdcbb1752e85ccb91712e,0xbf17d2f85ecbd1792f05,0x18530860cc11813005fc],#[0x31de36c658af1261dc3,0x3325fcb294f27e4bc899,0x684d019f13c272cdd9ab,0xc550a8b4f697d21a3344,0x96b1d61abf576add59aa,0xb9d71adf5b6b5d69acf5,0x782f01dfbbe77aeefdd6,0x2f21e3bc678af11e1bc2,0x41e7bce79af31e5bca79,0xebbd67aaf51e9bd27a2f,0xbde7baf71edbda7b2f61,0x73cc791f1be27c2f81ef,0xddfb7f67eb3d47a4f41e,0x7dafa7f3fe5fc7f87eff,0x3006fcbf77eafcdf8bef,0x2c00e04000027023d8,0x9c09107288d0f030a00,0xd20d40dc0d041087b020,0x690cd0580b0118630000,0x406f88ac86c86c8,0x10000405010040501000,0x30160200000000000116,0x683a82000196100ab080,0x40002000100c8d08,0x80000000000000000000,0x201008000402642c0690,0xc84c86504000000c840,0xc04000,0x0,0x0,0x0,0xa020000000000000000],#[0xc20080a02007111c441b,0x15a0ad0690800016,0xa6c2000000000100a420,0x236100a4200db0,0x0,0x6a08040,0x0,0x0,0x0,0xc200000000015b080000,0xb0800000000000000066,0x1d]]
def g251H6 := limbs80 #[#[0x80008600e6cd203080d2,0x3cf40000002722001,0xd6000000e012000114,0x1400000000000000340,0x240]]
def g251D7 := limbs80 #[#[0x55054619541517655054,0x4414250110e1d5415286,0xd8940441645011058940,0x50910589424416250510,0x44151541102195044186,0x59550441625411054950,0x54110a19504418654110,0x4437654110dc95044362,0xdd951443725451058951,0x54910589524438254510,0x4416258510dd95244186,0x61d6244176589105d562,0x58910dd1624428758910,0x4437659510e016244376,0x5d762443865d510e0975,0xdc91060b6544182d9110,0x44186dc9106177244165,0x5095048185dd910d9772,0x54120551504815154120,0x48165541205915048162,0x6115048181541205d950,0x54120a19504818654120,0x4838254120d915048361,0x5915448383545205d951,0x55120619544817655120,0x4813158120e195448187,0x54560481435812050560,0x58120585604815458120,0x48165581205916048162,0x6056048175581205d160,0x58120615604818358120,0x4817558520e096048364],#[0x61d644817459120e1d61,0x5d120e1d644838559120,0x481865d1206157448183,0xe1574483805d120a1974,0x5d92060576483865d120,0x48175d8520e117648184,0x5d76448182d852060361,0x5093060b6448180d9120,0x5028654130619504c186,0x5d542501655094058942,0x5094060d425017650940,0x50286509406194250185,0xd95425036350940d4942,0x58140509605038050940,0x501625814054d6050152,0x59560501645814058d60,0x58140609605017558140,0x50265581406156050183,0xd4d605035258140a1560,0x58940595625036258140,0x503655894061d6250175,0x595645038758d40e1562,0x59140609645017559140,0x50265591406156450183,0xe09645038059140a1564,0x5954061d655017559540,0x501825d5402197550382,0xe0975502865d54061975,0x5d940e1975503845d540,0x501855d94060d7650182,0xe0976503805d940a1576,0x995405d665503855d940],#[0x50165d49405935250176,0x5935350187d49405db52,0xd894061f5350176d4d40,0x50180d89405d76250165,0x6036550175d954061362,0x1d9505d87654184d9540,0x542871d9506107654182,0x21d4254176505505d931,0x50950591425415450950,0x542875095061d4254176,0x551435438050950dd942,0x54550e05435417650d50,0x54165545505895154076,0xd895154276545505d951,0x54550e09515436554550,0x54164551501d95454383,0x60954541765515059554,0x551509d9545418655150,0x5437455150d955454286,0x1d9605438655150e0954,0x58150509605408558150,0x54154581505456054143,0x59160541635815058960,0x581505c5605416558150,0x54183581506056054174,0xd4560542655815061560,0x58150d89605435458150,0x5437458150dc96054364,0xe0d605438258150dd960,0x585505d9615438558150,0x5438758550e096154372,0x59562541545895021d62],#[0x589505d9625417258950,0x542765895061d6254180,0xdd9625437458950a1d62,0x58d50e1d625438458950,0x5438758d50e156354176,0x61d64541765915059564,0x59150a15645426559150,0x5438059150dd96454287,0xe1d645438559150e0964,0x59550605655407659550,0x5438259550e016554184,0x59571540765c550e1165,0x5c5509d971541765c550,0x541765cd509d97254383,0x5d974541655d1501d974,0x5d95020976542765d150,0x541845d95060d7654181,0xe0976543815d950e0176,0x99550e1576543845d950,0x541859d95061a6554176,0x5db5454276d45505db51,0xd515061b5454181d5150,0x54187d85506036154276,0x5db6254154d8950dcb61,0xd89506136254180d8950,0x54287d895061f6254185,0x6036454374d8950dcb62,0xd955061f6454185d9150,0x54176dc55058b7154187,0xd8b7154276dc55061b71,0xdc9505977254164dc950,0x54276dc95061b7254184],#[0x5977354364dc950a1b72,0xdd1509db7354176dcd50,0x54182dd1506037454176,0x9db7454265dd15061b74,0xdd950d977454286dd150,0x54564551516137654181,0x6037254582d915160354,0xdcd515937354586dc951,0x55365dcd51d937354565,0xe0964552655915460964,0x5c15459570551645c154,0x551805d9549d97055176,0x61a64553845d954e0176,0xdc15460b7055164dc154,0x55186dc55460b7155186,0x55143581751d56060376,0x50d605cd435816350d60,0x5837450d60d4d4358186,0xd89515816254560e0543,0x54560e09515837254560,0x5818754d60e195158383,0x5d554581655516059154,0x55160619545818055160,0x58275551609955458187,0xe09545837555160a1d54,0x55160e19545838355160,0x58380585605896158387,0x61162581815896059162,0x58d60591635838058960,0x5816559160e016358165,0x60d6458182591605d564,0x59160995645818559160],#[0x5837459160a156458275,0x589715838059560e0164,0x5c5605d571581725c560,0x583845c560dc97158362,0x5d574581755cd6059173,0x5d560e0975583805d560,0x581869d5606026558386,0x61f5358180d4d6059353,0xd89606035458374d4d60,0x58175d89605536258143,0x5d77158275d91605d764,0xdc9605537258143dc960,0x58185dc9606077258165,0x5d77458181dcd605d773,0xdd1609977458185dd160,0x58580dc9616096458675,0xe1165591751d56461772,0x5c9645cd72591725c564,0x591809d564e117259380,0x9977059185dc16460b70,0xdc9645cb7159275dc164,0x95182dd5646177259173,0x21972951825925459564,0x5ca5459572951645ca54,0x952865ca546197295185,0x61972993865ca54d9572,0x50b4058942d03825da64,0xd017650b405d542d0165,0xd9542d028650b4061942,0x5434050950d008654340,0xd01655434059150d0162,0x61950d0176543405c950],#[0x54340d8950d028654340,0xd017258b4059562d0384,0xe1562d038058b4061d62,0x5934060964d016559340,0xd038759340e0964d0185,0x59172d03825974061d65,0x5cb4061972d01655cb40,0xd03855cb40d9572d0286,0xe0976d01825db40e1972,0xd8b4059762d03855db40,0xd0582d974061362d0175,0x61d65d0576547415c951,0x5cb4159572d078259741,0xd07655cb41a1972d0586,0x60976d07865cb41e1572,0x55350e1576d07825db41,0xd8164553515d164d4164,0xe0543d835350f6055143,0x54760e0951d817254760,0xd81745536059154d8383,0xe0d54d83825536061d54,0x5936061564d818259360,0xd81835cb6050d72d8285,0x60974d83855cb6061172,0x5d360e0974d82855d360,0xd83825d76060575d8385,0x60354d8174d4f6059353,0x5c36461570d918259361,0xd91835cb64e0970d9285,0xe0975d91805d76461172,0xf2fa3fc7e8f71be2fc3f,0xf67dcfa9df3ba6fcde97],#[0xafd5ba9f4fe9f53b9fd3,0xd7eafb5eebd577adf5ae,0xdb776ead7daeb3f66ecb,0xbd776ee5dbbaf73edf5b,0x87efe5fabed7baf5deab,0xb2fe5ecb793f1fe3ec77,0xfe7ecfb9ef3d677cdf9b,0xcfd9dafb5debad6fabf4,0xdf5be7776dedbbb6f6be,0xdcef9d72fe5dc7f8defc,0xbbb5f67ebdd73adf4fe7,0xd579ef37e6bc7f8eef5d,0x7daf9df2fe57baf5deaf,0x629e480cb5b9019fabee,0xfd2aa05ea796032d6ec0,0x511860cb12ca190c2602,0xd172825555d04a184c06,0x80e584244c90a54d7412,0x40cb0f395621e427202b,0x83921f90328440a26079,0xd7085303e4899a6ba8fc,0xce41f174cbc051d65809,0x24b9ca2994819eae5032,0x5913c302c87255dc8f12,0xb22701125ce7114c1e0a,0x21cc040ca1be899237d4,0xb2a8af77250013287eb6,0x97350832ca2b761545a2,0x248c34dd91b07c92924c,0x60b966bb1747593460f3,0x937ee3854b596ec9880e,0x591c0f30bf03e49d007c],#[0xe00b6e1c010dcb48ee17,0x80326cb804db870089f2,0xaecda9600db32c019365,0x79ccb20f396651ed6dc2,0xeb33e19ec66c33ce5195,0x45ccb009b9620100f30,0xcb99401c7f3002aee58,0x336ec4066d5880c5dc90,0x66d2180cdbc1019b5820,0xddbc3019b6860336b0c0,0xb6f76037670406ec5880,0x8793007645940e56cb01,0xab65412c8b28243f9803,0x57c901e719604edaca09,0x938603f210c07dbdd80f,0x732805b06480b38c9029,0xbe541061c9021198602d,0x3c80111b860455b2a08a,0xd96059572a0ab1e40156,0xb240b8e658187fbb0306,0xe40099dc1038c790070d,0xb28323f9002aeee804b0,0x8108c7f200d056601bc6,0x2211c0a1c2380c384741,0xd8231eca8463d9408e83,0xc03aef8408606ec11c05,0x2088bf280f1ae481e0bc,0x41392658202fca03e699,0x2a35c9054179809cd72,0x85817960ac2b30168566,0x91dee8140fe40280bca,0x1305658251fc80525595],#[0x30d8b106017920b82b24,0x74c1920eadaec186ce08,0xd87b301d1c65c3a56ca8,0x7ee6102fdcb205ec3920,0x29fc305f3d860befaec1,0x5b1650c98728196c5503,0xa7b0c196861832d8ca86,0x6c5503c9fc3065a2860c,0x9ec3079b1650f183281e,0x6d760c75ac818b06583c,0x5b2c18cce183198c3063,0x6483b39cb866af960c5,0xecc07671970ed5b2a1db,0xd760d15f281a30e48371,0xf241c30e4838bfc906b6,0x65c3956ca872c1920e67,0xb108ba1621107b301c9c,0x621257f2623e858847d0,0x2827b0e484fd0b109fa1,0x444abeba095a16412977,0xa095a18412b42a825686,0x21418f22234f61453d0c,0x8259c65c48ceb2090c39,0x452aeba897a19212ef2e,0x9d6d75130e72a26d75d,0xf98724289ce504ebfc9,0x2a92e58542bca87af176,0x647cba8cd01751942b2a,0x7e1598190972c3239614,0xc2f2e20856604076c38,0x140e404225cb08415971,0x60bcb084d796109a92c2],#[0x3592160bf2a2b5ee405,0xe07202b9ce40570acb8b,0xc05d4680aca8b2179515,0xacc0cee58519df2ea34,0x719617a050c2f406145e,0xd7242d9ce405b39c80b4,0x56585f25cb0b6489616c,0x4c90ba7190174e7202e0,0x5951802b302e976505d3,0xf28309ae486139c80c21,0xe486b0aca8c67390188b,0xc80d4ad951b15f2a35b0,0x821e772c43ceed48791f,0x2c3ce765879bcba8f3b9,0x887a5dcb0f39e961e573,0xb90d9d6421b3ac83d685,0x51f33b283e675907c38c,0x83de759081aeba9115d7,0x7d38cb90f9d6421f3ac,0x8fcbb9420b3ac8416759,0x1faf2ea3f679947eceb2,0x3f676147ecec98fd9d92,0x7fcf4a8fd9d951fb3d0a,0x7197212daea425b5d4,0x2b92c405ee508039c91,0x1aee508361c91075f962,0x84acb10ab9942152f2c4,0x179751e372c43c6ed487,0x752ca3aae658789ac30f,0xe65946d5acb0eb75761d,0xbabb0db75751b736ca36,0x5d971d96b243b2e64076],#[0x6f24372ee407116cc0ec,0xe640772ecb8dd61751b9,0x6cc0ee5d971dd6b243ba,0xf861bddb0c37dde486f1,0x720382ee40722fcb0dee,0xe40735dc80e65f951c2f,0xcb8e8b5921d173203a4d,0x872b1db0e558b660742e,0x2c5705660ad35c915ae5,0x608a4ac811949752242f,0x811615972345b284685e,0x52c9daea5ac05d4b439c,0x59b9614b335c9167497,0xb076c395e17982cc2b3,0x12c15922382f2c588566,0x25d772048de5d4969ac1,0x4a585d48f5dc8124ed75,0x902fc91205d97252c2ea,0x26ec98242a72c4854258,0x690b2c4aae640955dc81,0xc15e489825cb13015972,0x9a5cb1314896262c7284,0x2f89226607204c9ae489,0x5df284c85e48997dc913,0x39618a90bcb132d79626,0x76ba97101752dc2b3055,0x4896270e7204e12e58b6,0xbb2c50056589f25cb138,0xce409d6ac3136699226c,0x8c813c5f94274d7244e9,0x786278ab2a4f176509e3,0x7205140614a60ac9142d],#[0xe10a339c8146159529ce,0xc91487390290bf2851bb,0x90294972c5217e50a435,0x245412658a52eca14a71,0x95f9ddc13f3b9627e42b,0xb3f379767e75b2afceb5,0x47eafae4fd2ee59f95cc,0xfd1c65dfac8b2bf5378,0x2019bc24023f987e8793,0xc02ad9580722cb00ae65,0x7f6f2c8fedfe09fd38cb,0xfd9ce59fdb6cabfb6d65,0xfbd6cabf7ad657ed7724,0x5358680b5acb015ee5d,0xa6b2d012e65a029b434,0xe5b5d9fc57c93f936968,0xe39c93fd93867f3210cf,0xb9947e18324fc5b655f,0xd8724ff9c65df88cc33f,0x2e6520039cbbfebb947f,0x38cbc011b868015b2b00,0x9b657c732caf8eee41f1,0x6f24f95d5d9f1bababe3,0xd649f72ecbbe561757c9,0x6c33e62d987dcbb2efba,0xb907d4bf2afa3be19f37,0xb2efb2d649f69bc83eab,0x61206beb940c2d987d8b,0xb240d01878197329034d,0x768187b2b034d652069a,0xcb025d5920480cbc0d01,0xd60335cac095b65812b2],#[0x840a159781c5b2903d25,0x5865daeb0d85e560581c,0xb07856621a72c2c35497,0x21334c94266b92841df0,0x42215968502b31099765,0x848bb29091a64a1239c8,0x5aee42090acac2a1598,0xc2fcbc156175821daeb,0x3817928342b2f0717656,0x602b2b0b9ce42161fc84,0x1e4588e35fc99c615928,0x357c91c7338238f26c47,0xeaf9638f26ec71e41d8e,0x6b8ec74afe4ce956cb1d,0xcce14eb5dca1d697963a,0xbfb91c3a1623855f2a75,0x95963873ac870eb550e1,0x7f30708f260e1394b9c2,0x85c8e5c8b29cb3f82394,0xfba1cb9154397470472e,0x3723c7232a72a5e50e5a,0xb2878d7dd0f1c8aa1e3a,0x590f3bfc11e73f823cd2,0xb29e671943cebec879d7,0x9138a62ca7b4c550f6b6,0x2a7364594e6d6aa1c4c7,0x44f757ca9d933853b15f,0xa1c99d643915b2a7bb16,0x43935ac8722be48e4bdb,0xc7264dd8e4c83b1c9af7,0x4e756cb1e0af963915b2,0x1ce979239f24ca73e459],#[0x39f232a73e7e10e7ceba,0x75571d8ea4ac91e59295,0xf41f4c1e897963aabeec,0xe96e653d2daca7a1c648,0xa15f247440a60f480cc1,0x2b650eec9bb1d0af943,0xfc9bb1f0c3923b55d2e7,0xa95943d52d306fa5650d,0xa4aca691ae48be35c917,0x2be40cc79bb1a4f17634,0x35c919b4b763415b2068,0xad9033caf2e659525ccb,0x33286528648ca12cb1a2,0x2dd8ce51c919b4976329,0x6c826c27984d547249ad,0xd903edf7047d09661365,0x7247c8565cfb12ca9f63,0x6153d81b927615923f0d,0xb2a4417924f02b309eb9,0x76489e2ec913c1d92292,0xc8fd21d91f79bb244f2,0x611e2eca23c699247a0f,0x3242d786480d7249005a,0x252c2b30a71ae494c6bc,0xca7856614b6ac3296f98,0x8c60bc929a159853dab0,0x98d318531b5aa8635fdc,0x31a62ca634d590c68143,0x60585d8c01ecb18d3195,0xc14dcb1809996302c6ec,0x845f97305df0e60aee40,0x14bb286285e60c235c91],#[0x185658bf0acc18ad7863,0x434c91884b9630cd7246,0x415963102b306217650c,0x31aca804c61502c8b2a0,0x525d8fead3b201597640,0x24cb20d4965418d32483,0x25954207b20840566106,0x1f247fa8e48ff0acba10,0x564104adc92026b92407,0x4c920e4997410fb2a822,0x9964146f248185650fd3,0xb208485659050aca20a4,0xdc9400aca21225954247,0xb2a8b037450262a8a04f,0x96516b2eca2ca61545c6,0x2ca2be611457cc3a8a8d,0xd93e90c227cf998516b3,0xc27ce6874f9cb0e9f525,0x6519cb0aa3525954612c,0x8a10fe41410acc28c499,0x1437dc92875b924fc4f2,0xa46719048c2b28a205e5,0x550e320aa28e49512aca,0xa81ae49500acc2a85595,0x5638c82ac1598541db08,0xa4e5655482b30ab15655,0x4df724a9d9e49510bcb2,0x4956555538c82aa17945,0x77fbb192fd763265aca6,0x6b92322c6ec63d85d8c,0x9ceec85b95d90b2fca19,0x9ae492412caa186b9242],#[0xacc2b26b925604f30ab,0xaf90354bb2c6e58594dc,0x5b206dd2dd8d54dca1aa,0x565cdba5bb1b6999436d,0xfca1ac6b923584b306d9,0x1643755f206b8fe40d82,0xb2c6eb9dd8dd72bb1bb2,0x5d8d44dc91a9af903504,0xcb1b96176372c6ec6a58,0x9734d332869a8648d34c,0xec6b26e50d651c91ac56,0x48d6b2491ad6f9035a96,0xb1b29994366c7286b59e,0x3615f206c09660d9a5b,0x6d48e50d813c91b1339,0x93812c91bc55973695b2,0x26ea3924de5cec9c4b5d,0x4e8ab2e9d2b6413ab3c9,0x8a4c6151498c82722598,0x141ec92290287452650a,0x29319545264ca8a4c595,0x5206ec8a405d914994aa,0x68565d1512caa2b02974,0x63ecb222999444137288,0x65f94438d724870f6411,0xc972c879ae490f2eca22,0x856591224cb224379243,0xacaa2e159245c4b2a8b,0x37925244f24a40fe4947,0x2f24a4bee49497c49292,0xa6492583c324d4b76498,0xbc324e6b9249c2d30929],#[0xb92569af0c9415655286,0xb30af956555f38c82be6,0x6195bb6b2ab63d905742,0xcc2c25596579cacaae40,0x95580e320b005e495d0a,0xec8dcc6111b98c0a3655,0x511c4fc9a32af9046726,0x823aad904755f208d096,0x24c8fd308c096491d98c,0x8a53ee494a13ca266a39,0x8b990ca97737902ec2f2,0x25a15942f1af305cd6e4,0x4bebeec96cce152d9fc1,0x97cfe412fadbb25f2b85,0x2da5bb262fb764be572a,0x5473904aadf0a96dfe09,0xa8d724953ee092a7c412,0x715e552a2fca25463934,0x97cc2252fb824b9f1049,0xef9834beff2097bee112,0xdf70897be6112f7dc1a5,0xd9e552f7dc2a5f67854b,0x7cc8a5e15944beb72c97,0xfb934bdf32697bee452f,0xf32a97bee512f7cca25e,0xae492b7dcb25efb954bd,0x5c925873904b0af2a959,0x7944d04f249a05649303,0x2ed1505e496331c9ac42,0xe0d8787c1b0d61658aec,0xcbb12f383621f704c443,0x626707b20c5bcdd58a0a],#[0x8d7c5e09af8bc133719,0x11b377c23610b846ca17,0x9362ef756d1daeada3be,0x468232c8d01ae49c735c,0x8d046611a04bc833a3d9,0x5c24bc833e97906792b2,0x3968f927121308e1a4e4,0x724d724e49be45c82fca,0xe61ae49ca0acc392e585,0x835ec8306ff756142f28,0xbf90600c32ec1dcdd1,0x10bd2ebfdcdd181b9ba3,0x21765584b8c9b085d926,0xe1bc93183f90609db0cc,0xa3f946fa36c8df46591b,0xc6f24df85661c084c237,0x8f649a30bca37efb926f,0x85c23423d9468e32c8d1,0x6b926da1708dad2dd5a2,0x3ac8c81ae49cd7ebab9c,0x565d9784b232e3d9065f,0x2b2b1a15976607b20cc0,0x7926373f20c6e19958dc,0xf20c7619d58dc2bab1a8,0x659943fcb31ead9064d5,0xc83323f90644bb28cb1f,0x966486f24c91ae49921e,0x2ccd05655952acab2a1f,0x55ad1ec935b31657043b,0xa3489790690bb2ad60f6,0x26b50b28d4a5641a943c,0xd325655ad4ac935b198],#[0x9a542cab58979069d2f2,0x35485946a90f28d2a3e4,0x6ad2b20d5a5e41a80ecc,0xe307e61c547c938a4997,0xcf35c936e1d987192b20,0xa237927402b30e91ae49,0x41f124e81ae49d00acc3,0xd8f651ae0bc93a0fb927,0x873cc2fd67925f87f28d,0x317866e6370cdc4fe09b,0x3b28dd45e59b99fc837,0x95e563079c1c601f946f,0x37c8c76f1758c82b2f18,0x15948f8e7211e95e563c,0xc2eb169865e2e7ebac5e,0x56624676c248d0984916,0x2bac6ced748da12c91b0,0x7928cc2b2f1b8565e367,0x32f2385e4a352fc94688,0x6423a25cbc7297908e20,0xc847e49978e90b291d25,0x94900e32120056564139,0x27218564a420acc4805d,0x4a1e37cb43a1594910c7,0xc4486992890d725109be,0x288ce721110565a250ac,0xf1005656260acc446699,0x62839c844e179287c2b2,0x2d0179659c2b25148565,0x5a8c324b598e49690bc8,0xb2a6e496430c82d86390,0x65994b2cb3196596612c],#[0xa961768b04f2ab34ce59,0x212f20e985e41d50bcab,0x858e5c01b0c300097909,0x36bc32e507865c6170cb,0x2ed645e5af0cb9956557,0xbf24bc05e597972b2af,0x5e597b0bc92f561655e,0x91c2adabb905b42f24be,0x99905ba42cab7a6e556d,0xd724ba48e157617c92ee,0x8e15760ac92ea5f945d0,0x4c93d975927a02f24bed,0x5657a02b30f617651ec3,0xb0cf45d655e8bac2bd17,0x619e9b2c2bd377867a2e,0xcc3d269987a6b50cf4d6,0x867a8d330f6d6619ed35,0x2af39ae59ea7dc33d4f9,0x55ee34cabd86b957acd3,0xc3c161757957720f31a6,0x877ce320ef85e55dd0ac,0xf09ce41d80bc93bc159,0xdda8dc33b53784768e72,0xbb5379476a06e6ed405c,0x766372ced40dd5da80ba,0xf19be45e285c33b66f91,0xdc73cc3ac2d9075c2f20,0xc90197772332cee4d651,0x2c2b2af81ce41ef0bc83,0x51c6424a35c949215959,0xe39c849a57959302b312,0x3e00002b21279ae4a4],#[0xf00bd014801e802f0038,0x5780a38134023a03f006,0x378068c0c5018202f40,0x2821d042a07e40f581d0,0xa50143027704c6090811,0x66a0c5817802c9056a0,0x783d3077a0e4c1b4834e,0x114217842108240ff81f,0x984129023e846408a81,0x685180a1213f027704e0,0x7242d005810ab0150829,0xcac193831205fa0bb61,0xa86b30d441a3c33f066d,0xca838e07080df41bb036,0xf581e343b707500e641,0xa082c104820283f807d1,0x21443c085c10a8210841,0x117e22c4454889b111a2,0x308f611cc237846b08c7,0x50849d092c123c243848,0x130425e84b9096112a02,0x309b7134426684c9098a,0x8184fc09eb13c6274c4e,0x148a28f451a8a2d143a2,0x88a8214ee29bc5308a59,0xb305620ab615562a7054,0x16002be05780ae815b42,0x40b4016642c9458e0b14,0xe245bf8b6a16ba2d405a,0x178a2ed45d50b9f17222,0xe0c14181830005fa0be0,0x1b06310c57187830a460],#[0x195c324c6448c8118ee3,0xcd819a033206600cb8,0x49468b8d0f1a0a33c067,0x1ad635586a40d3b1a603,0xb8dac1b4236646c70d7a,0x8907080e021bce37486d,0x1d2a3a0c7348e531c803,0x68f1e1e103b947658eb1,0xe207b68f561e963d0c79,0x1f883ecc7d40fa01f2a3,0xa900d20003fbc7f38fcf,0x12c81f10362056408080,0x210641d0836105e20ac4,0x410c0216242a484f1096,0x3f087a10e121b2434486,0x225a449488d110f22084,0xf917022c245488a1913b,0x6c48d31197231e461c8b,0x23d847788e691c523784,0x9922b2436484090111fa,0x9c49301252249448ec91,0x255a4a9094c128f24f24,0xd930525dc4b8c96612b5,0xdf89b3935926664ca098,0x27d44f5c9e0939c27124,0xa14602882507ca0413fd,0x328a5f94b42952522ca3,0x2a0c53dca7614e429aa5,0x795432a7654b8a911513,0x638ac1957b2ade555caa,0x2b8256d8ad715a62b2c5,0xf15f22bd25780aea95cd],#[0x8c0b12961d2c225818af,0x2cc4594cb2596412c725,0x896a82d2e5a24b3f166b,0xb78b6b16cb2d845ae4b5,0x2e0c5bf8b7b16ee2dcc5,0x597402e6a5c98b8f1715,0xdd8bb717662eb65d4cba,0x2f605e70bca178c2f025,0x297fa2fde5f68be917c1,0xf8c1b182a302c6038c0,0x30e461a4c30985930966,0xa98a7313e625cc43187a,0x3b0c6f18d0319062f4c5,0x323c6454c8518ff31e86,0xe195432986510c9a992c,0x630cc1997b32e46590ca,0x337e66c4cd499a0332e6,0xe9a0e33ee67a0cf019d1,0x974d279a41346668acd0,0x35306a30d3e1a7434d66,0xf9acf358e6af4d589aa0,0xc58d871b0535fa6bb8d6,0x36b66d4cda21b35365a6,0xb9b8f370e6decdb99b67,0xf48de21bba37566e7cdc,0x38006fe0df71be437b46,0x9c373856708ce0c9c08,0x208e399c6338b27144e2,0x398c72dce579ca039227,0xf1cf639dc7398e6f1cce,0x49ce8f1d163a1c7418e7,0x3ab07528ea11d373a5e7],#[0xd9d8c3af275c4eb41d60,0x738ee31dbe3b6c76b8ec,0x3c0677e0ef69de13bac7,0xa1e2c3c487870f0a1e0b,0x9a0f2e1e503c9078f0f1,0x3d287a30f421e7c3ce87,0x39ebf3d6e7abcf539e9f,0xbc8f751ee23db47b48f6,0x3e407c48f851f023df47,0xe1f6f3eb87d34f9d1f2d,0xed0fd49f9c3f187e10fb,0x3fe87f94fee9fd53f847,0xd2047403880390021ffc,0x2b9053209840fc81c502,0x41be835d067a0c241708,0x2a1164218840107a20ea,0x5750a7a147427e84c109,0x434e867d0cba18f42e68,0x721e143b287450e1a1b5,0x88510ca210440c87e10f,0x44c08945123a23d44548,0xca2a845408a5913f226e,0xbbd17222d9459c8b1115,0x46668c61185a30345f28,0x5237346c08d591a3a33b,0xf051d923a447388e511c,0x48188ffd1f7a3dc47928,0xda46b48b6914d220242f,0x2c125424a04926920d23,0x49f8939126724c049709,0x9252a4a449469289250a,0x6312c225764a9094e929],#[0x4b8a96e12d5a5a34b289,0x826084c0097e12f525dd,0x90d31da6334c4c986d30,0x4cea99b5331a6534c969,0xca6ad4d429a65348a67d,0xbbd37226d84d929b0535,0x4e3c9c5938727034df69,0xc274d4e889ced399a72a,0xec53ce27824eda9d813a,0x4fd49f7d3e7a7c44f789,0x828235028a02540027f2,0x1cd434286050aca0ed41,0x5156a28d44a288c50fca,0x228dc51a8a331461a8ba,0x445484a8fc51e8a3b147,0x5280a4d94972926523ca,0x4a97952d2a5814aa2948,0x7154dba9ae5332a6454c,0x53e6a7a14eea9d5539aa,0xe2a315452a86d506a9ff,0x99152e2a545498a91151,0x5544aa515462a7c54d8a,0x9aae455aaab3555f2ab0,0xce95992b2a562cac0957,0x56e2ada55ae2b4b5686a,0xb2bae574cae595c72b82,0xfd15f22bdb579eaf0d5d,0x5842b065608ac095800a,0xac555892b105618ac29,0x28564aac8758f0b1b963,0x59b6b3316622cbc5960b,0xdad135a14b40967b2cea],#[0x5456a2ad3d5a62b48d68,0x5b10b6016ba2d6a5ab2b,0x52dbb5b62b69d6cf2d96,0x7c96f52de25bb4b7496e,0x5c5cb89570eae155c02b,0x2ae5d5ca8b92171f2e36,0xa417442e7f5ceeb9b973,0x5d74bac97552ea15d32b,0x9aeeb5dc0bb617682ec2,0xc7d78baf0b5e06bbed77,0x5ea8bd3179e2f345e50b,0xa2f8c5f08bdd57b5af63,0xf217ddafb05f50be817c,0x6014bff17fa2fe55fbab,0x8b0436074c0c580d3012,0x21583ab06d60c4c16582,0x6192c2e9859309e612cc,0xf31106202c3cd872b0d7,0x57d8a8b1436268c49988,0x638ac6f58d6b19762f6c,0x131f363d6c78d8edb1d3,0x8f5917b2276436c84d90,0x651ac9cd931b254648ac,0x9b2c46578cab19523295,0xc2d98132f265c6cb6d96,0x6682cce599833226634c,0x4337a66d6cd719a8b349,0xf099d7b3a6673cce419c,0x6828d0319feb3e967aac,0x1b4496882d0c9a15341c,0x30da57b49e690ad1b1a3,0x6a00d3e1a7634e469b8d],#[0xc35306a48d471a883508,0x5c9ab5355e6a9ed501a9,0x6b6cd6b9acfb5906b02d,0x435fd6be6d795aee35c5,0x8fdb1a36266c36d84db0,0x6d0cd9ddb34b6556c8ed,0x36c26d66da95b4eb68e,0xc69b8336fb6de6dbadb7,0x6ed2dd51ba6373f6e6ed,0xeb7916f12de05bbcb771,0xf55be637be6f5ede99bc,0x7012e001bfab7ec6fc2d,0x8b849706ce0a5c0cb811,0x2b9c4d388870f6e1a9c2,0x71cae371c6a38c77176e,0x539217230e431c81b8f5,0x579ca839437276e4cdc9,0x731ce619cbdb97372d6e,0x2b9d17384e6a1cd03997,0x88dd0d3a117406e7cdcf,0x74a8e931d223a3c7456e,0x93a8374e8e9b1d323a5c,0xb01d5c3ab07550ea69d4,0x75d0eb81d6c3ad07590e,0x3b187620ec21d803af0,0xd39da03b387660eca1d9,0x76ecedb9db33b5e76ace,0x7bba7773eee59dc53b7e,0xf6dde9bbcb7786eee9dd,0x7806efeddf9bbeb77c6e,0xc3c2b7846f06de09bc0b,0x2dde57bc997906f1b9e2],#[0x79d6f37de6bbcc7797ef,0x5bd237a34f445e84bd01,0x559ea5bd437a76f4cde9,0x7b1af5f9eb73d667abcf,0x63dc47b70f6c1ed1bd9b,0x839efbbdef7bc6f755ee,0x7c98f8e5f14be217c32f,0xabe8d7d02f9b9f303e58,0xb61f653ec27d68fab1f4,0x7e16fc0df7dbef37dc0f,0xa3f457e7afcd1f933f1e,0xdf5fbabf6d7ecafd75fa,0x7f68feb1fcebf957f0af,0xdbff37fd6ff71fe5bfbc,0x12601bc02880330025ff,0x80e301a6030c05980a30,0x409d812b0236042c07a,0x460100d80200c09c0,0x6402741d83066034186,0x6181d04205c015c1001,0x350070041a1048380760,0xc1036d0421f06813c0d0,0x8316040828010480003e,0x6c0860b409000060bc14,0x900460240ac1d4348,0x81780b8310c0f607b043,0x586b8110483c47917109,0x290170d6190730621e41,0x8301680ac0902a0500a0,0xf064620483c028a09829,0x10390860ff0343d42a09,0x1503703015c080888882],#[0x87308700c0686a819112,0x9883300a88809721d462,0x805b01187e090698044c,0x820c0c908e0b4158c03,0x1100d02810a4180b10d3,0x285679d41fb6b2184d00,0xfc90999d178a0fd9b364,0x905f1305099fcc6300f1,0xad28c60fa182844fc849,0x5f4920cbe23181762,0x41c9435cd4a24d6a5100,0x11e404c8db0ac79c4,0x3d41430fa4a100980f46,0xf504447b248496076d0a,0x5c335a28547e691050aa,0xdd8a0c6b78890cd68a13,0x9f449b3378476926cc0,0xa6d0bbc9841c650c6de,0x9b4312c31c6c346878ae,0x63c5c050b0e54838dc1,0x63610f9725903e5c964,0xb8af052f482070316196,0xd70c9de27e03866978a0,0x42070c598627eb866e4f,0x78660ccbce1e1985e614,0x8b38c457aa8800332f38,0xee0f0a426718935b1671,0x8127e82f607d813bab44,0x9239d0d658e74359403d,0xb0d6696aa2d099ff435,0xa0d9f1683cffa1ac89c6,0x8300ec18a1810000974d],#[0x2010c0c30201d6177f80,0xe840e8400031c080430,0x2c6040218186040e8400,0x80000000000020e85074,0xb08019d0f5866d0e89e0,0x1438227b68bd81e,0x24e06908076c2016fd04,0xd87b6100ed86909381a4,0x7ac2010027e82000000e,0xcaed0f683b410000ed8,0x850717434869096c2008,0x410000941941e3b8287b,0x2140690cbba283c61043,0x4069ec141a020080d,0x202ac582fdc10000000,0xea08b61ab0d21a425b08,0x21a420148618a0a9c0bb,0x61c1b41e1e2880ef8c1d,0x37662449576407182e60,0xdd07da3143d3906a7e51,0xd8caef6e41b3e35078ea,0x498d4576875ab82cfc13,0x96157d39066712898080,0x63931b01cab130100603,0x80b0160201d6183a1003,0x38100b6040180f58401,0x100370200c040331b1,0xc0580b01000094b04000,0x137038684dc08046c200,0x1602c04dc08000001b8,0x1960403b61ed84078200,0x24d84039c0800056e0d2],#[0x1941008638c601156,0x398d0d80f26563e4cac6,0xf2328842b011a0ccc686,0x85e6304c047a5a1e3028,0xa0ada41419544ad335b6,0xb5a917f32cc09446038c,0x320e41444db620bea348,0xbc44c0580b016035eb6f,0x6c86f1158881c090200,0x804a0c76e31804a0802d,0x12834840000ce840290,0x1283484035040201a42,0x410049c0802020001a42,0x4020001ee3166c348619,0x4e040000000000018080,0x8080003016024e040002,0x117a820000a42c040001,0xc0580c3820803b8c40bc,0xb0b80800c863e1880002,0x4f04c84000200019,0x6d85b6100a4200db08,0x4702012d8402c0690b01,0x1008000436100000000,0x470207a106c2000100b,0x8036c38685cd1d161a10,0xc1000096c2db0b6c2db0,0x80202643d86200d4181,0x468800020166851c0dae,0x190ea08059a1b3420086,0x405dc099080000019080,0x3c100004050140400361,0xa0200174280990802022],#[0x59a17702ee05dc085d0,0xce8401dc08,0x60402908000004000000,0x41138186504000100009,0x3282c04000000000219,0x21000000000000803016,0xb21b2132100b,0x1808000000000301,0x83b41e60400000000000,0xda0d368217035b58b6,0xd5d8b981603b410ba100,0x664d850100009b420000,0x3c7428a25b14787a4430,0x5014040258107b0a0c68,0x1d41d414058080000d0,0x45cc0800051a16034685,0x9b0800000336edc1d977,0x5814072c200017117302,0x480a03de588020001407,0x404be898e7509361bc4,0xb01602c05016023a420,0xa0804b364835a0802028,0x407ce751072624066d0e,0x628e2c4014e073610000,0x12bf8898848b08ea1471,0xea10ea1004716283a,0x8bb61000000008b08ea1,0x3b613bc0a2b38a,0x30cf43f0367cd8400000,0x1618b080638100000d87,0x1000000ed862c32e7d07,0x89d080000000758690b0],#[0x832820001a8b04000080,0x80590d21b21bb4200012,0x2010080005808000290,0x8284d8a0e5f704341006,0x40290a5d0b0100602ee7,0x41d219a09722a42012d8,0xb60690d21004059eea,0x8068d08051a1,0x68200341000000,0x742974201b21b2100404,0x11b080558b0400009,0xb0d6c35b0ea0d2160200,0xa1000000000000602015,0x7361ad86b6100cba1cb,0x5ce0a0d0e5a1cb42014e,0x6125e080004000354e08,0xcc8802c856284011,0x1b210ba100d90ea0ad04,0x64200274200000000000,0x36434c083814072c3643,0xc841c083810000b21070,0x6436c0800000402c86,0x18100d41405668401642,0x25c0a028080403,0x2000108b052e04000,0x8000402000132140400,0xb604000000020001000,0x8059080000000521000,0x808059a1000ba100b210,0xa0b01000032100008702,0x2d8100870201a8b829,0x402016c08040337b2880],#[0x16cd0c00b78387420148,0x39b0e6c31b0a6c30e040,0x32c0c3818d84033618b4,0x3512b9fb41abcfb41f6c,0x8000000076c201a74306,0x19b0804a08018f062d0,0x77bc1a1d0c5a18b42,0x800045a10043a100fb42,0x1b604022d08074e862d0,0xd861c0c3816020000000,0xeea0bdd4100403b6100e,0x6100008702d1ec52cd05,0x83008b82106000e04003,0xe304128d0abc02c70c1a,0x1000000d4100000fecb1,0x860d0c9a10000d4100b2,0x20d0f381cb43068402c,0x280db0201037345ce04,0xcc080521b60690803016,0x16e0402dc0f3022e505,0x3011bc8228e0d086c2,0x802df5228e99a098080,0x20000000001ec98200cb,0x364201b6041c08040364,0x6825e4400000160201a4,0xa0a8d083c2ac6009958a,0x9a0ea0cd069820aa1629,0x201d4100e6c378440100,0x548ad81a9100000040,0x65e02830000804029080,0x39b0add0e6c3ac5050e0,0x83a1000040],#[0x2d84032d0c1a10000,0x5ba1000000000000000,0xb61000000000000000,0x6c86c840000000000,0x580800,0x8460c300000000000000,0x6ad159568b6d5a207bd0,0x8001d08000006dbd45b,0x40200010f44119,0x6170400000180800000,0x100321005a08016c2ae,0xc056e6510019086c2,0x8ab6100321ed6c587420,0x2b6100b3d34401283dad,0x3100000077a6200ad840,0x1934200016c0803bd,0xd34200774200000000,0xc08000138149e0e9a100,0x107a169a1d3436645c,0x82000001484020000000,0x193]]
def g251H7 := limbs80 #[#[0x1406522402051d413111,0x2110014201027214031,0x149062807000001020,0x642a6c000000014533,0x2a0000000f55c8,0x400047f34597ac400445,0x6400000c6a8400000097,0x19,0x194613800176270,0x3ec00046200000,0xd38256de908cf8b00000,0x3c8004d70f0004778,0x93a8e4584e44a,0x4892340027e00000,0x656564bc000000000000,0x188000000000010a2,0x6000000000018a36567a,0x24dab80000080,0xc48000000000000,0x21c800001180,0x1400036f00000000021,0x1250000000000000,0xacc000000,0x0,0x1b440000002400,0xc6000000000000000000,0xb80000061b06e284002,0x20020f800,0x1a00,0x2298000000,0xcd60b8000006cc,0x80e215a1800000000000],#[0x416000000000000194a5,0x49800000000000008,0x397000e918d126800074,0x30780000000,0xd9d88000004c70001cc0,0x5d800000000003374,0x29c800c8600000289,0x6380000000000,0x1af66bc970000,0x78200000000000000000,0x25280000000089e8d800,0xc080002f05,0xb7000000000000000000,0xc000000000022aab8000,0xf441d80026f00021,0x10300008e306b500,0xdc000000000000ec8000,0xc01d6700000088c00000,0x13400000b5a,0x282b7001a740040d0000,0x4ea258000000019ef,0x500030400406baab6800,0x55c648000002d,0x16a3228cd108392ecbf0,0x621000000006d3d14,0x28000000000052800000,0x2700003154,0x1cd94c8,0x800055422000c4a4a800,0xb540a0010e48109,0x40,0x10dd2400000c66000],#[0x2400000000000,0x1b372bbcb000d6c0000,0x0,0x187800000308,0x0,0x1504c002040000000000,0xc220022029f000003594,0xa000000047e000eb2a2,0x13e0000960000000000,0xce95b0e11b00,0x820015e00005e298,0xc000000000000000010b,0x520015232c5220013c66,0x91c000000002b40007d4,0x65fd682ad6ee63c7d,0x7800001aa3600000004e,0xccfaea698d800001afb5,0x8db72542000000001694,0x48c800000000000000a5,0xc0005b0000033a00085,0xdac0a0011a000000c762,0x20e800000003,0x30000000049200186000,0x4e000003370d4dc40061,0x33fc38186000006e21,0x45600000000930,0x36822020000000095800,0x12300000137c3,0x117000c32ac0000,0x9c80006145a0000077f,0x6175dd9,0x13c324000a959e0]]
def g251D8 := limbs80 #[#[0x485105d4645c86455054,0x54110509105051050110,0x58910585105491054510,0x5d5105c9105951059110,0xd9510d9110d89105d910,0x505204c520dd910dc910,0x58120551205452054120,0x5d9205d1205912058520,0x5413050930d9120d8520,0x5d5305d1305913058930,0x5d13159131d9130d8930,0x549405094019540d9131,0x58d40589405814054d40,0x5d9405d5405954059140,0xd8940d4d40d494099540,0x5d54159541d9540d8d40,0x4c5501d950d95415d941,0x5455050d505095050550,0x58950585505815055150,0x5c550595505915058d50,0x5d9505d1505cd505c950,0xd5150d45509d95099550,0xd9150d8d50d8950d8550,0xdcd50dc950dc550d9550,0x5855155151dd950dd150,0xd51515d9515955159151,0xdcd51dc951d9551d9151,0x5d9545c15459154dd951,0xdc154d91549d95499154,0x4c5601d560dd954dc554,0x54d605456050d6050560,0x58d60589605856055160],#[0x5c9605c5605956059160,0x995605d5605d1605cd60,0xd5160d4d60d45609d560,0xdc960dc560d9160d8960,0x59161dd560dd160dcd60,0x1d564dc961dc16159561,0x5c9645c5645c16459564,0x9d564995645d5645cd64,0xdcd64dc964dc564dc164,0x5ca545965459254dd564,0x5ca64d96545da545ce54,0x5434050b405da645ce64,0x5cb40597405934058b40,0xd9740d8b405db405cf40,0x5db415cb415974154741,0x597505935055350d9741,0x55351d93505db505d350,0x4c760d93515db5159351,0x54f605476050f6050760,0x5cb605c7605936055360,0xd4f60d47605d7605d360,0x5c3645cb6159361d5360,0x5d7645cf645cb645c764,0xb76bf9fe7d9ee779be4f,0xbf6fbbdeefbbaedb7ede,0xddf6fdaf5fd3f3fbfefe,0xeebafebb9fdff7edf77b,0xfbbebf7fdef73cfeffbe,0x38700ffbfdfeffafdfef,0xb0784100b830f8d51070,0x4af7564311381267d621,0xf82531d81571381b42f8],#[0x80b833f13812b1181900,0x6000b83662180672b84b,0x381ac5564a74f87004d7,0x79152079d64049d42041,0x6036b76079165076b720,0x776083f8208677208677,0x63f820a67720a3f86086,0x51417860e43800b5b740,0x7820f5b7412158614158,0x515821517821017860f1,0x218a9421891511815851,0x16518915418ab8218a96,0xb4386184186186976189,0x41b81641bab821ba9621,0x3851b69751b69741b836,0x41802017871c3783194,0x71a15872035832039822,0x7871d15871d59741d158,0xe1587213982214180211,0x1f17861e17851e6b801,0x7862791652317841f6b8,0x18362318162319d42311,0x2e6975319f84319d643,0x9752e99622e9b522e9f8,0x933862e31862e59762e5,0x43b41803b17873215873,0x7873315873a15873b318,0x415873c31843c41803c1,0x2d5975343382349f803,0x1842d35832d39822d418,0x515873551753515872d3,0x73851753873653817873],#[0x5873d31843d41803d158,0x71786365b84361782361,0x5375b84371782376b803,0xd64af6972af9d42af178,0xe6976af9165af9f84af9,0x6ae5976ae5975ae9962a,0x172b04380b03386ae318,0x63184b61787b01587b06,0x6b31785b35964b31587b,0xb87b15975b13382b1178,0x71787b21587b25175b25,0x5b51782b51587b73184b,0x16249935149915149178,0x94382496b72498362498,0x44981644993544991544,0x265499165496b7449836,0x98076499385499085499,0x64727824737834783764,0x7874a14874a258656278,0x82585583583584180581,0x25d37834f16875815875,0x9544543804515865d158,0xb71654b1687451487458,0x74b16874b14874b49764,0x16559637259418059178,0x91587594976592585597,0x65e51655e15845e16875,0x1654c8954463f8146158,0xa17874c14874c27854c7,0x55a71655a3d815a41805,0x5865f16875a15875a258,0x88964482782485b74481],#[0x6485376485176488b744,0x37657517657278648258,0xd14874d43804d2586575,0x55b41805b17874d16874,0x9806016875b15875b258,0x5265605165601582606,0x4e4b764e43804e15866,0x764e27844e27824e938,0x425865425845473764e7,0x75c4b765c41805c26875,0x583423982423d8142158,0x31687424976423184423,0x534b76532785533b825,0x782536382536082536b8,0x51785535385531784531,0x4611582614b765525855,0x586bd5176bd8964bd158,0x21787be1587be5974be2,0x4bf5165c01587c22585c,0x7837a1784c15387bf278,0xd1687891587894180893,0x7e15828e33848243807,0x9848c1b847e83807e438,0x915858f15848f4b758c1,0x78a41808a5b74793f817,0xd819043807f16878a158,0xb41808b16877c79647c3,0x8016878b15878b3d818,0xb82808380805b7480438,0x115829119828d7b74801,0x8753758143808115859,0x175763d8176537587418],#[0x85375881b86863b82865,0x3ca15849215829219868,0x784cf1782ce1587d2378,0xc1587d33f81c91785cf1,0x7cc5175cc5974cc7964c,0x175d43d81d44180d4158,0x1782d01b82cd1587d45,0x2401784d11782d11785d,0x785ba6576b86572b8178,0x91587b95175b91786ba1,0x5bb1782bb1587bc1787b,0x5806a3f8263677263178,0xb5f646b5d646b15866a1,0x2668964625f656b5d656,0x176c38964c315806c178,0x61787c41587c45974c45,0x961784c51780c51587c,0xb7493158596158496158,0x61784d61780d65375945,0x2738a86008986001785d,0x58673516573596473158,0xd27856d1586741582741,0x56d89656d33826d15876,0x182708b856d88856d8a6,0xf17806f2585723186703,0x4a715807517846f5b846,0x365a76165a71786a7596,0x76186a76086a76185a76,0x5a85d65a86386a76286a,0x384a65b87a53382a55f6,0x94976aa3184aa4976a63,0x5016185011785011782a],#[0x585a01582a0518202638,0x21580a243809b1582a11,0x4981580a33f819c1585a,0x1759753759e31849e338,0x453759f3d819f41809f5,0x2ad1785ab1582a41580a,0x782d81785d71782d7178,0xb1780da1785d91780d91,0x204b562041782db1780d,0x58207b76207b56207b76,0x7b58607b48607b78207b,0x205b16205b78607b6860,0x1620ab36208b16208b36,0x6458606a16406ad6206b,0x609956509ad620947860,0x1810bb7800b4586096f7,0xb47840b6f740b6d740bb,0x50b6d750b87650b85650,0xf760b6d760b47850b6f7,0x16d74116e870b6d870b6,0x5118565114584116f741,0xd65144585116f75116d7,0xd45821247820c6f65146,0x2136e870d6f760d47820,0x76118b56118b54118458,0x8b76418b56418b58118b,0x11bb68618b58618b5841,0x5611bb5511bb5411bb53,0xbb5531bb5431bb5811bb,0x41bb5541bb5831bb5631,0x5851bb5651bb5841bb56,0x96d76176d75176d7616b],#[0x61c47851c6d751c6d761,0x1641a4585206d75206d7,0xa47861a45861a6d761aa,0x51d6d751dad821d6d871,0xd75216d871d6d761d478,0xe6d851e6d831e4585216,0x41f6d811f6e861e6d861,0xd6222b68623b586236d8,0x4478622458622a16422a,0x22947822545842847842,0x56231b75231b55231458,0x1b75331b55331b58231b,0x531b56531b58331b5633,0x1532eb68531b58531b66,0xea1832ea3632ea1632ea,0x62ea1852ea3652ea1652,0xd762fa1642fa2862ea18,0x96d7639956539a164396,0x532a18432a1643245863,0x785326d7532876532856,0xb85653b6d87326d76324,0x630a1643045853b6d753,0x5863a6d763aa1643a6d7,0xc6d7633a164334782334,0x534a18334a1823445823,0x28534a18534a26534a16,0x56d76356d7535478235a,0x23d4586386d76386d873,0xf82366d82366d753d458,0x66e86366d86366c86366,0x5376d83376d82376f863,0x762afb562af6e85376d8],#[0xfb486afb782afb582afb,0x5aeb786afb686afb586a,0x186aea185aea365aea16,0xa164b0b780b0a286aea,0x5b08765b08565b0a184b,0xd87b06d76b04785b06d7,0x34585b66d75b68565b66,0x6b36d85b36f65b36d65b,0x165b1a182b16e86b36d8,0x26d76b24782b2a185b1a,0x5b56d82b54582b76d87b,0x55149b54149b531496d8,0x9b77149b57149b56149b,0x249b54249b78149b5814,0x58249b77249b57249b56,0x9b56349b54349b78249b,0x349b58349b77349b5734,0x57449b56449b55449b78,0x9b78449b58449b77449b,0x649b78549b58549b5654,0xd7643956543b48749b77,0x49565446f72446f76436,0x5479565476f76446d764,0x562476f76476d7647976,0x79772479572479762479,0x64796764795764794764,0xf724a967656957656977,0xa6d764a95654a47824a6,0x2586f725847874a6f764,0xf724f6d724f458758458,0xf6c764f95654f47824f6,0x64f6f764f6e764f6d764],#[0xe765d6d765d95655d478,0x56f625d6d625d45865d6,0x645a17445a16445b7804,0xe87456d87456f76456d7,0xb95544bad724bb5804b6,0x54b95654b47844b6f744,0x6764b6d764b85764b958,0xb45874b6d874b6f764b8,0x459af725947874b6e874,0x576594584596f7459955,0x6d74509554504587598,0x45e6e76506d765095655,0x5655e45845e6d745e955,0xe45865e6e765e6d765e9,0x45e6f645e6d645e6d815,0x565466e865e6d865e6d8,0xc95654c6f76466d76469,0x75a47874c6f764c6d764,0xe76516d7651956551458,0xf6e765f6d765f95655f6,0x548956548a1644845865,0x586486f76486d7648976,0x89576489476489582484,0x64895864897764896764,0x7804d967657957657968,0xd95654da1744d47824db,0x54d96854d95854d96654,0xd874d6f764d6d764d478,0xb47874d6e874d45874d6,0x25245875b45855b45825,0xc7652966552956552478,0x26f76526e76526d76526],#[0x6606d766095656047865,0xf65606d65604586606e7,0xe47844e6e86606d86606,0x24e97814e95814e6f764,0x7834e95834e97824e958,0x497764e97844e95844e9,0x44245875c45845c95765,0xf8253ac8253b78053458,0x3978553478453478253a,0x1536d81536f765347855,0xd83536f82536d82536f8,0x36f84536d84536f83536,0x5554584554582556f855,0xd84616d8161458461458,0xe6d76be9585be9565be6,0x2776d84c19584bf6d87b,0xf75776f7277876277856,0x86f72788762788562786,0x27a87627a85627a6f757,0x7867a6f757a47827a6f7,0xd45878945868947877a4,0x57d47827d6f727d85627,0x7628285628247857d6f7,0x24782826f72826d72828,0x58e4785826f75826d758,0x5817e85647e45858e6d7,0xc85847e85747e85547e8,0x48c85738c85538c85438,0x564836d738385758c855,0xf6d738f6d75836d74838,0x18f45858f6d758f45838,0xd638f6d538f6d438f6d8],#[0xf6d658f6d548f6d838f6,0x379a56379a753796d858,0xf7579a37479a15479a57,0xb4587794586794585796,0x47b87647b85647ba5637,0x5648a45877b45867b6f7,0xa45848a6f748a87648a8,0x47f47827f45878a45868,0x5657f47847f6f747f856,0x4b7808447857f6f757f8,0x48487648485648447828,0xd75844784846f74846d7,0x6d75904785846f75846,0x37c47827cb5807c45859,0x6657c95657ca1647c478,0xc6f757c96757c95757c9,0x77c6d877c47867c45867,0x5658b47877c6e877c458,0x45878b45868b95758b9,0x38085828086658085658,0x58580867580857580858,0x586758d85758d8685808,0x5914583916e75856d758,0xd83914585916e75916d7,0x16d85916e65916d65916,0x4814783814782816e859,0x587874584876f7581478,0x6af8286ac8286b780864,0x68647848647838647828,0x58688458488478686878,0x76d83926d81924583924,0x5c86d72c86d75c76d72c],#[0xd75ca4782ca6d72ca6d7,0xf6d53cf6d43cf6d81cf6,0x3c96d84cf6d54cf6d83c,0x585c96d75c9a154c9a75,0x38564d36d74cb8564cb4,0x3cc4782cc4584d36d74d,0x582cd6d87cc6d75cc478,0x8685cd8585cd8583cd8,0x5d06d85d06d83d06d82d,0x7822a6d84d16d81d16e8,0x147823e47803e45822c4,0x5ba6d65ba45824145804,0xe86ba6d86ba6d85ba6f6,0xc6d87b96d76b94782b96,0x2646d85bb6d82bb4582b,0x58069478065458268478,0x56d80c56d87c46d76c44,0x5966d80966d65956d84c,0x780948582936d85966d6,0xe8582d56d84d64782944,0x46ea1646e47826e6d726,0xe766e6d766e95656ea38,0xd95656d47826d47866e6,0x26da3806da1806d6d766,0x3856da1856da3826da18,0xfa3846f47806f458272a,0x716f846f6f806f6d806,0x182a56e86a76d86a7458,0x96d76a6a185a5a165a5a,0x3996d72996d85a96d82a,0xd72a06e75996d75996d7,0x6d75a06d73a04582a06],#[0x3a06d82a04585a06e75a,0xd85a06e65a06d65a06d8,0x16d72a16d729a6e85a06,0x9bb7809bb4809b4582a,0x3849b6f739b6d739b478,0xb47859b6f759b6d759ba,0x5a26d75a26d73a287869,0xd85a26d65a26d83a2458,0x84582a347829c47809c6,0x29d47809d45809e47849,0x582a445809fa3849d478,0xd6d86ab6d85ab6d82a44,0x5d76d85d76d83d76d82a,0xd84d96d83d96d81d96e8,0x2000006d84db6d80db6,0xd000b7008f006600480,0x18a01630142012300fd0,0x21601f901e301c501a80,0x2c802af0284026402400,0x371034d0328030402ee0,0x41403f203d803bc03950,0x4c4049c047a045304300,0x57505510534050f04e60,0x633061305ee05c0059a0,0x6fa06c90696067f06600,0x792077f0757074407270,0x81b080d07f107d407b30,0x8c0089e087d086008400,0x98209520928090508da0,0xa0d09eb09d709ba09990,0xad30aa80a7f0a560a3a0,0xb640b4f0b230b070aee0],#[0xc210bf50bc10b900b7b0,0xcd20cb00c7c0c670c4b0,0xd7f0d5f0d290d080cf30,0xe020df50de10dc20da00,0xed40ea90e7a0e4f0e210,0xf910f660f440f230f060,0x471026100e0ff10fc20,0xdd10c210a7107a10621,0x19711721149111910fa1,0x26a1245121511ec11b71,0x30a12de12c712b512931,0x3ca13a11382136313391,0x45c14431426141813fb1,0x50314de14d014a614811,0x5b6159a1572154515201,0x68b165b162515fb15d71,0x74a171516e116c916aa1,0x7f217c517af178717691,0x8901870184d182c18101,0x927190c18ec18cb18b21,0x9c719a6197f195a193b1,0xa881a571a341a1119ec1,0xb471b251b0a1ae01ab71,0xc051be01bb81b8d1b6f1,0xcc11c941c781c5a1c2b1,0xd631d4a1d251d041ce31,0xe1d1df21dd01dad1d8c1,0xec61ea71e8f1e6f1e491,0xf681f491f241f081ee51,0x181ff51fd81faf1f891,0xd520ae208e206820422,0x19221652140211520f62],#[0x2412226220721de21b62,0x2f322c522a82280225b2,0x3a923882364234423182,0x464243f241123ec23cd2,0x51324df24bb248b24772,0x5b2259825722554253e2,0x675264c262925f925d72,0x72c270b26e526c326a12,0x7dd27b52792277927572,0x8652840282c281527fc2,0x8ee28d828c628a928892,0x985296f2946291b28ff2,0xa322a1029f029d529af2,0xadf2ac22a9f2a722a562,0xb5f2b462b2d2b142afa2,0xbf82be02bbb2b922b762,0xc832c6d2c4e2c3d2c142,0xd292d042ce12ccc2cb22,0xdde2dbc2d962d722d4a2,0xea52e7d2e592e302e072,0xf682f442f212ef82ec42,0xfff2fd52fb22f942f832,0xba30893063304830222,0x159313a311a30fa30db3,0x21731e631c3319a317a3,0x2d232a93280325a32343,0x369334c3326331032e93,0x3f733da33be33a433883,0x4ab34943466343b34143,0x544351b34ff34e034c43,0x5f535d235b53595356d3,0x699367f365b363e36183],#[0x7553730371836e936b93,0x80237e037cc379b377b3,0x8bb38973873384738223,0x98f3965393b391138e43,0xa2d3a0e39f539d739b33,0xaed3abc3a9a3a753a563,0xbba3b953b753b473b1a3,0xc7e3c5a3c2d3c113be03,0xd223cff3ce53cbe3ca63,0xdd83dac3d863d6c3d4d3,0xe863e603e443e273e093,0xf433f103eee3ec73ea83,0xfec3fd23fae3f8a3f673,0x8940694054403a40103,0x12b411140ed40c940a94,0x1a0418c4179416641494,0x21141f541dd41ca41af4,0x27c426d425e4244422c4,0x2ff42ea42d042bd42a74,0x38d437a435b434043204,0x40543ea43d743c143954,0x47c4465444c443344204,0x4f144cf44b9449d448a4,0x5864566454c453245144,0x5fc45e245c945b4459b4,0x6824662464d4638461f4,0x70646e646cc46bb46a04,0x77a4766474b473647214,0x7f747dd47c547a647934,0x87d485c483d4820480c4,0x8e648cf48bb48a7488f4,0x969495a4942492948fe4],#[0x9f749e349c749a6498a4,0xa644a4e4a384a224a0c4,0xae24acc4aae4a904a7a4,0xb584b3e4b294b0b4af64,0xbc94bad4b9c4b8b4b724,0xc554c3c4c244bfe4bde4,0xcc84cb04c9a4c854c694,0xd2f4d194d054cf04cde4,0xdb84da14d884d6e4d4f4,0xe2e4e1a4df84de44dcb4,0xe904e7c4e674e514e3c4,0xf0a4eee4ed44ec24ea94,0xf844f6b4f564f424f314,0xff14fe04fcb4fba4fa04,0x5e504f5036501c50054,0xd350b6509f509150805,0x15f51415123510d50f85,0x1ed51d751b8518451725,0x25052375225521351ff5,0x2d252b3528e5279525e5,0x3495331531b530252ec5,0x3b4539f538a5371535d5,0x40f540353ea53dc53c65,0x47a546154535439541b5,0x50354e054c354a054925,0x593557a5551553a55175,0x60855f455df55cc55b05,0x6835671565b563d561d5,0x717570356e656c956a65,0x772575e574a573957285,0x7f557d657b3579757865,0x872585d5843582558105],#[0x91658f158d158b458965,0x9d159ae5986595e593b5,0xa4c5a335a285a1859f05,0xabf5aac5a995a805a6c5,0xb435b1e5b035af05add5,0xbd55bbb5b9f5b7a5b5d5,0xc4b5c435c2f5c195bf55,0xcc25cad5c935c7f5c695,0xd315d1d5d025ced5cd85,0xdb05d9d5d825d645d485,0xe235e135e005de45dcc5,0xe745e6c5e565e425e305,0xef35edd5ec35ea85e8a5,0xf535f405f2d5f195f065,0xfba5fa65f935f7c5f655,0x34601c60005feb5fd65,0xae608b6076605f604e6,0x1426127610860e860cd6,0x1b4619e6183616861526,0x228621b61fb61ed61d46,0x2936278626b624c623a6,0x30562f062e362d062ae6,0x36c635363416328631b6,0x3cb63bd63af639a63866,0x428640e640163e763de6,0x47f646a6457644f643b6,0x4ef64d064bd64aa64966,0x554653f652b651d65086,0x5b865a26591657f656f6,0x62b660665f265d765c96,0x6a06685666f665766436,0x70266f166db66c566b46],#[0x77667606747672f671c6,0x7dc67c967b1679b678a6,0x861683b6826680a67f76,0x8bf68b2689b688a68766,0x920690f68f868e568cd6,0x981696e695f694769376,0x9f269d769bc69a969906,0xa596a3f6a2a6a156a076,0xacf6ac56aaf6a8b6a6c6,0xb3b6b246b006aed6ade6,0xbbe6b9d6b866b726b536,0xc596c346c146bf86bd86,0xcd76cbb6ca56c8c6c766,0xd456d376d246d026cf16,0xdbc6daa6d906d756d676,0xe486e2c6e056de46dce6,0xec66ea96e926e776e616,0xf3c6f206f0f6ef36ed96,0xfd46fb96fa36f7c6f626,0x6e7060704270216ffc6,0xe670c970a87091707c7,0x156713b712c711270fc7,0x1f871d271ba719671707,0x27c72617242722872127,0x31272f172d772b7729d7,0x3947379735e734173277,0x41a740173e373c473b27,0x46b74627455744874387,0x4c374b374aa749d74857,0x5317520750374f374e47,0x5ab75987587756a754a7,0x611760075eb75d975c47],#[0x690767d7658764b76397,0x6fa76d976cc76b776a57,0x77077557747772e77157,0x7ec77d577c477a777887,0x859783e7830781577ff7,0x8d278b7789c788978767,0x94d7937791778fc78e77,0x9c879b27996798179667,0xa637a3b7a2079fa79de7,0xac57aab7a957a807a6b7,0xb2d7b117b017aed7ad97,0xbab7b8b7b727b5c7b4e7,0xc1c7c007bec7bcf7bb97,0xc8c7c777c627c4d7c387,0xcef7ce17cc77cb57ca07,0xd6d7d507d387d277d0d7,0xdee7dd27db67d9a7d7e7,0xe557e417e2d7e1a7e067,0xece7eb67e977e837e6a7,0xf3f7f2e7f1b7ef87ee57,0xfa07f8a7f7a7f667f557,0x87ff77fe77fd27fb47,0x6b80578049803a80218,0xc580b08097808b807a8,0x11e810180f380e180d38,0x1808170815b814181328,0x20981e881c981b881938,0x28882788262824582228,0x30982ed82d182b082978,0x389836c8351833b831f8,0x40b83f583df83bb839f8,0x493846e8455844284278],#[0x4f984e884ce84bb84a68,0x56b855a8540852885148,0x5d085b985a4859485858,0x644862b860e85f185df8,0x6b58698867c866386568,0xc81b09c0801f0086d28,0x2182e08001835820cc03,0x8008f064060350da0842,0xc03a60d00a0c4108c05,0x83c02e0c1104d0fa0581,0x5c2d0b3010240f41482,0x3a06010360bc311102a,0xe0414600840400021487,0x41e024101861a0440829,0x540b0a205c188883883,0x20499a190606b020f490,0xe0a80088244430d43908,0x4600a11618c12014040c,0xe20807609c0c398403c,0x9443445090d30520016,0xc429080d19a1590c2517,0x23a19a1097c398544c21,0x82a174543f0d5030fa1c,0xc61148461d6660bc3d1e,0x63380a3c916110b26092,0x8568e718650dc40a388c,0x4c19b25d306445910bed,0x2941ef59aa35a396bb97,0xa77510bdcb86088d6787,0x28741e999583e983233a,0x5b64c974c1911a15c704,0x434757051525e1b0989e],#[0xe718668f9e5393d99aea,0xe0d8a4a8668e71865e68,0xe0b547b27085872941d3,0x9fe41b65a88672366f76,0xb09ff7accb510cb7ccd0,0x608387b0b83f7f652410,0x6587c6083eedea6d941c,0xfa13b97097033776d413,0x790468756429e86a7776,0xc0b232f7f820591997f8,0xf17d6f208f6dddb838ff,0x67eedaa7819a28f1f208,0x267e1c59196bcfebd602,0x459c40ed577249a9feb4,0xda02c61a2bbb318155fe,0x1d9c29fb6839bcd0d6fe,0xf47621e8bea28645d892,0xc272129e414469d412b3,0x881cc0b6487cc0c420be,0x45d78665b42c3023cb9e,0xff0ad088fc56839fcc74,0x9254c7445878315a111,0x8249afdc29aca38d7a26,0x8d7fffbc2001217eb709,0x57c3489d1ff1a508dc2d,0x630050dbfeec123425c1,0xfa55e091e83e0d931f76,0x17e1006607831489c28f,0x45a22c40d12cc2792c7d,0x495da1f788c3646b3efc,0x1ee55328755da196732,0x5cccf10fe8bd16cad10a],#[0x2b2063fc811acc9f8669,0xffe80e40449513c14798,0x25781045967f5d82465f,0xe4558cd0beed82472bd9,0x7408b2ed5f8d22d7f2eb,0x47abf869145fb49a842b,0x48bc903f0bb9172c3776,0x81a1a9bebc8833efed7c,0x9a6fad9030cec9f35e24,0x380720d937fffd264044,0x4419e7f5d8246deb6c12,0xa39fdd5201010ed4df5e,0x20ebd022c9dfda988011,0x8eb86913afbb6091f18f,0x4e41e7fb4118099f21b5,0x91a3f132c97b5489ede,0xb0cdcf5ad5c80d0ebfb6,0x98c237f50c1996adfd43,0x66637dc20b51c74468dd,0xc1fe2936d76ce09fd430,0x2c6bf141819e35f92c0c,0x21a2ef51660c5de05c03,0xbff1bc2001245a34d028,0x22bf068326f1ffd8008f,0x1a235f8a0c0cefdee60,0x1e022fda013a7fe39890,0x7e8c085c630c1f7c1819,0x3ffb0011efffa10051a4,0x42013dfff4200a0e03de,0xc88902d0d7ffd08028bf,0xa6cd7917bf06c39999df,0x8b3a7f5a0b32ac9e0791],#[0x69ffe30b1d0d1564d121,0x7c0b723436717110343c,0x8aaad0197a4abf01b919,0xbf9f924a822d05f97e32,0x42b30cc5ce8a87467918,0x26a36d0d99ab1961f90,0x665a7dc6838eba05939e,0x7864651f598e88c1c766,0xb42079358e3fb44d6588,0x4e874451ea8744677d42,0x763e411c7af7a2293b41,0xdfbb811813c8ba6b30c,0x8d3f4480248bf3bda014,0x125ac79ae04613fa5c0,0x776f8640026815d2cf74,0xac195611675d2cfd0024,0x6033acfd7408d4dd820e,0x283049239c0ea2f7b395,0xba4228dfea6802485f7c,0xfa00024a61d5a80cc7fe,0x79796883a6d0ca1175e7,0x2f749be0cb1fd24eb406,0x8310a92ff1a45497f8d2,0x9a1ffd023879358f1c5c,0x4653f84348dd2cf10651,0xd0d1f45f8401994ff252,0x22f6841fc0cdac1e5600,0x110e49420663b185ff50,0x40642e05ed4cadfe0199,0x2ea5ecc9df38266660ef,0x24747c629acc1c65a665,0x8f77ed226dfaf7081],#[0xd8b99a3e30c00d675fe1,0xe43489cffe4452292e15,0x757bb048f6e1e131a14f,0x28613fad00d0c11c5a99,0x957c3d0e7ec917ff8242,0x19eacda0c9a943feeb01,0x8ba0e50520c277a03c30,0x470e3c8203313f35064e,0xebc901c719641e3eab30,0x490fcab2b32af87a18,0xf9a85e7f056845e7f040,0x87b52acbd2ce566580a0,0xcf3f3cd82474ffb1cc85,0x2ee7254b337715974fc0,0x708b51983b4234c11276,0x5d23800034d32d2e042a,0x64b9d0c7fbf2c0124456,0x9a83e87e9901997ed824,0xbd740123cfabf6091c9f,0x86dec0cb8cbbbd01810f,0xc2398c0cfd0f38248676,0xd7ff42013dff9144501f,0xe669f04c123f6b4c10ac,0x7907d0e30f32d7ec1e72,0x815fc28cc3eb06091c19,0x8e8887d292597132d088,0xf208fa355dd685576821,0x839d26c90e0cc30997b1,0xcb6913f458827b24e0d8,0xc670f4a1a7fd5a000249,0x2397bfe0b2ccc87f517a,0xea44843ba7c4abf15cc9],#[0x9bfd3181949f83168487,0xb2c67ac82b99a2fc3489,0xf06913bfe4c42233ea92,0xebdb2c72b9b44765f20e,0x1e6b00d1574da24b5420,0x63bffc121140ffa1e609,0xb7f419166ce5ce648eb1,0x3acec8884785a12b2c49,0x84357f620c1f2d2d2e04,0x3fcbd82472ffd180caab,0x95102bf851997ddb048f,0x24695f63e411ebf86191,0xe9436ea35e801227f5d8,0x10ca52f11a0067f58ce1,0x89d08cdfd3500cc1ff54,0xe6675ffd7e1010249c5b,0x96a658cfaa4acb19eb4a,0x40286f01de45227887e,0xfd0180090bfc20011efd,0x17f98312147ff600230f,0x190e9b7e941b2c398183,0x1b24f03cd118dd3cc081,0x57ebd1147c5891193e04,0x911b78f0488c37939118,0xab4b2a7dd2554d987ae0,0x3f41a7f0f84f2319fba4,0x7dd29199b5f74a466e7c,0x2bd4070dcd95ea03866d,0xa2ae922ec8cdb75a8b9b,0x1c7c86417caa022174d6,0xc74441fc344587d32d08,0x1a22aff0d1167a1d1147],#[0x990624348e73874485fe,0x1d6a29f2a27e3d1221f6,0xbc74456f86464c2adc1a,0x6ef4ddbc4334f5fa222e,0x9df2fc584cdde9bb7886,0x86889daff3147ef03110,0xcb3164664f95792cb7ff,0xc1dff901114953da9913,0x514c30cf81186acaef41,0xf963076fb02c910e1f5f,0x6dedc10cd18c35186608,0xffd30010134173b1732a,0x5d91967f5d8246a68828,0x71c4c12447a45b699bb9,0xaa97a9428aa97a942efd,0x7ccf2eb482e838752b30,0xdad52b3c0176b54ace23,0x3f32b2c0274b54acf005,0x7df9b5321683f32b2968,0x8c254cc9f187992ab96c,0x3f8d34ca9f1a699003f,0xf8f10424268bff08489c,0x3b56219d3a61dab10cf5,0x132129d30e583433a74c,0x4b45919afff0844507ff,0x2da44f2eed84e9be878f,0xd45d5a177fae00104927,0x199abe98e34f0d04998d,0xd62432fbab90745fbe42,0x23c2d0950d0ff4199fbf,0x249debfb6091fdd5c834,0x5fe3104242689fac5e10],#[0xd226be0a9145f082451,0x9fd76091932f316466bf,0x91a3e6fa09334f2f4246,0x2bbfe4401802879fd760,0xc216283870b2ca8e7084,0x412e0e9d2b0c2169d2b0,0x1b0d142167451ef1085a,0x8a3dab094d382a45c20f,0x84ccdb6384ca9e2384ca,0xc794891f9a384cd1f9a3,0xdc98a2cc334715c7ab26,0xba932338197a82ee4c5,0x6cfc4107aa7d07dc98b,0xe045fa283697d63b7e85,0x6eb1bb37ceb42866702c,0x422ae90c58be83ee4c55,0xbf4283f7e80084d66fc0,0x6850c01dc9895d85f425,0x8993b93155bac6ecdcb2,0x7d141f72621d0f48905e,0xc989b614c64c7afa283e,0x481bb28b270448b2707d,0xc16d4b8488f1a6ecb5f,0x9bf60f9939f088377416,0xdb07e4782f2bcc1cde28,0xc1b74ef4b65249e60fd0,0x60fd9268345e4782f2bc,0x3a113dca83ea7b2d91bb,0xa8a0f7ec3f516d82e839,0x85dd1419b8a08dc505cf,0x33d16b931574c18fd8a0,0xc431a7ec0c75a60c73c9],#[0x552650927180a386082c,0x37c031e74c5ef292a84f,0xf018d635a1cb0c1530c1,0xcb68ec76f3c9e81218b,0x65909fd7050926865972,0x112cf7c192c67c210bf1,0x97920a5e482b59c173d4,0x920a5e48297920a5e482,0xb43b1384212c4e108497,0x68642c2591e081860b7c,0xd3fae63b59ca0fc0f05,0x558d5462b420b91f336a,0xc9a02177c55ed171ab05,0xbe0871c23630d8b6367b,0x631add0c5c1051e6a0c9,0x722743ac1886b7430e19,0x3247100cb2cdce86b908,0x864f5e83d55820e38578,0xcf0624f0cb1d7962d8f0,0x482a6057210c25e89d65,0x835c8439b3a18d5e86ce,0x82083cd18ab02ec76f60,0xc48f149a02163cd41929,0x3de4c221cd09365d0ebc,0xe417658a3c0b6307d808,0xb63d8f086b9087d96207,0xe60d18e9156d858e3c0,0xd05903f29226c2a3425e,0x687aa343e793d0242972,0xc132dce108cb738426f3,0xe3e01d1386685f90b18,0x312fc84c37c1647f4164],#[0x61417aa2770c491b117c,0x716019bbb4c70e1fa0fb,0x863d55820e385783257d,0xab10899ed31d71c18ea9,0x50dbf80c7262879e0c5,0xb618bd50d38628a7a1ef,0xd6fe032190ea0a0bd513,0x1512b8e0c67816305506,0x884d1a1e21bca43c0a4f,0x5ab2f09c146516b76583,0x2c449a5e91a7f90c03f5,0xd3b564a897ab2765c58e,0xc343061821c721e3182e,0x7c13b0b5b09e9aaf3083,0xcc5959b60f7b2f6cc44c,0x1a65fa99225870c81e14,0x4d8a22c527425f21618a,0x8f227558b0ee08a74923,0x7cfba8a13ce4193522f1,0x191e64d466e282e7d450,0x1b6f0a6d94dc50523714,0x8764c9debb2646f0a6d9,0x37068859b9b83442cc1f,0xf3c7408859b3d72d5b2f,0x9ce26c421767eb0e8d1,0x2d23cedc102b66e7132b,0xd82ae73d6654c7931d21,0x32e5b62ae4c5eea283d4,0x5d93265b622ecc59accb,0xac92e1841e73e3ec9973,0xec6522a7907b099a3f36,0xb26cadfdf64c8b23d222],#[0xb2300438416f7c865f20,0x9d7b1ae521c784c73723,0xc8726ea28f9493567044,0x6eaec79e0c4af6820d6b,0x5f7912bf4986413f5e44,0x44c706399438452ecc4b,0x62eb0ef2157d23cc2d66,0x9a3820037fa099860a3d,0xe23418fcde44afd26193,0xe3056c60a0ea1c1da4bc,0x1bc891eb115362b6304c,0x81127790f6321e5b6635,0xa17264276926b9a086bf,0x318f9081f06830f2663e,0x211ce291a526b9a09bcb,0x6cc2084a7c49074fb89,0xa2e841d9241a6bf3464,0x2099ea241895978347e2,0xb03986163cfc1ab64c79,0xe18ab862301f7e5b3324,0x20a4ea83301d09c9284a,0x90f235e6e80d1aa89c3,0x2d257014610c7a7e435a,0xe5c46832714c1afc847b,0xa121c063818dd50c7190,0xb72020d6835fd331806c,0xba08bb31006783177962,0xa474cc8c7850cbc73183,0xc982c68841af378345bc,0xc8a831d721e18a1ac06e,0x80e18e86466e91a9d08b,0xb5750ddc40c1da453e42],#[0x321c1779f31c534e4c19,0x4357a4106972d12e2422,0x8473f028c70863d42981,0xc79b31ec643dcfd91362,0x1d0a870931b3824d83b1,0xa4583a86de80c687f21e,0x9d81536e8592393149ec,0xb3c8c1db046920c9842b,0xc61b08d047fb21e1d0a,0x631f2145fa43d8c86de8,0x50c99137bf31a781f72a,0x28384ec5ea2983264530,0x54c0a3a60b9f5141f3ea,0x2ec48c12c19b8a08dc50,0x31b53f48032c7c7b2640,0x654fcc470889c08055d9,0x2717bb189c2a2ac3b62b,0x509d8058f5360adc8d14,0xe5bdc284caf8993dd906,0x3e265eeb0c265e87e064,0x84427c208b6a60c850fc,0xa0c1abf50418c4e87b9d,0x86b626f86165954e85aa,0xa3a8a1b0e1d0555495b0,0x10cb9620f5899f048391,0xf1b6240ccefd364844be,0xd724c773a4254bfd8446,0x9de6c90757128aded241,0xb125fec2256dd0c81d18,0xe9e9c4408507bbd83e8,0x87f51711c9cc085f724a,0x654727f44085a7c4906],#[0xfc8191d278650911d72f,0x138144ce482a60698128,0x97d0fb8356c86c356084,0x221c2257b020e2c7431,0x5de1ea15855592e0e7fd,0x2856173e2d8fbc7e5919,0x448303068b3f2063e23e,0x5842780306dfbf8193de,0x9b67724207e68c78ea82,0xc3820ab87440cb6fa0c1,0x2fb020cbe7c0c9afb041,0x4be08d3fe606407e1106,0x5d8106de56832534dc88,0x5c04b41d8426f2b4193,0x10056825ec0c60e89418,0x23b019c224fc320328ea,0x2100d7089996248f15b,0xf423ccb147c61992dc9a,0x1a1862c438d43de4c225,0xa64659630e40cdd962d5,0x430e8c43d7e3a0468b0d,0x80cb1615e1a1862c43d1,0x98ebcbcc68b3820faa5f,0x8eb1632f180c81b097d7,0x67604932a051cfdb7845,0xc0d06558b18f6431fa08,0xa30e40c8afb020c36157,0x5141f3ea2830e8c51c98,0xbba283371411b8a0b9f,0xd38e4c75d931c3820042,0x8e3c2d1919c9056f6920,0x82141eef60e29a638b61],#[0x3fa2042d3e2483823f99,0x1ea860e5826724100239,0xd05ba086be087ec5041c,0xc526d091a474c956476d,0xe22c5f15113aa63ac8b1,0xd0b9322754c75912f9b8,0x378628337862833eb234,0x71411b8a08dc5046e282,0x5d31ede8514f43dbd433,0x6305506d0a7f3276c2de,0x4c4df94a64863583ad31,0xe8a0f5978a0f5978a0eb,0xbf989bdf98ddfe8a0ddf,0x42f05c27055fcc49f98a,0xe408b842628c16107d8e,0x10a4f6b04270a883dc98,0x54f2920748f194115faa,0x434b928b2d0b0c50e30c,0x2781eb260bb4f01641ae,0x6c8a926b07d5fa6393a1,0x990cd5081c0c69b11e04,0xc41b09e04aea82c6a841,0x8a34d89bd974c9db0974,0x624f039e2a1d7f5cc64c,0x2d09d962afbd30a32d79,0x95678a884e0c8a84d7f1,0x4ea98e5f88d075de9851,0x9c46849b8e221b224f03,0x54c78701547ce9d507ce,0xf294c8876d161ca151a7,0x7aeeb27dbd445c21964a,0xd6a87171d157df98a32d],#[0x618d8a1a61c1a3059c18,0xe1f413b77cc12153cb4c,0x9a62ed3e98c3a310e950,0x831f244477082e680f07,0x32e44dfa431ec5099aea,0x311b220f74c6ce8824f0,0xa31d78d2992bd4b4c89c,0x4644e3931c58697238c3,0xf3ec1cc8dfc5a648f0b,0x13c]]
def g251H8 := limbs80 #[#[0x11132003100000000010,0x30000000010110000000,0x4010022216021011001,0x4000000,0x10200000300000208300,0x1010000204100001001,0x1000000011031,0x101200000300000050,0x10000014302300011000,0x40020043002000110020,0x1000003100001000,0x200120000101210000,0x30131110101000111,0x3000002001002000020,0x20110000020000100012,0x100000003020010001,0x20100000001100002,0x100123010000001000,0x20001040010000211022,0xd5000001102011020010,0x24430000000000130,0x8b1c000,0x0,0x20fc000094b00,0xb020000000,0xd4000000000000000000,0x134400000030,0x0,0x32400000000000000000,0xc,0x803c00000,0x0],#[0xe700,0xc00000000000000c0480,0x12b,0x347a00033cb,0x7c000000000000000000,0x21800070,0xb0280000000000000,0xc4c000000035000000,0x46ec0,0x3f9000000,0x380f00000000000000,0x0,0xc0000001837000247800,0xc0680000000000602,0xf3800000000000000,0xc9580,0x82800000000964a53400,0x3b35,0x2194000000000000000,0xcc9364000533c00000,0x0,0x380000000000107d0000,0x30,0x0,0xe5c000,0x0,0x1204000000000,0x300000000000000,0x0,0x0,0xe7b08190000000000000,0x3c1344440000000000],#[0x2190,0x9520000000000000000,0xc3300012c34b88000000,0x3bf900000000001,0x0,0x0,0xc6e40000000000,0xd048941b929800000000,0x2396000000093,0x45b00000000000000,0x21be0000,0x0,0x0,0x0,0x12540000,0x1e4000000000012b100,0x0,0xb2300000000000,0x710c27b00000,0x0,0x861025d0340000000000,0xb40000000000c4bc0008,0x4680000000f1e8000c4,0xfa81c40000000000000,0x2,0x0,0x51400,0x0,0x50000852400000000000,0xcda8000c0,0x0,0x0],#[0x302e438000000000000,0x0,0x30ea,0xe5c000000000000,0x0,0x41e0000000,0x7013a800000000000000,0x80000000000124a0d710,0x149f0000000000045,0x11ed00000000000000,0x3122000000004e40000,0x81000000000,0x0,0x9700000000000,0x8f1c00000000,0x39622facbbb20e000,0x0,0x0,0x800000024c241d000000,0x40f52a00decf9c000057,0xc7b8000000027d0001,0x1477490800000000,0x0,0x2c2c00022d3,0x50cd1de00000000,0xa330225868400000,0xdb80000000000000,0x0,0x6028000000000000000,0x4a4c000a1df3ef000000,0x4cc0000000000,0xbc000000000000000000],#[0xd28838f08,0x0,0x0,0x60000000000000000000,0xc27c0000000000000105,0x0,0x8be000000000000,0x102318c00,0x343e000,0xcb4a9c00000000000000,0x24,0x4ce617300032d7000000,0x3d000000000000000000,0xc,0x0,0x52c42470000000000,0x0,0x90000000000000000000,0xb0,0x337d000118900000b7,0x2051000000000000000,0x3f7000000000,0x0,0x81d8,0x0,0x8d8000,0x42f80000000000,0x934000000000000,0x0,0x311000,0x0,0x0],#[0x0,0x24c90000000,0x3415e3f400089938be0,0x21460000000000000000,0xbb00000000000000,0x255638900000310000,0x50b91ef000000000000,0x34fe000000,0x90ac0000000000,0x1314000000000000000,0x0,0x26800000000000000000,0x1bd15c8a840000003,0x40000000000000000000,0x30a,0x24f08e940a20000000,0x116f0,0xe67c0004aa1ac100,0x0,0x0,0x0,0x0,0xbdc0000768000,0xc7dc0000,0x8000000000000000d700,0x4ce,0x0,0x0,0xcabc0000001985000000,0x0,0x0,0x80000000000e35800000],#[0x8fc00000000000419,0xd16cf80000a1e37b0000,0x30,0x0,0x1024000,0xc30800000000000,0x20d6000000000,0x918000007a0000000000,0x4463,0x0,0x0,0x0,0x1285cef34a500000000,0x93e4000000000000,0x49c40000000000000,0xcc8c0000000,0x63fc00043cc00000000,0x0,0x0,0x48000d03800000030290,0x339e0000000d1,0x97ac5c29f227fdb02000,0xd800000000000001,0x0,0x0,0x2f280100000002482,0x0,0xa0180000000000000000,0x4ab,0x10d00000,0x244100000,0x0],#[0x0,0x0,0x911400000,0x4de40000000000000,0x63f8,0x0,0x2594000000000,0x0,0x0,0x504800000,0x28f00000008d4c000000,0xda8d64000c1c80000000,0x13,0x0,0x246500000000000000,0x0,0xc0000000000000394e00,0x4c0,0xa20711c496c0005138,0xc2b81e616200000,0x87840000000000000000,0x38a53d80000000000,0x5505000000000000000,0x348ae7,0x0,0x1200000000b200000000,0x11b4000000000000002,0xa46c000000000,0x3560000000,0x0,0x3101000000000,0x11ac0000000000000],#[0x0,0x104500000,0x1199000000,0x0,0x5436500000008f904e10,0x21,0x248f000,0x217c00000000000,0xd0180,0x0,0x0,0x0,0xd2a50000000000000000,0x22780003364481,0x0,0x3260c48c00000000,0x0,0x31dd00000000000000,0x227a0,0x9134000000000000,0x1295a818000000,0xe2a0,0xf0000000000000000000,0x207,0x0,0x22ee00000000,0x1df0ddc000000000000,0x0,0x4da4000cf100000000,0x0,0x0,0x34af000000000011a3],#[0x8a6c8d00,0x31524cb8000000102100,0x2972000,0x233e00032920000,0xb380,0x2436000000,0x174000000000000014b2,0x22570c3e354cba40008,0x80000000000000000000,0x459,0x39190000,0x8300000000000000000,0x0,0x0,0x0,0x0,0x39491a40000000000000,0x3177ca8800006cd,0x0,0x41dc000000000,0x2096,0xa49c00000000000,0x0,0xa530000000,0x0,0xf0000000000000065f40,0x121,0xdd83a600000000000000,0x13e000000000004,0x32590000000c2ac00000,0x0,0x4ca00000000],#[0x921400044580,0x0,0x0,0x23a400000000000,0x0,0x0,0x0,0x13d7000000000000,0x12ab8d74000928000,0x33190000000,0x64000000000000000000,0x63,0x4fac000000,0xdcd41000000000000000,0x131500000008cb01,0x0,0x209022800000001346,0x12c400000240,0x0,0x0,0x26000000000000000000,0xe0000000000000000032,0x1a,0x32df0000000,0x6009e000000000000000,0x4000000000007611254f,0x3b450000000cca,0x1400000006fd80000000,0x10e1905c0000001a,0x0,0x247c000,0x65580000],#[0x8c9d033000000000,0x4f64000000,0x16000000005a40000000,0x4,0xae53c3f0000000000000,0x1c00000000000000000,0x1,0xba0c368000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x231c00000006493a4700,0x106000,0xfd000000086fc0000000,0x8a25b,0xc735313475c00,0x23884ad30370000000,0x7c0008c9800000009c50,0x542f00000000000000c1,0x4e1c00005b,0x8f700002df4,0x0,0x19540000000000000,0x1253,0xfc000000000000000000,0xe,0x4978000470c362000,0x0,0x8540],#[0xc50400,0x0,0x245e00000000,0x0,0x198000,0x341a0f94,0x0,0x0,0x22860000000e560000,0x94000000000000000000,0x239fc2,0x1020000a000001229000,0xef400000003952e73,0x238a1b400000000,0x0,0x0,0x0,0x38dd00,0xc9aa2750d20000000,0x8ead0e587c0000,0x52c0000508c00000000,0x3e600039f3000000,0x0,0x0,0x171c694000000000000,0x1a400000000d1b,0xa6000104100000000000,0xc0000000000000000020,0x53ec000000020,0xc63c000,0x98000000000013100000,0x8000000000d00000002b],#[0x41d0000000000000011a,0x5a050000000000000001,0xd15aa09000020185a90,0x9400023de000000,0x4802c90ea00004af8000,0x1fd000000000000008,0x14fc000000000,0x0,0x0,0xc8e90c6000215500000,0x0,0x1069000000000002dd,0x5409c00000008b2c0000,0x3205c6010950000000b0,0x13c000,0x0,0x30000399000000000000,0x24fd52f000048f48d,0x52d7413e414000,0x30000c64e0648b800000,0x994a2c940000000000c4,0xcfe,0x0,0x30c3413400000000,0x0,0x18a1,0xc66800000000000,0x0,0x135,0x0,0x138000046f000000000,0x4834000000000],#[0x25bc000,0x61ec00000000000,0x4f1400000,0x0,0x0,0x0,0x125d0400000000000,0x1d90e2a8480000000000,0x2342cebf0e300000005,0x0,0xe5d40008cf,0x0,0xa000000000000008eb40,0x149840ba03,0xdce24b0000000cae0000,0x8ea400000000000,0x11ad00000000002a4500,0x8ff0000000,0x0,0x3454000000000000,0x90300000000000000000,0x918000c1330ec000339b,0xc,0x0,0x25993050000000000,0x0,0x885016800000,0xce34000000000,0xf24000,0x3297000000000014970,0x3040c10c00000,0x357493400042440000fb],#[0x0,0x0,0x11fc0000000000000000,0xc2b097900031a9,0x7400000030b100000000,0x537800012,0x0,0x9dd36c00000014350000,0x70000000000000000039,0x82e800000008a,0x49100000000000,0xccec00000000000,0xf00e0000000d22f17b00,0x202a0000000730,0xd20000000402330e86e8,0xe0000000802507500014,0x3a41000395,0xf00000c61c0000608000,0x30000000000000000000,0x14050a0c3004a,0x0,0x31293078,0x248c4c100000,0x8088000000286c000000,0x4e8b96b,0x1174000000000000000,0x0,0x0,0x88a0,0x0,0x14bb0000000000000,0x0],#[0x0,0x1235000000000,0x0,0x236f0000,0x67d800024800,0x949000000,0x241c,0x0,0x21150000000000000000,0x0,0x438000000000004688,0x8e3843d00000,0x0,0x18980000000,0x0,0x329a811000000000,0x0,0x53980000000,0xc44f500,0x653c0000000000b29c00,0x5140004bc10b20000000,0x2,0x0,0x0,0x0,0xc61b8b400000,0xeee6cc2ae8800,0x0,0xc56000000000000,0x33a10649ae3000000000,0x0,0x0],#[0x47fc000000000000000,0x0,0x45000000000000000000,0xcb0400000000004,0x3d00000000000000000,0x41b00000000000000000,0xe8b000044740000126,0x0,0x0,0x8188000,0xc39448451100000,0x40000000000000000000,0xe5df1fe00000008c0,0x210300000000000,0x0,0x0,0x0,0xc087e00000b84a700000,0x1809000000046,0x307000326f000001c000,0x0,0x4a0a901000000000000,0x1003000000006d400,0x0,0x290a84ff04e03700000,0x42109680004a2000000,0x0,0x31f200000000000,0x8478000c8b80,0x7f000,0x2f40000000,0x298f000000062900000],#[0x0,0x0,0x9040000e2000000000,0x81cc00000000,0x4ad6492000000,0x2cc00011bc0000003355,0xd,0x0,0x0,0xdd000000000000000,0x20e7000246100000,0x331e0000000000000,0x0,0x0,0xa81b0000000000227900,0x4ae,0xe7000000009402b71240,0x85281,0x0,0x0,0x0,0x21610000000000000000,0x0,0xe100018eb00030270000,0x38,0x0,0xc700000,0x0,0x0,0x2d200000000000000000,0x9300000004cbc000ab77,0x50054],#[0x0,0x0,0x3bec0,0xd05000000,0x9f000000000000000000,0xf40000001,0xc0002013d1c922400010,0x33c,0xbe8000,0x0,0xd13c00000,0x8c740000000000000,0x0,0x0,0x4f800000000000c27400,0x0,0x0,0x34e000000000,0x11b70000172000,0x317d00000000000,0x2b510d81a000000000,0xa38000,0x126bd3180000000000,0x3bfa000000000000000,0x80000000000000000000,0xb000043a8cfc000c69,0x10464844,0x8000,0xa640001028000000000,0x3b80008d9c00000034dd,0x89fd0549,0x0],#[0x0,0x9b0000,0x1000000000000008f280,0xaaf506c0000000000139,0x245f46380000000bf8,0xa7000000000000000,0x1b3900,0x42a4000000,0xe1d40000000,0x50000000000000000000,0x51c00000031e,0x20c0000000000,0x287a000224f0,0x2a4a000000000,0x0,0x8781950000,0x70000000000000000000,0x20b50000000000323,0xaa800000000000000000,0x1233000000053eb0b3c,0x33e1000000000,0x8a2b11389a40004c6,0x0,0x0,0xa294000876c00,0x0,0xc000000000000000000,0xce,0x6158000484e3f5f2a,0x0,0x0,0x2bf7000337e000000],#[0x0,0x108c00000000,0x65448b6000205000,0x0,0xc6f400000000000000,0x70a4000000000000000,0x0,0x0,0xa4740000,0x0,0x44a4000,0x8fec0000000,0x10c40,0xa4100000000000931c00,0x345c14040000000000,0x0,0x0,0x3a7c000,0x390000000000000,0x0,0x0,0x449c000,0xc61fa48e53b20c112400,0xd46000000000000000a3,0x4ca473,0x0,0x0,0xd2b0000000000,0x32d1b0740000000000,0x32b301200004d6e4a30,0x0,0x34140c0000000000000],#[0x867b,0xbcde8000000217e00000,0x16,0x0,0x0,0x0,0x0,0x0,0x0,0x29a20000000000000,0x1b01c9200df0000000,0x0,0x0,0x0,0x22da00000000000,0x0,0x0,0x20824d2897400010db,0x0,0x31f6e5cc00000,0x0,0x0,0x853c000000000000000,0x628c00,0x8000010d3,0xc5d800000011850,0xabe0000000000000000,0x48240000000000000,0x8e180000000,0x0,0x3455000000,0x26400042600000000144],#[0xec000000000000000005,0x2bfb48ec0008a,0x10f6000,0xcc000000000023170000,0x4bf800000022,0x0,0x4334000,0x5e0000000930c0000,0x34ae00,0x0,0x236b00000000000,0xe0000000000000000000,0x3b800033b,0x21f90000000,0x12e8000000000000000,0xbe40000000000000000,0x0,0x9e000018400000000000,0x70000000000000000002,0x38e,0x1151,0x33cf000000063b00000,0x3341000000000,0x2c600000000000000000,0x4374000450e,0x442d15b000000000000,0x0,0x601b217,0x0,0x12d4136800000,0x9c336d0000000000,0xa4000000003d40000000],#[0x11,0x0,0x0,0x0,0x88d0000000000000,0xb90000000000,0x0,0x0,0x0,0x0,0x14be000000000000000,0x46e00011b1000000000,0x0,0x30000000000000000000,0x3,0x533400,0x2284,0xa400000032e100000000,0xc2a0000000000000007,0x3b80000000000000,0xcac00000000000000,0x52fc00000000,0x0,0x0,0x196a0,0x21c10000000cd1c00000,0x3ba40000167000,0x24300000000000,0x4b8e14b000000000000,0x0,0x3cf7d144000,0x0],#[0x0,0x0,0xecdc,0xd0000000000000000000,0x65c00004d0231000333,0x24f500000004e70000,0x33d3656502b0,0x1b3300,0x0,0x0,0x8220000000000000000,0x13ac0000000000000000,0x11c6000001b0000000,0x0,0x0,0x12f10000000000,0xcc28,0x0,0x728000828c000c95000,0x0,0xc8b23df00000000,0x935c00000,0x3128000,0xce800000000,0x0,0x881800,0x0,0x0,0x24590001267841c00000,0x0,0x69380000000,0x2c88000000000000000],#[0x0,0xdc000081940004a40000,0xca6800000008738,0x12c200,0x0,0x0,0x0,0x0,0x0,0x247c00000000,0x1b00824c000000327400,0x8df00000000000000000,0x705a03b00010590002,0x539400000000,0xc0400000ae4000500c00,0x0,0x5b00000000,0x117f0000000e30000000,0x21e2479000,0xc3000000000000000000,0x3a,0xe30000000000,0x6568000,0x0,0x23f400,0x0,0xe000000000000000000,0x449800000011,0x2ae5ef94000000000,0xb9f0c7f24c,0xb5800000000,0xa0c0000000000000000],#[0x0,0x3370000,0x866f27e00000,0x47c0000c08000,0x0,0x3aa00000000000c610,0x1500a8e2dc000349b00,0x8338000000,0x0,0x3343000000000000,0xc88800,0x3bb6a4b4620000000,0x0,0x40000000000000000000,0x3f24880000000000923,0xbcfc8000c4400000003,0x8ff4000000000000033,0x42bc0000000000000000,0x82240000000000,0x90d000000000000,0x80000be4000000000000,0xcd,0xce08,0x0,0x0,0x908000000000089dc028,0x21040000000a,0x80000000000000000000,0x49d,0x0,0x0,0x0],#[0x0,0xb4f000000000000000,0x8b031c250fd42700,0x47592d80000000000000,0x700003b640002c180002,0x14,0x3375a2dc00,0xe8c00053c80008ccc000,0xa,0x2335d2a8000000000000,0x0,0x0,0x90000000000000000000,0x2b2,0x0,0xbf00000000,0x0,0x24000000000ca0,0x0,0x123c422c0,0x0,0x0,0xcc5800012b40000,0x0,0x40184a9eee8000000,0xa54000000000004590,0x0,0x4d2c000000000,0x0,0x0,0x74200000000000000000,0x401],#[0x0,0x118c000032c0,0x0,0x4d800000000000000000,0xc,0x391088c800000,0x0,0x34dcacfc,0x7000000053bd44800000,0x10a601,0x0,0x20cf8afc00000000000,0xc00000021d050c000000,0xb05,0xd500014d34da0,0xc0c00,0x23ac0000000000000,0x0,0x0,0x40150000000000000000,0x18e30000000c53,0x13b40000,0x914c000000000000000,0x87580000000000000000,0x4f8000c74a053d19818b,0x8800000002a95200000c,0x331a47,0x33f6000,0x0,0x0,0x132d0000000000000,0x0],#[0xba5000000000000000,0x3abf000000000,0x0,0x2e40000,0x4ed000000000000,0x29180000000000000000,0xe1000000000000000000,0x4480000,0x0,0xe298000000,0x82640000000,0xcf54000000000000000,0xc17000000030ed000000,0x0,0x709c00000000000,0x12b0000000000,0x5098000e3250c5000,0x8634,0x90c09023cbac00000000,0x110f00000004db2ca,0xd171480000000,0x0,0x30e900,0x0,0x0,0xb0000000000000000000,0x42f000000033d,0x5821f300000000000000,0xdc000000000000000008,0x4000000000000021b2c3,0xcc90220494,0x0],#[0xbce60000000000000000,0x4a60003b0ac32290,0x3b6,0xac000418000000000000,0x7,0x38fa000,0x465800000000000000,0x127300000,0x109a0000000000000,0x0,0x236000000000000000,0x0,0x0,0xf70000000cf040000000,0x4,0x0,0xeff00000000000,0x21d9000000000000000,0xc22a0000000000131200,0x16500000008df,0x0,0x0,0x824800,0x0,0x220ee71091c00022660,0x6394000000132500,0x0,0xa57000067e4,0xe0000000000000000000,0x89f13a,0x0,0x47240000],#[0x0,0x0,0xab640008ec4,0x0,0x3019a34542d000000,0x47a800031dc000,0xfcc3ab00000000,0x0,0x31c50000000000,0x5e80000000,0x19c0000001b9d00000,0xc45c0000000000000000,0x9320000000080e,0x34f3000290300000000,0x22fc000000000,0x82380000000000000,0x123e00000000000,0x80002ac947c400000000,0x43fd0638faaa4,0x5e000000000000000000,0x4,0x0,0x4008000000,0xf3874716300000000000,0x70000000000000000032,0x14e2000000000022e,0x1600000000000,0xa1d00000,0x325c000000000019bf00,0x10390000000462,0x7900030e400000000000,0x11],#[0x84e00000000000000000,0x1392000000000032d6,0xf4000000000000000000,0x4,0x0,0x0,0x0,0x2105ca5800,0x24d5,0x44000000000000000000,0x808000000000012,0x0,0x2c000000000000000000,0x132100001,0x116e3a30000000519000,0x240200000000000000,0x1331000000000000000,0x2474000000000,0x12de0000000000,0x4ed4,0x0,0x87540000000000000000,0x0,0x147d00000000,0xcd10000000000000,0x0,0x38c87208,0x33108ba800000000,0x0,0xcd8000000234f0000000,0x6,0x0],#[0xe35,0x0,0xc574000000000000000,0x13c40000000000000000,0x92e80000000000,0x34470,0x0,0x1a000000000000cbb000,0x3,0x411000000000,0x0,0x315600000000000000,0x0,0x40000000000000000000,0x2ef000000000000008af,0x0,0x86040,0x0,0x0,0x1b400000000000,0x14b40000000000000000,0x11f00000000000000000,0xeb000000084640000003,0x90ec00000010,0x0,0x34b7,0xc91400000000000,0xd2c67c00000,0x70c8000000,0x53b000000000000000,0x0,0x807c00],#[0x116835a,0x20a1000000000000000,0x0,0x0,0x134d00033c80000,0x6cd8615a402800000000,0xf0842a,0x20aa00000000000000,0xce040000,0x8940000000000312e00,0xc82b32a8e740000df,0x11420000,0x46bc000000000000000,0x2190000000,0xbc00000000000000000,0xc3280004,0x0,0x13ff0000000000,0x0,0x20a8000000000f80,0x68140000000000000000,0x0,0x0,0x65f306a2d7028b00,0x0,0x0,0x0,0x6cd00000000000000000,0x4d400000000000,0x0,0x0,0x46700000000000000],#[0x57000000000000000000,0xe67800000000000c8a1,0x29570000000000000,0xf200000000000000,0x0,0x0,0x294000000000000008d3,0x3,0x44ae47800000000,0x2b1800,0x0,0xc8000000000000000000,0x30800000c,0x1100000000000000000,0xaacbec00000000000002,0x38,0x886f3dd000000,0xf5800000000000000000,0x8,0x36300,0x0,0x0,0x393000000000000,0x10ae0000000000000,0x18587f00003cde7c4000,0x2340000,0x22300000000000245d00,0x2c10000000,0x0,0x342a00012fd00000,0x4ab3c200003e3000000,0x22ed],#[0x21f4a7ed446c71011a0,0x0,0x0,0x321600012270000,0x13500000,0xe56c00,0x145000000000000000,0x318a000000000001590,0x0,0x6b0000000831c000000,0x30e848700000001,0x80000000000000092500,0x92e40000000000646848,0xb6000000000000000000,0xdb8da00000004b40ad8c,0x4b34000000000086,0x34d60b6c000000,0xc3e4,0x0,0x0,0x44f4490000000000029f,0x2,0xc0004c6c000000000000,0xd19,0xab1124e51fa3ba0000,0x0,0x0,0x0,0x7e22f600000000,0x80000000000000000000,0x15060000000412,0x0],#[0x16e6f6c0,0xc9b80000000000000000,0x320b4e9ca4b,0x0,0x13fe00018e8000342c00,0x95300000000000000000,0x330600000000001,0x70000124000000000000,0x7ee45,0x190e,0xbb200000008a380000,0x3e0a9300033b000,0x0,0x0,0x92ac0,0x0,0x0,0x386e4fa000000000000,0x53911e6000000000,0x0,0x22490000,0x0,0xe2fc4c0000000,0x474c000,0x4af49ac8740000,0x0,0x578c200000000000239,0x37000000000000000000,0x80a34000c2ec00000014,0x488c00086d01c,0x113200000000000000,0x23b700000000],#[0x0,0xae4c72e1c709b0000000,0x47c6a000000000000002,0x1496d20400000019,0x1408000000000,0x36000000000000000000,0x1c628,0x0,0x0,0x4f18,0x88400000000,0x0,0x938c000,0x33720,0x0,0x0,0x80580000000,0x9d21c000000000000000,0x302d000000000034e,0x0,0x8800000000008a040000,0x40000000000d20c000c9,0x2e8,0x0,0x5000000001ec00000000,0x207c000000000002f,0x10d900000000000000,0x0,0x4f4800004c400000,0x92840000000000000,0x902c0000000,0x165a0000000000000000],#[0x8ecc000e57c00000013f,0x3a400000000000000,0x40000000005200000000,0x237149572ff00000004e,0x0,0x0,0x0,0x0,0x34e700000000000000,0xca440000,0x301e000000000,0x0,0x0,0x3bfe000048600000,0x469c0004fa400,0xfb400000000000228000,0x23780000000c,0x498c000000000000,0x0,0x83c0,0x446a8000000000000000,0x4c30000000000000032a,0xb8800008410b40000366,0xee0113b6,0x0,0x21f55078000000,0x4d4800000000000000,0x296d000000000000,0x937c00013a0000000000,0x30bd0002108,0x0,0xfe20e6860c00000],#[0xac500000000000000000,0x47000000000000000000,0x20,0x40980009360000000000,0x6740000000000c12c000,0xab08cc74,0x241900,0x39c20000000000,0x3200000008ad80000000,0x26800004ce000000020,0x51cc00,0x44c00000000000000,0xed0000000000000,0x3055000000000,0x30fe0000000000,0x0,0x0,0x3c3d0000000000000,0x40f00000000000,0x339a00000000,0x80000000000000000000,0xcb9,0x0,0x8214000000000000000,0x349c8ab4000000000,0x0,0x14cc0,0x0,0x19100000008d4611b000,0x348e00000000003,0xd2309610b5400000000,0x882113a10c800],#[0x0,0x0,0x80000000000000000000,0x42d,0x0,0x0,0x8b971ac0001471000000,0x0,0x0,0x40000000000000000000,0x42800000000000000909,0x6ac0000003,0x0,0x0,0x0,0x1c00000021d46b2c0000,0xc2,0x52f40000000000000,0x5316976c2c141f0000,0x8d240,0xca740000003442853800,0x0,0x500006bd800000000000,0x80000000000633c00045,0xcf8,0xcc240000000,0x42207b000000000,0x290c0000000000000000,0x0,0x121ce000000000000000,0x3c3000000000030fdc2,0xe160000000],#[0x0,0x0,0x1cc501000,0x0,0x0,0x342400,0xd10,0x424,0x0,0x9c800000d4c28000000,0x4428000,0x13c0000,0x138b8530000000000000,0x0,0xf10000000000347b0000,0x315f000000000000,0xf442ca8b3c00,0x0,0x0,0x252000000,0x1e00000121000,0x0,0x80000000000000000000,0x4d7c35,0x2e04110000000000043c,0x1f07e00000002b280005,0xc0,0x8d00000000,0x8b6400000012c50000,0x0,0x74000c80c00,0x8fc00000000000000000],#[0xe4000000000000000008,0x126dc97c0000000000ce,0x32000033850003252000,0xb2000000000000000003,0x632d0ef000000000022,0xe37000,0x24ce000000000018b3,0x0,0x444b0000000000000000,0x54c000000122b498,0x0,0x0,0x3a08000000,0x102c00000000000000,0x0,0x22d0000000000000000,0xd2783ee0000000000,0x0,0xcd7800000000,0x423c0000000000000000,0x22a000000000001a0a,0x1258000000000000000,0x29460000000000000000,0x0,0x483f38000000000000,0x83ec00023d400000000,0x20400000000000000000,0x31e800004a70000000,0x1334506000000000000,0x0,0x9940000000000000,0x41000000000000000000],#[0xa53feb42000000000032,0x807000221,0x32ac00000000000000,0x1e344dc00000011750,0xc6e20c100,0x42000]]
def g251D9 := limbs80 #[#[0x505404c5304811019054,0x99254591615815454550,0xd7f64d8760d4750d0740,0xeff3f7fafbfdfafb7bbb,0xae751dcd3ffff7f7efef,0xc6a8e15cdc4b93a15400,0x8ae6125c826b8851700,0x16a6026d91e13a84175,0x51162822c4845aa80b54,0x57312ee4255c858b08b1,0x957512ee8255d04bb989,0xf5501aeec255d84bba8,0x19355022aec355d07ab0,0xbb1157522ae84b58c96a,0xaba9a964352846d580ca,0xab94294286aa1055d8c,0x10abb41575852c9055ce,0xc90bb8a275144aa28d58,0xdd113aa2255442ee685d,0x5dd90abb2266544aca85,0x255d252aa4957194aa32,0x4b75896bb8ad57694acb,0xc8b75916bb9ad7725bec,0xae5455c68bbaad7745be,0xaaeb455d28eb251573a2,0x3e2c2755d8aaba171512,0x28e2a3155d8eaba9e943,0x768aaeb155ce34a1c557,0xc734aee49c5852bb8255,0x67544caa895dcd37b9a6,0x4d5709aeec955d92bba2,0x93177062aed355d272aa],#[0xb23177363ec6c758d8bb,0xab85577562ee8c7d918e,0xaaba55d64aaae7555caa,0x14bb8a977052aec055d6,0xc9cbbb29576554c8aa59,0x5d9cababa96472ae6e55,0x5dc1aaba855730aae415,0xf5dd5abb9b57726aee2d,0x1655d9eababd5737aae4,0xeb655cecab959571b2ae,0x2c42e5485ca10b93212a,0x72c82ed8c5cb18bb6217,0x1f2623ed945cb28bb641,0x41f6c23e5847ca88f941,0x62272844ed907cb20f95,0x965276c84e5909db1139,0xb962376a46e548ddb293,0x9b963376a66e54cddb11,0x29ba65372ca6e194ddb1,0xb2c3965876c50e58a1db,0xcb0a3951472828e4c51d,0x1ca123b71472e28ed851,0xd1db923972476c48e589,0xcd1cb9a3b63472c68e50,0x5d11db223964472a88ed,0xe1d91db2a3965476e88e,0x2e5925dbb23a76472ec8,0x2be5457ca0af9315f6c9,0xc4bedc57cb8af9615f6a,0x2a6be50d7db92f9725f2,0xf6e6be5cd7cb1afb535f,0x5f2e8be5917daa2f9545],#[0x55f0eabe9957cb2afb74,0x41a72634edd57d3aaf97,0x953a72874ed469ca8d39,0x79642f6a94e5529da9d3,0xc79658f6ca7e594fdb21,0x2a79654f6c89e5913db2,0xb1b3b72676c93e5927db,0xcb22b970572cace5919c,0xdcb2bba76572ecaed915,0x5bcb8b7b706f2e0ded95,0xcdbcb9b7b726f2e4dedc,0x5d5bc3ab7a656f2caded,0xfc0200003b756f4eade,0x9c0cd02bc09701d40590,0x816e054013a047010303,0x23b08701fd07681b7064,0xfe0b882c30a982820984,0xb0eb838d0d843440c5c2,0x1298488118c43810143d,0x60c55314bc50d139c4c8,0xe064a18845f317345a71,0xc72e1bf86dd1afc69b19,0x8021f847b81e3476c1d2,0xfa232489e21dc8552094,0xb265496c253092b24448,0x29f4a5528aca0527789b,0xdb4b3c2c58aec2b10aa1,0x44c323048bdd2ed8b922,0xccee3344cb23258c7931,0xdb2363cd753564d3a342,0x673938e2f3850df53720,0x63c34eed3af4ea33a14e],#[0x3f00f923dd8f573cf8f2,0x1f906041050133fd8fd9,0x112143f90e242d109a4,0x51e846e519745cd15b45,0x2bd4a6927b4941230483,0x884d893444ca12fc4b65,0x5516142b50053d84e953,0x54e5508538d4b8525147,0x93161157915b7563d562,0x57125ba96c55a916805,0x980d5f857bd5e4d76d5d,0x92063f98dc629d86f60e,0xf667319a966199646509,0xc6b75aaf6a45a6568a19,0x6f79bb66e19b526c79af,0x3c5cce72adc7770fdc13,0xa9db37639d6274c9d0c7,0xdeca7a99e807951e2577,0xfb47e19f5e7cf5f167bb,0xc5824206880e20097f85,0xf866a173852a11c83c60,0x8a1e25b88c220b878a1b,0xe223578c9e3008b5e2a9,0x8a47b91324228fce3b28,0x257f953e51593be4cc92,0x66f993262798025d596a,0x589cc27099b6a6ad9a3e,0x6a05e7f19f2e7a39dee7,0xa3ce8cfa2ae888a19684,0x78e9b5a61e961a4e2917,0x7aa77a95ea37a8729fba,0xeb59acdeb0dab9aabdaa],#[0xc69b0d6bffaf86bb4ae2,0x100190d83b3cecc0b256,0x830ca060282c10370300,0x1e2916838230d8306058,0x8420050a87436148123c,0x14146408818682e2a428,0x7020b90841878704e902,0x40188200660287002080,0x61709090e8121ec004c4,0x8e47a03218f8882305a6,0x1d8306d1847230603c12,0x46178c4801f13114150c,0xb4dca28af94446de4f2e,0xdca2774e9b8cb1edd8c9,0xec13534b04e7a72c13ec,0xd110f4e58275f7a221ed,0x99aad4c8d98f4e58279b,0x21957f9ca4231430eb01,0xce34146ccfadccadfd77,0x9aeff1624f3ebbe9123a,0xd68a3530c5a132dd6881,0x123467eb98ebf5b99262,0x4a449295f6e64cfa8494,0xb1021212bed44cb35d77,0x820923c0ff8882381fe6,0x30f84ef98848debe57f0,0x2e595df4a184a4facad3,0x5f056a330aaca18468e5,0x46fe020823b472972cac,0x6fe02082387f2a901203,0x44d1f014090be2c84224,0x1bc29aa0cf1c3b485e03],#[0x7595b8659ffcd9724127,0x8e7a73413ee74c48242,0x49b6351e220012b73a66,0x5de54460dbc5b32d7f1b,0xc56b544791cc6612092b,0x5bdca2151cfad81850bf,0x9f0f82051337c6b21089,0x30cef988926fdb6ec314,0x883479127336f7cc4495,0x6fe0127b6df6193ec6e2,0x7d11410cfbfa22a2248b,0xcbebb02412366bb89a37,0xe362ebc1824d6186840c,0x8dbf808208f9594a5d0c,0x149ddd5f0a0485ff0820,0x4a9ebb85511f6117598,0x9e394a5d0cc3fbddec09,0x8945cffc220a6fffc220,0x101c1c161078fdbb7cc2,0xdc4c1f87288acdcec55a,0x4c51f97992bda8d90f2e,0x882c82489e1b518f2edc,0xd336b28b5afab1957fbf,0x879a0a7e2414239f4b04,0x34a7f48c83e842d72a49,0x44b9d128cfc2c20bf858,0xe1341a7806cc99f7b332,0x9fe44c83fad662ad493e,0xeaf111365f9135788894,0x18120fdab49bbe6d332,0x4bb546c9966b441ff78f,0x4c3ff1f9608246a5a1d1],#[0xceb5c9a74ba0463fed90,0x14394788020689f61116,0xee904d23d70411e62f71,0xa42236cdca22ca8c453f,0x6bb00095b8c28e234ffd,0x937008e79e9c3028de9c,0xff9cdb9048efaaa265df,0x88cb3f6e411ebf05e326,0xe559048dacfdb28db4de,0xa0f4e58275aef445dffc,0xaa094795b7262e7fe110,0x9314c14a5167de10e2eb,0x9ffcc0a94244d1f17620,0x19048390e584eb555945,0x28e236eeaf841049dce9,0xb88ebe6d5d75504a1f8c,0xb30f1ff26c41207dd6b4,0x958ec7882524b7ae9892,0x695f1a009bbfd0ac3004,0x6618934af8d004c9e312,0x6948c5b5323652da99d1,0x34012963c78d291e7e3c,0xccd3fe4e1a00922bfc9c,0xccb9ad90b2eb3d7b8718,0x492bfa47e42090d0fd02,0xf272c42449317f4d3d4a,0x89265ffe54f7d04d168f,0x997329712655fcd2b484,0xa70995b42e72656d0b9c,0x1ed02c9953d29c2654f4,0x8fc9220a62c0f68164ca,0x4901a24e5fcf80206892],#[0x8a69ce5414c5b3ff34c8,0x88fbff94491124ae646e,0x30492cf4da3a299d365,0x6ff39d248298b57ebd72,0xd248298ad7ebc4281892,0x6d1252fc79a56b6892ef,0x4fd6e1629ed1260f34ad,0xe1c63328ffb81a9ed125,0x4480c97a4d1fa733596b,0x24f3f89f08e8ae79b084,0x637e430899b7f5d02649,0x205001367e39aca42402,0x8d873d2060097bfd873d,0x473c27804803fce27804,0x240f689d512392c14521,0x48d49e8106d9870606b1,0x180b6fdb74ca8a87b133,0x527e76c84602ca79db21,0x5fe3590900937ff76140,0x6de06629bf7ed33b222b,0x8205735ff31924324bbf,0x24834ff0f8205469fe5c,0x3ed67e2449226bfe6262,0xb2f7e7a3199b63fc4892,0x723ef9062439243ed4ee,0x324ee460e84449cabe46,0x209438ce27234fc67841,0x280eb804c033eef42261,0x6ff50ee8a1a49fe67928,0xfa64814921dbcdcc2996,0x48ffe0942327a0513a09,0x1befe30ca47d72d6352a],#[0xc8893241fb75ca08d2da,0xf80a0470e7f9c220a957,0x76601626238fc20823ee,0x9490eff3b03895d25e12,0x27fbf039142a0ff3b0c8,0xeafb09048bbfcc2d865,0x9407da9dd65efcf46333,0xba082d0be4672292668e,0x2914ede6e614cadbca3,0x2647b75ca08d2cd3f4c9,0x4113367fb0411332f911,0x44948f27fd12523e7fb0,0x1c0a07e330a1202549ff,0x7a7822654f4f044ca69c,0x34f5c4ed234f5c4ed232,0x8166697d1132ed67ce92,0x824576b524acc5fe8b4,0x2afc64e1920943ffd8ae,0xd2f8e265e2605235d871,0xe123f7d55132f7d55132,0xf2940915f4649952fe8a,0x14c80cf67f9c220a67d1,0xe42c109723e4d02387db,0x14d48ee1f55103388ef4,0x9058978e723a8bb8ff3d,0xb999b66c0a8985df1ced,0x5f92a10913e42cc7c891,0xa882448af36c91154b5f,0x377aa]]
def g251H9 := limbs80 #[#[0x850516000000208106,0x18180222810400043050,0x41210410310001088600,0x8022180020a005800a0,0x3000c20100002020600,0xc0a0c18b060400018387,0x10086080200100083828,0x41458602141080800490,0x14200061810116000860,0x42850000080221800502,0x4833600000001c000020,0xd0a1458304014000004,0x3001000400004030e1c0,0x14003000c18f082420,0xe0139d04141020258080,0x40002080001e907851,0x60a84280001c28502,0x8600000810400089081,0x68e0c00e20080810640,0x200005000204b0002043,0xc081860024008140c00,0x8003002831b0a10105,0x80120a0848018046851,0xc083000480402045142a,0xb0000000010010003100,0x21000204180800004,0x904046840804a2c0c180,0x8604001858d300810,0x41c18306942010208000,0x8295068c01900080820,0x703463c0000214e8c06,0x3220c0020208102041],#[0x130004850e042850c40,0x2000442e0004a8002041,0x240039f0e040810c5078,0xbb823b0e230060000604,0x22370be044cad42308c,0xe32643600011b400,0xbecb79adb0000000000,0xa4ec000af673e80001,0x967e81aa40e815f85ac0,0x2c0b137000023,0x97b0bf000333dc8a23be,0x2a78cec0000cca1790,0x80009153010486800000,0x24a40e42e80000000c8d,0x6c45f7bb80000000d2ac,0xa27e54bd217031f4e8b3,0xd29d0ec2da445b000292,0x1e1477000117ad2eb30d,0xbb3cb318737000000006,0x6100e026bda530740f26,0x474b38000001ab465,0xc681d4000000218a8268,0xc14400083d800000002,0xc32f1eecaf6140000000,0x7400000000006990000,0x1d90a951750000000c,0xc00000000000c3000000,0x8b24000cc8f10daf3,0xac1400000012052c1c,0x102cc88a000000000000,0x290e8cb000019,0xea0000000000000024ae],#[0xc7bc17f0000000c,0x400010cf341866400000,0x26884680000f58000a51,0x454b151f043e435ec4cf,0xc00f0000000000002003,0x445000048300000003bf,0x1704390000000d0ba418,0x8a138000000000000009,0x34a9d2dd302113a19eef,0xc8200000000000000ca0,0x2400022450000a970002,0xb0002c40466d285278d4,0x69c1c48c01d45f000131,0xae716aa9bd0e4c18e43e,0x3458128c00000024bce,0x82a9cf3e41311a425c00,0x2a49176a55000219dc42,0x6c638c0d3c508000c61d,0xa00000000a894cb8382a,0x493092943148d9000220,0x11040005010000,0x8a0a4522c00000003670,0x8000d09a9564b33036c4,0x1880003b6c12e0000531,0x9968f886b48762fc0c7a,0x500020d68be81c990852,0x138e000228286830f,0xa8c00052284734c5e265,0x104e0b40b938aa00000,0xd8c82fed9dcc62400000,0x854deac598a38b4400e,0x4220ecb6e0000000c59b],#[0xccab6be400011af00030,0x4a68000c7e04198b710f,0x882164000325b44b7031,0x970b40cad2dbb0213b56,0xb24b852438300021cb4c,0x1540002020d20003dc47,0xed4fa80004662876e88c,0x185911ca40146c61,0xae3c000d26018289dc00,0xcd4800069b4000,0x1a98297c00047380000,0x400000002e2a3613dd00,0x23000232e00009e8cce,0x71000000000000000002,0x3203000205900034,0x1083000244d000000,0x2ec00000000000000000,0x9b127000000000013cc4,0x201f0a6f2290001bdcc0,0x1e200023a7ae6aa2ec3d,0x4a0003311482c0000001,0x89840c7000149251018,0x6ca800,0x87500038d60000000,0x7d256467021800002a60,0x215900011da47d89ea26,0x48e8f1000085cd147000,0x680ebd21200000004ec8,0xd0dc0000002857a1c5a,0x49f311821d19e1908c00,0x2b000000000,0x448456c3428ae80000],#[0xc00002b912047a634900,0x2d3a7adbab238746c871,0xbb637b09fa34432663f1,0x804471760000000e8dfb,0xd513de0087b3e12270e,0x309bea87c8000e98b1b0,0xcc00005c44c7cf622406,0x801e700b3d50003050a0,0x87763541568e08000800,0x1c000294688f7a600000,0x50003c2100021e6a65e3,0x112c00000012e9000104,0x9f11d700000000000000,0x54113c5dc335000226fa,0xd2690c032368f78b,0x2d6cffe07f8f8ba564ac,0xd503b408b814dc0a2eea,0x88931b80f440008935b,0xd13c4530000b452a5800,0x4c503a90000000,0x21c800000013640,0x33c2e9412be000187000,0x33564ef6312cda,0x872831d00003730000,0x9c08a14f52522d700000,0x11d08d3c85100003b,0x19e9e0e80006390000,0x125a09458d2cb66b150,0x53eb0f8300a000215e00,0x3ae84a000000011b749e,0x328f00030eb0992,0x10000000000000000000],#[0x4ab11be0000000caff24,0x41a0bd413c0000000000,0x7c000016f196100cc7c4,0x13010003afe87100000f,0xa930fd00000003493118,0x47d4000ca580000001,0x13ec0001213911c0,0xe40509b0000000000000,0xe24000000237ea4e4000,0xc829c8bc236f02e8068c,0xc0000000000873d2e385,0x161b2e62ca0000000830,0xd40000a594e5400001c8,0x943dc16800033d300031,0x21dd0000a6,0x3a180001284035c000,0x3484ca300000001a440,0x32df000000000033d900,0xa16aa44119219c000000,0xc000223100019320000,0x48bfd0daacf322bc4740,0x10c1e8ffaad2f7810,0x1f60e5cf05499cbd1304,0xb800061990b58db4000c,0xc0000002cbf0001165ec,0x1580001b9d0002bf9c25,0x70c271c588c170c40000,0xf308a3658e1122147a10,0x919311f91e110800031d,0xd33d70ec61ebee9b076,0xbd13c2814000e99c0008,0x88d0a315355d1990b76d],#[0x2f6a93e414c58000007f,0x2f7d016000108d24eb,0x67c04ac024308c00000,0x827a00b09123ac923043,0xd9810e00000000000000,0x4c157cf2545e00034d08,0x47c26791b648c81ffec,0x94e9e0000a1b4000000,0xff00024518f6c4050003,0x31fdaed40000af1a,0x10a8025c4ec00,0x14200000000c228000,0xb702c8854000c6504320,0xa46e00000008c431fc8f,0xf22c000c90b02e8f6,0x1a92cb2c0008a50,0xe00029bf09ec27a4a240,0xe8f000083c603,0x41443a06ce0ad0000000,0x9a47540720d010ff0050,0x39b5206181861429e02,0x467d0f3331111ac5a48f,0x65926d329c0b61eac803,0xee8790618000000edc98,0x10bc865e85e000214,0x29350000000052b1e4,0x983cec32800000000000,0xa1460d18000c12400046,0x254858d04ba283210cd6,0xd6000000000000000003,0x60836c0024cc0000003b,0x28bde96f362000249],#[0xe7c00000000000000000,0x3206e00023c300000004,0x509d0003225000234d83,0x3f0000326c404a38d054,0x8b000200400000004181,0xd8dec0000000a73264f1,0x91c000a9fa9d,0xae000000004760003425,0x14000485c000028f1c2c,0x834bc29435f084524ea1,0x259000000000033bb4fb,0x869785a45400000002,0x18505043000000000000,0x4cf8000512bbb9000043,0xa8400020c91390000000,0x468cb2000000033214,0x400000020a80b8020100,0x2978f1c074806400089c,0x46a000000000000002,0xf699639c80270a74e180,0x39e600010efc10791,0x5bc0008720000,0x7e4aa529822a4d440000,0x8cfc000000000081,0x16c000000080ad8f0000,0xe6a093cbe400021b8,0xe01dc00000018c642380,0x1a5a000130,0x5400000021010000000,0x10244c58000d,0x3c95000311000033f100,0xa44000000],#[0x2bf20a200000000000,0x900024bbcaba88f00000,0x33a14610a61000112,0x31a900003f3e112227,0xa3aa90b1f42f600000,0x6444c88daaa0e2e0e200,0x10c00022eb4e7a11c025,0x3020302dd00011c18ef0,0x712bc000e9aa377c0040,0xe7dd2f12c2206a4cf2c4,0x67c30f0000000d1c0292,0x72486ec0713a0000000c,0x4000000000004f90ab52,0x3aa879f4a2add7037c71,0xb8feec23cee00009117,0x4a6c2bf8d3301cda8093,0x28ca45101ac02854b,0xf4a2e745200004780442,0x224600032880b1dc20e,0x142f6f422e58d6ea1500,0x6484b34a1d85d000,0x75021019acccd47aa890,0xe4d1f4ad000013f00022,0x49b80000002089e9e741,0x118603740000000102,0x34000ce4bacf00000000,0x32ab4e1c000c6,0x96e4c0222c630000000,0x89000120e000321e0002,0xd0dd800000000000d8e8,0x476f99d0002ab80001a5,0x325f4df484ec48c000],#[0xd308000293ba140,0x82bb217f3c6000249100,0xc39d044cd303e4e89,0xe8869c00009402738220,0xc8b6a4c3826131a4822b,0x818ab2b878c000000c1e,0x7781530eda16ec3ed27d,0xe6c01278a02fd300c436,0x20af651d45a4d383438d,0xb710002488000292bc98,0x3ab22ac7d4a600000002,0x3e201369c6b40000d2a2,0x214,0x40a8000,0x322c74c00000012490,0x4000321f9e0000000000,0x42d67930b8527c000ceb,0xfd0a18000000204790b2,0x498f3,0x246a000000046f000,0x2b0459403c2cf00011fa,0x9738aae580000ba9b6a0,0xb4b31d400000023b0ce,0x0,0x960,0x60000000102044300000,0x3c0,0x3ff85b8d70c3f8b12013,0x500000ca8000a9ac2724,0x236e2a,0x14dcaceb9e000390b064,0x8360852d290],#[0x20000000000207900000,0x8ae52d10001202000086,0xf7000001b6a5e,0xb400044b0000c7ef2900,0xdad86f000188b0b,0x3fc00000008cb4000114,0xdf00028f800022190001,0xc514000000000051b60,0x337169473d00b0000,0xa4600004cb10c9,0xa4000000000000000000,0x400000029fb04d0000d0,0x5b505551e400045a,0xcd081f98f509e3090000,0x60000000c0238d7d2404,0x298d9f58364000c13788,0xc18b6b4bb00000000000,0x10d732f00028238,0x0,0x9c00003a7a41c7052000,0x463c00000000008fe5,0xcd33b448d6c7e0e400,0x49ac0000000000000000,0xa64000218f49e0150a1f,0xdc00000002fbc9d34c4a,0x14854f8c0000d2329f8e,0xb702b680000000000000,0x7b000000000000000001,0xa00033a600028dac1281,0x3860000000000033f,0xda800050e240c0000131,0xe39619349db2e48],#[0x80000000402d31542b00,0x38f00003590003081e7b,0xc688bc00000000000002,0xe6730580000000118f0,0xc6002afc684000000000,0xcaa9082,0x121f00000000,0x4608d0000000000000,0xc0540000000000000,0x4a100032b60000,0x3048000000000000,0xc2180000001057000000,0xb5000045f8226,0x205d9870,0x30b9054a4a8440ec9300,0x898b0990001a9c000,0xea000000000000000000,0xec77004c00031d800020,0xcefe2208a8000000003f,0x2a57c4f64a50000000,0x6b353a26800000000000,0x11830998000523e49d6a,0x1ac6d51bb8a55319000,0x3dc6e8000000035749b6,0x6000234043ea9f200014,0x8fc800085721254b6333,0x18aa540001b6d40cc000,0x81a1b51971e1c1b110f9,0x14566a5409112,0x487c9a40000000000000,0xf5a7bc00000001de8179,0x844b8000000332400023],#[0x4424000ca0c00000004c,0x3380000000000cdfc000,0xa4000923641000000005,0xcdc800000013e571,0xd25e22c24b,0xc3c012b0000,0x4c544b2870f45200000,0x42a73970000000000000,0x0,0x3a520,0x1a66819c0000003be500,0xa7d00033ab0000000000,0xf000030312d8000c59c,0x1c5c3c740000000abf68,0x883c0dc41a69af51bfc8,0x40a00001f100021d1,0x75017f10a0d505740000,0x33c8525400041,0x123f000,0x26800005068,0x4bc800000000,0x203209559ed000000,0xd1f400011ae457,0x562144f2a2ce61342e10,0x528d834410b92c0b03c4,0x8e7c8b5381cc0000092e,0xe3043e68fbc,0x60e14000e8d902900000,0x4cbca4000000000030e,0x10f2cdf00000002c6a,0xc4000ec3b014030b0650,0xfe000101b00000924a],#[0x4bf00018340000000000,0x48c00b0ce500000003,0x80000000000303500000,0xc3a400049e10dea7cf17,0x5f0000c4a84820f351bd,0x3847400010730859a584,0x4339398d01aa5386,0x95c000341b000,0x6a8400001ec,0x306fe8eda21821c0,0x47cdc648bdc000103400,0xb0a2b20b04c8e0dd4000,0xfa8f5c86d374016a3c0c,0x61d64f5223840a339649,0x9dfcf4ac8c452c0002e6,0x204cecc0004756,0x881b2c3419a33886fc0,0xa7f40000cc0000000000,0x50380000000000,0x6000000030c892d729d0,0x527f0c4f858b1173ba4c,0xa2c0000000d1fc0000b3,0x6728f433742d800080fc,0x9b2f80000003361cfa72,0xc93e07e933fb3f0974c4,0x13a000023f8ac2538c,0x918fd00012436c2c0b20,0x316200038d300001c641,0x3990000000a9732f5000,0x2f8de01f700000004e4d,0x602a8000000295d00038,0x45300008c2a3a383b811],#[0xb480000000000e66c000,0x18f90002461c6bb2574,0x213000000000000a3000,0x8f6908a9e50000155000,0xff449a32700021210000,0xfc06200ea19000000038,0x22528d7611b0001a0,0x340b08cf2704f170f8,0xd840705680e3a1cf3200,0x18c06cb4455c3503078f,0x47e8d8106b323f2ef8ad,0xd0105fbb600011b2868b,0xcef8743b50440000000a,0xb3a8bf80f38e751c,0x8b80008700000,0x4821c120d391ef9c0000,0x328a0002aa80a2c00010,0x42813a4894fc5b4ca,0x2f93290cd00000000000,0xef07e08f8bcc00000001,0xcd10000434b35040e023,0x10db04d91a300020fd,0x41f0000000c8270270,0x141690a000041e800000,0x1056000,0xf9e86c0000,0x1000026a81e386100000,0xcad4000d1272fd40374b,0x29300030b1502741d,0x3112000000090720400,0x2a6e0f84434845d1e500,0xa9dd1a4000],#[0xd600005003a9f0000,0x4ca042b74ce800000000,0x12f81b9eef447b87e517,0xecec0e1033c05c,0x1c2488b98000000007c0,0x135132400000003f7c4,0xc045831049]]
def g251D10 := limbs80 #[#[0x350543405013048110ff,0x561d4551d05414c76058,0x364991641925455054d8,0xc62a4941dc630fc2100,0x1a46217253530438ea36,0x6956388a60c7c9d570,0x2c810f010e83820d050,0x91b2b250203181d04102,0xb29210c1c0b09132a2d1,0xfbd055fc3404ef3db480,0xd4077bfc4042e00419ec,0xa9c0077001cf21c04ec,0x80828b9d7a00a4eec130,0x80c19f01efe240605577,0xc84eeb605293680c3b30,0x40cc7f000c1bad822f80,0x40cf7f82080]]
def g251H10 := limbs80 #[#[0x56060043202028080002,0x14058a80e030004010,0x40f6a832820001d1b864,0x642a46028e4224d200,0x4520310002018480c020,0x601148601213000682c0,0xc0a7160c0c9e0e091750,0x14c1e273b80c081f0013,0x9c412bc01b50840c5b,0x3a0c000c401759941118,0x8003903800022b00000,0x30e6c234800242f09858,0xfa6ed5fa93c59841e314,0x471a3a563c4887a26db8,0x35c77c5a06a26260c385,0x4524f6ff5011fe11624e,0xe2c40ba3560b04c68766,0x4412432a9436405c955,0xc16042324340d62b669c,0x22583e80047368101805,0x8307660e056b84158000,0x7385d5e241050a628000,0x858263a1d24f353d8966,0x6667580047e426000454,0x4683c72800586c4ac7aa,0x80021680024e57847063,0x80f8d26b000652053a1d,0x290840d0f761217c533,0x80007961c80380002ee6,0x8548911000000028e560,0x46869700002a80076b0,0x31294100007c28cb9000],#[0x46162e51c21e4b800013,0xaa29c8180000037b8002,0x228e2e02fa4d15680045,0x8f08bc7505e40e844800,0x47685f87e88a25d40d8,0x80073788aa3328f95500,0x65219e5ec3727982720a,0x9b5421063d80193aa306,0xa40410a3c60620935258,0x6a654000465e1482a009,0x922be74778a4780028eb,0x11383783fe7fa92d1486,0x9643200857b52be49651,0x8561a89e8623be9507d4,0xc5596a86bf7dd58c87e4,0x12b82e7101b11d15ce45,0x1c7db87261600e1585f0,0x73c7708580026ae4fd1,0x67846e3d108211800000,0x9156639379c156593122,0x362694922d0a46f02861,0x6e42022140758da1e195,0x397e26fd59341b59f21e,0x64842c3888840ce7b43,0x8cc08827968e2421a08b,0x561f35ee29184b578005,0x23cd6358380060268c53,0x5b466c4532fb68586000,0x52d75b41f81469267be,0x62cc36260e07c52895c0,0x6cc84023f1d85da36936,0xfc26a7880036ca05a39e],#[0x583474e3f10b61611300,0x4ed6f080387c7f373000,0x284b096a4a02d091a0a0,0x38e31ee8d61e82220168,0xf617203486a3ad1742f,0x8c05655631a6301ac570,0x87855189128274284745,0x3e750e04c1c088890734,0x589355175de7ce57c70e,0x45b84da7242544451,0x13f4fc84f2dc38280800,0xf64208dc50006c1b86d6,0xd0ff2b26895d220e49f5,0x18822f5b84ca5651f061,0x22dc02843d7974243b4]]
def g251D11 (j : Nat) := if j=0 then 0xc1010027f else 0
def g251H11 := limbs80 #[#[0xd00fcf40c308564f0080,0x33923801a31e10340001,0x3d9973db80298b64b,0x1628065920d61a5001a8,0x8014c9c00ac000024be,0xb32e8fc88983440157]]
def g251L : Nat → Packing
  | 5 => (15,6,7,983054,68,7,1024,g251D5)
  | 6 => (227,5,7,6619315,120,11,1048,g251D6)
  | 7 => (1287,4,7,7275088,122,15,1171,g251D7)
  | 8 => (1233,3,7,3014876,104,16,1186,g251D8)
  | 9 => (303,2,7,983063,69,14,1116,g251D9)
  | 10 => (23,1,7,65537,0,10,1055,g251D10)
  | 11 => (1,0,7,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupShort 4 47 2 7 4 1 g251H6
  | 7 => lookupShort 67 673 4 11 8 1 g251H7
  | 8 => lookupShort 399 8161 4 14 11 1 g251H8
  | 9 => lookupShort 402 2579 7 14 11 1 g251H9
  | 10 => lookupShort 103 449 9 12 9 1 g251H10
  | 11 => lookupShort 10 53 5 8 5 1 g251H11
  | _ => fun _ => none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P5_0 : block g251 5 0 15=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B5 : block g251 5 0 15=true := g251P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_7 : block g251 6 7 220=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 227=true := (@block_merge g251 6 0 7 220 g251P6_0 g251P6_7)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 71=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_71 : block g251 7 71 512=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_583 : block g251 7 583 512=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_1095 : block g251 7 1095 192=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 1287=true := (@block_merge g251 7 0 583 704 (@block_merge g251 7 0 71 512 g251P7_0 g251P7_71) (@block_merge g251 7 583 512 192 g251P7_583 g251P7_1095))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1 : block g251 8 1 20=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_21 : block g251 8 21 445=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_466 : block g251 8 466 512=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_978 : block g251 8 978 255=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 1233=true := (@block_merge g251 8 0 21 1212 (@block_merge g251 8 0 1 20 g251P8_0 g251P8_1) (@block_merge g251 8 21 445 767 g251P8_21 (@block_merge g251 8 466 512 255 g251P8_466 g251P8_978)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 13=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_13 : block g251 9 13 145=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_158 : block g251 9 158 145=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 303=true := (@block_merge g251 9 0 13 290 g251P9_0 (@block_merge g251 9 13 145 145 g251P9_13 g251P9_158))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 23=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 23=true := g251P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 1=true := g251P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 11 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g251B5
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K247) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=50397251) (before_sound K247 V247) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K247 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V247 low251 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ff00000000000f,0xf007fd90b01c89b605f2])),(BitVec.ofNat 152 (word80 [0x944a2512928944a252,0x51289590900c09960110]))),((BitVec.ofNat 152 (word80 [0x1ff0,0xff8000c0060004c411c])),(BitVec.ofNat 152 (word80 [0x8d46a351b1a8d46a36,0x351a8c04002000084118]))),((BitVec.ofNat 152 (word80 [0x3fe0000007fffe000,0xc0810e839fbf])),(BitVec.ofNat 152 (word80 [0x3c1e0f078783c1e0f0,0xf0783c00800000839fbf]))),((BitVec.ofNat 152 (word80 [0xfc0000007f80000000,0x7fc230301f30a8a4f])),(BitVec.ofNat 152 (word80 [0x68341a0d0d068341a1,0xa0d06820010012088a4f]))),((BitVec.ofNat 152 (word80 [0xff8000000000,0xff8000c0c02000c2015])),(BitVec.ofNat 152 (word80 [0x72391c8e4e472391c9,0xc8e47008040000042005]))),((BitVec.ofNat 152 (word80 [0x3fffff,0xf00002300ffc03f13261])),(BitVec.ofNat 152 (word80 [0x40a0502808140a0501,0x28142200fd052600040]))),((BitVec.ofNat 152 (word80 [0xffffffc00000,0x3c00ffffc01c388])),(BitVec.ofNat 152 (word80 [0x80c0603010180c0602,0x30183401afaec300000]))),((BitVec.ofNat 152 (word80 [0xffffff000000000000,0x3fff0000001fc00])),(BitVec.ofNat 152 (word80 [0x30180c0606030180c,0xc06000e600000006000]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(2,0,253,0,12),(4,0,251,0,12),(16,0,239,0,12),(1,0,254,0,11),(8,0,247,0,11),(128,0,127,0,11),(9,0,246,0,10),(32,0,223,0,10),(64,0,191,0,10),(0,2,205,48,9),(0,16,173,66,9),(5,0,250,0,9),(12,0,243,0,9),(32,2,205,16,8),(33,0,222,0,8),(40,0,215,0,8),(64,16,173,2,8),(65,0,190,0,8),(72,0,183,0,8),(129,0,126,0,8),(136,0,119,0,8),(0,1,86,168,7),(0,8,54,193,7),(41,0,214,0,7),(48,2,205,0,7),(66,16,173,0,7),(73,0,182,0,7),(96,0,159,0,7),(137,0,118,0,7),(160,0,95,0,7),(192,0,63,0,7),(1,8,54,192,6),(8,1,86,160,6),(32,1,86,136,6),(64,8,54,129,6),(128,1,86,40,6),(128,8,54,65,6),(40,1,86,128,5),(65,8,54,128,5),(160,1,86,8,5),(161,0,94,0,5),(164,0,91,0,5),(192,8,54,1,5),(200,0,55,0,5),(168,0,86,0,4),(168,1,86,0,4),(193,0,54,0,4),(193,8,54,0,4)]
def g255A : List (List Nat) := [[],[48,65,101]]
def g255D7 := limbs80 #[#[0x5d570541b8e899759550,0x543b2699755c15069986,0xe19755c15065b865d570,0x5d5506e975d9570541a6,0xedba266176543b0e8996,0x65d65581b8e899759560,0x583b5e899759560ec3a2,0xe89985d560ec9a65d570,0x5d9606ea96e4175583b5,0x6e7a05d765583b0e8995,0x64187597b5e899061d65,0x597a56839261d65edba2,0x6839261d65ecda0e4987,0x61d65ed9a0e4987597b5,0x6cfa5e4987597a6e5792,0x5d5655c3a6e979261d65,0x5c3b0e89965d5706dba0,0x5d59099570ec9a6e4175,0x219756d97564e655c1b6,0x6e7a2619805d7b268d86,0xe41835d5b9e898660d75,0x5d5b8a9b9060d756e296,0x6839261975e95a0e4986,0x61975ed5a0e49865d7b3,0xed5a3e49865d7b068f92,0xe49865d5b0e979261975,0x5d7a7e9792619756cfa5,0xe8996e0175e97a265b80,0xe01756c1a9a1b805d7b5,0x663a364176997b26a686,0x66176997a2681985da65,0xd43b26a3935da656c3a2],#[0x8f39d6a4faec9a65d560,0x5ab54eb5aa76a95ba3ea,0xbc3eb0f3c2eee5ab95ad,0xc96f23bc6eb17ac5cf15,0x4eb51bce6b35acceb273,0x6f71ada6b65ad66b55ad,0x4227c30d5e1026f085e8,0x30bc30346485c3202578,0x7bb52fbdc672edc7b76e,0x7b7277da937ed4917864,0xb7323e11b1f08fc76e56,0x2751e1381f099af6e74f,0x42ddab56f15bb76ad9fc,0x27dba54e9d3976e8cfb7,0x7d3affe9d6974eacfa75,0xe1e4c6cf217857ffa762,0x95a2f0df17878b3b3c18,0xd85702c2b815b5c0b9bd,0x40f0a11b8160dc0adddb,0xfe9e45f52f0fc0801e14,0xe9e7874f33ba795ddbc6,0x238153ba7a5dd3d0e,0x44a100380c0280801803,0xc9322c811dc6d1945d15,0xcd733cc72fcb72b8a326,0x92a47d14420fd3c8e737,0x1785c1685714d5153d4c,0x9ca709ba6b5a56759060,0xa0a809fa7c9ea789da74,0x36c19c198b5c188a1a84,0xbbc400cac1c05f037c,0x941b213857c4],#[0x401004000000c050100,0x5808000000,0x90d21d41a42809010000,0x321a644000148402,0x22c20001b412f2200]]
def g255D8 := limbs80 #[#[0x6a587595506a17659550,0xe899759550e819759550,0x659755c150619755c150,0xa19755c150699755c150,0xa99755c150a59755c150,0x5d7655c150e19755c150,0x65b865c150687655c150,0xe81965d550659865d550,0x6a6965d550e89965d550,0xe89955d95065b865d550,0xe89985d950e81985d950,0xe99985d950e8d985d950,0x6a3955d950663955d950,0x6829661d506589661d50,0x6a575d955065d75d9550,0x61d90d95506a176d9550,0x69997e19506a197d9550,0xe8175595606a17559560,0xe8d87595602958759560,0xe899759560e819759560,0x65f9059560e959759560,0xa15755c160699755c160,0x5d6655c160a99755c160,0xe89965d56068e655c160,0xe89985d560e95965d560,0x69b905d56065b905d560,0xa63905d560a5b905d560,0xe81955d96069b985d560,0x6a6955d960e89955d960,0x6549561d60657905d960,0x6979361d606579361d60,0xa979361d60a579361d60],#[0xe8d87995606a57699560,0x69d969956061d9499560,0xe8d87a15606a576a1560,0x69d96a156061d94a1560,0x69597d9560e8175d9560,0xe99905d56569576e1560,0xe81935d565e59935d565,0x69b905d565e99935d565,0x683965d565e1f905d565,0x2957660165e817560165,0xe818760165e957660165,0xe958760165e898760165,0xe499061d65e419061d65,0xe899061d65e559061d65,0xe959061d65e8d9061d65,0xe4b9061d65e999061d65,0xe579261d656839261d65,0xe979261d65e839261d65,0xe5b9561d6568f9561d65,0x29975595706a576e0165,0x66175595706197559570,0xe617559570a197559570,0xe819859570e817559570,0xe8d9859570e899859570,0xe999859570e959859570,0x697865957069b8559570,0xe89965d570e81965d570,0x69b905d570696965d570,0x659759957069b9061570,0x5d590995706997599570,0xe1993995705d59399570,0x6999799570aa19699570],#[0x69997a15706a196a1570,0x69995e19706a575d9570,0xe89862197568d8621975,0xea58621975e8d8621975,0xe8186601756199021975,0xe898660d75e898660175,0x61b9060d756a29660d75,0x69b9060d7565b9060d75,0xa5b9060d75a1b9060d75,0xe499061975a9b9060d75,0xe899061975e559061975,0xe959061975e8d9061975,0xe899361975e819361975,0x64f9261975e959361975,0x68f92619756839261975,0xe5f9261975e579261975,0xe8f9261975e839261975,0xe9f9261975e979261975,0x68f95619756839561975,0x69590a1975e5f9561975,0x68195a19756a190a1975,0x68186e017568d95a1975,0x68196e0175e8986e0175,0xe9596e0175e8996e0175,0x659935d6656a686e0175,0x661905da65e81935d665,0x661935da65e8d905da65,0xe81985da65681985da65,0x6a3935da65e89985da65,0x6597560e656997560265,0x6997560e6568d7560e65,0x6a57660e656597660e65],#[0x6599061e656817661265,0x69975583506599361e65,0x6998758350a997558350,0x659865d750a998758350,0x6a69661f50e89965d750,0xe89955db60e899759760,0x69576617606a6955db60,0xa37d0fe87dc3de1bf0bf,0x797b4bce4ff1fe8fdc7e,0xfe7f53db9bd4d7a5f72f,0xf3a73d37e9af4bfa5f51,0x3fa9f94fba7d53de9ed4,0x5dbaddd67eafd57baafd,0xd8fec7d5fcafd57cebbd,0xf69eb3f59eecbf65eb2b,0xddb5edad6d3b5ddaded3,0x3d6fab7b5bcedcf6deb6,0xae5d6eeb5757bab5c7ee,0x17d8bbc3fdf6aef575eb,0xcade3fb1f78f7c79e2ff,0xf33f97ecbde5df2bf95e,0xed2de8ff3f59f3cede6e,0xdf53fa7ed3de9df4bfa5,0xfad79eb7b5b7abed5dea,0xd6f6adb3ed9dec7f63da,0xbbadcf6e6f6f5b5edae6,0xf2ef8fdc7be2ff0df7b5,0xfd3ee9df47f9f5cf3e6d,0xff6ebb3dd9beaf756faa,0xa7ebaf4f7a6fcbde5bf0,0xf5d433f35f5af9d7c7bd,0xdb107506a42d71a80b6],#[0x2c6e020ffb3050e6e81d,0x40fb201436c42507b206,0xa4be8c544fb61f02ecc0,0x10c3b8c349e586c03ba1,0xc9296df18c1b8c43d6df,0xcada5a62d6d5d4b80fb2,0x52c3ded4a8f5b62b3f6c,0xe52009b94117ecd08f5b,0xb236046e8d415ba34056,0xec8f009b94517ecd180f,0x3b23d026e8f85db43e18,0xdec1a007ba3b176d0fc6,0x55b57d3d6c19cf5b06a3,0x4be8d641bb2780fec9dc,0xcd7b0bc18ecd816fa763,0xf7665ef8d3b2bd2bedee,0xc00fb2b90aecafc2fb0b,0x901d6c6406fb28d03eca,0xe9d3fa7a248ea61411ba,0xa0b19ecea06fb2a85069,0xd42513b50645ec819c1b,0xa60a896582a25a604446,0xec800efb30d90ec81a25,0xbb30033ec80033b3000d,0x9ec00d67a2022aedc00c,0x93b21d836c07135b8035,0x1cec880abb71e33ec878,0x51fa70e1cec8384bb720,0x238ec048dfb20e07ec84,0x41c3a70f75e883cdfb21,0x106eedc41d7b0106ee9c,0xc6073b218636184d94b8],#[0x61409edc6437b21912ed,0x98559fa31560e9c5193a,0xb71563ed8557fa71563e,0xe9c5d7ba71662e98597f,0x7b5154de98553ba6145a,0x7e9c5d33a6164ded8553,0x6bb3211cec8847bb0214,0x91ecb0d1bb2c312edc84,0xe33b2c53cecb162fb8c3,0x965ee32197a8c837ecb1,0xaa3fb22a45ec8a937b2c,0x2236ecc88dfb2228eed4,0x9d67b02759e8898b7b7,0x72385ed4a61bb2294d6e,0x8898c6b924622a4963b9,0xa52780e5c99cfa52674e,0xed49dd3b0277fe5c9dcb,0xba2267ee5ca18cb82772,0x4e949e1bb02785e949a1,0xffb72784ed49d5ba5278,0x56ec9008fb2407a2e09d,0x89fb23223ec9248fb243,0x380edcca17b53286ec8c,0xbdcba52f86ec8cc9fb23,0x3165ed4c5aba7306be9c,0x91137b23656ec8d97fb7,0x24a23ec91d5bb24423ec,0xdcea1bb23a07ec8e4cfb,0xa7386ce9cddd3a23780e,0x2e0e1afb73874ec0e1af,0xbb63d1a6d8f86bb63c63,0x3ee3298fa8ca1a6d8fc6],#[0xcfb2cd7aee329eba8ca6,0x56ecb318fb8cb63ea32c,0x4fab96740ecda111b66c,0xb40ecda50bb26944ec1a,0xb59bb0730cecdc911b06,0x6e67e8db993a66d66e95,0x9b997b56e63e99b997a5,0x77061e99c18ba66f63ed,0xd9f20db67b5ae9dc577a,0xb57e42ec9ea0db079816,0xec9dc83b28220ec9fc59,0x3a57471e89d1c3b57771,0xeed5d5c7b0756ee95d5c,0x47b278706c1d97cb8756,0x1aece0073b28059ec9e0,0xc73b2831eec20c83b281,0x289e1d484bb7831aece0,0x4dfb975351e5d520f975,0x5487e1d508ab95331ae1,0xd59e7975568e8955fb97,0x26677e5d5da3b05678e5,0x1d2d83874d07ec93ccfb,0x874d446c14043b24f6ae,0xe1d45ab874e7ee1d31c3,0xba65957e956563a3596a,0xee1d717f875b57e556d5,0x6b875e5de1d7557a65a5,0x246cd8623876184e5985,0x9bb36088e1d8e13a661,0x223ed98093b56057e958,0x9213a663246cd8d5fa56,0x5887e1d9577876455e59],#[0xd6593a65866e9561f792,0x5963e996597a55967e8,0x9565efa5597ce8d65f7b,0xa7594de9965eba6594de,0xe996d97a55b67e8d6de3,0x7b55b65e556d7fa75b63,0x2e99717fb75b63ed96d9,0x87a65d61e99697ba75c6,0x7d6c17d6ba75e5de9d75,0xdfb56065e9580ebb360,0x22eedd817fa76033ed98,0x84ddb3615fe9d8997a56,0x6188e9d862ba6618ae59,0x98cddb3631c6cd8471b0,0x3607de818223a7638ae9,0xd98073b5604de9581f3b,0xb6621c6d58937a5621ce,0xe599071b3631c6c18c71,0x7b2bd37ecaf4dfb2ba61,0x4ecac59986b239ecf023,0x31b8b44c662d17987b42,0x4decae473b2b51cecacc,0x873b2b64de8ad931b3b9,0x84d6c2e137a2b71aeced,0x2473b2c21cecb0537b0b,0xab4d6e629a3b08a68e8a,0x2b0bfb7ab38ed6ada3a2,0x5ae4decac139b0b0686c,0xdeb95fb5ae53e9eb95fa,0xa7af256c2bd35b8ae53e,0xe96b9a1b0ae68e8ab547,0x9b0af4ded6b935b5ae4d],#[0x5ed6389fb28e3ceca347,0x95b591286c64487b78e2,0x86ea4479b891216de44,0x1e7b78d7deca349fb28d,0x86ea4095b590286c64,0x3c97b58f27eca3c79b59,0x92256d648a1b19221ede,0xe2d9fa38b1e6e24885b7,0x2880deca3135b98b67ec,0xca11ebb9857aea615ebb,0xb9844aea610abb78433e,0xece1d29b3874aea61853,0xfa79357e964d63a3934a,0x2e5e594f979557e56554,0x9fb09b51e5e5d47a7945,0x82e5e7883b79b24ed66c,0xa0ba79e246ce7891b09e,0xc206c27dbba7a282e5e8,0x7093b59c57e96709bb39,0xa057e968083b79c53e9e,0xe7493b59d27ec2754fa7,0xa253e9e8483b79d53e9,0xc28e0ba7a2246ce8891b,0x979a53e5e65539798206,0x6c2994797a551e5e9147,0x640001fedea87fb7a91f,0x8903d81980b1041817c0,0x33e1950bc05b82c81360,0x12108984001d60d986a4,0x46522fa1680aa44ee24c,0x61f78f5076a38e1ba0d6,0x4c8f846222290ec84240],#[0x5f29d14989e84cd25812,0x7f8bb85c52d4967cb065,0x6c334999eccc663c3101,0x1d6ce7873238a9be0ddc,0xe7dd3e09eb4f2c78c3c1,0x9a1ad0c6846417a044fd,0x728ab44ea25511087b43,0x8e24511fc8e846e23251,0x2d695e4a7a50d26692b4,0x4e2a6c93409934c2a5cd,0x14089f54f6a7953ba9cd,0xd52128d9452a1c50a283,0x1d4fea77537a99d4b4a4,0xb7557aa9d53ea97547aa,0xc255f6aeb56e2b3958ca,0xb635a52cd564cb19588a,0x2ee1754b9a5c92e156f0,0xac0f5ffafdd7cebdf5e4,0xbb12d87ac35616b09583,0x2ec8f640b1e58cec5f62,0x7bb38d9aecc765932999,0xa7ed37697b47da1ed036,0x6c6b605ae8d676afb53d,0xdbceddb6e3b6edb58d98,0x67173899c3ce166ffb7d,0xdcdce6672f3959c82e3,0xc175cbaa5d3ce93745ba,0xc8de24ef57743b65d92e,0xf757b6bd95ea0f407983,0xbec9f4ef9a7c6be15efa,0xeffe7f13f69fa4fca7de,0xec1b20c1054822c0d202],#[0xd10d586142ce14308d83,0x9bc4be24f11f88443c21,0x3091748b645822a91438,0x8e146c635319c8ca4632,0xe42f20c8fe47963b51ca,0xa9314946481238913c87,0xc25432929454a0a4f526,0x97acbaa5c52d595eca,0xd0a66d32a98c4c426113,0x3979c24de26cf35b9a7c,0xcf7a7a73c89d94e9e73f,0x1440a15d0567ff3f49f4,0xdd24290b47aa32d17689,0xdb4daa67d3129734a6a4,0xac5502a5b51aa83d3f29,0xb45596ac4d5f6ae3564a,0xafdd7bebc55daae756ce,0xec99636b15585ec17603,0x4b4c5a42d01673b35d98,0x76d996c4b5e5ad2d596a,0x2eb935c56e0d6f5b72db,0xe9ef37784bb0dd36e797,0x7f4bf35f7af9f7babd95,0x616309b842c12e053009,0xd8cfc5f62c314588ec38,0x164d323f904c7e63bb1c,0x1d980cbc659f2bf951ca,0xea67333819b2cd266733,0x423a09cfde7cf3d19dcc,0xd3ae99b4bda48d156867,0x75abac4d5b6a7f521a84,0x4d98ec5b617afcd766b8],#[0x3b6ffb70db46d6b699b4,0xcdde2eef776bba8dcdee,0x7b811c00df8efa77b7b,0xc6de2f715b89dc40e157,0x72f795dca6e4972138eb,0x9d16e85740b9e7cd6e65,0x5f56faa7d46e9f74c7a4,0x1d83707e0fc0f85d73eb,0x8a0740dac1781e0f831c,0x6ce44cb78809f81a1bc,0xcc591b22a702c1bc1d89,0x2015983d140720e022d0,0xe8647bc2e86d8a856e,0x99030461ac00820050f0,0xa8741001383d81703ac8,0x24a48c9786e1f6338383,0xe3e47c944468881750e6,0x823e80e102ae13126e18,0xba8008562588910b1582,0x8bb0c25dc33864746594,0x84ee292000b22624a076,0xfc300a3956180f211c22,0x2708b0ff0c8b91682f03,0x48a82c0e0285a03e727e,0x91d51e4882900f24ec05,0xa43b41f4250aa0e09e85,0x1782b8068091401e0e12,0x15c2b703e08e22c38835,0xb85050946243440160b4,0x8999d18a630fe1f90ea5,0xb1d80019c001be5f6206,0x7f55c824ae3fe002367e],#[0xbf1ed00066bfe804a04f,0x41243f2a0019aefd009a,0xfc008300802027bfaae,0x198bfb0003280401004,0x115beb600066cffad80,0x342797f1000660097f0,0x702fe2000cddf2f83300,0xff2e180019e7febec004,0x13c5063fe178d800921,0x8a4f160002163f0063,0x8a0eb8031d75006451fc,0xc5a3c5060147e00c6027,0x3268f141d700638fc018,0x492f36e000cd0fc008,0xe000198fe0140ffc05fa,0x10dfe022069b78032879,0x800084ae00c73fe00880,0x851ebc04497e0002121f,0xa78031a78031829f8000,0xf76780330077fd298033,0xa4e0014607880a3008bf,0xa9bbc00042ae3f004500,0x5b2c86f9051c158c0200,0x906c80d7c8ac2672c51b,0x7c06992489a2072,0x7434c0e6c2011618b080,0x63e0818f82d4180ec4b,0x66d0ea0f0e0804b8100,0xa3562ab0e6c337a1004d,0x9702000000e742018ea0,0x83486c84682341000000,0xd046],#[0xe0ec426d84025c080000,0xf1056e06ac20000db0f2,0x22c316125c924b82a0d5,0x55caa25ba1a607a7040,0x19b0f8e0803dd08,0x20015b10000590d30200,0xae08baa0ac872d080530,0xc1d0ea0ea0c7f316a0f,0xab08045d0c5d080007ce,0xa0db818fe62a43643d61,0x4e551007ee0ea0c7f316,0x5d50548400000003,0xc8548690800075a28800,0xe147b41c703aa840000b,0x29ba19ba1da08cd08043,0xd0468200000000012f98,0xaaa8c000000683486908,0x2bc1a7f3a41b7d758fed,0x4388433c1d41d419702,0x7505ea60a9c0cf685ab3,0x7d4ba200efa200c,0x7ba100d41d4129e0ea08,0xe8400b78201161000000,0x301aba1ad8184c068,0xe8400f78273c10035e08,0x44341d703ae040000020,0x602c040068277a1,0x90990ad04c84c87a5620,0x980800066562321d5a11,0x1521a4348580b010ba28,0x58200862c101c5441745,0x90d21a4348618b04010c],#[0x39d18a90d21a43d858a,0x2ce8c59d18b3a3130117,0x682642642b4132103e0a,0x400c855ee941ead08c85,0xc8732b11908000190ad0,0x15a0800061cba2aa2688,0x62000000000032100c3a,0x4783b6853782e742015a,0xcd5499c6c4abc18d8401,0x6080180d90eac4c2032c,0xaba1a3a18d84038d0db0,0xa2602c07edd1346cbc1,0x1b60490e08cf220a353e,0xb6040227b613af06d8,0x3b686d81060c14bd1383,0xed87b61007de0805b0,0x301b210000b21ed87b61,0xb62e68e07820001db080,0x1b21e703ce04031f3822,0x36431bc1b60796861438,0x52fb1a0d80fb815e42a4,0xeb81000d8436100ee8c,0xc20000003411a08d075c,0x864c8a200670201db0f6,0x1ee040002581ce958cc,0x83ee0402b2d8a581f702,0xc84019c0f1fa4a8cc856,0xd0807584006823419604,0x29]]
def g255H8 := limbs80 #[#[0x64000000502080409a,0xa30a000001816e01d840,0x47c2f370548000000092,0x989780000274a8024600,0x6ee56960005001,0xc800040000233a99a000,0x4000000932f3983c,0xa013130000000000,0x400d700001d30e000000,0xc223598a061b1e4044a7,0x34c00006c306000027,0x4468835b610aa858ad1c,0x266068e83b040a]]
def g255D9 := limbs80 #[#[0x595505d9655417559550,0x543905955065d6554187,0x61970541755c15059570,0x5c150a1970541965c150,0x543865c150d957054296,0xa1975541965d55061975,0x5d550e1975542965d550,0x541955d9506197654390,0xa6176542865d95066176,0x5d950e5576543865d950,0x541976195061d8654398,0x659875409661d50e4186,0x9d550e41875429661d50,0x54187a195061a7654186,0x5d76554195a195064686,0xd955061f6554176d9550,0x54197d95506476554190,0x5d56558197e195066365,0x5956061d655817659560,0x58390595609d56558197,0x61570581755c16059570,0x5c16099570581955c160,0x583655c160a557058285,0xa1575581985d56065975,0x5d560a6175582965d560,0x583965d560e417558385,0xa5576581955d960e6175,0x61560e5576583905d960,0x5809561d6061d8558176,0xe41875829561d6065587,0x995605d6655839361d60,0x581909956061e6558176],#[0x65a65581949956064e65,0xa156061e8558176a1560,0x58196a15606528558193,0x65f6558187d95605d765,0x5d5652597559576e1560,0x597875d56564d7559590,0xe5975597935d565e4175,0x601655d9805957560165,0x596756016565d8059587,0xe41875959061d659d980,0x9d565e55875979261d65,0x5c187e01655db8059698,0x641655c186595705d565,0x59570a19655c19859570,0x5c39859570e19655c385,0x659755c1865d57025975,0x5d570a59755c2865d570,0x5c28661570619855c390,0xe4d865c39061970e4185,0x99570642655c17599570,0x5c19699570652655c193,0x61a855c3869957065e65,0xa197065e855c196a1570,0x5c175d9570662865c197,0xe17655c191d957064365,0x21975657865c196e1570,0x5d48660175640865d586,0x219835d6866017561980,0x60d75659835d58660d75,0x5d79060d75a59835d686,0xe41865d5936197564186,0x61975e4d865d79261975],#[0x5d590a1975e5d865d795,0x61b805d786a197565686,0xe0175a1b805d596e0175,0x5d686e0d7561b835d696,0x64175995865d665a5b83,0x5d66565975995935d665,0x995875da65e617599793,0x66176995935da6564176,0x5da65e4d76997905da65,0x99576602655d58099795,0x659839957660e655d583,0x61a655d9849959760e65,0x9979061a6565d8699590,0x64d879959061e65e5d86,0x583505d560d419661e65,0xd41865d75065d60d4187,0x66176d42965d75065975,0x61f5065987d419761b50,0xd81965d76065d65d8296,0x5d985d82955db6065576,0xe3fe3ee3de2fe9561f60,0x7fe7fa7ee7de77e6fe5f,0xf6beebdebbeb7eafe9fe,0x6deedded7ecfebfebfab,0xeeeedeebee7edfedfadf,0x7ef7af76f6ef5eefeefa,0xaff6ff2feefdefdafbaf,0x3ef3df3bf37f2ff1feff,0x7f57b55f4ff3ff3fb3f7,0xf6bf67f5ff5fb5f75ef5,0x77776f75f6ff6fb6ef6d,0xff7fb7f77ef7db77f77b],#[0xf9ff9fb9ef9df97f97b8,0xb6fb5faffafbaefadfa7,0xfbbefbdfbdbbbfb7fb7b,0xfd7fd7bcffcfbc7fc7bb,0xf6fefbeefe7fe7bdfbde,0xa2159dc3034e6181bf7b,0x4ba9a82e8b5c0f462a0b,0x81e8e61baeb14e17589c,0x681745600ba2bf03d1c9,0xa16a9a10bccba8280ea6,0x860612d485926a02f32e,0xccb0366a181b330c0d49,0x666981b314c0d9a9606c,0x1ccf4e0f9ba606cd5303,0xe1291a50954d084d2e9c,0xa50a49d28427e8c20cb4,0xeba82126a028cb4e1491,0x39e5c004b4e090976048,0xc4f40060da90219d301,0xe5509762a8eba9508e88,0x972766c395c65d4ada30,0x9d314ae660a17b304ee5,0xbe9c35a30c240fa72d1,0x34af4e1b6f8612b6c309,0xe1e8da10f9fd386dbe80,0xa20e49d007066a43cab4,0xad40823684412340208b,0x8be9c4c4b4032bfa9221,0x60db4a2d37a713afd009,0xc2a3fa31521d10a8b69c,0xa5150fd18a88e8854674,0x3d18ab2e8855a7402a1b],#[0xaee98541f4a2abfa5156,0x68634c2eb7a71507d30a,0xc36bba92306d28d06694,0xa01c24d38eade5c6c674,0xbd28e0fe8c708744384b,0x6e9c997b0e4ccd87251,0x85a32c42b5972419d312,0x43e4ba01f5ccb0f34e58,0xa0201bd28f8fe8c7c874,0xdcb100d694808b424049,0x5769b4b554da3a9a6d15,0x4d274ba69fa3d3af5369,0x1ac37a8d545d16a92ea3,0xa2d71ad46b1569f59234,0x1d16c90e8b619745ae43,0x836a7685b4fb449a0da2,0xe53b4673917535ccba9a,0xe727da639ccba9ca6690,0x8536c8ba9e096a4e4cb4,0x8d31b52e14db350a6d99,0x2768ce8cf4e6f92a636c,0xe0cb4e747da63a4cd21d,0x7665a73b3ed31d9fe98,0xa73484bb1a475d4d0935,0xdcb981be94c0ff406025,0x9e80c86f4a623fa3316,0xd2132e69a9753411d119,0x5edb972f3fd0179f69c,0xa331375499e3e5cbf574,0xbd198d7e80c4df4a6277,0x1fe80caa74a6350a531a,0xca174064db97323dd119],#[0xaa817a5327dd29941e88,0x755568c3aa425d9523ae,0xebb2b3161d5602ecab11,0x3665d49f32ca2c187567,0x4c2f4eaeb987570ad4a9,0xbab597531bd2a98fe8d,0xa95eabd1af3665d74ff4,0x54b21c26590e1340bebb,0xc26990da70a86d298438,0xfd0b467ed2a843855321,0xa806fa53d16d3a11b698,0xa33e21d11f0968110db4,0xfd19f08e88f86f4a7c3f,0x85699146b4a8217a63e0,0x2c7f4696db974a06d322,0xcb6c5875a80bb2d2de5d,0xa9586ccbac3061d6dfae,0xfd1ac85e9d71730eb815,0x42655216b2eb237a5591,0x1cfb408e7ba2463fd023,0x9231a84738d2239d68d,0xa05093c9a7c268124fb4,0x24aa85ee8142f7269f27,0x31e55418d2aa0c595506,0x418d4aa0c5a5506252a8,0x49a4ba04d5ecaa631e95,0xa04e19d3268fe8d34874,0xfcaa70e691387b469c49,0x8cea36cf745b631a64e5,0x74f745babba8db83d16d,0x1bc51a7de3ad1ef0cea3,0xa6e01ed1f0056a778635],#[0xcbabb836a7805b4fc031,0xe3a19d71b0ceb9ba075c,0xd8634cf58fa675c6533a,0xaf651a7793ed03c9fe81,0xa0781fd1bc10e89e06b4,0x9d3bc07e8de04744f027,0x34e1a24234ef825a07c0,0x21cb2d10c3868b63c345,0xb2ab5978e1ad2c739ea6,0x859676bacb34e1655e2e,0x2d3410c69a5d6b3128cf,0x15e95f8b746fc67a07e3,0xf423530055a58032d040,0xafe5fa27f33d03f99681,0xa58130d0c09968204af4,0xfd1c18969a15a30d0a55,0xde963c7f471ebb96841,0x1c4b4b0d27938663d1cc,0x132c7a39309d2c949e82,0xa96c73cbb44fe1da1a74,0xb54b6b6e5da66f0ed21a,0x90e89d16f2ed443a26a0,0x8cdf4cc42da0640ad033,0xc26fa6637dcb31a4e81,0x876736d0339baa184db4,0xbcab80668dc8ab40c98f,0xbee59c62f4ae14787708,0xb88744dccb926e9fc3b8,0x4de33a66e1bd2b70fe8d,0xa57065cab85ae55c1972,0x5d03832681c28f4ee16b,0xd4e59c46b46e2cba5706],#[0x1acb478a0da37106d038,0xd8b6596c5b2d0628fe8f,0x97c6aacb630fe831acb4,0x2cbe38fea7187b538d41,0x8ee83247f4d903fa7c76,0xe127417037a8b71dd1e4,0x76c37a0b65ec35d0dea2,0xa3bb1ad05da2e8ae46f4,0x6d460836a3016b0f8035,0x90e8afc5f477819a3c20,0x2c1b4f98cba2bf07d05f,0x33843a2d006d06690e8b,0x969e22d0cf10e8a741d5,0x6d4d891686c487455ebb,0x32e8ac087456023a2b00,0x91a30d48d086a422d0d9,0x5400ea99f69c35234a1a,0xa5a222d0d11268288874,0x4d05a10e8acd772d4435,0x836a6d06b4b6845a1b42,0xd46b4b6a45a1b524d05a,0x3355ba29a5cc34d8b69e,0xa5a875cbd445e56a1775,0xcd05539e5ea9d74f5117,0x3c69eb23b4b5819a3aa0,0xb837475a1ba0ad68d456,0xc19a6a606d2d3030c682,0xa50126d400a5e94070b2,0x9d00193e980ac35003af,0xcae880e674006a7a2035,0xa35b4a5121a92791d281,0x5921a52c98d016586a0],#[0xa50e53d1073565835ab5,0x4d4881a69c412b4a2097,0x6fe803ae32c2371960d1,0x516740299fa70eddd107,0xc32b1a019b0c30a29e88,0xa01926d40cb566066c30,0x7d3899ae9c4dab0c3331,0xe1e805547462aa7a215a,0x56c74c2b7fa315c1d10a,0xc2ed7a615a7d38a93e98,0xa62e27d30da5694689b4,0x8cb6a6169b4b7b4da2d5,0x60e8b5ee751abbba2d5b,0xdb4aea6b83a2d9c1d16c,0x5eb1a63b59d31c69698,0xa530b8d417efe80bd674,0x9d01913e94c6ff466283,0xcae88ca674064a7a2325,0xcb674465b7a032b05498,0xeaf0da95287d2996be94,0xa64398cb21c36957e1b4,0x7d29eece88f54f447b31,0x4369d721b52b197a73dd,0x1d4f448cb3a046b0d2b0,0x8e69a74740d323ac681,0xa246dbd0230a6a51c9b5,0x6d32713e99372f4e8db3,0xece8b72c751b7b3a2db2,0xdec751bbb3a2ddb0d2ef,0xceb9d8675d3d3bbe95d5,0xa67acfcc3ae7661d73f4,0x9d03c13695ed4746ec4d],#[0x1ae9de14746f0a7a2785,0xe2ff46f183a278c3d03c,0xf94fa778b1d33c5ce95,0xa08cced3441a69df1634,0x6c2cb3d69a35ad511931,0xe8e89ff4f40fef5a9949,0x14d34b026ba57fcfd2bf,0xd22d5a89098d0482c69a,0xa0686ad34cbda9a45eb4,0xfcbb46fe81a1ef2ed0b3,0xbde5da52f4ad296a96cc,0xb72f2ed3afa569d652b4,0xed4a7a26a59d03520aa5,0xa56ac1d13561e81a9ef2,0x1d1b5a9e89ae9f2ed573,0x6be95cd074cd697a56b5,0xcec74ae773a574c1d13a,0xc629a665a7c3b1586a5,0xa06714d33353e1d8d674,0xfc3b125e99885346ce29,0xefe818f3f0eca95a665c,0x9b3f0ec697a66391cb31,0x6ce95a067cfc3b325699,0xa36e53d1374ae49b92b4,0x1d33725e95ba472adca3,0xc8e55be5724df4f876e4,0xc2572ae1bb9570a7c3b7,0xae12ba07094d0386ee95,0x906ed7cb38a568dc6574,0xfd1b760e89bb0724dd87,0x13e95bae74add73956eb,0xbe9f4edc4fa66eb1d337],#[0xe0d7956fb9cab7e0e49,0xa570c1cab860e81c3034,0x8d3619368dc49b40e383,0xdd68326e34d8b85a0c4b,0xe2e30d717186b7bad1e4,0x57371a3b6b8d05b4865a,0x87bd51d1dea5e8ee7774,0xacc5f5361ef9ab317b4d,0x93e82fe9b47794da0bc6,0x29af417ed5a0bfc1d15f,0xd9d83a2cb27d06593e9f,0xa3d0c1d1683565b3dab2,0x3d04ea5e96754f453a4f,0x93e9676e74b3b83a29dc,0x792b4b3cada19ea7d3ce,0xb5f83a2afc2d05793696,0xa5b095d15853e9ebee74,0x1d15861682c1ef4f6123,0x4c65a930b0d48d7a5b0c,0x92650d493186a4994b52,0x740a7a2a09953524c69a,0xa7a0bfd1d060e8a81474,0xad2d12868e895b43454f,0xa5e96854f45424da5a24,0x8d2b4b46ada1a335d3d0,0xf6783a2b326d4519a69e,0x92a5b1d1cd5868e6a9f4,0x1cad2a8e8e954f454b2b,0x9ae9e95ef2f4a97a5a59,0xa1ef2f4f2395a795c953,0xb51bb95a895c9d44a64e,0xa7a8d1cbd46ee96a2572],#[0x4d1d44ae82a2534151a3,0x2ce829a574b512ba3a89,0x99ef2f4c97a5a653d153,0x75495a0aa7bcbd49ae9e,0xa0ab14d1d567e5ea92b4,0xbc0004868eb643415a69,0x24a03c8064009300c400,0x821303cc06f00c881600,0x7418102d2053c09ac11e,0x8240f601d6837606920c,0x51809c412c023b04470,0x242f305c40b4815c02a3,0xd741a6833c06560c5418,0x87700e921c9c38106de0,0x9041688050fac1ed83c8,0x2a6249047a08c3113821,0x89f313ae26ec4d5097b1,0x705610a9714d628f450a,0x7682e385ab8b2d16022b,0xc8418b430e860b8bec1,0xec6a90d301a083360658,0xc6a38046f70dd51b5a35,0x8eaa1d363a047390e561,0xb07a50f191dee3b9c76a,0x6840407f10fb51f203d,0x111321d042f084890662,0x88eb91a8230045788a1,0x58a4a8893b124a244048,0x93a526ea4d2098f12f12,0x1ca2b942e28204fa09de,0xa605448a7694c4292e52,0x95fd2b965660aba95562],#[0xb0b6096a62cf4597cb14,0xf445de4ba297292e165b,0x1877309c6060bf617be2,0xc8c99991831e2631cc4f,0x42867c8ceb99b4332865,0x9aec35846a48d3a9a4a3,0x50dd49b7d36a26cd0d8a,0x93a71b4e259c1a37de6f,0x1d3d3a5a7400e719cc83,0x10eef1dc33b327610eaa,0xdf47b0cf441e5b3c6678,0x9fb93f027db0fab9f273,0x8503d205040608038fed,0x29a849507ea0de419082,0xa21243da87150cea1754,0x3517a22c4453089b511e,0x7c88ec91c1a36546708c,0xa48c48c8915121fa4154,0x352ae252a49e89329257,0xccc98e9307a5e24b7096,0x274c4e169bad36026964,0x3141a28094fc49e9d3b9,0x288a45d46d28a750faa1,0xaa345402a72d4d129775,0x5587aae7557caa55531,0x80aaf895d72b7a56a0ad,0xaca4591eb1b162b2c2c5,0xb96a5ad365a0cb369662,0xc86b82d6f52dc55b2ab5,0x2f105dd0bb457552e795,0x657f3afbb5f16bd6d79b,0x1c2c2f58483069608ac0],#[0x318e62bec4d9887b0fa6,0xd1925321e63f6c74d8dc,0x6baccdd988b2dd6560c9,0x341567d0cef59cf33776,0xd9a65b4b06904d15da15,0xb7cd669abfb5506a5ad3,0x36746ca4d8c1b04b5d96,0x51b8fb6ed6d96dad9b47,0x6ce021bf0b7af6efadd,0x390b71c6e2e5c44386d7,0x15cfa39d37356e5c1c9b,0x56aea3dd36ba427462e8,0x3b527654ec31d7bbad47,0xdde0cbbf1779eeea9dbb,0x9caf2f9e503c8178c6f0,0xbda37adaf4f9e94bd0a7,0x11f4ebe687c68f811ee8,0xf44fdd9fa5bf1c7de0fb,0xc07f80b500ba0013fd97,0xe0aec12b820d036e058,0x4ab08ba10241d9834b06,0xc33685f70b72154427c8,0x620543ea876d0e461ae,0xa1513aa261449588e311,0x45d58b4115e22aac52e8,0xe235fc6828cc518da303,0xf871e763b5c7478e411b,0xc8719093208e403c7eb8,0x3249348ee919d22b6446,0x42d27764dd499692e725,0x4ae895812a5a535ca419,0x865c94b7b96a72cc2588],#[0x84130325fc4bd197852e,0xcc9698ed31966254c359,0x6669acd139a0133a665a,0xba136d66cecd869ae535,0xce5e9c9138c670c4df89,0x4a7784ed49d733a4e73c,0xf173dee7b1cf429e673c,0x50139fef3f6e7e0cfa69,0x5a840506ca0ab40fa815,0x1fd43b286e50c5a15742,0x516ea2af44f2890d111a,0x428fa51e0a38946a28c3,0x5394a22939d255a46d48,0xd314a5ff4b9a96352b1a,0xfe9cd5385a6c34d02995,0x89950dea0d53fea7c34e,0x54cda973525ea415462a,0x6aa9d5528aa2353daa71,0xb9556caacdd586aadf55,0xd63fac4f5856afa55e2a,0xfeb70d6c6ad1f59ceb28,0xef15d92ba7d72fae275b,0xd802afcb5f32bd85794a,0x42c3c585cb08560dac0f,0x23563fec7358dab17762,0x59a9b30b65becac593cb,0xad0fda0cb3e56762ce0,0x57f6a7ad44da74b4bf69,0x5b30b62f6bfad74dad0b,0x3eddc5b9eb6ff6d8eda8,0x8b170eae0e5c02b7d16f,0xdcc1b95d725ee45dc73b],#[0x96ea15d25ba1573bae6c,0xbb97702ed65d96bafb75,0x5e55bc7d788aeffddf3b,0xf6f6fdeb8bd357a3af39,0xf137dcafac5f2fbe297b,0x5ff8bfbf7f22fdadfa2b,0xdf04c607ac09f80af009,0x27f846708060e3c18b82,0xe1bcc35386430bce15bc,0x571176216c40787b30ea,0x5a98acb14de283c4dd89,0xe374c6c58cfb18d62fac,0x1f2156403c7c38f0f1cb,0x9d3931b254e489c8d391,0xe571caa194bf28de501c,0x1f2f4e5cfcb6996832c4,0xd0199a73296635cc4598,0x6703cdcd9b37358e698c,0x473c16773cea39cb738d,0x2f9fe73eee7c7cf639e,0xe897d0ffa1bf428e82dd,0x7349ee916d1e3a36b459,0x407a78f4e0e99cd2f1a5,0xea9fd4ffa97751eea1dd,0x7759c6b1dd5ffab8755f,0x7cbaf175d76b94d6e1ad,0x6c5bd88bb0bb60c6bfbd,0xb766c6cbed94bb247639,0xb1bb5b36a1ed1fda0db3,0x6e16dbf5b79b6e7edadd,0xab74d6e7fdcc7b93f71b,0x3c2f077816ee7dd97ba],#[0x41509c1d0874506f86f,0x382361b06e0ec507a1d7,0x4f43d1911a1828846c10,0xab08b0c11321c47161b0,0xd48839c6438c18782f0,0x1ec447420e1707922137,0x211347b13b181624d833,0x168746c9151e88c3a456,0x2007174220b4c561f115,0x5f44d2185c148e02045b,0x214109247d1c8da39930,0x3c5a0ad4443c88106177,0x5053a4cc471e91605c0c,0x5c9e414484542521081c,0x278750d8454bc4f0c124,0x2085a0c9784047d04053,0x1d14e0b039181432e0fe,0x4c4d03c2e3289d07e052,0x1e0d927c6854549442c9,0x189252e8521a089281c4,0x1c041444b30e5281e125,0x194c099123185042090b,0x4d5310c44d0903d00551,0x39001295113243350ab3,0x67cfd689d0000d3bef19,0xe3d28000d01faff82002,0x24004aafc2080099c3e9,0xfdbd764c000348c7fc74,0xc000430107fc18001a2b,0x28650b7eb801209f30,0x4337ae21c04ceaffb69,0xfff668480095cff02000],#[0x8c00494ffc972560068d,0xd74002437dd807dfff66,0x69df78c9a0024cff9,0x43fa6500033a7b7f0892,0xa000686edffa7214001a,0xaeffc9d0000d1dfefe9c,0xa0001a1bcedf48420006,0x3f8ffaca000686f3b7f,0xb7110006718fde238012,0xe1009d3ff25c95801a0b,0x61ffc00469f4380118f9,0x82fe10400067987f0023,0x80283f9e1009cfe37402,0x8f200471d76e0047adbf,0x6f5e0008c3fe000047da,0x332fc98011b6ff280024,0x67ad5fc028ef32801,0x440f5539002467f9719,0xda93c801a1df99528440,0x10e37e3800122bfd3,0x22dafe8000021e1f8340,0x379ea00091bff6fe7001,0x804cf0055fffc3d00090,0x3cf8e8008d43f804d43f,0xbf9f1c000246ff8da002,0xc6a0000ce2fb3a10010c,0x246fc6d0011dffe0068f,0x23f5f9c0023ce31faa01,0xd700047aff9ca744400d,0x19ddff8000000022271,0xc026cfe0000cb1ff1900,0x19ebe95000067bf2f],#[0x99d39fc00019bbfc00,0x1199f36c000219abfe08,0x4ce9ff6200266debc00,0x337fb10013377f5ff0c8,0xc301000043b91067fcc0,0x61fe00445fa800234bf,0x75000067600b7f801290,0xdffe0004ea00ce80337f,0x7d6a02466ffd3b500133,0x44f334801217a938011c,0x71fe26004899ffe05012,0xe25420021c7f940011e4,0x33f7d3a000067c7f,0x19e9bb34900a1a3fd8,0x26afc0a58000d0df9e80,0x3a0011c3ff840273f1c0,0xcf3c7ff19009207ff,0x3a001217f200454f8be8,0x67cfe362200679faf,0xa00246fd0f82464ff620,0x4757f760000432fefd9,0x3abfbb00002197ffb340,0x23afdc034be96500004,0x1156bd7d0091c7fbf530,0xcf4d8f500067df880,0xf70280490c00c5ffe6c0,0xd090123d7f4300099d7f,0x62e3d40019afe1c226df,0x1297ff000234fe0004,0xe57f1d88009431ff1911,0x782a1034274fca000338,0x3584004933d804d9ffc5],#[0x73fd74002419ec0269e3,0x6013193d804f667b009e,0x2387ff1be8800345cf,0x88e0048b9ec0269ffc81,0x81a2bfa5900019c63f7,0xf3fd7040048cffe2bc15,0x13ff18800475fe21c008,0xe7ae870023ecff5d0009,0xfe3921336000d4df7601,0x1ee3e7009cd6ff8028ef,0xdc00277dfc00f33c9801,0x679f7f2c7c980128ff,0xc00268393e01337fc400,0x1207e2af400484ebf20,0x9f009aebfc013efaadd0,0x4480033a07f80000339c,0x7f801ebfa0000033f7fc,0xc400006787d9400010cf,0xb4800338f938008fdfff,0xe0911bfe200003397f95,0xffae8480920e4f804c3f,0x6c830009a2f6012b0036,0x4dbff5180023bdc01a3f,0x1a0716de0048afd80,0xcf94ff4000cd5fc547,0xf93b788c001a53dbc460,0x408647f36a0d008111df,0xc3ffd630000902fd5200,0xd5200000443b801dde00,0xf7cc00926ffe00139bf8,0xf00011b7cc000479f7f2,0xf8000066cfc9540019e7],#[0x467ec01a1f1400042c7,0x80033043ed800334faa0,0x80033043ed80033043ed,0x80033043ed80033043ed,0xa000666f8e00033043ed,0x338d7ffe000024265ff,0x20a5f8400019e91bf800,0x1333fe60187febf00001,0x347bffa80019d3ff9400,0x874ffec04004cf7f9801,0xf0d88009a19f3e020000,0x15ba00fbff0b80023c78,0xf99801193fe0000199c0,0x203c3f9000660fc844d3,0x3d004087f7e746980002,0x33e7a7f4e80819d1f8c,0x678fc4000019e31fa800,0xeff600000ce9fd3a0000,0xfcc400267cf4f8900067,0x140019d7ff3500047eff,0x104004d43f54008d9f97,0x689fcce0011f3fff3a56,0x46e4040d2dff3a374000,0x338fdd7000474ff875,0xd580019edb009a3e1f50,0x10ebb7c7e002447ff9,0xe01ec360006927f67460,0x21e1e36700010d1ff,0x85cfcbe8000cc0fe1808,0x8827c28000d30ff30000,0x19c3fa0e1a0003467,0x467ec3868000d019f97d],#[0xe3ff58800471fe632012,0xf83e08000d03ffe08048,0x6895ff3a0012080377,0xf8661004087efbf5f640,0x7ff900023afb8f824687,0x91dfe006df9be480920,0x28c7c80919fc00d147c8,0x6777abc8000867f80,0xe79e004eff005aff5e10,0x5780000436bfc800085b,0x3e3000465ff18002313f,0xc000d027e3e3cbc80096,0x87eb20000043e7ff9420,0x121f74034ff3c00047,0xc004719ff00011c7f880,0xce9fdbcac000ceb7eb,0x9c3960000ce9febe800,0xd7a800339745edf8004d,0xf9000142eff5e0023643,0x5d001331b97dc600a185,0xfbc008edf006afa01347,0xf00810dc5fcf00066985,0xdc01cfe7fc8002957cde,0xf5e0008cdf960000ccfb,0xfa5e00475aff25e00489,0x21a3fd83ab07c801a56b,0xf9320000043ebb386200,0xfac44008e33fe00023ab,0x2717c300010b5ba0138,0x21b39f2b00033dfd90,0xac6200487d80333f9000,0xc00268afed4c000ceb3f],#[0x4ac000cefbdc01f36fd0,0x1427fe61d3e20068efd,0x4abfff4d480122f9f20,0x47e4226807fe00463f98,0xfc4c0142e78157680034,0x967d7c00465e7f0011a1,0xfb0065ef8fc0047bfd00,0xff263000043cfd78008c,0x80019eba7f7ac4000d24,0xd02ff480800043c7ef6,0xe3ec580033574fdba400,0x64a5002888ff48480019,0x929400a1eff6012e3ec0,0x28008f9afbc00033c3eb,0x69c35feb00091bf7f,0xe7e7e0001a403ffc2f44,0x88008d87bff0008f5ed7,0x377afbc00033b201b7f,0xfc200236f0bfe4004834,0x963e1813237478604ccb,0x5f580115ed00cd8f0c09,0x7dffa90246d783900285,0xffc80046b7fca4200008,0xf03f5812387a6000cab,0xc9baa3ac784911e18132,0xebc09163e18132478604,0xac4a1813368f7af0247d,0x7e800487bc028efe0045,0xcdfeda97a000342ff1c,0xddd0000438baffd0001,0x21fde3e1400021cdf,0x7fc5c108001a59f5609e],#[0x2abe0002181cfc00042c,0x7a40019e9889e0002181,0x67c777400010d1ff7,0x3bf574328000888f8397,0x1bd48c4086afef480033,0xf9e20046c1bd48c4086c,0xc00033001fd5000010fb,0x40047c7e6800010c5fcf,0x1336be2c0200010e38f8,0x438f3c4008c1c3d08,0x9f2a5f2800339bdc0e8c,0x354be500066ac6dd0001,0xdff50000218ba728003,0xbfc8011413f8e1e8409a,0x2004704fe387a10804d4,0x23877fc352081340f7bf,0xcfc387a1026855df900,0xf450dc400288b3fcc026,0xcf00230780f51280341b,0x250066a707e2001434f1,0xfe210265b3fcc026cfea,0x97c71a12317f10e02662,0x39f3f0001a33fa894019,0x86ea7b4bd0003437d,0x26f2bf580008607c1ed8,0xf71b88dc400289b3fcc0,0xc0199dee02bf0000110c,0x604ca1ebac0019aa1ebc,0x42dbe9ab880050e09f8,0x804b9fd44a00ccafc000,0x2bf000010a7f9804a7f9,0x131fe6012e7f5128033],#[0xee34246bff6c013d9fe6,0x302660efff6042000691,0x8604cb9ec70c0999bd1c,0xff998027cc7c302656c7,0x6717f969040000445,0xcd1d3fc800337174e5,0x1993fef6000662c3fec0,0x194bd3c800198bd3c800,0x73d90b4fe2522123e000,0xbf4ac2338162aec789bd,0xd2e08986e824c2b38103,0xbc832704103b60b0ce08,0x7a864779248845c213ba,0xb2b1e3922f73802c3c7b,0xf6952122fc2b096cc8f2,0x658638cb62d64b41a58a,0x6c522175e8941a76e31f,0xb1e7d818e36d12195df1,0x5e41ca2c5838cd0942bc,0xe5162c1fb1f16110bed,0x7e1584245f856139f272,0x5e0ac68f8d12849b4208,0x4193c9c8327939062743,0xc774d81476418d478fe0,0xba031f740636fa62ee80,0x26892b782a79209be98b,0xd8224c8ecc883d431aef,0x6b5d6d13dfeb41b701ca,0xdbd244165afd8632f5ac,0x8ed760b0cda68f0cda68,0xd2864261db256152f6ba,0xd760b11704244e951a7e],#[0x3a7249684270413bb60a,0x68499a358c9c1054fa68,0x2f7fa17432f7e998194e,0xd746909df0426866ab19,0x8d6497d4a8357fba4193,0x924884b0d096c3849de6,0xaec1243e4d0cb4332477,0xb19f1c325b5d82e51c15,0xe082a72512842e988328,0x63a96cc719c24cd1ac64,0x1eb596f42300b763cf76,0x425e846016ec75991f60,0x4b0b11187351478fc5a4,0x6790a327a0e640747c84,0x11e0aca8eb9707ad904b,0xe5f7320f5b2085c7044,0x1b7f418e30fb1925f732,0x2ee80c70f26083223f34,0xfb18e38f51903f406360,0xb4da51084ff66214216b,0x508427267067a8f25941,0x84a58e58f3e30191dd3d,0xd8fba0b1bbfcca842466,0x4d0d767344c784a0d13a,0xac6b3e0b45d62f939093,0xf3d186588ab1e3c20a22,0x88376bc1238960eb0c51,0x188bf842d911c4b070f4,0x83c0f22ec916e5d469e,0x820d5b4b077702885e9,0xa564c4fe95905e528317,0x46429796883ef2d1313f],#[0xd431e191d107062b1958,0xab51fbd0e8387d1583e,0xe31d4cc6139d1001a4a3,0xde20e0fda60ac3ba2cfb,0x8391eda7749a835d218e,0x83bbe00d1a9e9a2579cf,0xaba153e96164d418458f,0x123a531d0078b46ed14e,0x821128e2b8e4d4abf821,0x146d620fb831a78063df,0x3aa0f1e95061f018c3f3,0x50ce7b094d498f4a8335,0xe0190b9f5a6497c94ce9,0xe0034747820519c065fe,0xc86f2330042db04a0e4,0x20cbd031a65c20c992ee,0x304b1e38020fb8316380,0xd85895b63ec2c41f018e,0xc78cd82f626c1cbe4a64,0x175f88c88488e0c65fc0,0x7aa4c775488427b044a6,0x124f420327b17a4438a1,0xc80d84a77690d2f570ba,0x85b0a0e8e14427694f0,0x63ece5508f603ba3a7ba,0x62d193ea59423be99c42,0x41c710b1f9194d5a4a2e,0x1199f05550908b046e97,0x18a2e7a197f031caeec6,0xb4b24e6868801ad591bf,0xf56b24576200d74c91e7,0xf1a5d8eee05145ab638a],#[0x44c3831adb3551a61c18,0x5206b628b56c715ead6,0x223845cfedab4229e750,0xf9086be4218a0fab421c,0xf90868edab420dd8c22a,0xb83156ea51a5eb52a522,0xf8a10a6e60f075ed2c71,0x5702efab42c48dc2f1ae,0x820d1b2d2c24b03b8e58,0x177d5a151ca1082155f0,0x6ee315d092f81cfc238,0xa0e30c23b1e30c23b44b,0x308ec78c308270718523,0xfb10c209c1c6148e838c,0xf819798b041cdad2b460,0xe413c00692383157f18,0x1cea6b7a297e063a78c2,0x763ef818c34936c9df03,0xada9a3df8687db431b43,0x8d17383e8edb1d3ac11d,0xd49ec4d83f626c1a3360,0x3613bdd415b6cf47b094,0x5c56db2f634adb2dbf12,0x4e60e08344f622fc0c6c,0xc88f10592f063c55e0d8,0xf5846e03a7c4106c5fc0,0x8346ad107bfd60894b26,0xbc28]]
def g255H9 := limbs80 #[#[0x890430c620510c340180,0x400010100004130e1802,0x1d600208528000004104,0x40033450413ce090031,0x404034b10004008e6020,0x901441010410450de94,0x4d31020c0412411850cb,0x42570506000821820006,0x10320234b34021200904,0x10b000c2000103103206,0xdc00150800042357000,0x7a4376682766f92612dd,0x10bc4440000006,0x108000000000000000,0x34bd960394000757720,0x22ec0034f46cc6880,0x24093400016ac3bfc2,0xd965b21000000311c000,0x33b333a72d45e1033,0x4c000000000000000000,0x1b10575d5c80000002bc,0x734001c803e82b34,0x37800071f0246b70f91f,0x3d00012d4002448002,0x64721325f27086b80000,0x358303057c6da1d314,0x1cf216823524637c,0x80000031e40100032140,0xc134a22b2312040eaa9,0x940000000020ed0606fe,0x15a702e5f64936c40cd6,0x6b00000027491be61f87],#[0x292cf5fa0920754a4002,0x32e306560400117f3,0x73fa8c0000000000ac00,0x34d829800201c0b824e,0x410f3f70e1cb00000000,0xc7256c7d0fe2a35323d,0x361800000042531f2fa,0x45c534400066400008c0,0x43f4cd94800036c0033e,0xcb7195b00012426e8001,0x34280004e128c32c0001,0x3a800039059a70400211,0x2400026c00000276a15a,0x351c0024432662392,0x5963fb4dc00137000222,0xbf75a25272a1a74644d5,0x631b1080039a67511aa6,0x2d966f2b800000205747,0xb4248dd10737013773a5,0x1932e904823e4c65b62,0x3121d5d45128571,0xed4ac17156f67e3fc52c,0x274d4b80031,0x1b53800005000135000,0x169c00000121f3f3c01,0x44a919503d280afa65c0,0x1555a312caa2dd645,0x15273580005e958c,0x3c7554fda80034800000,0xaf239c06b58400000,0x14f0000000,0xc00309d095d880000000],#[0x59ca9e35662960c002cb,0x4e4fc00000335c0003b8,0x23cc0000000000016,0x63a1f80000039ab55400,0x580000000000015442ac,0x21b800262c0000013200,0x316c5100036ed28800,0xfc0000000000000011a0,0x460856821b7380006361,0x6011c75de29e5ac12,0xf062150e1c018c003578,0x95140023980020e541c6,0x5760403c000034c0021e,0x1236b2a95c25900024b3,0x34680014c80ca12805c4,0xc09cd35480006500046e,0x3da42585222f155b0d1,0x446f38c0005517400000,0x151f74b64145602c45e,0x92d9d48753630c000b01,0x80d66740020866422e76,0x5e000000351864933020,0x1185aff,0x3008001dcc0000014300,0x18000204c00000000000,0x344d82f8be0a4179,0x558b77000020c7600000,0xf430a06d65730355e6e,0xb766000053d1b0139680,0x325fd4b2c00022a40001,0x6f45fd0793c92c81e000,0x8c0032fe3113162f6630],#[0x36dc0016d348c00033f6,0x76c00,0x111400345a1cc5a8,0x3ca00000000000000,0x4400000000000000,0x600000000000016d4dc0,0x20880000000001,0x47c03800000000149800,0x38000000002439564003,0x800326a6466a40000029,0x35421673800030f34f,0x302307d70e624,0x23853ee14800015e5075,0x35d000000115000,0x2c0023a0000000d2c000,0x33885daba41740000032,0x17450980035295b800,0xd776463d40f3e3af414c,0x83600000014620b6d0a5,0x3615b0749c00294e48,0xa303642d334000000000,0xe0a00006855cc0000026,0x4970d80ab3ad366297ae,0x397256102796985ee5bd,0x113e1dbd463dc00118ad,0x4e702800373232420214,0x7000000219c00d402a61,0x33c40006a800247b1992,0x1af2d213400000000000,0x921d74a21de6cb306406,0x73b64d2c6a1196700012,0x27c0014ee4e86c171]]
def g255D10 := limbs80 #[#[0x5d5505c1505955061c65,0x9d55061d50619505d950,0xe1950d9550a19509d950,0x5d5605c16059560e1d50,0x9956061d60615605d960,0xd9560a15609d9609d560,0x601655d565e1d60e1560,0xe1d65e01659d56561d65,0x615705d5705957019570,0xa1970a15709957061970,0x21975e1970e1570d9570,0xa19756197560d7560175,0x5d665e1975e0d75e0175,0x6126560e65602655da65,0x5835061a7561e6561a65,0x61f5061b505db505d750,0x5db605d760597609db50,0x7dcf79d76061f6061760,0xdfbbef7beefdbfaff3fe,0xfdbfb5f5fe7fbff7fafe,0xfdd7faf6ffdfdbef7bee,0xfdfeffdef7fefbcff7fe,0x39324aaea0bffffeff7,0x604baea08e5d5b03c91c,0x532028ae400a7c3024d8,0xcae40184cc0a259114,0xf61839fc3033d8606e72,0x8405cc040998086b0c10,0x5cb854f900a133020d61,0x60997162b2a24964448,0x17576132c302e58327c8,0x789b0eeda9d9db4bb3b7],#[0x730f42661e9ac33d3d86,0xf8266201ac3402990801,0xd94734b28e0b967e172e,0x695c80d4f851cbaea39a,0xc38d66751acaea35ae40,0x313971a232e34de1c69a,0x962633284c764c994c81,0xe57203c465cb9ac39711,0x26582660a08cb140b981,0xd5d8c08cb1619942c3b,0x54835c8102b9020132e6,0x27c8121f9324232a544e,0xac1099532172a491e4c9,0x1197826b0f0599d60b2b,0x884133108f616109cbc1,0x133118465a31ec2c60b9,0xb144e56185cbc4357688,0x2661006cba0299040172,0xd294c8250b9842b2ea84,0x6cba559754a332894764,0x282591505320a0266128,0x9904c57208d7e41104cc,0x48132ca42661306cba62,0xb2e9ca64138fc9a42b90,0x782e40004caaa09984e1,0x9d8f1abb1e3e753c7aea,0xd19c39a139634132e78d,0xc39a679634c92c685e4c,0xc2392382d3074564cead,0x95389724702e40e19c39,0xc7aead42640f85ca9c3f,0x2ed91659b22bb363d756],#[0xcf61998bc9b341766e8b,0x61a18c3b41795687f30c,0x85c8390b97701720e026,0xb312b905a132cc02e4dc,0x17955c4724b8d619584c,0x65e2b2abc9645794c82f,0x1720e8264d904c832378,0xc0a0d94140b2820b9374,0xa58140cb02828605030,0xc0b73b016d7602eaea06,0xaba8a2f97025b2e05461,0x32d9714a30e29b5d853,0x68606eb0c0cbe581a8c3,0x6ed2c0dd6581ba4b037,0x30c11b618217ca847796,0x114660229c3046e8608a,0x654417cc045298085b30,0x2c1c8052d9810db0c20b,0xcb8551970a5f2e15461c,0x683900c5b2e25461c4a9,0x960ca32c194258317cb0,0x9032eee05d9da9cb0652,0x30f54619ebb4b3c75967,0x94a59fa8cb3f51977ca3,0x14740c28e82651d02ca3,0xbaba8d82951d032a3a0a,0xb8d51871adaec35d9d46,0x6d871adaea34be5c696c,0x626eaea4dbe5c6b6cb8d,0xdaea5cb65c9a8c3936d7,0xa3dda147bac28f83901e,0xbe587b74b0f6d961ea70],#[0x7a94c0f2d981ea3303c,0x6cc142d9628eb0a50be6,0x91518722daec460e4089,0xd972ca30e59b5d8b17cb,0x20db2a41b254817ca902,0x7264a0e40937ca906e95,0x4946549284a922f9524f,0x65e0b6bac1539524a52a,0x228cc426d9684a30b09b,0xcac56e9586db2b0d465e,0x18190425b30814a562a8,0x8642db0c854e150b0baa,0x25b308546610a9c3216e,0x2c954e19297cc2152984,0x14e15430baa82d984a5b,0x19130c3222d9850db0ca,0x314b22619644c12c898a,0x32351864707208d8e591,0x2d964ca30c98be591a94,0x54e5f2a91ee4d241c824,0xecea6dd5d4da8c8002d9,0xe6d461cdb73b1b6d7636,0xb5d8f3aba9e2f9736a70,0x8f28ba9e2d973ca30e79,0x7c99a2f9034a32e7945d,0x9a779034eb2068be58d1,0xf9038ef2c69de4cd3ac9,0x38a32071de54e3fc91c2,0x3207cb640fa9ca9c5390,0xcdd6419a8bb3651766aa,0xe4da17c834759666eb26,0xca8cbb8519070a330d0b],#[0x432c519672a326e54641,0xc538658a50cb14619628,0x9660a50cc14619817cb2,0xb0720b54a59828cb302d,0xcb54a196a8c32d50865,0x54a198a8c3312f965aa7,0x415a94b315196625b2cc,0x3fc92e2f905c5b26acb6,0xbae2f955cef2ab8be4d7,0x2d955e5b26bcb6417b1c,0x364a320c8b64d916c832,0xaec05464dd28c83a519,0xa121a581c2cb03859703,0x1660242c3048795090b2,0x87c2cb8d85751b0f3012,0x2c2a18695210b2a42165,0xa88798430b308616190c,0x587370aec6e15d4dc2c2,0x350b206a1e5cdc2cb9b8,0xf2a721e40e42c81c8593,0xb21619642c9b48590690,0x6596c3432d85865b0d0c,0x743c82e85905d0d2cb61,0xc00087955d0f26ba164d,0xd302bc08d0190042007,0xa0061015704b811103d4,0x90421c08201e707081,0xb602ba0a5c28409c426,0xe343790d4c3330c7c301,0xa444610dc4120fbc3c30,0xc4fe13784cf12b848d11,0x5b1162856514f4519142],#[0x70197462e18485e81730,0x71c706f31b346b11a606,0x1f887c61ee078d1dac74,0x2c889d21bc844206c7f6,0xe495b24c491e23d48cf2,0xa1a28289e127389a625,0xabe2a80a802980a5328b,0x372c98b192c20aed2b34,0x72f68bab2e3cb732d20b,0x3304c9031b8c373024be,0x668d7e3580d3b341cce3,0xb0e3f388cdff3744db63,0xf213c00ee13ad4e8939,0xfec3f28fa63e3cf633d3,0xcb428d081418103f4044,0x3460515f44d511843a90,0x499d23748351e8470d1a,0xd453324c3d2ec4b01297,0xa54034f913be4e5d3714,0x54e7531149951a944f50,0x5d656dd59555ad53b545,0xa95a11660591d62e57e5,0x55d557345c416eb5b2d6,0x60697fb5f717ba5e2577,0x4018d262a987c617583a,0xa99c6665d97365399256,0xdaa569f9a5b68d5a1067,0xb6c6d19b206c45aee6b2,0x2f703dbef6f45bac6e39,0x6732dcac723dc707145c,0x7619d5c7539d287411ce,0x8a5e01775ddc976e5d95],#[0x39ee27af1e9979d1e527,0xdfbe7e89f757d19f217c,0x9781d205b80fe0197fd,0x6e853612a83de0db830a,0x688861fe87761ba866e1,0x8b362b08a8628c89a624,0xe5e3748d323338c5e2ef,0x2245b90ce40a8f863ba8,0x653294264de93164a592,0x5d896d25a59652584956,0x7e9956643986a60997e2,0xb9caa70b9b8a6bf9a726,0x9fde7d99ede7979dd274,0x2e6899a1ea857a0de819,0x52972a4f691aa3fa8d9a,0x6a3da872a00a78a9c3a6,0xb0cabaaabfaa7ea82a98,0xb6ae5ab7fad82b49acc2,0x9b20ac59b0b6bffaf86b,0xb54ad28b412cedb302c9,0x986e36b82edd5b6b6d7d,0xef17bbf6ee4baeae89b,0xaff8bf4afa2be06f68bd,0xe4c2f3092c1cb052c08,0xd4c6bb185c56312dc433,0xdca0b268c907220c7eb1,0xcd7f32dcc072d1cadf29,0x177437d0773f0cf03389,0xf513d3cf4c9d27f485d,0x3617d7ef5ced687577d5,0x6e6db3b6b5da2b66bd90,0xaade17767dd1f728dc03],#[0xde11f82fe0237ebdf3b7,0xe4538f0e30f8a2e1fb85,0x74f9bbe69397be58f93b,0xd3a90e9aba47e88f9fae,0x3b7bed43b23ebcbad5ea,0xc71f133c27eff7bceee9,0xc370b81c1f36fcbbf257,0x21070444e1e62d143a1b,0x901523b218d11c2d1826,0x1a27064424e902887218,0x3e21828e48a1f0f4711f,0x4038b789c3178a88b086,0xe22e2b0e290fc194c10c,0xa5283a14200d0bd0c1,0x4142d1d4964c4ac02885,0xa20b0ba9423090251b2a,0x5a4f45c9259251613b82,0xe7f8f00985784a030906,0x11c69bf82471cef8008,0xd00547f0b20140fcfea0,0x9f3c013179ce80505cf2,0x923fe97610473d2e013,0x9009cfd9009b7d6b9000,0x7ef20137ff8900283cfd,0x8013c9fd000121e801df,0x50e801dd003bc014fec,0x978411ce7d00273cf970,0x8052ee00cffaf0040efe,0x53d8031f6672005347ac,0xf40400933ffe4dc51002,0xdf3cc0283bfc9804fb8a,0xf80013dfff80027000e4],#[0xd3dec00475f8800231ff,0x15200a005dfc00046400,0xc051f3f95a01487f2b40,0xc0135e5feb40297fb6ce,0x3ff27a800aafae009efd,0x39fecfc8d002b7fb6008,0x3f58022e7ffa800a5b00,0x8e9f08800331f2e013,0x53bfc6a0001217ff06d,0xe0024dff9a004f7fe8a0,0xa0077ffa007401578b4b,0x77fc1d008ed9f5000667,0xbff340055bfc6a000121,0x580504fac0275b803d9f,0xba007127f200024dcfbf,0x241e558051df12b00033,0x63efe590029dff955e00,0x860063fffb00014bb00,0x9c00bbf8800012060,0x6bff80098ffd0009cffe,0x1cfc80135fcc8013a00,0xb18011de00af00500298,0x937dc004f5fc004f3ff0,0x3a78052005dfe1670000,0xa0d009535feb8b002406,0x128b39e00291b8ffeb,0x805277bbe8056ff0b328,0x5205d7a69a040d37633b,0xe40263c39009cff34600,0x80155de00273e3c0263e,0x804d7e61e00507ffd2d7,0x6e009fbf2822000d079d],#[0x70780148fff72800241e,0xcfee001183f78013dfff,0x92fda0187f8ca20024,0xec880297ed00c27f8588,0x4c7e10011cdff480283f,0xcffe9004f3cffcc40024,0x8f35fa00231bfe9009,0xbf8248bffd004dbff348,0x4f820152fd001157fc69,0xb5f500230d37f048e67e,0x120bfcfd005197d4008d,0xd13f7e5400246fcca00,0x7edf8fc00909dbeb7000,0x67ce8019e2f9fc4008e1,0x27fe10051bfee00119b9,0x2465f500232fc80046,0x66bb7ff50052b97e4,0xda8000cd3f10011bbf12,0x6867db011df6a0003377,0x7fe16400241708fac000,0xffd056384907fe1200a0,0x8b6a2000d1b97e400244,0xdde401436b86a240cf5f,0x251ed5fd80a1ef0008c7,0x4d1f8026991ffea5c00,0x981d00a8bec3a00aa3f0,0x5373ce804f73cb401497,0xa6ef32f00a2cfe5580,0x163b003afff3004dfd80,0xa17ffe400a3ff853ed00,0xfe5009bfb400515f9000,0x263f280140efd7500c5f],#[0xbfccfb0028dfefa90001,0xfe940011d7d76fd00049,0x73be2002abfccf70014a,0xfe8340000d173be40053,0xc7fe70028cbfc000472,0x8e6737f80145fff6000a,0x14cce7c000489e78000,0x479cf80008f7edf88,0x2933ffb000a10036ebc,0x770083cf97009eff7d80,0x27ce8013dcfc9000a4ff,0xa005067da0050fff2c01,0xc6be400a28f1e0145ebf,0xdf600f776400a2cfe004,0xa4eff8300a2c7f00277,0xff8e80011c0063b9c930,0x320039fff80013a0065,0x5efb40152ffc740008e0,0xfe168029bcb9cda0155e,0x20bf0b2014cf57b00122,0x73ff27a0002b98999801,0x7c5002cbff820014b600,0x6008bdfce10001653f77,0x52bfffcc2800004b6ff,0xec0117fa7000151cf1a0,0x937ff1400a1fbe00cdf,0xfba010fdd00799f81c00,0xeb00275fff6183c0092d,0xeeb5000485fa800235ff,0x35fff60027bfec004ebf,0x144e75000475fa8002,0x600023deffb00273ffd9],#[0x3bfde80210030e80267d,0x117f9f96005079f2e01,0x607e400121eac012fd6e,0x48be4fa00517ef3400a0,0x2a8fff718014a9fd1000,0xcf73fde2005373fde200,0x139e57009cbf6cf4000,0xd7030004967d8041eede,0x7df900285e3d6000246d,0x801d001f6eb8180024de,0xfd0009dbfffa00290031,0x5e7800006770031801cf,0x7d008af3c0000339c00f,0x3efdf8014efd8fa028ff,0x28bf8e004f3e17700048,0xa27515e0009113cf00,0x7fe004f5fb8005165f7c,0x559dfe004f7e7801359,0xf9fa01567dc0050ba7f0,0x145fd18014177f00273e,0xdf008bfd8780145fd180,0x6b20000255e1de00293d,0x3c800120fd9e00281ffe,0x17cff008a3c78051bffe,0x7801430fff4028dbfc02,0xe795c027bcfe00139f0f,0x28ddf949400927bb7804,0x5a0267d560011ee7dc00,0x6d00e7d2600a1bb403ad,0xcfe54c400497ebd68097,0x4495f8a88009478e6013,0xdfe2a200240fbfe62002],#[0x122fff2cc0143d4808,0x7ee0011dfb4030fff0b1,0xdff48029afdb500019d5,0xc00246e725444002587f,0xcebe7b35cc40025aaafd,0x87fdff48029afd208000,0xc28d3fc1249ff9d82014,0x45cd0098af7ffd80299f,0x5057bffc90054fe4c0,0xa79660141fa0098bfcfd,0xcf71c0285d738f220049,0xe204004a9ba3fe00122f,0xdc6a0046dc6a004651f5,0x7fe550011caffffa8029,0x43f7d660246ff1100121,0x7fdfe1200aa73c7c4002,0xe5b3fd80bdffe1900238,0x63f8c0006679acff602d,0x9a3f0a0003336e77e02,0x4d4f20133bec808a790,0x24266805f8003453c8,0x5d3ffb0f2015aafef1c,0xff81c00254cbfc6c009,0x12036c3a74001a17cc,0x59000914f20132fcfc0e,0xf4f20134cff1c0023efe,0xa7ffdc0023afffdb0008,0x3f13b56384937acb0052,0xf9000923ffeea9900095,0x400482b9ffe1201505ab,0xa2000cf6b3804e3c4ff8,0xb480501fffdd200a73f4],#[0x5bd201367fcd400067bd,0xfd4d0011d77e807be402,0x28bb53c028cbd0f85177,0xfe0146e0b7ab5332ebe0,0xd1f75e428a5068f645c6,0x31e864998eec70540c8f,0x146afff203271f9100a,0x155183ca909f82ce3f22,0xb7a29023d4450d1c7eb6,0x3fc9a154cd0eb1070566,0xb98490ce3c8288744c96,0xfb0290cdaa6bcc3d488e,0x8b4ee0fa66dae3aca8c9,0x822c7d02019729ff8a11,0x58ced2f282e64168df81,0xce3fa204795223841e5e,0x810b877dd520b1e02ad4,0x485073cb3e4ac0141fa6,0x46bbc8419a3215df2cc1,0xca5a262f8330ffb8d823,0x27ac608b4187c0]]
def g255H10 := limbs80 #[#[0x20809202000090a0c081,0x18032003030a044800,0x82000048005124060900,0x69908146040200200006,0x1c58806080010834,0x20618a02020000406001,0xc480030028303061800,0x405011e140211a04710,0x1c102043050600300800,0x8a960000d893c4450306,0x30302280080e1839f021,0x1518085291c240900484,0x8005810b180040106042,0x340c480180c68042100a,0x9cba1040819200d0804,0x103880a2438300201930,0x2060041401720838208,0xb880044403040c182020,0x891304012060d6816810,0x104380780e018852030c,0x4289852508004003440,0x5a39f51ef97e8001880,0x7e01d13f0a9364043000,0x4b4b42b2f0c41485d09,0xd200098d008b16200000,0x53b37600000000021,0x2abc0009720,0x58b0bd63a68f8af0c3f4,0x92eb14431f87349a7a09,0xac02000000000054744f,0xe33b0000cad3ae041128,0x61530140530aed3],#[0x88800188847dc0e521e0,0x86d000443a9739a8934f,0xac865b15fb8b20000551,0x51a9d2c800235925a0be,0x492f09892d000650641,0x8d11a91c6c3e0aa6a600,0x9415040011d253a13f32,0x18ac57460f75492849,0x88000341cec356e8000,0xf3ce2d5000018b168000,0x554c618e0c9a7dd33296,0xf043d4c96f7800316191,0xa1ece800061817609b43,0x7280009ae00050d24ea0,0xa85522044dbc799f2fe4,0x6635c5fa5f000000335e,0x200014b02382ef997549,0x291f3920000002b3b55,0x4e00000000000011fd00,0x8df9e7245a1100005403,0xbda0858f96c0a09e0008,0x14b858107572e228,0xc6f8000000afb,0xa7f0000000000000000,0x333a000000493e61200,0x414d79886400000000,0xbc37880c509a45c5c80,0x22d03500000019ee75fd,0x22b1cb4c3a800162e,0x331831803cc0011f86c3,0x26582cb13200020e,0x5ae77013000300226f00],#[0x2acc0000000f00000b,0x1abc00029e0,0x0,0x1aeb957d7ce24c000000,0x6d1c9ab124000d0f800,0x452cf0aa41fe94400092,0x91f472c0002c800062,0xa04000000080015c0000,0xc60ba09c72100000002,0x62106a27fcaa898c000,0x69ff44c265a63a000000,0x683eb9956d204300011a,0xb13d5880031d016b44,0x76800046e2d0d1248f40,0x1e40004,0x346a00000022fc,0x126782f64e8000e88,0x1112000000,0x102a80500035fed7c00,0xce57728eb00e00000000,0x9e82f6314c5ca9f15d2c,0x502039000007e8ad9,0xd4f8138df22a0390,0x289f46c408d1ae000000,0x26ac22800096b219a32,0x2e000d9580024410bd00,0x166a8526ea6cc71c8710,0xb0f8610002a3d1c107b5,0xcbe0894000143cb068bb,0x713800000063940002ba,0x3851e3251fd9480000ae,0xe95c1eb39650983bd72c],#[0xdb680053f4dd8b7c3047,0x914d1200000848be5446,0xe8108e67440012cf4a62,0x68a566530e180e03a623,0x600000043d04a7824000,0xd61eb4c400010347d394,0x249fb0c6000028e88b93,0x53bb461338ff8b6cc6f0,0x526081000678c0686c14,0x87782d73ee05081f70ba,0x19180002329056190,0x301d81030132908dba43,0x52b05a07d0a23516608c,0xdcd20794ccdece62e9b,0xa5ec86ecb4868000001b,0x668a0deb33c28c,0x3ab000124c448476a14c,0x110900030c0522000cb6,0x70c942df2bcc37333c00,0x12520bce2000002cc59,0x50800000017880000,0x60905b7010000472a9a0,0xb2504f597400000048a2,0x103c41b0c4b432000,0x49ab58c00000000021c,0x583b981c000406800000,0xec24c001a39b400003,0xa740000000000b733700,0xe008219e1186,0xb46532524d017e7b04b0,0xd120a5e588000000a9f,0xf84923ba127b56a84800],#[0xf599a00000c92a984a0e,0x153fa7385f288b2,0x5198480000000c8c1040,0xcb300024830ee4004b53,0x456fa9c51e49ec000000,0xd4970002176087268051,0x93c44ee867eb,0x950000024aab600000,0x30ce13300000600000,0x60818303640001299600,0x25271a40a2d4d800134c,0xe93200000032069780e3,0xe95905aa8214680022b,0xe8a2a2becb6b6170d5c7,0x6f00004ab0dccef60185,0x42d1e883a05356060004,0x17300038f82d3a526764,0x104d0000003268000,0x389649f80002fc000000,0x1700cac7c31379b,0x15fab0400125787100,0x66800000000000000,0x148010000001058c4e8,0x6c143832c40930446638,0x93f859a07c001868498,0x6213b148af652e97b2c5,0x160160004c2a38f1db90,0x63c7042aef2bc86b64,0x5db05f82c85a52c313c0,0x9c3d60000000000,0x3164011d0da7e5430000,0xad1b6bfe1898f06bd00a],#[0x26b531c2c91a00ead196,0x414418682c001314f206,0x388000a872a1c001e,0xd66350000000191e0000,0x82c78ec0000580e9fe,0x55dcbb0000000000,0x1a4a8cfc8c0c6d000000,0xbab1985d0c780009f692,0x63a4e50320766658001d,0x3ae00000067531410799,0x86e8bdebc15810000001,0xc5e4b2f0362bf9d56a95,0x304ba8002fee42f54b50,0xc94aa8336d65295121a,0x3300000015160002d327,0x2620a68cc042b511ea,0x1c5d53f5dc5c5aeacda8,0x6984001ac5d9167cc37e,0x6dea2f80000000187908,0xe41700012aab45e75447,0xc42d958400001d489425,0x8de58c1522b4c63e5c73,0xdffd64eac320583a2,0x23215642940000000,0xb863e2b8d8caf603b008,0xad6f2224001a26d6bc73,0xac0001aa00025649f6b2,0xfed9048685840008c1ab,0x9ed04f2a035b75,0xaf3000378b56a0000000,0x609632631500d8000000,0x173183a8c8381ed3000],#[0x87b113e2000000433c00,0xdbc2d0000000001e3d46,0x9266e84040f9194c4874,0x88c47501d45d15f1015,0x4249265c3deed35c60b,0x44900008db78e8a3ba40,0x7000415a0ba8ab000059,0x54000aac92a297030a0e,0x2c0000000001ae387b22,0x2e0001a1d482a1dd47e0,0x80d0000000402000832e,0x692b20c00000049e41b6,0xc95e0fe4a8f6478e6c94,0x447332fc000c8c80ab3c,0xee80b8ca6687d6d2882f,0x32c9dc001aae94cc1f41,0xc778eb08b0001662000d,0xc7c4471e9c3e46c1,0x39fa59f923000239f9e1,0x40004a95462000cc08be,0x1819b04900026e6d8518,0xb0006b7c64c0004c72a,0x3b0018aca880000011,0x4a995580033ea0000000,0x4af954d2c60000000000,0xad1860e3d6196aad000,0x4daa80006ca000233000,0x85e264078000001078c3,0x2134000418c1af0,0xb0a000cce466c2a75030,0x483d9f2ab891a011b,0x32ac95200061cd15ced5],#[0x2d3864285ce12f000266,0xfd16c82ecff06f606f07,0x1f52168374ec92b00041,0x666119b270c5daba2811,0xcd282964420000b72,0xccb7066a7249c22f0000,0xd250476000000185ac23,0xf4740000000818000049,0x2c00000041175f518600,0xae03084579d692f063e1,0x23b1ead02c3380012cdc,0x10c5b5e0003]]
def g255D11 := limbs80 #[#[0x9d6655d5705956054065,0xf7fbfdfeffbdeefd8350,0xa8e5c04308c5836ffffe,0x14c38ae18530c36751ab,0x98784c3455d632c10b87,0xec4b8529b294594b2e04,0x662cb2b8724c3949d8a2,0x2e151aea898798bb4a61,0xba9ae00d30e098005c32,0x364c032e1cd30e76753a,0xab8054c3b2619aaeac98,0x30ce98374c03ae195706,0xd87aec3d751fb28f5945,0x475da3b0e3e861ec30f9,0xf3a975d4bcca5d652f3b,0x759ec3975d8bd0a5d852,0xa9e654eb2a71953ceb3d,0xfd0c9d864f42a76153ec,0xe1cfb0e7d753fc01f600,0x1af60d7f00bd805ebb37,0xfc32fa197b0cbc865fc,0xa208607406204302000,0x3e1281100fa0db0c90b4,0x61c11ad19918517115d1,0x27125423721a2021ea1d,0x1c3042ea2cf2b829b286,0x43ba3a238836a34f3373,0x47545c43e42340a3ef3d,0x335214fc4e04b949f48d,0x65dc5bd5a95915755585,0x69c6826686466296155f,0x7c75a74271e6fc6d96b5],#[0xe8188007e47ca7af7947,0x8fd8e18c38a687e86083,0x54807084586c2c1c0924,0x688851bc61d1311470ec,0x59321280f0627051e874,0x743142d84238e0a18171,0x401407e6e3028be7d402,0xdfd3c021e0066801cf93,0xc920143800edc0081c01,0xa1f80087eb0073e8022d,0xa0105e00e5a0107c2e00,0x801cf4010fc00cf800e5,0xfbf0021fb401df34021e,0x7a00e7c700277ffc0043,0x41f880827d2013bcc01d,0x273f88086fea01dbf4c0,0x9cfe7c039fc40446f80,0x20fa60219fa808b0fb0,0x1d6fec03adfd80767ea,0x7b8f9009d7eec03a7de,0xe90050e00ef8e0103fb8,0x297fd6008be5f400056e,0xfff6b0050e00f7f78300,0x5a012ffec00e7ff40096,0xf3e0087ba740165e00ee,0xfe780145e00effc3c025,0xf801ddba009bf0b000a4,0x54ffcd6a016eb70087e,0xd400a8fd8d00292fb1a0,0x8be81c00a5adc0209f4,0x29bf5c03b74f8086b70,0x293f880853fe80847e2],#[0xf38086eb35e02efc33c8,0x13b3009c3f71b300a9bd,0x598052d3ef010fcf9c04,0x2e2cc028bfcc]]
def g255H11 := limbs80 #[#[0x20c38016702010204182,0x3578226ac2040a040010,0x33928305022a0858402,0x5810a6958d1200b84600,0x302a420500080030c00,0x41c317830048494003c2,0x111083247098c090438,0xa5c38504449051200089,0x1c1583abd5841e302002,0x10040e2806b0204,0x1f4c653211e04c898a0,0x13065480242b45035930,0xdd80e9e18ed97384409a,0x14276572a911e94c1,0x94a01d9fd5711fa73,0x27cddd98c000,0xcf49b4a6348f12e0,0x2ec2950aa99ea910c600,0xf018618e2c5312a3b94f,0x102c20f1590188d2337d,0x1052b20f9eae182a5fa7,0xcb9e3b1e00117d17488d,0x80000000000d98924bc8,0xb344a32432840000000c,0xbe235d68897890000213,0x8e3a23b6495f6,0xaf8b00000000b1600000,0xa5b869a92001af3a45,0x1ad0000a4b3448a79520,0x17a001ab812c69200081,0x900010a28c01f24f6f65,0x82a19781407435dafac],#[0xfd90e04684183709a00,0x54168a1a00005e000065,0x114400133e1a10720f0a,0xde6a588010509de00200,0x1ab4001c8d9f7aa6000,0x800102e0002e10da0000,0x12de0000019d3141c2,0x6c8b986f744000001e94,0x1a26b77add0380000012,0x2ea2cfb5785858803400,0x388bcb6930200000150f,0x60004770258522e569e1,0x8780b0ab60011192c92f,0xf237d9fe4748708e68cc,0x2dde0ac9e980cec79438,0x1320001a6e369d1909a5,0x198b26a88999dd05a9b,0xaaa308a7320000009ac0,0x36a001124aca2b192873,0x8000095a464000000cd5,0x949030f69468844a5b,0x9d41e580400024800,0x789b11cf8ce001900000,0xac1520ab32000b48a31b,0x2011aa0001b70b25142d,0x1c9a883a31ca96001949,0x21349a5a896a6031a2de,0x10fee60a5c21786aac,0xb2034b7351a25828000,0x233bc94a9d13a1950a4b,0x26622e0ee0008f5a37a8,0x1016a0009b22bb264314],#[0x8000c4a000001106d84c,0x8a0f59ebbb2c1d6000dd,0x6fb11e23c1312736c000,0x6d68c4001d6b239621d,0x24cb1834c0000012d828,0x72354812b0876a8676c9,0x1ca00183f24699b1eba,0x17727bb0d0099f400088,0x42746c2a8de8c90c58f,0x1a07d30aa40162,0x95c9efd62aee24e00000,0x12f059616c36292a001,0xb213758220000000000,0xbb86010a0002aa00,0x1c920c0000019c4910,0x98ae001b0f4728de07c0,0x6c422be9735303d1d8b2,0x3c01a161a20aaf09d6db,0x1241180f6cad400005d1,0x33998929e97f35b113b3,0x6f2d7260c23a8a1c21e6,0xc1c021d2335642d291ba,0x20807a425b4e0d1c691b,0x302cc31a4be9bb3660eb,0x8b729900019170bea991,0xf660000d535eb61d720e,0x432fcdda00021fb7089e,0x200187f36ec8acfbafe8,0x56db2bd27b461be00134,0x51a189c706c37ba3d286,0x1ed537eea023e84ea691,0x89832284aac052c00021],#[0x116400000181f056,0x3179aadd2a0000000000,0x25600117102706,0x4000001cfc000914b3c,0x2b0696f9561b89361ae3,0x2bca50001af50868e58c,0x5a807b244d034b,0x18fb1660016651cd0540,0x2e9f6811c75a5134ee00,0x249ec6d8883f4874bae6,0x42e28dd032962a8f84c6,0x821abe358b2600180a5e,0x1f38200108f4d200027e,0x82151220000000a9ec16,0x9931a20018d7e428b6a7,0x20000000876340000000,0x19841988e1e982a113e9,0x2c6f380008489db95542,0xf9c6a0b4000a760001f0,0x1d17a284c364132f1]]
def g255D12 := limbs80 #[#[0xaca32ae1b02c1a82a1ff,0xeae86684224013aaeb32,0x8345101e0c2813b18eec,0x10001d8008084c88e0b1,0x2003a003b50040007700,0xc00e60077a004]]
def g255H12 := limbs80 #[#[0x220f031140171011020,0x3f00000a4c0041003056,0xa70000000091e3901b,0x21012f4500000000,0x678000000004caed00,0xa0000000000000,0x24c24fc0f3d4d400c84,0x90fa97d242327c00001,0xb600000000004ce348a7,0x89c564b857b28,0xe800000295080,0x10f0000048800000,0x92858008610c05400000,0x878000000000000ebe,0x11100000850,0x1b00000000c200000000,0x1d0000000000001,0x1d4400b0c0000150000,0x12cec00003,0x1f000000000000000000,0x2f00000000850014c003,0x336000000014a002,0xbe8a9910000000000000,0x10b00000464008c7,0x1c500000d4800000,0xee0006380045c00000,0x1c002370000000146000,0xb2001320000000225d08,0x4b0000023a000,0x1560d8f143000,0x7d4c0000000d0400b2c,0x8e000b3f],#[0x2b0008f00000c1400134,0xc98000000000128c13,0x400000000000000000,0xb700000c9000000,0x2d001481124eb30,0xec400421540030e868]]
def g255D13 (j : Nat) := if j=0 then 0x146042005ff else 0
def g255H13 := limbs80 #[#[0x52af652100200003e092,0x1f08803400839a90ba00,0x19c37]]
def g255L : Nat → Packing
  | 7 => (60,6,6,2097204,86,10,1037,g255D7)
  | 8 => (477,5,6,9568462,136,13,1189,g255D8)
  | 9 => (821,4,6,7340257,120,15,1216,g255D9)
  | 10 => (450,3,6,2228295,103,14,1122,g255D10)
  | 11 => (88,2,6,524298,52,12,1062,g255D11)
  | 12 => (10,1,6,65537,0,8,1037,g255D12)
  | 13 => (1,0,6,0,0,0,0,g255D13)
  | _ => emptyPacking
def g255I : Nat → Nat → Option (Nat × Nat)
  | 8 => lookupShort 15 101 7 9 6 1 g255H8
  | 9 => lookupShort 131 787 6 12 9 1 g255H9
  | 10 => lookupShort 242 1319 7 13 10 1 g255H10
  | 11 => lookupShort 139 691 7 12 9 1 g255H11
  | 12 => lookupShort 28 293 4 10 7 1 g255H12
  | 13 => lookupShort 4 23 4 7 4 1 g255H13
  | _ => fun _ => none
def g255 : Forest := ⟨255,13,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P7_0 : block g255 7 0 60=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B7 : block g255 7 0 60=true := g255P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_0 : block g255 8 0 65=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P8_65 : block g255 8 65 412=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B8 : block g255 8 0 477=true := (@block_merge g255 8 0 65 412 g255P8_0 g255P8_65)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_0 : block g255 9 0 13=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_13 : block g255 9 13 464=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=7)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P9_477 : block g255 9 477 344=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B9 : block g255 9 0 821=true := (@block_merge g255 9 0 13 808 g255P9_0 (@block_merge g255 9 13 464 344 g255P9_13 g255P9_477))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_0 : block g255 10 0 4=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_4 : block g255 10 4 166=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_170 : block g255 10 170 238=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=6)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P10_408 : block g255 10 408 42=true := by
  apply cellsBlock (ar:=11) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B10 : block g255 10 0 450=true := (@block_merge g255 10 0 170 280 (@block_merge g255 10 0 4 166 g255P10_0 g255P10_4) (@block_merge g255 10 170 238 42 g255P10_170 g255P10_408))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_0 : block g255 11 0 2=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_2 : block g255 11 2 44=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P11_46 : block g255 11 46 42=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B11 : block g255 11 0 88=true := (@block_merge g255 11 0 2 86 g255P11_0 (@block_merge g255 11 2 44 42 g255P11_2 g255P11_46))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 10=true := g255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P13_0 : block g255 13 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B13 : block g255 13 0 1=true := g255P13_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 13 := by
  intro k hk
  interval_cases k
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact rfl
  · exact g255B7
  · exact g255B8
  · exact g255B9
  · exact g255B10
  · exact g255B11
  · exact g255B12
  · exact g255B13
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=13) (i:=0) (before_sound K251 V251) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_32157

open PEqualNP.Outside.L_meta_32157 in
theorem PEqualNP.Outside.L_meta_32157 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 2, 6, 3, 6, 4, 6, 0, 7, 2, 7, 3, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
