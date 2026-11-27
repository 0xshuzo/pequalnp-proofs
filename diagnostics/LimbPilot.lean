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
theorem sampled : block g251 8 21 224=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=5)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
end PEqualNP.Outside.L_meta_32157
