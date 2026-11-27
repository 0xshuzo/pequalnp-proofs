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
def packedAt (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


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
def g251D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3868c16284880e1828,0x4060808003dd5532d96c,0xb59765b8ca4bb6912d94,0x2b68e1dc34764acdb1f7,0x2c87dd06b0c28da1722b,0x53192ac4d623aa6552aa,0x93532a61d2cc94e458e1,0x3d03b6a774d4d43581a4,0x25980d51516889660354,0x5459625980d5151e8964,0xdc96054076e4d7158150,0x29d6254560541a6e4975,0xd89405d594d896050386,0x55142541202615450950,0x480a8589515411068886,0x54550441862195154110])
def g251D6 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0xe1be0fdb,0x2daad8ed6ad5cd3ad36d,0x2ed1ed1bceacdaccecca,0xcbacaecaac9ec7ac73c6,0xec6bc5bc3ec3bc3ac2fc,0x1bbd8bccbcabaab9ab8e,0xb6ab5cb5ab4eb3ab2eb2,0xbb1eb1bb0eaeaadcadaa,0xd9aceabaaaea7ca7aa79,0xa73a6ea6ba67a5ba4fa3,0xea3b9ea9dc9ae9ab97a9,0x7396b96795b94f93e93b,0x92e91f8fa8ee8de8be87,0xe87b83f83b663655cb41,0x662865cb41e4182d9740,0x64b655cb4064a865cb40,0x5cb8058b40a5b8454340,0xa1b845434065b8454340,0x61b84543405978454340,0xe1362543405957254340,0x21965543406556454340,0xe616254340e116254340,0x5c962543402616254340,0x59542543405894254340,0x64886543406188654340,0x64b6550b4064a8650b40,0xe416250b405956250b40,0x661655ca54615655ca54,0x649645ca54615645ca54,0x654865ca54640865ca54,0x618865ca5465d809d564,0x651809d564e53805c964,0x5cf805c96466275dd160,0x66265dd1605d581dcd60,0xe4954dc96066374d4d60,0xe43825d5605d7845c560,0x657745916065f8355160,0x64382551609956455160,0x59564551606577450d60,0xdd35350d6065f5350d60,0xe49751d560a5980d5151,0x25980d5151e4964dc950,0x9d981d51505d981d5150,0xe57825d950e43825d950,0xe17825d950647825d950,0xe17805d950e0b805d950,0xe09815d950209815d950,0x610825d9505db835c550,0x1db835c5501d9655c550,0xa1f8059150a178059150,0x64b74589509d97258950,0x6508758950e0b7258550,0x59782581505538258150,0x5937258150dcb6258150,0x55362581501d97458150,0xe4d71581501d97158150,0x99564581505956458150,0xe096258150dd16258150,0x595625815025d6258150,0xe4954581505915458150,0x1d95458150e095158150,0x58951581501d95158150,0xdc942581505894258150,0x55142581506507658150,0xe4165551505db8354550,0x25d62545506487654550,0x5d876545505db8150d50,0xa1f80509506537650950,0xdd9545095021d5450950,0x5d9821d950e61761d950,0xe49761d9505d584d8940,0x5d580d8940e4975d8940,0x5d565d894066176d4d40,0xe4976d4940617805d940,0xe41835d940618865d540,0xe518759540e418759540,0x24987595402597559540,0x65362581405d76258140,0x59353581405935258140,0x2597558140e496458140,0xa556458140a156458140,0x99564581406156458140,0x5d564581405956458140,0xd494258140a594258140,0x5d542581405894258140,0xd9562509405956250940,0x66175d9120657845d920,0xa1b805d120617805d120,0x64b64581205898158120,0x5d164581205d16258120,0x59162581205516258120,0x59154581205895158120,0xe4187551206617655120,0xa1962541205516254120,0x5895154120e194254120,0x55142541202614254120,0xe4975d89105977254110,0x21965541102616254110,0x5895254110e495154110,0xdd95154110dc95154110,0xa1951541106195154110,0x58951541102195154110,0x64886541106188654110]) else (if j<2 then (word80 [0x7f67eb3d,0x47a4f41e73cc791f1be2,0x7c2f81efbde7baf71edb,0xda7b2f61ebbd67aaf51e,0x9bd27a2f41e7bce79af3,0x1e5bca792f21e3bc678a,0xf11e1bc2782f01dfbbe7,0x7aeefdd6b9d71adf5b6b,0x5d69acf596b1d61abf57,0x6add59aac550a8b4f697,0xd21a3344684d019f13c2,0x72cdd9ab3325fcb294f2,0x7e4bc899031de36c658a,0xf1261dc318530860cc11,0x813005fcbf17d2f85ecb,0xd1792f05dcbb1752e85c,0xcb91712e05bcb716d2d8,0x5acb51692d059cb31652,0xc858cb11612c057caf15,0xd2b856cad1592af95b2a,0xe544a59452824f49c933,0x25d4a892d21a3a462895,0xd20f40e7fcfb9ef3ce7,0x7ceb9cf38e6fcdb9ae34,0xc674ca98c3065c8b2959,0x2a25249e13424e47c8a1,0x92023e4788e91c23646,0x60c41782c8540a012c23,0x4207c0e81b03105208c,0xe81702302c02c001fe8,0xa42232d1f13968e41d0c,0x6bbea645db0d2647a097,0xaac34b2be9a518f412b0,0xb967c84cb3da3691ed2b,0x44f60fa0b107d05945e5,0xa1def30fa0ba28b05d14,0x612e8a147f450ac9a082,0x65d04082e8a1222c9067,0xba28a05d1440fe8a0087,0x44fc39a97f7ac2c49168,0x224df450c6fa4743bd1b,0xa4ae59de772cec0ba96f,0x2dd3379fe81bdf728e30,0x393710554b83ee51c2cf,0xae5577675adbb39d7dd,0x9c9df4484ef984177d4a,0x1836a5ac2b52d499a079,0x49d13c4bdd934f744903,0x5a57a7cc23d3fe819e52,0xcad2a5a5685ad03439e1,0x918c34c8953864506d4a,0x3a9689b0ef44dc69a46d,0x3ad1369969598fb40cc2,0x3a94994bb250c6912cef,0x449945a54e5ad1303269,0x1759748b8c9a45566d12,0xab2e895a8ac8ae97a265,0x4bd1324c6518d6f44c74,0x594619cca310b691616b,0x44b4cfa259b8b2add165,0x93e0930a38964515a53a,0x864551416348bcb5a25e,0x9a3b2fb2691499b44a52,0x392545453a986692c08f,0x415c47a0afb4b25695e8,0x268af41377d7598a0bb4,0xc84ea6722b0d3acda2a5,0x46d2d63f65eaac32f508,0xda5ab4fd154aee9e917f,0x454d1d95a7b6b2d38669,0x28c3349416d65a2824c5,0xe159685af453e9ca89e,0xc8b2cf3fe10e4bf4c747,0x3a43a03d49c39e58dddf,0x2c6af396367fca1b4124,0x8d94b44680ba23c14d31,0xf3d614f94f447a6fa240,0x3fd11f8d694eda340477,0xd75225ad117a16a0b49b,0x5258d3a22a985494ace8,0x8a662ea5cb1a72bc0ba9,0x5e05d4a2632e62b7a232,0x98ba99cc65cc09b524cd,0x1a22698cb12e25d49249,0x304e0ba22006d48f9c69,0x7cfb443e5ca61e05d11,0xbc258540f4c280fa014,0x9cba8eace946e632e2eb,0x7a51a5ad38c625d06697,0x28394f931644d409b369,0x44ee30c241da60e8bcb0,0x835e983dab4c1f7b860f,0xbcc307e35d83d2950222,0x9a60d09d48045618059b,0x4416bfa20c0cd205252a,0x26ef0c0adfa204bac30,0x13669009bb4404c1a207,0x28d3044fdd821834c0c9,0xba8034c540180ea645c3,0xd26e986925053ab0969,0x16219304918980ff8af4,0xaf2af1af0ef0becae9ce,0x9ae8ee6ae5ae4ee3ae1e]) else (word80 [0x1db080,0x66c200,0x15b0800000000,0,0,0,0x6a080400000,0,0x236100a4200db0a6c2,0x100a4200000,0x15a0ad0690800016c200,0x80a02007111c441b0a02,0,0,0,0,0xc040000c84,0xc86504000000c8402010,0x8000402642c06908000,0,0x40002000100c8d08683a,0x82000196100ab0803016,0x2000000000001161000,0x4050100405010000000,0x406f88ac86c86c8690c,0xd0580b0118630000d20d,0x40dc0d041087b02009c0,0x9107288d0f030a00002c,0xe04000027023d83006,0xfcbf77eafcdf8bef7daf,0xa7f3fe5fc7f87effddfb])))
def g251H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x240,0x1400000000000000340,0xd6000000e012000114,0x3cf40000002722001,0x80008600e6cd203080d2])
def g251D7 (j : Nat) : Nat := if 12 ≤ j then 0 else (if j<6 then (if j<3 then (if j<1 then (word80 [0x26559150,0x61d64541765915059564,0x5438758d50e156354176,0x58d50e1d625438458950,0xdd9625437458950a1d62,0x542765895061d6254180,0x589505d9625417258950,0x59562541545895021d62,0x5438758550e096154372,0x585505d9615438558150,0xe0d605438258150dd960,0x5437458150dc96054364,0x58150d89605435458150,0xd4560542655815061560,0x54183581506056054174,0x581505c5605416558150,0x59160541635815058960,0x54154581505456054143,0x58150509605408558150,0x1d9605438655150e0954,0x5437455150d955454286,0x551509d9545418655150,0x60954541765515059554,0x54164551501d95454383,0x54550e09515436554550,0xd895154276545505d951,0x54165545505895154076,0x54550e05435417650d50,0x551435438050950dd942,0x542875095061d4254176,0x50950591425415450950,0x21d4254176505505d931,0x542871d9506107654182,0x1d9505d87654184d9540,0x6036550175d954061362,0x50180d89405d76250165,0xd894061f5350176d4d40,0x5935350187d49405db52,0x50165d49405935250176,0x995405d665503855d940,0xe0976503805d940a1576,0x501855d94060d7650182,0x5d940e1975503845d540,0xe0975502865d54061975,0x501825d5402197550382,0x5954061d655017559540,0xe09645038059140a1564,0x50265591406156450183,0x59140609645017559140,0x595645038758d40e1562,0x503655894061d6250175,0x58940595625036258140,0xd4d605035258140a1560,0x50265581406156050183,0x58140609605017558140,0x59560501645814058d60,0x501625814054d6050152,0x58140509605038050940,0xd95425036350940d4942,0x50286509406194250185,0x5094060d425017650940,0x5d542501655094058942,0x5028654130619504c186,0x5093060b6448180d9120,0x5d76448182d852060361,0x48175d8520e117648184,0x5d92060576483865d120,0xe1574483805d120a1974,0x481865d1206157448183,0x5d120e1d644838559120,0x61d644817459120e1d61,0x4817558520e096048364,0x58120615604818358120,0x6056048175581205d160,0x48165581205916048162,0x58120585604815458120,0x54560481435812050560,0x4813158120e195448187,0x55120619544817655120,0x5915448383545205d951,0x4838254120d915048361,0x54120a19504818654120,0x6115048181541205d950,0x48165541205915048162,0x54120551504815154120,0x5095048185dd910d9772,0x44186dc9106177244165,0xdc91060b6544182d9110,0x5d762443865d510e0975,0x4437659510e016244376,0x58910dd1624428758910,0x61d6244176589105d562,0x4416258510dd95244186,0x54910589524438254510,0xdd951443725451058951,0x4437654110dc95044362,0x54110a19504418654110,0x59550441625411054950,0x44151541102195044186,0x50910589424416250510,0xd8940441645011058940,0x4414250110e1d5415286,0x55054619541517655054]) else (if j<2 then (word80 [0x159572d0,0x7825974161d65d057654,0x7415c951d0582d974061,0x362d0175d8b4059762d0,0x3855db40e0976d01825d,0xb40e1972d03855cb40d9,0x572d02865cb4061972d0,0x1655cb4059172d038259,0x74061d65d038759340e0,0x964d01855934060964d0,0x16559340e1562d038058,0xb4061d62d017258b4059,0x562d038454340d8950d0,0x2865434061950d017654,0x3405c950d01655434059,0x150d01625434050950d0,0x8654340d9542d028650,0xb4061942d017650b405d,0x542d016550b4058942d0,0x3825da6461972993865c,0xa54d9572952865ca5461,0x972951855ca545957295,0x1645ca54219729518259,0x2545956495182dd56461,0x77259173dc9645cb7159,0x275dc1649977059185dc,0x16460b70591809d564e1,0x172593805c9645cd7259,0x1725c564e1165591751d,0x5646177258580dc96160,0x96458675dd1609977458,0x185dd1605d77458181dc,0xd605d77358185dc96060,0x77258165dc9605537258,0x143dc9605d77158275d9,0x1605d76458175d896055,0x36258143d89606035458,0x374d4d6061f5358180d4,0xd6059353581869d56060,0x265583865d560e097558,0x3805d5605d574581755c,0xd6059173583845c560dc,0x971583625c5605d57158,0x1725c560589715838059,0x560e01645837459160a1,0x56458275591609956458,0x1855916060d645818259,0x1605d5645816559160e0,0x1635816558d605916358,0x38058960611625818158,0x96059162583805856058,0x9615838755160e195458,0x38355160e09545837555,0x160a1d54582755516099,0x55458187551606195458,0x180551605d5545816555,0x160591545818754d60e1,0x9515838354560e095158,0x37254560d89515816254,0x560e05435837450d60d4,0xd435818650d605cd4358,0x16350d6055143581751d,0x5606037655186dc55460,0xb7155186dc15460b7055,0x164dc15461a64553845d,0x954e0176551805d9549d,0x970551765c1545957055,0x1645c154e09645526559,0x1546096455365dcd51d9,0x37354565dcd515937354,0x586dc9516037254582d9,0x15160354545645515161,0x37654181dd950d977454,0x286dd1509db7454265dd,0x15061b7454182dd15060,0x37454176dd1509db7354,0x176dcd505977354364dc,0x950a1b7254276dc95061,0xb7254184dc9505977254,0x164dc950d8b7154276dc,0x55061b7154176dc55058,0xb7154187d955061f6454,0x185d91506036454374d8,0x950dcb6254287d895061,0xf6254185d89506136254,0x180d89505db6254154d8,0x950dcb6154187d855060,0x36154276d515061b5454,0x181d51505db5454276d4,0x5505db51541859d95061,0xa655417699550e157654,0x3845d950e0976543815d,0x950e0176541845d95060,0xd76541815d9502097654,0x2765d1505d974541655d,0x1501d974541765cd509d,0x972543835c5509d97154,0x1765c55059571540765c,0x550e11655438259550e0,0x16554184595506056554,0x7659550e1d645438559,0x150e09645438059150dd,0x9645428759150a156454]) else (word80 [0x29772827,0xb0e484fd0b109fa16212,0x57f2623e858847d0b108,0xba1621107b301c9c65c3,0x956ca872c1920e67f241,0xc30e4838bfc906b6d760,0xd15f281a30e48371ecc0,0x7671970ed5b2a1db0648,0x3b39cb866af960c55b2c,0x18cce183198c30636d76,0xc75ac818b06583c9ec3,0x79b1650f183281e6c55,0x3c9fc3065a2860ca7b0,0xc196861832d8ca865b16,0x50c98728196c550329fc,0x305f3d860befaec17ee6,0x102fdcb205ec3920d87b,0x301d1c65c3a56ca874c1,0x920eadaec186ce0830d8,0xb106017920b82b241305,0x658251fc80525595091d,0xee8140fe40280bca8581,0x7960ac2b3016856602a3,0x5c9054179809cd724139,0x2658202fca03e6992088,0xbf280f1ae481e0bcc03a,0xef8408606ec11c05d823,0x1eca8463d9408e832211,0xc0a1c2380c3847418108,0xc7f200d056601bc6b283,0x23f9002aeee804b0e400,0x99dc1038c790070db240,0xb8e658187fbb0306d960,0x59572a0ab1e401563c80,0x111b860455b2a08abe54,0x1061c9021198602d7328,0x5b06480b38c90299386,0x3f210c07dbdd80f57c9,0x1e719604edaca09ab65,0x412c8b28243f98038793,0x7645940e56cb01b6f7,0x6037670406ec5880ddbc,0x3019b6860336b0c066d2,0x180cdbc1019b5820336e,0xc4066d5880c5dc900cb9,0x9401c7f3002aee58045c,0xcb009b9620100f30eb33,0xe19ec66c33ce519579cc,0xb20f396651ed6dc2aecd,0xa9600db32c0193658032,0x6cb804db870089f2e00b,0x6e1c010dcb48ee17591c,0xf30bf03e49d007c937e,0xe3854b596ec9880e60b9,0x66bb1747593460f3248c,0x34dd91b07c92924c9735,0x832ca2b761545a2b2a8,0xaf77250013287eb621cc,0x40ca1be899237d4b227,0x1125ce7114c1e0a5913,0xc302c87255dc8f1224b9,0xca2994819eae5032ce41,0xf174cbc051d65809d708,0x5303e4899a6ba8fc8392,0x1f90328440a2607940cb,0xf395621e427202b80e5,0x84244c90a54d7412d172,0x825555d04a184c065118,0x60cb12ca190c2602fd2a,0xa05ea796032d6ec0629e,0x480cb5b9019fabee7daf,0x9df2fe57baf5deafd579,0xef37e6bc7f8eef5dbbb5,0xf67ebdd73adf4fe7dcef,0x9d72fe5dc7f8defcdf5b,0xe7776dedbbb6f6becfd9,0xdafb5debad6fabf4fe7e,0xcfb9ef3d677cdf9bb2fe,0x5ecb793f1fe3ec7787ef,0xe5fabed7baf5deabbd77,0x6ee5dbbaf73edf5bdb77,0x6ead7daeb3f66ecbd7ea,0xfb5eebd577adf5aeafd5,0xba9f4fe9f53b9fd3f67d,0xcfa9df3ba6fcde97f2fa,0x3fc7e8f71be2fc3fe097,0x5d91805d76461172d918,0x35cb64e0970d92855c36,0x461570d9182593616035,0x4d8174d4f6059353d838,0x25d76060575d83855d36,0xe0974d82855d3606097,0x4d83855cb6061172d818,0x35cb6050d72d82855936,0x61564d818259360e0d5,0x4d83825536061d54d817,0x45536059154d83835476,0xe0951d817254760e054,0x3d835350f6055143d816,0x4553515d164d41645535,0xe1576d07825db416097,0x6d07865cb41e1572d076,0x55cb41a1972d05865cb4]))) else (if j<4 then (word80 [0x2afa3be1,0x9f376c33e62d987dcbb2,0xefbad649f72ecbbe5617,0x57c96f24f95d5d9f1bab,0xabe39b657c732caf8eee,0x41f138cbc011b868015b,0x2b002e6520039cbbfebb,0x947fd8724ff9c65df88c,0xc33f0b9947e18324fc5b,0x655fe39c93fd93867f32,0x10cfe5b5d9fc57c93f93,0x69680a6b2d012e65a029,0xb43405358680b5acb015,0xee5dfbd6cabf7ad657ed,0x7724fd9ce59fdb6cabfb,0x6d657f6f2c8fedfe09fd,0x38cbc02ad9580722cb00,0xae652019bc24023f987e,0x87930fd1c65dfac8b2bf,0x537847eafae4fd2ee59f,0x95ccb3f379767e75b2af,0xceb595f9ddc13f3b9627,0xe42b245412658a52eca1,0x4a7190294972c5217e50,0xa435c91487390290bf28,0x51bbe10a339c81461595,0x29ce7205140614a60ac9,0x142d786278ab2a4f1765,0x9e38c813c5f94274d72,0x44e9ce409d6ac3136699,0x226cbb2c50056589f25c,0xb1384896270e7204e12e,0x58b676ba97101752dc2b,0x305539618a90bcb132d7,0x96265df284c85e48997d,0xc9132f89226607204c9a,0xe4899a5cb1314896262c,0x7284c15e489825cb1301,0x5972690b2c4aae640955,0xdc8126ec98242a72c485,0x4258902fc91205d97252,0xc2ea4a585d48f5dc8124,0xed7525d772048de5d496,0x9ac112c15922382f2c58,0x85660b076c395e17982c,0xc2b3059b9614b335c916,0x749752c9daea5ac05d4b,0x439c811615972345b284,0x685e608a4ac811949752,0x242f2c5705660ad35c91,0x5ae5872b1db0e558b660,0x742ecb8e8b5921d17320,0x3a4de40735dc80e65f95,0x1c2f720382ee40722fcb,0xdeef861bddb0c37dde4,0x86f16cc0ee5d971dd6b2,0x43bae640772ecb8dd617,0x51b96f24372ee407116c,0xc0ec5d971d96b243b2e6,0x4076babb0db75751b736,0xca36e65946d5acb0eb75,0x761d752ca3aae658789a,0xc30f179751e372c43c6e,0xd48784acb10ab9942152,0xf2c41aee508361c91075,0xf96202b92c405ee50803,0x9c91007197212daea425,0xb5d47fcf4a8fd9d951fb,0x3d0a3f676147ecec98fd,0x9d921faf2ea3f679947e,0xceb28fcbb9420b3ac841,0x675907d38cb90f9d6421,0xf3ac83de759081aeba91,0x15d751f33b283e675907,0xc38cb90d9d6421b3ac83,0xd685887a5dcb0f39e961,0xe5732c3ce765879bcba8,0xf3b9821e772c43ceed48,0x791fc80d4ad951b15f2a,0x35b0e486b0aca8c67390,0x188bf28309ae486139c8,0xc215951802b302e9765,0x5d34c90ba7190174e72,0x2e056585f25cb0b6489,0x616cd7242d9ce405b39c,0x80b4719617a050c2f406,0x145e0acc0cee58519df2,0xea34c05d4680aca8b217,0x9515e07202b9ce40570a,0xcb8b03592160bf2a2b5e,0xe40560bcb084d796109a,0x92c2140e404225cb0841,0x59710c2f2e2085660407,0x6c387e1598190972c323,0x9614647cba8cd0175194,0x2b2a2a92e58542bca87a,0xf1760f98724289ce504e,0xbfc909d6d75130e72a26,0xd75d452aeba897a19212,0xef2e8259c65c48ceb209,0xc3921418f22234f6145,0x3d0ca095a18412b42a82,0x5686444abeba095a1641]) else (if j<5 then (word80 [0x9ae49241,0x2caa186b92429ceec85b,0x95d90b2fca1906b92322,0xc6ec63d85d8c77fbb192,0xfd763265aca649565555,0x38c82aa179454df724a9,0xd9e49510bcb2a4e56554,0x82b30ab156555638c82a,0xc1598541db08a81ae495,0xacc2a85595550e320a,0xa28e49512acaa4671904,0x8c2b28a205e51437dc92,0x875b924fc4f28a10fe41,0x410acc28c4996519cb0a,0xa3525954612cc27ce687,0x4f9cb0e9f525d93e90c2,0x27cf998516b32ca2be61,0x1457cc3a8a8d96516b2e,0xca2ca61545c6b2a8b037,0x450262a8a04fdc9400ac,0xa21225954247b2084856,0x59050aca20a49964146f,0x248185650fd34c920e49,0x97410fb2a822564104ad,0xc92026b924071f247fa8,0xe48ff0acba1025954207,0xb2084056610624cb20d4,0x965418d32483525d8fea,0xd3b20159764031aca804,0xc61502c8b2a041596310,0x2b306217650c434c9188,0x4b9630cd7246185658bf,0xacc18ad786314bb2862,0x85e60c235c91845f9730,0x5df0e60aee40c14dcb18,0x9996302c6ec60585d8c,0x1ecb18d319531a62ca6,0x34d590c6814398d31853,0x1b5aa8635fdc8c60bc92,0x9a159853dab0ca785661,0x4b6ac3296f98252c2b30,0xa71ae494c6bc3242d786,0x480d7249005a611e2eca,0x23c699247a0f0c8fd21d,0x91f79bb244f276489e2e,0xc913c1d92292b2a44179,0x24f02b309eb96153d81b,0x927615923f0d7247c856,0x5cfb12ca9f63d903edf7,0x47d096613656c826c27,0x984d547249ad2dd8ce51,0xc919b497632933286528,0x648ca12cb1a2ad9033ca,0xf2e659525ccb35c919b4,0xb763415b20682be40cc7,0x9bb1a4f17634a4aca691,0xae48be35c917a95943d5,0x2d306fa5650dfc9bb1f0,0xc3923b55d2e702b650ee,0xc9bb1d0af943a15f2474,0x40a60f480cc1e96e653d,0x2daca7a1c648f41f4c1e,0x897963aabeec75571d8e,0xa4ac91e5929539f232a7,0x3e7e10e7ceba1ce97923,0x9f24ca73e4594e756cb1,0xe0af963915b2c7264dd8,0xe4c83b1c9af743935ac8,0x722be48e4bdba1c99d64,0x3915b2a7bb1644f757ca,0x9d933853b15f2a736459,0x4e6d6aa1c4c79138a62c,0xa7b4c550f6b6b29e6719,0x43cebec879d7590f3bfc,0x11e73f823cd2b2878d7d,0xd0f1c8aa1e3a3723c723,0x2a72a5e50e5afba1cb91,0x54397470472e85c8e5c8,0xb29cb3f823947f30708f,0x260e1394b9c295963873,0xac870eb550e1bfb91c3a,0x1623855f2a75cce14eb5,0xdca1d697963a6b8ec74a,0xfe4ce956cb1deaf9638f,0x26ec71e41d8e357c91c7,0x338238f26c471e4588e3,0x5fc99c615928602b2b0b,0x9ce42161fc8438179283,0x42b2f07176560c2fcbc1,0x56175821daeb05aee420,0x90acac2a1598848bb290,0x91a64a1239c842215968,0x502b3109976521334c94,0x266b92841df0b0785662,0x1a72c2c354975865daeb,0xd85e560581c840a1597,0x81c5b2903d25d60335ca,0xc095b65812b2cb025d59,0x20480cbc0d01768187b2,0xb034d652069ab240d018,0x78197329034d61206beb,0x940c2d987d8bb2efb2d6,0x49f69bc83eabb907d4bf]) else (word80 [0x9d00acc3,0xa237927402b30e91ae49,0xcf35c936e1d987192b20,0xe307e61c547c938a4997,0x6ad2b20d5a5e41a80ecc,0x35485946a90f28d2a3e4,0x9a542cab58979069d2f2,0xd325655ad4ac935b198,0x26b50b28d4a5641a943c,0xa3489790690bb2ad60f6,0x55ad1ec935b31657043b,0x2ccd05655952acab2a1f,0x966486f24c91ae49921e,0xc83323f90644bb28cb1f,0x659943fcb31ead9064d5,0xf20c7619d58dc2bab1a8,0x7926373f20c6e19958dc,0x2b2b1a15976607b20cc0,0x565d9784b232e3d9065f,0x3ac8c81ae49cd7ebab9c,0x6b926da1708dad2dd5a2,0x85c23423d9468e32c8d1,0x8f649a30bca37efb926f,0xc6f24df85661c084c237,0xa3f946fa36c8df46591b,0xe1bc93183f90609db0cc,0x21765584b8c9b085d926,0x10bd2ebfdcdd181b9ba3,0xbf90600c32ec1dcdd1,0x835ec8306ff756142f28,0xe61ae49ca0acc392e585,0x724d724e49be45c82fca,0x3968f927121308e1a4e4,0x5c24bc833e97906792b2,0x8d046611a04bc833a3d9,0x468232c8d01ae49c735c,0x9362ef756d1daeada3be,0x11b377c23610b846ca17,0x8d7c5e09af8bc133719,0x626707b20c5bcdd58a0a,0xcbb12f383621f704c443,0xe0d8787c1b0d61658aec,0x2ed1505e496331c9ac42,0x7944d04f249a05649303,0x5c925873904b0af2a959,0xae492b7dcb25efb954bd,0xf32a97bee512f7cca25e,0xfb934bdf32697bee452f,0x7cc8a5e15944beb72c97,0xd9e552f7dc2a5f67854b,0xdf70897be6112f7dc1a5,0xef9834beff2097bee112,0x97cc2252fb824b9f1049,0x715e552a2fca25463934,0xa8d724953ee092a7c412,0x5473904aadf0a96dfe09,0x2da5bb262fb764be572a,0x97cfe412fadbb25f2b85,0x4bebeec96cce152d9fc1,0x25a15942f1af305cd6e4,0x8b990ca97737902ec2f2,0x8a53ee494a13ca266a39,0x24c8fd308c096491d98c,0x823aad904755f208d096,0x511c4fc9a32af9046726,0xec8dcc6111b98c0a3655,0x95580e320b005e495d0a,0xcc2c25596579cacaae40,0x6195bb6b2ab63d905742,0xb30af956555f38c82be6,0xb92569af0c9415655286,0xbc324e6b9249c2d30929,0xa6492583c324d4b76498,0x2f24a4bee49497c49292,0x37925244f24a40fe4947,0xacaa2e159245c4b2a8b,0x856591224cb224379243,0xc972c879ae490f2eca22,0x65f94438d724870f6411,0x63ecb222999444137288,0x68565d1512caa2b02974,0x5206ec8a405d914994aa,0x29319545264ca8a4c595,0x141ec92290287452650a,0x8a4c6151498c82722598,0x4e8ab2e9d2b6413ab3c9,0x26ea3924de5cec9c4b5d,0x93812c91bc55973695b2,0x6d48e50d813c91b1339,0x3615f206c09660d9a5b,0xb1b29994366c7286b59e,0x48d6b2491ad6f9035a96,0xec6b26e50d651c91ac56,0x9734d332869a8648d34c,0xcb1b96176372c6ec6a58,0x5d8d44dc91a9af903504,0xb2c6eb9dd8dd72bb1bb2,0x1643755f206b8fe40d82,0xfca1ac6b923584b306d9,0x565cdba5bb1b6999436d,0x5b206dd2dd8d54dca1aa,0xaf90354bb2c6e58594dc,0xacc2b26b925604f30ab])))) else (if j<9 then (if j<7 then (word80 [0x41d08361,0x5e20ac412c81f103620,0x56408080a900d20003fb,0xc7f38fcf1f883ecc7d40,0xfa01f2a3e207b68f561e,0x963d0c7968f1e1e103b9,0x47658eb11d2a3a0c7348,0xe531c8038907080e021b,0xce37486db8dac1b42366,0x46c70d7a1ad635586a40,0xd3b1a60349468b8d0f1a,0xa33c06700cd819a0332,0x6600cb8195c324c6448,0xc8118ee31b06310c5718,0x7830a460e0c141818300,0x5fa0be0178a2ed45d50,0xb9f17222e245bf8b6a16,0xba2d405a40b4016642c9,0x458e0b1416002be05780,0xae815b42b305620ab615,0x562a705488a8214ee29b,0xc5308a59148a28f451a8,0xa2d143a28184fc09eb13,0xc6274c4e309b71344266,0x84c9098a130425e84b90,0x96112a0250849d092c12,0x3c243848308f611cc237,0x846b08c7117e22c44548,0x89b111a221443c085c10,0xa8210841a082c1048202,0x83f807d10f581e343b70,0x7500e641ca838e07080d,0xf41bb036a86b30d441a3,0xc33f066d0cac19383120,0x5fa0bb617242d005810a,0xb0150829685180a1213f,0x27704e00984129023e8,0x46408a81114217842108,0x240ff81f783d3077a0e4,0xc1b4834e066a0c581780,0x2c9056a0a50143027704,0xc60908112821d042a07e,0x40f581d00378068c0c50,0x18202f405780a3813402,0x3a03f006f00bd014801e,0x802f0038003e00002b21,0x279ae4a4e39c849a5795,0x9302b31251c6424a35c9,0x492159592c2b2af81ce4,0x1ef0bc83c90197772332,0xcee4d651dc73cc3ac2d9,0x75c2f20f19be45e285c,0x33b66f91766372ced40d,0xd5da80babb5379476a06,0xe6ed405cdda8dc33b537,0x84768e720f09ce41d80b,0xc93bc159877ce320ef85,0xe55dd0acc3c161757957,0x720f31a655ee34cabd86,0xb957acd32af39ae59ea7,0xdc33d4f9867a8d330f6d,0x6619ed35cc3d269987a6,0xb50cf4d6619e9b2c2bd3,0x77867a2eb0cf45d655e8,0xbac2bd175657a02b30f6,0x17651ec34c93d975927a,0x2f24bed8e15760ac92e,0xa5f945d0d724ba48e157,0x617c92ee99905ba42cab,0x7a6e556d91c2adabb905,0xb42f24be05e597b0bc92,0xf561655e0bf24bc05e59,0x7972b2af2ed645e5af0c,0xb995655736bc32e50786,0x5c6170cb858e5c01b0c3,0x97909212f20e985e4,0x1d50bcaba961768b04f2,0xab34ce5965994b2cb319,0x6596612cb2a6e496430c,0x82d863905a8c324b598e,0x49690bc82d0179659c2b,0x2514856562839c844e17,0x9287c2b2f1005656260a,0xcc446699288ce7211105,0x65a250acc4486992890d,0x725109be4a1e37cb43a1,0x594910c727218564a420,0xacc4805d94900e321200,0x56564139c847e49978e9,0xb291d256423a25cbc72,0x97908e2032f2385e4a35,0x2fc946887928cc2b2f1b,0x8565e3672bac6ced748d,0xa12c91b056624676c248,0xd0984916c2eb169865e2,0xe7ebac5e15948f8e7211,0xe95e563c37c8c76f1758,0xc82b2f1895e563079c1c,0x601f946f03b28dd45e59,0xb99fc837317866e6370c,0xdc4fe09b873cc2fd6792,0x5f87f28dd8f651ae0bc9,0x3a0fb92741f124e81ae4]) else (if j<8 then (word80 [0xa9ff53e6,0xa7a14eea9d5539aa7154,0xdba9ae5332a6454c4a97,0x952d2a5814aa29485280,0xa4d94972926523ca4454,0x84a8fc51e8a3b147228d,0xc51a8a331461a8ba5156,0xa28d44a288c50fca1cd4,0x34286050aca0ed418282,0x35028a02540027f24fd4,0x9f7d3e7a7c44f789ec53,0xce27824eda9d813ac274,0xd4e889ced399a72a4e3c,0x9c5938727034df69bbd3,0x7226d84d929b0535ca6a,0xd4d429a65348a67d4cea,0x99b5331a6534c96990d3,0x1da6334c4c986d308260,0x84c0097e12f525dd4b8a,0x96e12d5a5a34b2896312,0xc225764a9094e9299252,0xa4a449469289250a49f8,0x939126724c0497092c12,0x5424a04926920d23da46,0xb48b6914d220242f4818,0x8ffd1f7a3dc47928f051,0xd923a447388e511c5237,0x346c08d591a3a33b4666,0x8c61185a30345f28bbd1,0x7222d9459c8b1115ca2a,0x845408a5913f226e44c0,0x8945123a23d445488851,0xca210440c87e10f721e,0x143b287450e1a1b5434e,0x867d0cba18f42e685750,0xa7a147427e84c1092a11,0x64218840107a20ea41be,0x835d067a0c2417082b90,0x53209840fc81c502d204,0x7403880390021ffc3fe8,0x7f94fee9fd53f847ed0f,0xd49f9c3f187e10fbe1f6,0xf3eb87d34f9d1f2d3e40,0x7c48f851f023df47bc8f,0x751ee23db47b48f639eb,0xf3d6e7abcf539e9f3d28,0x7a30f421e7c3ce879a0f,0x2e1e503c9078f0f1a1e2,0xc3c487870f0a1e0b3c06,0x77e0ef69de13bac7738e,0xe31dbe3b6c76b8ecd9d8,0xc3af275c4eb41d603ab0,0x7528ea11d373a5e749ce,0x8f1d163a1c7418e7f1cf,0x639dc7398e6f1cce398c,0x72dce579ca039227208e,0x399c6338b27144e209c3,0x73856708ce0c9c083800,0x6fe0df71be437b46f48d,0xe21bba37566e7cdcb9b8,0xf370e6decdb99b6736b6,0x6d4cda21b35365a6c58d,0x871b0535fa6bb8d6f9ac,0xf358e6af4d589aa03530,0x6a30d3e1a7434d66974d,0x279a41346668acd0e9a0,0xe33ee67a0cf019d1337e,0x66c4cd499a0332e6630c,0xc1997b32e46590cae195,0x432986510c9a992c323c,0x6454c8518ff31e863b0c,0x6f18d0319062f4c5a98a,0x7313e625cc43187a30e4,0x61a4c309859309660f8c,0x1b182a302c6038c0297f,0xa2fde5f68be917c12f60,0x5e70bca178c2f025dd8b,0xb717662eb65d4cba5974,0x2e6a5c98b8f17152e0c,0x5bf8b7b16ee2dcc5b78b,0x6b16cb2d845ae4b5896a,0x82d2e5a24b3f166b2cc4,0x594cb2596412c7258c0b,0x12961d2c225818aff15f,0x22bd25780aea95cd2b82,0x56d8ad715a62b2c5638a,0xc1957b2ade555caa7954,0x32a7654b8a9115132a0c,0x53dca7614e429aa5328a,0x5f94b42952522ca3a146,0x2882507ca0413fd27d4,0x4f5c9e0939c27124df89,0xb3935926664ca098d930,0x525dc4b8c96612b5255a,0x4a9094c128f24f249c49,0x301252249448ec919922,0xb2436484090111fa23d8,0x47788e691c5237846c48,0xd31197231e461c8bf917,0x22c245488a1913b225a,0x449488d110f220843f08,0x7a10e121b2434486410c,0x216242a484f10962106]) else (word80 [0x10c0f607,0xb043000900460240ac1d,0x43486c0860b409000060,0xbc148316040828010480,0x3ec1036d0421f06813,0xc0d0350070041a104838,0x76006181d04205c015c,0x100106402741d8306603,0x4186000460100d80200c,0x9c00409d812b0236042,0xc07a80e301a6030c0598,0xa3012601bc028803300,0x25ffdbff37fd6ff71fe5,0xbfbc7f68feb1fcebf957,0xf0afdf5fbabf6d7ecafd,0x75faa3f457e7afcd1f93,0x3f1e7e16fc0df7dbef37,0xdc0fb61f653ec27d68fa,0xb1f4abe8d7d02f9b9f30,0x3e587c98f8e5f14be217,0xc32f839efbbdef7bc6f7,0x55ee63dc47b70f6c1ed1,0xbd9b7b1af5f9eb73d667,0xabcf559ea5bd437a76f4,0xcde95bd237a34f445e84,0xbd0179d6f37de6bbcc77,0x97ef2dde57bc997906f1,0xb9e2c3c2b7846f06de09,0xbc0b7806efeddf9bbeb7,0x7c6ef6dde9bbcb7786ee,0xe9dd7bba7773eee59dc5,0x3b7e76ecedb9db33b5e7,0x6aced39da03b387660ec,0xa1d903b187620ec21d80,0x3af075d0eb81d6c3ad07,0x590eb01d5c3ab07550ea,0x69d493a8374e8e9b1d32,0x3a5c74a8e931d223a3c7,0x456e88dd0d3a117406e7,0xcdcf2b9d17384e6a1cd0,0x3997731ce619cbdb9737,0x2d6e579ca839437276e4,0xcdc9539217230e431c81,0xb8f571cae371c6a38c77,0x176e2b9c4d388870f6e1,0xa9c28b849706ce0a5c0c,0xb8117012e001bfab7ec6,0xfc2df55be637be6f5ede,0x99bceb7916f12de05bbc,0xb7716ed2dd51ba6373f6,0xe6edc69b8336fb6de6db,0xadb7036c26d66da95b4e,0xb68e6d0cd9ddb34b6556,0xc8ed8fdb1a36266c36d8,0x4db0435fd6be6d795aee,0x35c56b6cd6b9acfb5906,0xb02d5c9ab5355e6a9ed5,0x1a9c35306a48d471a88,0x35086a00d3e1a7634e46,0x9b8d30da57b49e690ad1,0xb1a31b4496882d0c9a15,0x341c6828d0319feb3e96,0x7aacf099d7b3a6673cce,0x419c4337a66d6cd719a8,0xb3496682cce599833226,0x634cc2d98132f265c6cb,0x6d969b2c46578cab1952,0x3295651ac9cd931b2546,0x48ac8f5917b2276436c8,0x4d90131f363d6c78d8ed,0xb1d3638ac6f58d6b1976,0x2f6c57d8a8b1436268c4,0x9988f31106202c3cd872,0xb0d76192c2e9859309e6,0x12cc21583ab06d60c4c1,0x65828b0436074c0c580d,0x30126014bff17fa2fe55,0xfbabf217ddafb05f50be,0x817ca2f8c5f08bdd57b5,0xaf635ea8bd3179e2f345,0xe50bc7d78baf0b5e06bb,0xed779aeeb5dc0bb61768,0x2ec25d74bac97552ea15,0xd32ba417442e7f5ceeb9,0xb9732ae5d5ca8b92171f,0x2e365c5cb89570eae155,0xc02b7c96f52de25bb4b7,0x496e52dbb5b62b69d6cf,0x2d965b10b6016ba2d6a5,0xab2b5456a2ad3d5a62b4,0x8d68dad135a14b40967b,0x2cea59b6b3316622cbc5,0x960b28564aac8758f0b1,0xb9630ac555892b105618,0xac295842b065608ac095,0x800afd15f22bdb579eaf,0xd5db2bae574cae595c7,0x2b8256e2ada55ae2b4b5,0x686ace95992b2a562cac,0x9579aae455aaab3555f,0x2ab05544aa515462a7c5,0x4d8a99152e2a545498a9,0x1151e2a315452a86d506]))) else (if j<10 then (word80 [0xa0200174,0x2809908020223c100004,0x50140400361405dc099,0x80000019080190ea080,0x59a1b342008646880002,0x166851c0dae08020264,0x3d86200d4181c1000096,0xc2db0b6c2db08036c386,0x85cd1d161a100470207a,0x106c2000100b01008000,0x4361000000004702012d,0x8402c0690b01006d85b6,0x100a4200db0800004f04,0xc84000200019b0b80800,0xc863e1880002c0580c38,0x20803b8c40bc117a8200,0xa42c04000180800030,0x16024e0400024e040000,0x180804020001e,0xe3166c348619410049c0,0x802020001a4201283484,0x35040201a4201283484,0xce840290804a0c76,0xe31804a0802d06c86f11,0x58881c090200bc44c058,0xb016035eb6f320e4144,0x4db620bea348b5a917f3,0x2cc09446038ca0ada414,0x19544ad335b685e6304c,0x47a5a1e3028f2328842,0xb011a0ccc686398d0d80,0xf26563e4cac600019410,0x8638c60115624d84039,0xc0800056e0d21960403b,0x61ed8407820001602c04,0xdc08000001b813703868,0x4dc08046c200c0580b01,0x94b0400000100370,0x200c040331b1038100b6,0x40180f5840180b01602,0x1d6183a100363931b01,0xcab13010060396157d39,0x66712898080498d4576,0x875ab82cfc13d8caef6e,0x41b3e35078eadd07da31,0x43d3906a7e5137662449,0x576407182e6061c1b41e,0x1e2880ef8c1d21a42014,0x8618a0a9c0bbea08b61a,0xb0d21a425b080202ac58,0x2fdc100000000004069e,0xc141a020080d2140690c,0xbba283c6104341000094,0x1941e3b8287b85071743,0x4869096c20080caed0f6,0x83b410000ed87ac20100,0x27e82000000ed87b6100,0xed86909381a424e06908,0x76c2016fd0400000143,0x8227b68bd81eb08019d0,0xf5866d0e89e080000000,0x20e850742c604021,0x8186040e84000e840e84,0x31c0804302010c0c3,0x201d6177f808300ec18,0xa1810000974da0d9f168,0x3cffa1ac89c60b0d6696,0xaa2d099ff4359239d0d6,0x58e74359403d8127e82f,0x607d813bab44ee0f0a42,0x6718935b16718b38c457,0xaa8800332f3878660ccb,0xce1e1985e61442070c59,0x8627eb866e4fd70c9de2,0x7e03866978a0b8af052f,0x482070316196063610f9,0x725903e5c964063c5c05,0xb0e54838dc19b4312c3,0x1c6c346878ae0a6d0bbc,0x9841c650c6de09f449b3,0x378476926cc0dd8a0c6b,0x78890cd68a135c335a28,0x547e691050aaf504447b,0x248496076d0a3d41430f,0xa4a100980f4600011e40,0x4c8db0ac79c441c9435c,0xd4a24d6a51000005f492,0xcbe23181762ad28c60f,0xa182844fc849905f1305,0x99fcc6300f1fc90999d,0x178a0fd9b364285679d4,0x1fb6b2184d001100d028,0x10a4180b10d30820c0c9,0x8e0b4158c03805b0118,0x7e090698044c9883300a,0x88809721d46287308700,0xc0686a81911215037030,0x15c08088888210390860,0xff0343d42a09f0646204,0x83c028a098298301680a,0xc0902a0500a0290170d6,0x190730621e41586b8110,0x483c4791710981780b83]) else (if j<11 then (word80 [0x5a207bd0,0x8460c300000000000000,0x580800,0x6c86c840000000000,0xb61000000000000000,0x5ba1000000000000000,0x2d84032d0c1a10000,0x83a1000040,0x39b0add0e6c3ac5050e0,0x65e02830000804029080,0x548ad81a9100000040,0x201d4100e6c378440100,0x9a0ea0cd069820aa1629,0xa0a8d083c2ac6009958a,0x6825e4400000160201a4,0x364201b6041c08040364,0x20000000001ec98200cb,0x802df5228e99a098080,0x3011bc8228e0d086c2,0x16e0402dc0f3022e505,0xcc080521b60690803016,0x280db0201037345ce04,0x20d0f381cb43068402c,0x860d0c9a10000d4100b2,0x1000000d4100000fecb1,0xe304128d0abc02c70c1a,0x83008b82106000e04003,0x6100008702d1ec52cd05,0xeea0bdd4100403b6100e,0xd861c0c3816020000000,0x1b604022d08074e862d0,0x800045a10043a100fb42,0x77bc1a1d0c5a18b42,0x19b0804a08018f062d0,0x8000000076c201a74306,0x3512b9fb41abcfb41f6c,0x32c0c3818d84033618b4,0x39b0e6c31b0a6c30e040,0x16cd0c00b78387420148,0x402016c08040337b2880,0x2d8100870201a8b829,0xa0b01000032100008702,0x808059a1000ba100b210,0x8059080000000521000,0xb604000000020001000,0x8000402000132140400,0x2000108b052e04000,0x25c0a028080403,0x18100d41405668401642,0x6436c0800000402c86,0xc841c083810000b21070,0x36434c083814072c3643,0x64200274200000000000,0x1b210ba100d90ea0ad04,0xcc8802c856284011,0x6125e080004000354e08,0x5ce0a0d0e5a1cb42014e,0x7361ad86b6100cba1cb,0xa1000000000000602015,0xb0d6c35b0ea0d2160200,0x11b080558b0400009,0x742974201b21b2100404,0x68200341000000,0x8068d08051a1,0xb60690d21004059eea,0x41d219a09722a42012d8,0x40290a5d0b0100602ee7,0x8284d8a0e5f704341006,0x2010080005808000290,0x80590d21b21bb4200012,0x832820001a8b04000080,0x89d080000000758690b0,0x1000000ed862c32e7d07,0x1618b080638100000d87,0x30cf43f0367cd8400000,0x3b613bc0a2b38a,0x8bb61000000008b08ea1,0xea10ea1004716283a,0x12bf8898848b08ea1471,0x628e2c4014e073610000,0x407ce751072624066d0e,0xa0804b364835a0802028,0xb01602c05016023a420,0x404be898e7509361bc4,0x480a03de588020001407,0x5814072c200017117302,0x9b0800000336edc1d977,0x45cc0800051a16034685,0x1d41d414058080000d0,0x5014040258107b0a0c68,0x3c7428a25b14787a4430,0x664d850100009b420000,0xd5d8b981603b410ba100,0xda0d368217035b58b6,0x83b41e60400000000000,0x1808000000000301,0xb21b2132100b,0x21000000000000803016,0x3282c04000000000219,0x41138186504000100009,0x60402908000004000000,0xce8401dc08,0x59a17702ee05dc085d0]) else (word80 [0x193820000014840,0x2000000000107a169a1d,0x3436645cc08000138149,0xe0e9a10000d342007742,0x193420001,0x6c0803bd3100000077a6,0x200ad8402b6100b3d344,0x1283dad8ab6100321ed,0x6c587420000c056e6510,0x19086c20100321005a0,0x8016c2ae061704000001,0x80800000000000402000,0x10f4411908001d080000,0x6dbd45b6ad159568b6d])))))
def g251H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x13c324000a959e0,0x6175dd9,0x9c80006145a0000077f,0x117000c32ac0000,0x12300000137c3,0x36822020000000095800,0x45600000000930,0x33fc38186000006e21,0x4e000003370d4dc40061,0x30000000049200186000,0x20e800000003,0xdac0a0011a000000c762,0xc0005b0000033a00085,0x48c800000000000000a5,0x8db72542000000001694,0xccfaea698d800001afb5,0x7800001aa3600000004e,0x65fd682ad6ee63c7d,0x91c000000002b40007d4,0x520015232c5220013c66,0xc000000000000000010b,0x820015e00005e298,0xce95b0e11b00,0x13e0000960000000000,0xa000000047e000eb2a2,0xc220022029f000003594,0x1504c002040000000000,0,0x187800000308,0,0x1b372bbcb000d6c0000,0x2400000000000,0x10dd2400000c66000,0x40,0xb540a0010e48109,0x800055422000c4a4a800,0x1cd94c8,0x2700003154,0x28000000000052800000,0x621000000006d3d14,0x16a3228cd108392ecbf0,0x55c648000002d,0x500030400406baab6800,0x4ea258000000019ef,0x282b7001a740040d0000,0x13400000b5a,0xc01d6700000088c00000,0xdc000000000000ec8000,0x10300008e306b500,0xf441d80026f00021,0xc000000000022aab8000,0xb7000000000000000000,0xc080002f05,0x25280000000089e8d800,0x78200000000000000000,0x1af66bc970000,0x6380000000000,0x29c800c8600000289,0x5d800000000003374,0xd9d88000004c70001cc0,0x30780000000,0x397000e918d126800074,0x49800000000000008,0x416000000000000194a5,0x80e215a1800000000000,0xcd60b8000006cc,0x2298000000,0x1a00,0x20020f800,0xb80000061b06e284002,0xc6000000000000000000,0x1b440000002400,0,0xacc000000,0x1250000000000000,0x1400036f00000000021,0x21c800001180,0xc48000000000000,0x24dab80000080,0x6000000000018a36567a,0x188000000000010a2,0x656564bc000000000000,0x4892340027e00000,0x93a8e4584e44a,0x3c8004d70f0004778,0xd38256de908cf8b00000,0x3ec00046200000,0x194613800176270,0x19,0x6400000c6a8400000097,0x400047f34597ac400445,0x2a0000000f55c8,0x642a6c000000014533,0x149062807000001020,0x2110014201027214031,0x1406522402051d413111])
def g251D8 (j : Nat) : Nat := if 12 ≤ j then 0 else (if j<6 then (if j<3 then (if j<1 then (word80 [0x386ae318,0x6ae5976ae5975ae9962a,0xe6976af9165af9f84af9,0xd64af6972af9d42af178,0x5375b84371782376b803,0x71786365b84361782361,0x5873d31843d41803d158,0x73851753873653817873,0x515873551753515872d3,0x1842d35832d39822d418,0x2d5975343382349f803,0x415873c31843c41803c1,0x7873315873a15873b318,0x43b41803b17873215873,0x933862e31862e59762e5,0x9752e99622e9b522e9f8,0x2e6975319f84319d643,0x18362318162319d42311,0x7862791652317841f6b8,0x1f17861e17851e6b801,0xe1587213982214180211,0x7871d15871d59741d158,0x71a15872035832039822,0x41802017871c3783194,0x3851b69751b69741b836,0x41b81641bab821ba9621,0xb4386184186186976189,0x16518915418ab8218a96,0x218a9421891511815851,0x515821517821017860f1,0x7820f5b7412158614158,0x51417860e43800b5b740,0x63f820a67720a3f86086,0x776083f8208677208677,0x6036b76079165076b720,0x79152079d64049d42041,0x381ac5564a74f87004d7,0x6000b83662180672b84b,0x80b833f13812b1181900,0xf82531d81571381b42f8,0x4af7564311381267d621,0xb0784100b830f8d51070,0x38700ffbfdfeffafdfef,0xfbbebf7fdef73cfeffbe,0xeebafebb9fdff7edf77b,0xddf6fdaf5fd3f3fbfefe,0xbf6fbbdeefbbaedb7ede,0xb76bf9fe7d9ee779be4f,0x5d7645cf645cb645c764,0x5c3645cb6159361d5360,0xd4f60d47605d7605d360,0x5cb605c7605936055360,0x54f605476050f6050760,0x4c760d93515db5159351,0x55351d93505db505d350,0x597505935055350d9741,0x5db415cb415974154741,0xd9740d8b405db405cf40,0x5cb40597405934058b40,0x5434050b405da645ce64,0x5ca64d96545da545ce54,0x5ca545965459254dd564,0xdcd64dc964dc564dc164,0x9d564995645d5645cd64,0x5c9645c5645c16459564,0x1d564dc961dc16159561,0x59161dd560dd160dcd60,0xdc960dc560d9160d8960,0xd5160d4d60d45609d560,0x995605d5605d1605cd60,0x5c9605c5605956059160,0x58d60589605856055160,0x54d605456050d6050560,0x4c5601d560dd954dc554,0xdc154d91549d95499154,0x5d9545c15459154dd951,0xdcd51dc951d9551d9151,0xd51515d9515955159151,0x5855155151dd950dd150,0xdcd50dc950dc550d9550,0xd9150d8d50d8950d8550,0xd5150d45509d95099550,0x5d9505d1505cd505c950,0x5c550595505915058d50,0x58950585505815055150,0x5455050d505095050550,0x4c5501d950d95415d941,0x5d54159541d9540d8d40,0xd8940d4d40d494099540,0x5d9405d5405954059140,0x58d40589405814054d40,0x549405094019540d9131,0x5d13159131d9130d8930,0x5d5305d1305913058930,0x5413050930d9120d8520,0x5d9205d1205912058520,0x58120551205452054120,0x505204c520dd910dc910,0xd9510d9110d89105d910,0x5d5105c9105951059110,0x58910585105491054510,0x54110509105051050110,0x485105d4645c86455054]) else (if j<2 then (word80 [0xab36208b,0x16208b36205b16205b78,0x607b68607b58607b4860,0x7b78207b58207b76207b,0x56207b76204b56204178,0x2db1780db1780da1785d,0x91780d91782d81785d71,0x782d71782ad1785ab158,0x2a41580a453759f3d819,0xf41809f51759753759e3,0x1849e3384981580a33f8,0x19c1585a21580a243809,0xb1582a11585a01582a05,0x18202638501618501178,0x5011782a94976aa3184a,0xa4976a63384a65b87a53,0x382a55f65a85d65a8638,0x6a76286a76186a76086a,0x76185a76365a76165a71,0x786a75964a7158075178,0x46f5b846f17806f25857,0x23186703182708b856d8,0x8856d8a656d89656d338,0x26d15876d27856d15867,0x41582741586735165735,0x964731582738a8600898,0x6001785d61784d61780d,0x65375945b74931585961,0x584961580961784c5178,0xc51587c61787c41587c,0x45974c45176c38964c31,0x5806c1782668964625f6,0x56b5d656b5f646b5d646,0xb15866a15806a3f82636,0x772631785bb1782bb158,0x7bc1787b91587b95175b,0x91786ba1785ba6576b86,0x572b81782401784d1178,0x2d11785d01782d01b82c,0xd1587d45175d43d81d44,0x180d41587cc5175cc597,0x4cc7964cc1587d33f81c,0x91785cf1784cf1782ce1,0x587d23783ca158492158,0x2921986885375881b868,0x63b82865175763d81765,0x37587418087537581438,0x8115859115829119828,0xd7b74801b82808380805,0xb748043808016878b158,0x78b3d818b41808b16877,0xc79647c3d819043807f1,0x6878a15878a41808a5b7,0x4793f817915858f15848,0xf4b758c19848c1b847e8,0x3807e43807e15828e338,0x48243807d16878915878,0x941808937837a1784c15,0x387bf2784bf5165c0158,0x7c22585c21787be1587b,0xe5974be2586bd5176bd8,0x964bd1584611582614b7,0x65525855517855353855,0x31784531782536382536,0x82536b80534b7653278,0x5533b825316874249764,0x23184423583423982423,0xd814215875c4b765c418,0x5c26875425865425845,0x473764e70764e27844e2,0x7824e93804e4b764e438,0x4e15866052656051656,0x15826069806016875b1,0x5875b25855b41805b178,0x74d16874d14874d43804,0xd2586575376575176572,0x78648258648537648517,0x6488b744889644827824,0x85b744815865f16875a1,0x5875a25855a71655a3d8,0x15a41805a17874c14874,0xc27854c71654c8954463,0xf814615865e51655e158,0x45e16875915875949765,0x92585597165596372594,0x1805917874b16874b148,0x74b49764b71654b16874,0x51487458954454380451,0x5865d15825d37834f168,0x75815875825855835835,0x841805817874a14874a2,0x58656278647278247378,0x34783764980764993854,0x99085499265499165496,0xb7449836449816449935,0x4499154494382496b724,0x98362498162499351499,0x151491785b51782b5158,0x7b73184b71787b21587b,0x25175b25b87b15975b13,0x382b11786b31785b3596,0x4b31587b63184b61787b,0x1587b06172b04380b03]) else (word80 [0x55f6e765,0x16d765195655145875a4,0x7874c6f764c6d764c956,0x54c6f76466d764695654,0x66e865e6d865e6d845e6,0xf645e6d645e6d815e458,0x65e6e765e6d765e95655,0xe45845e6d745e95545e6,0xe76506d76509565506d7,0x45095545045875985765,0x94584596f7459955459a,0xf725947874b6e874b458,0x74b6d874b6f764b86764,0xb6d764b85764b95854b9,0x5654b47844b6f744b955,0x44bad724bb5804b6e874,0x56d87456f76456d7645a,0x17445a16445b780456f6,0x25d6d625d45865d6e765,0xd6d765d95655d47864f6,0xf764f6e764f6d764f6c7,0x64f95654f47824f6f724,0xf6d724f4587584582586,0xf725847874a6f764a6d7,0x64a95654a47824a6f724,0xa9676569576569776479,0x67647957647947647977,0x24795724797624795624,0x76f76476d76479765479,0x565476f76446d7644956,0x5446f72446f76436d764,0x3956543b48749b77649b,0x78549b58549b56549b78,0x449b58449b77449b5744,0x9b56449b55449b78349b,0x58349b77349b57349b56,0x349b54349b78249b5824,0x9b77249b57249b56249b,0x54249b78149b58149b77,0x149b57149b56149b5514,0x9b54149b531496d85b56,0xd82b54582b76d87b26d7,0x6b24782b2a185b1a165b,0x1a182b16e86b36d86b36,0xd85b36f65b36d65b3458,0x5b66d75b68565b66d87b,0x6d76b04785b06d75b08,0x765b08565b0a184b0a16,0x4b0b780b0a286aea186a,0xea185aea365aea165aeb,0x786afb686afb586afb48,0x6afb782afb582afb762a,0xfb562af6e85376d85376,0xd83376d82376f86366e8,0x6366d86366c86366f823,0x66d82366d753d45823d4,0x586386d76386d87356d7,0x6356d7535478235a2853,0x4a18534a26534a16534a,0x18334a1823445823c6d7,0x633a1643347823345863,0xa6d763aa1643a6d7630a,0x1643045853b6d753b856,0x53b6d87326d763247853,0x26d7532876532856532a,0x18432a164324586396d7,0x639956539a164396d762,0xfa1642fa2862ea1862ea,0x1852ea3652ea1652ea18,0x32ea3632ea1632ea1532,0xeb68531b58531b66531b,0x56531b58331b56331b75,0x331b55331b58231b5623,0x1b75231b552314582294,0x78225458428478424478,0x622458622a16422ad622,0x2b68623b586236d841f6,0xd811f6e861e6d861e6d8,0x51e6d831e4585216d752,0x16d871d6d761d47851d6,0xd751dad821d6d871a478,0x61a45861a6d761aa1641,0xa4585206d75206d761c4,0x7851c6d751c6d76196d7,0x6176d75176d7616b5851,0xbb5651bb5841bb5641bb,0x5541bb5831bb5631bb55,0x31bb5431bb5811bb5611,0xbb5511bb5411bb5311bb,0x68618b58618b58418b76,0x418b56418b58118b7611,0x8b56118b541184582136,0xe870d6f760d47820d458,0x21247820c6f65146d651,0x44585116f75116d75118,0x565114584116f74116d7,0x4116e870b6d870b6f760,0xb6d760b47850b6f750b6,0xd750b87650b85650b478,0x40b6f740b6d740bb1810,0xbb7800b4586096f76099,0x56509ad6209478606458,0x606a16406ad6206b1620]))) else (if j<4 then (word80 [0x7806f458,0x272a3856da1856da3826,0xda1826da3806da1806d6,0xd766d95656d47826d478,0x66e6e766e6d766e95656,0xea3846ea1646e47826e6,0xd726e8582d56d84d6478,0x2944780948582936d859,0x66d65966d80966d65956,0xd84c56d80c56d87c46d7,0x6c445806947806545826,0x84782646d85bb6d82bb4,0x582bc6d87b96d76b9478,0x2b96e86ba6d86ba6d85b,0xa6f65ba6d65ba4582414,0x5804147823e47803e458,0x22c47822a6d84d16d81d,0x16e85d06d85d06d83d06,0xd82d08685cd8585cd858,0x3cd8582cd6d87cc6d75c,0xc4783cc4782cc4584d36,0xd74d38564d36d74cb856,0x4cb4585c96d75c9a154c,0x9a753c96d84cf6d54cf6,0xd83cf6d53cf6d43cf6d8,0x1cf6d75ca4782ca6d72c,0xa6d75c86d72c86d75c76,0xd72c76d83926d8192458,0x39245868845848847868,0x68786864784864783864,0x78286af8286ac8286b78,0x864587874584876f758,0x14784814783814782816,0xe85916d85916e65916d6,0x5916d83914585916e759,0x16d75914583916e75856,0xd758586758d85758d868,0x58085858086758085758,0x8583808582808665808,0x5658045878b45868b957,0x58b95658b47877c6e877,0xc45877c6d877c47867c4,0x5867c6f757c96757c957,0x57c96657c95657ca1647,0xc47837c47827cb5807c4,0x585906d75904785846f7,0x5846d75844784846f748,0x46d74848764848564844,0x78284b7808447857f6f7,0x57f85657f47847f6f747,0xf85647f47827f45878a4,0x5868a45848a6f748a876,0x48a85648a45877b45867,0xb6f747b87647b85647ba,0x5637b458779458679458,0x5796f7579a37479a1547,0x9a57379a56379a753796,0xd858f6d658f6d548f6d8,0x38f6d638f6d538f6d438,0xf6d818f45858f6d758f4,0x5838f6d738f6d75836d7,0x4838564836d738385758,0xc85548c85738c85538c8,0x5438c85847e85747e855,0x47e85817e85647e45858,0xe6d758e4785826f75826,0xd75824782826f72826d7,0x28287628285628247857,0xd6f757d47827d6f727d8,0x5627d458789458689478,0x77a47867a6f757a47827,0xa6f727a87627a85627a6,0xf75786f7278876278856,0x2786f75776f727787627,0x78562776d84c19584bf6,0xd87be6d76be9585be956,0x5be6d84616d816145846,0x14585554584554582556,0xf85536f84536d84536f8,0x3536d83536f82536d825,0x36f81536d81536f76534,0x78553978553478453478,0x253af8253ac8253b7805,0x345844245875c45845c9,0x5765497764e97844e958,0x44e97834e95834e97824,0xe95824e97814e95814e6,0xf764e47844e6e86606d8,0x6606f65606d656045866,0x6e76606d76609565604,0x786526f76526e76526d7,0x6526c765296655295655,0x247825245875b45855b4,0x5825b47874d6e874d458,0x74d6d874d6f764d6d764,0xd47854d96854d95854d9,0x6654d95654da1744d478,0x24db7804d96765795765,0x79686489586489776489,0x67648957648947648958,0x2484586486f76486d764,0x8976548956548a164484,0x5865f6e765f6d765f956]) else (if j<5 then (word80 [0x699367f3,0x65b363e361835f535d23,0x5b53595356d3544351b3,0x4ff34e034c434ab34943,0x466343b341433f733da3,0x3be33a433883369334c3,0x326331032e932d232a93,0x280325a3234321731e63,0x1c3319a317a3159313a3,0x11a30fa30db30ba30893,0x63304830222fff2fd52,0xfb22f942f832f682f442,0xf212ef82ec42ea52e7d2,0xe592e302e072dde2dbc2,0xd962d722d4a2d292d042,0xce12ccc2cb22c832c6d2,0xc4e2c3d2c142bf82be02,0xbbb2b922b762b5f2b462,0xb2d2b142afa2adf2ac22,0xa9f2a722a562a322a102,0x9f029d529af2985296f2,0x946291b28ff28ee28d82,0x8c628a92889286528402,0x82c281527fc27dd27b52,0x79227792757272c270b2,0x6e526c326a12675264c2,0x62925f925d725b225982,0x5722554253e251324df2,0x4bb248b24772464243f2,0x41123ec23cd23a923882,0x3642344231822f322c52,0x2a82280225b224122262,0x20721de21b6219221652,0x140211520f620d520ae2,0x8e2068204220181ff51,0xfd81faf1f891f681f491,0xf241f081ee51ec61ea71,0xe8f1e6f1e491e1d1df21,0xdd01dad1d8c1d631d4a1,0xd251d041ce31cc11c941,0xc781c5a1c2b1c051be01,0xbb81b8d1b6f1b471b251,0xb0a1ae01ab71a881a571,0xa341a1119ec19c719a61,0x97f195a193b1927190c1,0x8ec18cb18b2189018701,0x84d182c181017f217c51,0x7af17871769174a17151,0x6e116c916aa168b165b1,0x62515fb15d715b6159a1,0x57215451520150314de1,0x4d014a61481145c14431,0x426141813fb13ca13a11,0x38213631339130a12de1,0x2c712b51293126a12451,0x21511ec11b7119711721,0x149111910fa10dd10c21,0xa7107a1062104710261,0xe0ff10fc20f910f660,0xf440f230f060ed40ea90,0xe7a0e4f0e210e020df50,0xde10dc20da00d7f0d5f0,0xd290d080cf30cd20cb00,0xc7c0c670c4b0c210bf50,0xbc10b900b7b0b640b4f0,0xb230b070aee0ad30aa80,0xa7f0a560a3a0a0d09eb0,0x9d709ba0999098209520,0x928090508da08c0089e0,0x87d08600840081b080d0,0x7f107d407b30792077f0,0x7570744072706fa06c90,0x696067f0660063306130,0x5ee05c0059a057505510,0x534050f04e604c4049c0,0x47a04530430041403f20,0x3d803bc03950371034d0,0x328030402ee02c802af0,0x28402640240021601f90,0x1e301c501a8018a01630,0x142012300fd00d000b70,0x8f00660048002000006,0xd84db6d80db6d84d96d8,0x3d96d81d96e85d76d85d,0x76d83d76d82ad6d86ab6,0xd85ab6d82a44582a4458,0x9fa3849d47829d47809,0xd45809e4784984582a34,0x7829c47809c6d85a26d6,0x5a26d83a24585a26d75a,0x26d73a287869b47859b6,0xf759b6d759ba3849b6f7,0x39b6d739b47809bb7809,0xbb4809b4582a16d72a16,0xd729a6e85a06d85a06e6,0x5a06d65a06d83a06d82a,0x4585a06e75a06d75a06,0xd73a04582a06d72a06e7,0x5996d75996d73996d729,0x96d85a96d82a96d76a6a,0x185a5a165a5a182a56e8,0x6a76d86a74580716f846,0xf6f806f6d806fa3846f4]) else (word80 [0x9a969906,0x981696e695f694769376,0x920690f68f868e568cd6,0x8bf68b2689b688a68766,0x861683b6826680a67f76,0x7dc67c967b1679b678a6,0x77667606747672f671c6,0x70266f166db66c566b46,0x6a06685666f665766436,0x62b660665f265d765c96,0x5b865a26591657f656f6,0x554653f652b651d65086,0x4ef64d064bd64aa64966,0x47f646a6457644f643b6,0x428640e640163e763de6,0x3cb63bd63af639a63866,0x36c635363416328631b6,0x30562f062e362d062ae6,0x2936278626b624c623a6,0x228621b61fb61ed61d46,0x1b4619e6183616861526,0x1426127610860e860cd6,0xae608b6076605f604e6,0x34601c60005feb5fd65,0xfba5fa65f935f7c5f655,0xf535f405f2d5f195f065,0xef35edd5ec35ea85e8a5,0xe745e6c5e565e425e305,0xe235e135e005de45dcc5,0xdb05d9d5d825d645d485,0xd315d1d5d025ced5cd85,0xcc25cad5c935c7f5c695,0xc4b5c435c2f5c195bf55,0xbd55bbb5b9f5b7a5b5d5,0xb435b1e5b035af05add5,0xabf5aac5a995a805a6c5,0xa4c5a335a285a1859f05,0x9d159ae5986595e593b5,0x91658f158d158b458965,0x872585d5843582558105,0x7f557d657b3579757865,0x772575e574a573957285,0x717570356e656c956a65,0x6835671565b563d561d5,0x60855f455df55cc55b05,0x593557a5551553a55175,0x50354e054c354a054925,0x47a546154535439541b5,0x40f540353ea53dc53c65,0x3b4539f538a5371535d5,0x3495331531b530252ec5,0x2d252b3528e5279525e5,0x25052375225521351ff5,0x1ed51d751b8518451725,0x15f51415123510d50f85,0xd350b6509f509150805,0x5e504f5036501c50054,0xff14fe04fcb4fba4fa04,0xf844f6b4f564f424f314,0xf0a4eee4ed44ec24ea94,0xe904e7c4e674e514e3c4,0xe2e4e1a4df84de44dcb4,0xdb84da14d884d6e4d4f4,0xd2f4d194d054cf04cde4,0xcc84cb04c9a4c854c694,0xc554c3c4c244bfe4bde4,0xbc94bad4b9c4b8b4b724,0xb584b3e4b294b0b4af64,0xae24acc4aae4a904a7a4,0xa644a4e4a384a224a0c4,0x9f749e349c749a6498a4,0x969495a4942492948fe4,0x8e648cf48bb48a7488f4,0x87d485c483d4820480c4,0x7f747dd47c547a647934,0x77a4766474b473647214,0x70646e646cc46bb46a04,0x6824662464d4638461f4,0x5fc45e245c945b4459b4,0x5864566454c453245144,0x4f144cf44b9449d448a4,0x47c4465444c443344204,0x40543ea43d743c143954,0x38d437a435b434043204,0x2ff42ea42d042bd42a74,0x27c426d425e4244422c4,0x21141f541dd41ca41af4,0x1a0418c4179416641494,0x12b411140ed40c940a94,0x8940694054403a40103,0xfec3fd23fae3f8a3f673,0xf433f103eee3ec73ea83,0xe863e603e443e273e093,0xdd83dac3d863d6c3d4d3,0xd223cff3ce53cbe3ca63,0xc7e3c5a3c2d3c113be03,0xbba3b953b753b473b1a3,0xaed3abc3a9a3a753a563,0xa2d3a0e39f539d739b33,0x98f3965393b391138e43,0x8bb38973873384738223,0x80237e037cc379b377b3,0x7553730371836e936b93])))) else (if j<9 then (if j<7 then (word80 [0x1c59196b,0xcfebd60267eedaa7819a,0x28f1f208f17d6f208f6d,0xddb838ffc0b232f7f820,0x591997f8790468756429,0xe86a7776fa13b9709703,0x3776d4136587c6083eed,0xea6d941c608387b0b83f,0x7f652410b09ff7accb51,0xcb7ccd09fe41b65a886,0x72366f76e0b547b27085,0x872941d3e0d8a4a8668e,0x71865e68e718668f9e53,0x93d99aea434757051525,0xe1b0989e5b64c974c191,0x1a15c70428741e999583,0xe983233aa77510bdcb86,0x88d67872941ef59aa35,0xa396bb974c19b25d3064,0x45910bed8568e718650d,0xc40a388c63380a3c9161,0x10b26092c61148461d66,0x60bc3d1e82a174543f0d,0x5030fa1c23a19a1097c3,0x98544c21c429080d19a1,0x590c251709443445090d,0x305200160e20807609c0,0xc398403c4600a11618c1,0x2014040ce0a800882444,0x30d4390820499a190606,0xb020f4900540b0a205c1,0x8888388341e024101861,0xa0440829e04146008404,0x2148703a06010360b,0xc311102a05c2d0b30102,0x40f4148283c02e0c1104,0xd0fa05810c03a60d00a0,0xc4108c058008f0640603,0x50da08422182e0800183,0x5820cc030c81b09c0801,0xf0086d286b58698867c8,0x66386568644862b860e8,0x5f185df85d085b985a48,0x5948585856b855a85408,0x528851484f984e884ce8,0x4bb84a68493846e84558,0x4428427840b83f583df8,0x3bb839f8389836c83518,0x33b831f830982ed82d18,0x2b082978288827882628,0x2458222820981e881c98,0x1b8819381808170815b8,0x1418132811e810180f38,0xe180d380c580b080978,0x8b807a806b805780498,0x3a802180087ff77fe77,0xfd27fb47fa07f8a7f7a7,0xf667f557f3f7f2e7f1b7,0xef87ee57ece7eb67e977,0xe837e6a7e557e417e2d7,0xe1a7e067dee7dd27db67,0xd9a7d7e7d6d7d507d387,0xd277d0d7cef7ce17cc77,0xcb57ca07c8c7c777c627,0xc4d7c387c1c7c007bec7,0xbcf7bb97bab7b8b7b727,0xb5c7b4e7b2d7b117b017,0xaed7ad97ac57aab7a957,0xa807a6b7a637a3b7a207,0x9fa79de79c879b279967,0x9817966794d793779177,0x8fc78e778d278b7789c7,0x88978767859783e78307,0x81577ff77ec77d577c47,0x7a777887770775577477,0x72e771576fa76d976cc7,0x6b776a57690767d76587,0x64b76397611760075eb7,0x5d975c475ab759875877,0x56a754a7531752075037,0x4f374e474c374b374aa7,0x49d7485746b746274557,0x4487438741a740173e37,0x3c473b273947379735e7,0x3417327731272f172d77,0x2b7729d727c726172427,0x228721271f871d271ba7,0x19671707156713b712c7,0x11270fc70e670c970a87,0x91707c706e706070427,0x216ffc6fd46fb96fa36,0xf7c6f626f3c6f206f0f6,0xef36ed96ec66ea96e926,0xe776e616e486e2c6e056,0xde46dce6dbc6daa6d906,0xd756d676d456d376d246,0xd026cf16cd76cbb6ca56,0xc8c6c766c596c346c146,0xbf86bd86bbe6b9d6b866,0xb726b536b3b6b246b006,0xaed6ade6acf6ac56aaf6,0xa8b6a6c6a596a3f6a2a6,0xa156a0769f269d769bc6]) else (if j<8 then (word80 [0x810fbd74,0x123cfabf6091c9f9a83,0xe87e9901997ed82464b9,0xd0c7fbf2c01244565d23,0x800034d32d2e042a708b,0x51983b4234c112762ee7,0x254b337715974fc0cf3f,0x3cd82474ffb1cc8587b5,0x2acbd2ce566580a0f9a8,0x5e7f056845e7f0400049,0xfcab2b32af87a18ebc9,0x1c719641e3eab30470e,0x3c8203313f35064e8ba0,0xe50520c277a03c3019ea,0xcda0c9a943feeb01957c,0x3d0e7ec917ff82422861,0x3fad00d0c11c5a99757b,0xb048f6e1e131a14fe434,0x89cffe4452292e15d8b9,0x9a3e30c00d675fe10008,0xf77ed226dfaf70812474,0x7c629acc1c65a6652ea5,0xecc9df38266660ef4064,0x2e05ed4cadfe0199110e,0x49420663b185ff5022f6,0x841fc0cdac1e5600d0d1,0xf45f8401994ff2524653,0xf84348dd2cf106519a1f,0xfd023879358f1c5c8310,0xa92ff1a45497f8d22f74,0x9be0cb1fd24eb4067979,0x6883a6d0ca1175e7fa00,0x24a61d5a80cc7feba42,0x28dfea6802485f7c2830,0x49239c0ea2f7b3956033,0xacfd7408d4dd820eac19,0x5611675d2cfd0024776f,0x8640026815d2cf740125,0xac79ae04613fa5c08d3f,0x4480248bf3bda0140dfb,0xb811813c8ba6b30c763e,0x411c7af7a2293b414e87,0x4451ea8744677d42b420,0x79358e3fb44d65887864,0x651f598e88c1c766665a,0x7dc6838eba05939e026a,0x36d0d99ab1961f9042b3,0xcc5ce8a87467918bf9f,0x924a822d05f97e328aaa,0xd0197a4abf01b9197c0b,0x723436717110343c69ff,0xe30b1d0d1564d1218b3a,0x7f5a0b32ac9e0791a6cd,0x7917bf06c39999dfc889,0x2d0d7ffd08028bf4201,0x3dfff4200a0e03de3ffb,0x11efffa10051a47e8c,0x85c630c1f7c18191e02,0x2fda013a7fe3989001a2,0x35f8a0c0cefdee6022bf,0x68326f1ffd8008fbff1,0xbc2001245a34d02821a2,0xef51660c5de05c032c6b,0xf141819e35f92c0cc1fe,0x2936d76ce09fd4306663,0x7dc20b51c74468dd98c2,0x37f50c1996adfd43b0cd,0xcf5ad5c80d0ebfb6091a,0x3f132c97b5489ede4e41,0xe7fb4118099f21b58eb8,0x6913afbb6091f18f20eb,0xd022c9dfda988011a39f,0xdd5201010ed4df5e4419,0xe7f5d8246deb6c123807,0x20d937fffd2640449a6f,0xad9030cec9f35e2481a1,0xa9bebc8833efed7c48bc,0x903f0bb9172c377647ab,0xf869145fb49a842b7408,0xb2ed5f8d22d7f2ebe455,0x8cd0beed82472bd92578,0x1045967f5d82465fffe8,0xe40449513c147982b20,0x63fc811acc9f86695ccc,0xf10fe8bd16cad10a01ee,0x55328755da196732495d,0xa1f788c3646b3efc45a2,0x2c40d12cc2792c7d17e1,0x6607831489c28ffa55,0xe091e83e0d931f766300,0x50dbfeec123425c157c3,0x489d1ff1a508dc2d8d7f,0xffbc2001217eb7098249,0xafdc29aca38d7a260925,0x4c7445878315a111ff0a,0xd088fc56839fcc7445d7,0x8665b42c3023cb9e881c,0xc0b6487cc0c420bec272,0x129e414469d412b3f476,0x21e8bea28645d8921d9c,0x29fb6839bcd0d6feda02,0xc61a2bbb318155fe459c,0x40ed577249a9feb4267e]) else (word80 [0xb65249e6,0xfd0db07e4782f2bcc1c,0xde289bf60f9939f08837,0x74160c16d4b8488f1a6e,0xcb5f481bb28b270448b2,0x707dc989b614c64c7afa,0x283e7d141f72621d0f48,0x905e8993b93155bac6ec,0xdcb26850c01dc9895d85,0xf425bf4283f7e80084d6,0x6fc0422ae90c58be83ee,0x4c556eb1bb37ceb42866,0x702ce045fa283697d63b,0x7e8506cfc4107aa7d07d,0xc98b0ba932338197a82e,0xe4c5dc98a2cc334715c7,0xab26c794891f9a384cd1,0xf9a384ccdb6384ca9e23,0x84ca8a3dab094d382a45,0xc20f1b0d142167451ef1,0x85a412e0e9d2b0c2169,0xd2b0c216283870b2ca8e,0x70842bbfe4401802879f,0xd76091a3e6fa09334f2f,0x42469fd76091932f3164,0x66bf0d226be0a9145f08,0x24515fe3104242689fac,0x5e10249debfb6091fdd5,0xc83423c2d0950d0ff419,0x9fbfd62432fbab90745f,0xbe42199abe98e34f0d04,0x998dd45d5a177fae0010,0x49272da44f2eed84e9be,0x878f4b45919afff08445,0x7ff132129d30e583433,0xa74c3b56219d3a61dab1,0xcf5f8f10424268bff08,0x489c03f8d34ca9f1a699,0x3f8c254cc9f187992a,0xb96c7df9b5321683f32b,0x29683f32b2c0274b54ac,0xf005dad52b3c0176b54a,0xce237ccf2eb482e83875,0x2b30aa97a9428aa97a94,0x2efd71c4c12447a45b69,0x9bb95d91967f5d8246a6,0x8828ffd30010134173b1,0x732a6dedc10cd18c3518,0x6608f963076fb02c910e,0x1f5f514c30cf81186aca,0xef41c1dff901114953da,0x9913cb3164664f95792c,0xb7ff86889daff3147ef0,0x31109df2fc584cdde9bb,0x78866ef4ddbc4334f5fa,0x222ebc74456f86464c2a,0xdc1a1d6a29f2a27e3d12,0x21f6990624348e738744,0x85fe1a22aff0d1167a1d,0x1147c74441fc344587d3,0x2d081c7c86417caa0221,0x74d6a2ae922ec8cdb75a,0x8b9b2bd4070dcd95ea03,0x866d7dd29199b5f74a46,0x6e7c3f41a7f0f84f2319,0xfba4ab4b2a7dd2554d98,0x7ae0911b78f0488c3793,0x911857ebd1147c589119,0x3e041b24f03cd118dd3c,0xc081190e9b7e941b2c39,0x818317f98312147ff600,0x230ffd0180090bfc2001,0x1efd040286f01de45227,0x887e96a658cfaa4acb19,0xeb4ae6675ffd7e101024,0x9c5b89d08cdfd3500cc1,0xff5410ca52f11a0067f5,0x8ce1e9436ea35e801227,0xf5d824695f63e411ebf8,0x619195102bf851997ddb,0x48f3fcbd82472ffd180,0xcaab84357f620c1f2d2d,0x2e043acec8884785a12b,0x2c49b7f419166ce5ce64,0x8eb163bffc121140ffa1,0xe6091e6b00d1574da24b,0x5420ebdb2c72b9b44765,0xf20ef06913bfe4c42233,0xea92b2c67ac82b99a2fc,0x34899bfd3181949f8316,0x8487ea44843ba7c4abf1,0x5cc92397bfe0b2ccc87f,0x517ac670f4a1a7fd5a00,0x249cb6913f458827b24,0xe0d8839d26c90e0cc309,0x97b1f208fa355dd68557,0x68218e8887d292597132,0xd088815fc28cc3eb0609,0x1c197907d0e30f32d7ec,0x1e72e669f04c123f6b4c,0x10acd7ff42013dff9144,0x501fc2398c0cfd0f3824,0x867686dec0cb8cbbbd01]))) else (if j<10 then (word80 [0xb5750ddc,0x40c1da453e4280e18e86,0x466e91a9d08bc8a831d7,0x21e18a1ac06ec982c688,0x41af378345bca474cc8c,0x7850cbc73183ba08bb31,0x6783177962b72020d6,0x835fd331806ca121c063,0x818dd50c7190e5c46832,0x714c1afc847b2d257014,0x610c7a7e435a090f235e,0x6e80d1aa89c320a4ea83,0x301d09c9284ae18ab862,0x301f7e5b3324b0398616,0x3cfc1ab64c792099ea24,0x1895978347e20a2e841d,0x9241a6bf346406cc2084,0xa7c49074fb89211ce291,0xa526b9a09bcb318f9081,0xf06830f2663ea1726427,0x6926b9a086bf81127790,0xf6321e5b66351bc891eb,0x115362b6304ce3056c60,0xa0ea1c1da4bce23418fc,0xde44afd261939a382003,0x7fa099860a3d62eb0ef2,0x157d23cc2d6644c70639,0x9438452ecc4b5f7912bf,0x4986413f5e446eaec79e,0xc4af6820d6bc8726ea2,0x8f94935670449d7b1ae5,0x21c784c73723b2300438,0x416f7c865f20b26cadfd,0xf64c8b23d222ec6522a7,0x907b099a3f36ac92e184,0x1e73e3ec99735d93265b,0x622ecc59accb32e5b62a,0xe4c5eea283d4d82ae73d,0x6654c7931d212d23cedc,0x102b66e7132b09ce26c4,0x21767eb0e8d1f3c74088,0x59b3d72d5b2f37068859,0xb9b83442cc1f8764c9de,0xbb2646f0a6d91b6f0a6d,0x94dc50523714191e64d4,0x66e282e7d4507cfba8a1,0x3ce4193522f18f227558,0xb0ee08a749234d8a22c5,0x27425f21618a1a65fa99,0x225870c81e14cc5959b6,0xf7b2f6cc44c7c13b0b5,0xb09e9aaf3083c3430618,0x21c721e3182ed3b564a8,0x97ab2765c58e2c449a5e,0x91a7f90c03f55ab2f09c,0x146516b76583884d1a1e,0x21bca43c0a4f1512b8e0,0xc67816305506d6fe0321,0x90ea0a0bd513b618bd50,0xd38628a7a1ef050dbf80,0xc7262879e0c5ab10899e,0xd31d71c18ea9863d5582,0xe385783257d716019bb,0xb4c70e1fa0fb61417aa2,0x770c491b117c312fc84c,0x37c1647f41640e3e01d1,0x386685f90b18c132dce1,0x8cb738426f3687aa343,0xe793d0242972d05903f2,0x9226c2a3425e0e60d18e,0x9156d858e3c0b63d8f08,0x6b9087d96207e417658a,0x3c0b6307d8083de4c221,0xcd09365d0ebcc48f149a,0x2163cd4192982083cd1,0x8ab02ec76f60835c8439,0xb3a18d5e86ce482a6057,0x210c25e89d65cf0624f0,0xcb1d7962d8f0864f5e83,0xd55820e385783247100c,0xb2cdce86b908722743ac,0x1886b7430e19631add0c,0x5c1051e6a0c9be0871c2,0x3630d8b6367bc9a02177,0xc55ed171ab05558d5462,0xb420b91f336a0d3fae63,0xb59ca0fc0f0568642c25,0x91e081860b7cb43b1384,0x212c4e108497920a5e48,0x297920a5e48297920a5e,0x482b59c173d4112cf7c1,0x92c67c210bf165909fd7,0x509268659720cb68ec7,0x6f3c9e81218bf018d635,0xa1cb0c1530c137c031e7,0x4c5ef292a84f55265092,0x7180a386082cc431a7ec,0xc75a60c73c933d16b93,0x1574c18fd8a085dd1419,0xb8a08dc505cfa8a0f7ec,0x3f516d82e8393a113dca,0x83ea7b2d91bb60fd9268,0x345e4782f2bcc1b74ef4]) else (if j<11 then (word80 [0xd4b4c89c,0x311b220f74c6ce8824f0,0x32e44dfa431ec5099aea,0x831f244477082e680f07,0x9a62ed3e98c3a310e950,0xe1f413b77cc12153cb4c,0x618d8a1a61c1a3059c18,0xd6a87171d157df98a32d,0x7aeeb27dbd445c21964a,0xf294c8876d161ca151a7,0x54c78701547ce9d507ce,0x9c46849b8e221b224f03,0x4ea98e5f88d075de9851,0x95678a884e0c8a84d7f1,0x2d09d962afbd30a32d79,0x624f039e2a1d7f5cc64c,0x8a34d89bd974c9db0974,0xc41b09e04aea82c6a841,0x990cd5081c0c69b11e04,0x6c8a926b07d5fa6393a1,0x2781eb260bb4f01641ae,0x434b928b2d0b0c50e30c,0x54f2920748f194115faa,0x10a4f6b04270a883dc98,0xe408b842628c16107d8e,0x42f05c27055fcc49f98a,0xbf989bdf98ddfe8a0ddf,0xe8a0f5978a0f5978a0eb,0x4c4df94a64863583ad31,0x6305506d0a7f3276c2de,0x5d31ede8514f43dbd433,0x71411b8a08dc5046e282,0x378628337862833eb234,0xd0b9322754c75912f9b8,0xe22c5f15113aa63ac8b1,0xc526d091a474c956476d,0xd05ba086be087ec5041c,0x1ea860e5826724100239,0x3fa2042d3e2483823f99,0x82141eef60e29a638b61,0x8e3c2d1919c9056f6920,0xd38e4c75d931c3820042,0xbba283371411b8a0b9f,0x5141f3ea2830e8c51c98,0xa30e40c8afb020c36157,0xc0d06558b18f6431fa08,0x67604932a051cfdb7845,0x8eb1632f180c81b097d7,0x98ebcbcc68b3820faa5f,0x80cb1615e1a1862c43d1,0x430e8c43d7e3a0468b0d,0xa64659630e40cdd962d5,0x1a1862c438d43de4c225,0xf423ccb147c61992dc9a,0x2100d7089996248f15b,0x23b019c224fc320328ea,0x10056825ec0c60e89418,0x5c04b41d8426f2b4193,0x5d8106de56832534dc88,0x4be08d3fe606407e1106,0x2fb020cbe7c0c9afb041,0xc3820ab87440cb6fa0c1,0x9b67724207e68c78ea82,0x5842780306dfbf8193de,0x448303068b3f2063e23e,0x2856173e2d8fbc7e5919,0x5de1ea15855592e0e7fd,0x221c2257b020e2c7431,0x97d0fb8356c86c356084,0x138144ce482a60698128,0xfc8191d278650911d72f,0x654727f44085a7c4906,0x87f51711c9cc085f724a,0xe9e9c4408507bbd83e8,0xb125fec2256dd0c81d18,0x9de6c90757128aded241,0xd724c773a4254bfd8446,0xf1b6240ccefd364844be,0x10cb9620f5899f048391,0xa3a8a1b0e1d0555495b0,0x86b626f86165954e85aa,0xa0c1abf50418c4e87b9d,0x84427c208b6a60c850fc,0x3e265eeb0c265e87e064,0xe5bdc284caf8993dd906,0x509d8058f5360adc8d14,0x2717bb189c2a2ac3b62b,0x654fcc470889c08055d9,0x31b53f48032c7c7b2640,0x2ec48c12c19b8a08dc50,0x54c0a3a60b9f5141f3ea,0x28384ec5ea2983264530,0x50c99137bf31a781f72a,0x631f2145fa43d8c86de8,0xc61b08d047fb21e1d0a,0xb3c8c1db046920c9842b,0x9d81536e8592393149ec,0xa4583a86de80c687f21e,0x1d0a870931b3824d83b1,0xc79b31ec643dcfd91362,0x8473f028c70863d42981,0x4357a4106972d12e2422,0x321c1779f31c534e4c19]) else (word80 [0x13c0f3ec1cc8dfc,0x5a648f0b4644e3931c58,0x697238c3a31d78d2992b])))))
def g251H8 (j : Nat) : Nat := if 15 ≤ j then 0 else (if j<7 then (if j<3 then (if j<1 then (word80 [0x41e0000000,0,0xe5c000000000000,0x30ea,0,0x302e438000000000000,0,0,0xcda8000c0,0x50000852400000000000,0,0x51400,0,2,0xfa81c40000000000000,0x4680000000f1e8000c4,0xb40000000000c4bc0008,0x861025d0340000000000,0,0x710c27b00000,0xb2300000000000,0,0x1e4000000000012b100,0x12540000,0,0,0,0x21be0000,0x45b00000000000000,0x2396000000093,0xd048941b929800000000,0xc6e40000000000,0,0,0x3bf900000000001,0xc3300012c34b88000000,0x9520000000000000000,0x2190,0x3c1344440000000000,0xe7b08190000000000000,0,0,0x300000000000000,0x1204000000000,0,0xe5c000,0,0x30,0x380000000000107d0000,0,0xcc9364000533c00000,0x2194000000000000000,0x3b35,0x82800000000964a53400,0xc9580,0xf3800000000000000,0xc0680000000000602,0xc0000001837000247800,0,0x380f00000000000000,0x3f9000000,0x46ec0,0xc4c000000035000000,0xb0280000000000000,0x21800070,0x7c000000000000000000,0x347a00033cb,0x12b,0xc00000000000000c0480,0xe700,0,0x803c00000,0xc,0x32400000000000000000,0,0x134400000030,0xd4000000000000000000,0xb020000000,0x20fc000094b00,0,0x8b1c000,0x24430000000000130,0xd5000001102011020010,0x20001040010000211022,0x100123010000001000,0x20100000001100002,0x100000003020010001,0x20110000020000100012,0x3000002001002000020,0x30131110101000111,0x200120000101210000,0x1000003100001000,0x40020043002000110020,0x10000014302300011000,0x101200000300000050,0x1000000011031,0x1010000204100001001,0x10200000300000208300,0x4000000,0x4010022216021011001,0x30000000010110000000,0x11132003100000000010]) else (if j<2 then (word80 [0x5cef34a5,0,0,0,0,0x4463918000007a00,0x20d60,0xc308000,0,0x1024000000000000000,0,0x30d16cf80000a1,0xe37b00000008fc000000,0x41980000000000e,0x35800000000000000000,0,0xcabc00000019,0x85000000000000000000,0,0,0x4ce800000000000,0xd700000000000000,0xc7dc00000000000bdc00,0x768000000000000000,0,0,0,0xe67c0004,0xaa1ac100000000000000,0x116f00024f08e940a,0x20000000000000000000,0x30a400000000000,0x1bd15c8a8,0x40000003268000000000,0,0x13140000000,0x90ac00,0x34,0xfe000000050b91ef0000,0x2556389000,0x3100000000bb000000,0x214600000000,0x3415e3f4000,0x89938be000000000024c,0x90000000000000000000,0,0,0,0x311000000000000000,0x9340000,0x42f800,0,0x8d8000000000000000,0,0x81d8000000000000,0x3f70,0x20510000000,0x337d000118,0x900000b7000000000000,0xb0900000000000,0,0x52c424700,0,0,0xc3d0000000000,0x4ce617300032,0xd7000000000000000000,0x24cb4a9c000000,0,0x343e000000000000001,0x2318c00000008be0000,0,0xc27c00000000,0x105600000000000,0,0,0xd,0x28838f08bc0000000000,0x4cc00,0x4a4c000a1df3,0xef000000060280000000,0,0xdb800000,0xa3302258,0x684000000000050cd1de,0x2c2,0xc00022d3000000000000,0x14774908,0xc7b8000000,0x27d000140f52a00decf,0x9c000057800000024c24,0x1d000000000000000000,0,0x39622facb,0xbb20e000000000008f1c,0x97000,0,0x810,0x31220000000,0x4e400000011ed000000,0x149f00000,0x45800000000001,0x24a0d7107013a8000000]) else (word80 [0x3177ca8800006cd3949,0x1a400000000000000000,0,0,0,0x830,0,0x391900000000,0x4598000,0x225,0x70c3e354cba400081740,0x14b20000,0x24360000000000,0xb3800000,0x233e000329200000000,0x29720003152,0x4cb80000001021000000,0x8a6c8d000034,0xaf000000000011a30000,0,0x4d,0xa4000cf1000000000000,0x1df,0xddc0000000000000000,0x22ee000000000000,0,0x207f000,0,0xe2a00000,0x1295a8180000000000,0x91340000000000000000,0x227a00031,0xdd000000000000000000,0,0x3260c48c000000000000,0,0x22780003364481d2a5,0,0,0,0,0xd01800000,0x217c000000000000000,0x248f0000000,0x215436,0x500000008f904e100000,0,0x11990000000000,0x1045000000000,1,0x1ac00000000000000000,0x31010000000000000,0,0x35600000000000,0xa46c000000000011b,0x40000000000000021200,0xb2000000000000,0,0x348ae70550,0x50000000000000000003,0x8a53d800000000008784,0,0xc2b81e61620000000a2,0x711c496c00051380000,0x4c0c000,0x394e000000,0x24,0x65000000000000000000,0,0x13da8d,0x64000c1c8000000028f0,0x8d4c0000000000,0x5048000000000,0,0,0x25940000000000000,0,0x63f80004,0xde400000000000000000,0x9114000000000,0,0,0,0x2441000000000,0x10d000000000,0x4aba018,0,2,0xf2801000000024820000,0,0,0xd80000000000000197ac,0x5c29f227fdb020000000,0x339e0000000d14800,0xd038000000302900000,0,0x63f,0xc00043cc000000000000,0xcc8c00000000004,0x9c400000000000000000,0x93e40000000000000128]))) else (if j<5 then (if j<4 then (word80 [0x40000000,0xd1b0171c69400000000,0,0,0x3e600039f300,0x52c0000508c0000,0x8ead0e587c,0xc9aa2750d2000,0x38,0xdd000000000000000000,0,0,0x238a1b40000,0xef40000000395,0x2e731020000a00000122,0x90000000000000000023,0x9fc29400000000000000,0x22860000000e56,0,0,0x341a,0xf940000000000000019,0x80000000000000000000,0x245e0000,0,0xc5,0x4000000000000000000,0x85400000000000000000,0x4978000470c36,0x20000000000000000000,0xefc00000000000000,0,0x12530001954000000000,0,0x8f70000,0x2df400000000004e1c00,0x5b542f000000000000,0xc17c0008c980000000,0x9c500023884ad3037000,0xc73531347,0x5c000000000000000008,0xa25bfd000000086fc000,0x10,0x6000231c00000006493a,0x47000000000000000000,0,0,0,0,0,0xba0c36800000000,0,0x101c0000000000000,0xae53c3f000000000,0,0x416000000005a4000,0x4f6400,0x8c9d03300000,0x6558,0x247,0xc0000000000000000000,0x10e1905c0000,0x1a1400000006fd8000,0x3b45000000,0xcca4000000000007611,0x254f6009e00000000000,0x32df000,0,0x1ae000000000000000,0x322600000000000000,0,0,0x12c40000,0x2400020902280000000,0x13460000000000000000,0x131500000008,0xcb01dcd4100000000000,0x4fac00,0,0x636400000000000000,0x3319000,0x12ab8d7400092,0x8000000013d700000000,0,0,0,0x23a40000000,0,0,0x92140004,0x45800000000004ca0000,0,0x32590000000c2ac0,0x13e00000000,0x4dd83a60000000000,0,0x121f000000000000006,0x5f400000000000000000,0xa53000,0,0xa49c0000000,0,0x2096000000041dc00000]) else (word80 [0x14bb0,0,0,0x88a000000000,0,0x1174000,0,0x4e8b96b80880000,0x286c00000000000000,0x248c4c10000000000000,0x3129307800000000,1,0x4050a0c3004a30000000,0xf00000c6,0x1c000060800000000000,0x3a41000395e0000000,0x802507500014d2000000,0x402330e86e800000020,0x2a0000000730f00e0000,0xd22f17b0000000cce,0xc0000000000000000049,0x10000000000000000008,0x2e800000008a70000000,0x399dd36c00,0x1435000000000000,0,0x53780001274000000,0x30b100000000000000c2,0xb097900031a911fc0000,0,0,0x35749340,0x42440000fb00000003,0x40c10c0000003297000,0x1497000000000,0xf240000000000c,0xe3400000000000000000,0x88501680000000000000,0x25993,0x5000000000000000000,0,0xc918000c1,0x330ec000339b90300000,0x3454,0,0,0x8ff000000011ad0000,0x2a4500000008ea,0x400000000000dce24b00,0xcae000000000000,0x149840ba03a0000000,0x8eb4000000000,0,0xe5d40008cf00000000,0x2342ceb,0xf0e3000000051d90e2a8,0x480000000000000125d0,0x40000000000000000000,0,0,0,0x4f14000000000061e,0xc0000000000000000000,0x25bc00000000004,0x83400000000001380000,0x46f00000000000000000,0,0x13500000000,0xc66,0x80000000000000000000,0x18a100000000,0x30c3,0x41340000000000000000,0,0xcfe994a2c94,0xc430000c64,0xe0648b80000000000052,0xd7413e41400000024fd5,0x2f000048f48d30000399,0,0,0x13c0003205c601,0x950000000b05409c000,0x8b2c000000106900,0x2dd00000000,0xc8e90c6,0x21550000000000000,0,1,0x4fc000000000001fd000,0x84802c90e,0xa00004af800000000940,0x23de0000000d15aa09,0x20185a905a050000,0x141d00000,0x11a80000000,0xd00000002b98000000,0x1310000000000000,0xc63c00000000005,0x3ec000000020c0000000,0x20a6000104,0x1000000000000000001a])) else (if j<6 then (word80 [0x22400010,0xf40000001,0x9f000000000000000000,0xd05000000,0x3bec0,0,0,0x50054,0x9300000004cbc000ab77,0x2d200000000000000000,0,0,0xc700000,0,0x38,0xe100018eb00030270000,0,0x21610000000000000000,0,0,0,0x85281,0xe7000000009402b71240,0x4ae,0xa81b0000000000227900,0,0,0x331e0000000000000,0x20e7000246100000,0xdd000000000000000,0,0,0xd,0x2cc00011bc0000003355,0x4ad6492000000,0x81cc00000000,0x9040000e2000000000,0,0,0x298f000000062900000,0x2f40000000,0x7f000,0x8478000c8b80,0x31f200000000000,0,0x42109680004a2000000,0x290a84ff04e03700000,0,0x1003000000006d400,0x4a0a901000000000000,0,0x307000326f000001c000,0x1809000000046,0xc087e00000b84a700000,0,0,0,0x210300000000000,0xe5df1fe00000008c0,0x40000000000000000000,0xc39448451100000,0x8188000,0,0,0xe8b000044740000126,0x41b00000000000000000,0x3d00000000000000000,0xcb0400000000004,0x45000000000000000000,0,0x47fc000000000000000,0,0,0x33a10649ae3000000000,0xc56000000000000,0,0xeee6cc2ae8800,0xc61b8b400000,0,0,0,2,0x5140004bc10b20000000,0x653c0000000000b29c00,0xc44f500,0x53980000000,0,0x329a811000000000,0,0x18980000000,0,0x8e3843d00000,0x438000000000004688,0,0x21150000000000000000,0,0x241c,0x949000000,0x67d800024800,0x236f0000,0,0x1235000000000,0]) else (word80 [0x1b01c9200d,0xf000000000029a200000,0,0,0,0,0,0,0,0x16bcde80000002,0x17e00000000000000000,0x867b034140c00000,0,0x32b30120000,0x4d6e4a300032d1b07400,0xd2b00,0,0,0,0x4ca473d46000000000,0xa3c61fa48e53b2,0xc112400000000000000,0x449c000000000000000,0,0x3900000,0,0x3a7c000000000000000,0,0x345c140400,0xa41000000000,0x931c00000000000000,0x10c400000000008fe,0xc0000000000000000000,0x44a4000000000000000,0,0xa4740000000000000000,0,0x70a40000000,0xc6f4000000,0,0x65448b60,0x20500000000000108c,0,0x2bf700033,0x7e000000000000000000,0,0x615800048,0x4e3f5f2a000000000000,0xce0c0000000000,0,0xa2940,0x876c00000000000000,0,0x8a2b11389,0xa40004c6000000033e10,0x12330000000,0x53eb0b3caa8000000000,0x20b500000,0x323700000000000,0x87,0x81950000000000000000,0x2a4a0,0x287a,0x224f0000000020c00,0x51c0,0x31e500000000000,0xe1d,0x40000000000000000042,0xa4000000000000000000,0x1b3900000a70000000,0x245f463800,0xbf8aaf506c00000,0x139100000000000,0x8f280000000000000,0x9b0000000000000000,0,0,0x89fd05493b80008d9c00,0x34dd0a6400010280,0,0x8000000000000000,0x1046484400b000043a8c,0xfc000c69800000000000,0x3bfa0000000,0x126bd31800,0,0xa38000002b510d81a0,0x317d000,0x11b700,0x1720000000000034e0,0,0,0x4f8000000000,0xc27400000000000000,0,0x8c7400000,0xd,0x13c00000000000000000,0,0xbe8000000000000000,0x33cc0002013d1c9])))) else (if j<11 then (if j<9 then (if j<8 then (word80 [0x728,0x828c000c950000000,0,0xcc280000,0x12f100000000000000,0,0x11,0xc6000001b000000013ac,0x822,0,0,0,0x1b33000000,0x33d3656502b00024,0xf500000004e70000065c,0x4d0231000333d000,0,0xecdc0000,0,0,0,0x3cf7d1440000000,0x4b8,0xe14b0000000000000000,0x243000000000000000,0x3ba4000016700021c1,0xcd1c000000000,0x196a00000,0,0,0x52fc00000000000c,0xac000000000000000000,0x3b800000000000000c2a,0x7a400,0x32e1000000000000,0x22840000,0x5334000000,0x33000,0,0x46e,0x11b1000000000014b,0xe0000000000000000000,0,0,0,0,0xb900000000000000,0x88d00000000000000000,0,0,0,0x11a400,0x3d400000000000,0x9c336d00000000000000,0x12d41368000000000,0,0x601b2170000,0x442,0xd15b0000000000000000,0x4374000450e2c60,0,0x3341000000000033c,0xf000000063b000000000,0x11510000,0x38e7000,0x29e00,0x184000000000000000,0xbe4,0x12e,0x80000000000000000000,0x21f900000000000,0x3b800033be000,0,0x236b000000000000000,0,0x34ae000005,0xe0000000930c00000000,0x43340000000,0,0x4bf800000022cc00,0x231700000000,0x10f60000000,0x2bfb48ec0008aec00,0x52640,0x426000000001440000,0x34550000000000,0,0x8e1800000000004,0x82400000000000000abe,0,0xc5d8000000118500000,0x8000010d30000,0x628c000853,0xc0000000000000000000,0,0,0x31f6e5cc000000000,0x20,0x824d2897400010db0000,0,0,0x22da000000000000000,0]) else (word80 [0x459000040184a9eee800,0,0xcc5800012b4,0,0,0x123c4,0x22c00000000000000000,0x2400000000,0xca00000000000000000,0xbf0000,0,0,0x2b29000000000000000,0,0,0x2335d2a800000000,0,0xae8c00053c80008cc,0xc00000000000003375a2,0xdc000000000000000000,0x14700003b640002c18,0x247592d8000000000,0x8b031c250fd4,0x270000b4f00000000000,0,0,0,0,0,0x49d8000000000000000,0x21040000,0xa908000000000089d,0xc0280000000000000000,0,0,0xce080000000000000000,0xcd80000be400000000,0x90d00000000,0x8224000000,0x42bc000000000000,0x8ff400000000000,0x330bcfc8000c440000,0x303f2488000000000,0x9234000000000000000,0,0x3bb6a4b462000,0xc8,0x88000000334300000000,0,0x833800,0x1500a8e2dc00034,0x9b00003aa00000000000,0xc6100000000000000000,0x47c0000c0,0x800000000000866f27e0,0x337,0,0xa0c000000000000,0xb580000,0xb9f0c7,0xf24c0002ae5ef9400000,0x44980000,0x110e00000000000000,0,0x23,0xf4000000000000000000,0x656,0x800000000000e3000000,0,0x3ac300000000000000,0x21e247,0x9000117f0000000e3000,0x5b0000,0,0xc0400000ae400050,0xc000000000053940000,0x705a03b0001059,0x28df0000000000000,0x1b00824c00000032,0x740000000000247c0000,0,0,0,0,0,0x12,0xc20000000ca680000000,0x8738dc000081940004a4,0,0x2c8800000000000,0x6938000,0,0x24590001267841c0,0,0,0x88,0x18000000000000000000,0xce80000,0x312,0x800000000000000935c0,0xc8b23df0000,0])) else (if j<10 then (word80 [0x4724000000000000,0,0x89f13ae0000000,0,0xa57000067e400000000,0x6394,0x1325000220ee71,0x91c0002266000000000,0,0x82480000000000,0,1,0x6500000008dfc22a0000,0x131200021d9000,0xef,0xf0000000000000000000,0,0x4f7000000,0xcf04000000000000000,0,0x236000,0,0x109a0,0,0x12730000000465800,0,0x38fa00000000000,0x7ac000418,0,0x3b600004a60,0x3b0ac32290bce60000,0,0,0xcc9022049440000000,0x21b2c3dc000000,0x85821f300,4,0x2f000000033db0000000,0,0,0,0x30e90000000000,0xd,0x171480000000000110f0,0x4db2ca90c09023,0xcbac0000000000000000,0x863400050980,0xe3250c500000000001,0x2b000000000000000709,0xc0000000000000000000,0xc1700000,0x30ed0000000cf54000,0,0x8264000000000000000,0xe29800000000000000,0,0x4480000e1000000,0x29180000,0x4ed,0,0x2e4000000000000,3,0xabf00000000000ba5000,0,0x132d0,0,0,0,0x33f600000000000,0x331a4788000000,0x2a95200000c4f8000c7,0x4a053d19818b87580000,0x914c000,0,0x13b4000000000018,0xe30000000c5340150000,0,0,0x23ac0,0,0xc0c000000000d,0x500014d34da000000000,0xb05c0000002,0x1d050c000000020cf8af,0xc0000000000000000000,0,0x10a60170000000,0x53bd4480000000000000,0x34dcacfc00000000,3,0x91088c80000000000000,0xc4d800000,0,0,0x118c000032c000000000,0,0x40174200000,0,0,4,0xd2c00000000000000000,0xa54000]) else (word80 [0xf0842a,0x6cd8615a402800000000,0x134d00033c80000,0,0,0x20a1000000000000000,0x116835a,0x807c00,0,0x53b000000000000000,0x70c8000000,0xd2c67c00000,0xc91400000000000,0x34b7,0,0x90ec00000010,0xeb000000084640000003,0x11f00000000000000000,0x14b40000000000000000,0x1b400000000000,0,0,0x86040,0,0x2ef000000000000008af,0x40000000000000000000,0,0x315600000000000000,0,0x411000000000,3,0x1a000000000000cbb000,0,0x34470,0x92e80000000000,0x13c40000000000000000,0xc574000000000000000,0,0xe35,0,6,0xcd8000000234f0000000,0,0x33108ba800000000,0x38c87208,0,0xcd10000000000000,0x147d00000000,0,0x87540000000000000000,0,0x4ed4,0x12de0000000000,0x2474000000000,0x1331000000000000000,0x240200000000000000,0x116e3a30000000519000,0x132100001,0x2c000000000000000000,0,0x808000000000012,0x44000000000000000000,0x24d5,0x2105ca5800,0,0,0,4,0xf4000000000000000000,0x1392000000000032d6,0x84e00000000000000000,0x11,0x7900030e400000000000,0x10390000000462,0x325c000000000019bf00,0xa1d00000,0x1600000000000,0x14e2000000000022e,0x70000000000000000032,0xf3874716300000000000,0x4008000000,0,4,0x5e000000000000000000,0x43fd0638faaa4,0x80002ac947c400000000,0x123e00000000000,0x82380000000000000,0x22fc000000000,0x34f3000290300000000,0x9320000000080e,0xc45c0000000000000000,0x19c0000001b9d00000,0x5e80000000,0x31c50000000000,0,0xfcc3ab00000000,0x47a800031dc000,0x3019a34542d000000,0,0xab640008ec4,0,0]))) else (if j<13 then (if j<12 then (word80 [0x3e0a930,0x33b00000bb20000000,0x8a380000000000000000,0x190e000000000000,0x7ee45700001240000,0x3306000,0x1953000000000,0x13fe00018e80,0x342c00000000000000,0x320,0xb4e9ca4bc9b800000000,0,0x16e6f6c0000000000000,0x150600,0x412800000000000,0x7e22f6,0,0,0,0xab1124e51f,0xa3ba0000000000000000,0xd19c0004c6c0000,0,0x244f449000000,0x29f000000000000,0,0,0xc3e400000034d60b,0x6c00000000004b340000,0x86db8da0000000,0x4b40ad8cb60000000000,0x92e400000000,0x646848800000000000,0x925000000030e8487,0x106b000000083,0x1c000000000000000000,0x318a0000000,0x1590001450000000,0,0xe56c00000000000000,0x13500000000003216000,0x12270000000000000000,0,0x21f4a7ed446,0xc71011a0000000000000,0x22ed04ab3c200003,0xe30000000000342a0001,0x2fd00000000000000000,0x2c,0x10000000223000000000,0x245d00000000000000,0x234000018587f00003c,0xde7c400000010ae00000,0x3930000,0,0,0,0x36300000000000000,0x8f58000000000,0x886f3,0xdd000000000000000000,0x38aacbec000000,0x2011000000000,3,0x800000cc80000000000,0,0,0x2b18000000044ae478,0,0x3294000000000,0x8d3000000000000,0,0xf2000000,0x295700000,0xe6780000000,0xc8a1570000000000,0x467000000,0,0,0x4d4000,0x6cd000000000,0,0,0,0x65f306a2,0xd7028b00000000000000,0,0x681400000000,0x20a80000,0xf80000000000000,0x13ff00,0,0,0xc32800040bc000000000,0x21,0x90000000046bc0000000,0,0x11420000000c82b32a8e,0x740000df089400000000,0x312e00000000000000,0xce0400000020aa000000,0]) else (word80 [0x40f000000000000003,0xc3d00000000000000000,0,0,0x30fe00000000000000,0x30550000000000000,0xed00000000000000004,0x4c000000000000000000,0x51cc000268,0x4ce0000000203200,0x8ad800000000000,0x39c200000000000000,0x2419000000,0xab08cc746740,0xc12c0004098,0x93600000000000000,0x204700,0xac50,0,0xfe20e6860c000000000,0,0x30bd0002108937c,0x13a00000000000000,0x296d000000000000004d,0x48000000000000000000,0x21f550780000000000,0,0xee0113b6b880,0x8410b400003664c30,0x32a446a,0x80000000000000000000,0x83c00000,0,0x498c0000000000000000,0x23780000000cfb40,0x2280000000,0x469c0004fa4000000,0x3bfe0000486000000000,0,0,0x301e0000000000000,0xca4400000034,0xe7000000000000000000,0,0,0,0x2371,0x49572ff00000004e4000,0x52000000000003,0xa4000000000000008ecc,0xe57c00000013f165a,0,0x902c00000000009,0x28400000000000000000,0x4f4800004c4000000000,0x10,0xd9000000000000000002,0x7c000000000002f5000,0x1ec000000000000,0,0x2e84000,0xd20c000c98800,0x8a0400000000,3,0x2d000000000034e9d21,0xc0000000000000000000,0x805800000000000,0,0,0x337200000,0x938c0000000,0,0x884000000000000,0x4f180000,0,0,0x1c6283600,0,0x14080000000000000,0x1496d2040000001947c6,0xa000000000000002ae4c,0x72e1c709b00000000000,0,0x23b7000000000011,0x32000000000000000000,0x488c00086d01c80a3,0x4000c2ec000000143700,0x578,0xc2000000000002390000,0,0x4af49ac87400000000,0x474c0000000,0xe2fc4c00000000000,0,0x224900000000,0,0x53911e60000000000386,0xe4fa0000000000000000,0,0,0x92ac00000,0])) else (if j<14 then (word80 [0x23d40000,0x483f3800000000,0,0x2946000000000000,0x125800000000000,0x22a00000000000,0x1a0a423c000000000000,0xcd780000,0,0xd2783ee000000,0x22d000000000000,0,0x102c0000000000,0x3a0800,0,0,0x54c000000122,0xb498444b000000000000,0,0x24ce0000000000,0x18b300000000000000e3,0x70000632d0ef00000000,0x22b200000000000000,0x33200003385000325,0x2000126dc97c00000000,0xcee400000000000000,0x88fc0000000000000,0x74000c8,0xc000000000000000000,0x8b6400000012c5,0x8d0000,0,0xc01f07e00000002b28,0x52e04110000000000,0x43c000000000000004d,0x7c358000000000000000,0,0x1e0000012,0x10000000000000025200,0,0,0xf442ca8b,0x3c000000315f00000000,0xf10000000000347b,0,0x138b853000000000,0x13c,0x442,0x800009c800000d4c2800,0,0,0x4240000000000000000,0xd100000000000000034,0x24000000000000000000,0,0x1cc50,0x10000000000000000000,0,0xe16000,0x3c3000000000030,0xfdc2121ce00000000000,0,0x290c000000000000,0x42207b00000,0xcc24000,0,0xcf880000000000633c0,0x45500006bd80000000,0,0xca74000000344285,0x38000000000000000008,0xd240005316976c2c141f,0x52f4000000000,0,0xc21c00000021d46b2c,0,0,0,0x6ac000,0x34280000000000000,0x9094000000000000000,0,0,0x8b971ac000147100,0,0,0,0x42d8000000000000000,0,0,0x882113a10,0xc8000d2309610b540000,0x348e0000000,0x319100000008d4611,0xb0000000000000000000,1,0x4cc00000000000000000,0x349c8ab400000,0x821400000000000,0,0,0xcb98000000000000000,0x339a0000]) else (word80 [0x4200000000000,0xc6e20c100001e344d,0xc000000117500032ac00,0,0x807000221a53feb42,0x3241000000,0x9940,0,0x1334506,0x31e800,0x4a7000000020400000,0x83ec000])))))
def g251D9 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0x3d84e953,0x884d893444ca12fc4b65,0x2bd4a6927b4941230483,0x51e846e519745cd15b45,0x112143f90e242d109a4,0x1f906041050133fd8fd9,0x3f00f923dd8f573cf8f2,0x63c34eed3af4ea33a14e,0x673938e2f3850df53720,0xdb2363cd753564d3a342,0xccee3344cb23258c7931,0x44c323048bdd2ed8b922,0xdb4b3c2c58aec2b10aa1,0x29f4a5528aca0527789b,0xb265496c253092b24448,0xfa232489e21dc8552094,0x8021f847b81e3476c1d2,0xc72e1bf86dd1afc69b19,0xe064a18845f317345a71,0x60c55314bc50d139c4c8,0x1298488118c43810143d,0xb0eb838d0d843440c5c2,0xfe0b882c30a982820984,0x23b08701fd07681b7064,0x816e054013a047010303,0x9c0cd02bc09701d40590,0xfc0200003b756f4eade,0x5d5bc3ab7a656f2caded,0xcdbcb9b7b726f2e4dedc,0x5bcb8b7b706f2e0ded95,0xdcb2bba76572ecaed915,0xcb22b970572cace5919c,0xb1b3b72676c93e5927db,0x2a79654f6c89e5913db2,0xc79658f6ca7e594fdb21,0x79642f6a94e5529da9d3,0x953a72874ed469ca8d39,0x41a72634edd57d3aaf97,0x55f0eabe9957cb2afb74,0x5f2e8be5917daa2f9545,0xf6e6be5cd7cb1afb535f,0x2a6be50d7db92f9725f2,0xc4bedc57cb8af9615f6a,0x2be5457ca0af9315f6c9,0x2e5925dbb23a76472ec8,0xe1d91db2a3965476e88e,0x5d11db223964472a88ed,0xcd1cb9a3b63472c68e50,0xd1db923972476c48e589,0x1ca123b71472e28ed851,0xcb0a3951472828e4c51d,0xb2c3965876c50e58a1db,0x29ba65372ca6e194ddb1,0x9b963376a66e54cddb11,0xb962376a46e548ddb293,0x965276c84e5909db1139,0x62272844ed907cb20f95,0x41f6c23e5847ca88f941,0x1f2623ed945cb28bb641,0x72c82ed8c5cb18bb6217,0x2c42e5485ca10b93212a,0xeb655cecab959571b2ae,0x1655d9eababd5737aae4,0xf5dd5abb9b57726aee2d,0x5dc1aaba855730aae415,0x5d9cababa96472ae6e55,0xc9cbbb29576554c8aa59,0x14bb8a977052aec055d6,0xaaba55d64aaae7555caa,0xab85577562ee8c7d918e,0xb23177363ec6c758d8bb,0x93177062aed355d272aa,0x4d5709aeec955d92bba2,0x67544caa895dcd37b9a6,0xc734aee49c5852bb8255,0x768aaeb155ce34a1c557,0x28e2a3155d8eaba9e943,0x3e2c2755d8aaba171512,0xaaeb455d28eb251573a2,0xae5455c68bbaad7745be,0xc8b75916bb9ad7725bec,0x4b75896bb8ad57694acb,0x255d252aa4957194aa32,0x5dd90abb2266544aca85,0xdd113aa2255442ee685d,0xc90bb8a275144aa28d58,0x10abb41575852c9055ce,0xab94294286aa1055d8c,0xaba9a964352846d580ca,0xbb1157522ae84b58c96a,0x19355022aec355d07ab0,0xf5501aeec255d84bba8,0x957512ee8255d04bb989,0x57312ee4255c858b08b1,0x51162822c4845aa80b54,0x16a6026d91e13a84175,0x8ae6125c826b8851700,0xc6a8e15cdc4b93a15400,0xae751dcd3ffff7f7efef,0xeff3f7fafbfdfafb7bbb,0xd7f64d8760d4750d0740,0x99254591615815454550,0x505404c5304811019054]) else (if j<2 then (word80 [0xc0a94244,0xd1f176209314c14a5167,0xde10e2ebaa094795b726,0x2e7fe110a0f4e58275ae,0xf445dffce559048dacfd,0xb28db4de88cb3f6e411e,0xbf05e326ff9cdb9048ef,0xaaa265df937008e79e9c,0x3028de9c6bb00095b8c2,0x8e234ffda42236cdca22,0xca8c453fee904d23d704,0x11e62f71143947880206,0x89f61116ceb5c9a74ba0,0x463fed904c3ff1f96082,0x46a5a1d14bb546c9966b,0x441ff78f018120fdab49,0xbbe6d332eaf111365f91,0x357888949fe44c83fad6,0x62ad493ee1341a7806cc,0x99f7b33244b9d128cfc2,0xc20bf85834a7f48c83e8,0x42d72a49879a0a7e2414,0x239f4b04d336b28b5afa,0xb1957fbf882c82489e1b,0x518f2edc4c51f97992bd,0xa8d90f2edc4c1f87288a,0xcdcec55a101c1c161078,0xfdbb7cc28945cffc220a,0x6fffc2209e394a5d0cc3,0xfbddec0904a9ebb85511,0xf6117598149ddd5f0a04,0x85ff08208dbf808208f9,0x594a5d0ce362ebc1824d,0x6186840ccbebb0241236,0x6bb89a377d11410cfbfa,0x22a2248b6fe0127b6df6,0x193ec6e2883479127336,0xf7cc449530cef988926f,0xdb6ec3149f0f82051337,0xc6b210895bdca2151cfa,0xd81850bfc56b544791cc,0x6612092b5de54460dbc5,0xb32d7f1b49b6351e2200,0x12b73a6608e7a73413ee,0x74c482427595b8659ffc,0xd97241271bc29aa0cf1c,0x3b485e0344d1f014090b,0xe2c842246fe02082387f,0x2a90120346fe020823b4,0x72972cac5f056a330aac,0xa18468e52e595df4a184,0xa4facad330f84ef98848,0xdebe57f0820923c0ff88,0x82381fe6b1021212bed4,0x4cb35d774a449295f6e6,0x4cfa8494123467eb98eb,0xf5b99262d68a3530c5a1,0x32dd68819aeff1624f3e,0xbbe9123ace34146ccfad,0xccadfd7721957f9ca423,0x1430eb0199aad4c8d98f,0x4e58279bd110f4e58275,0xf7a221edec13534b04e7,0xa72c13ecdca2774e9b8c,0xb1edd8c9b4dca28af944,0x46de4f2e46178c4801f1,0x3114150c1d8306d18472,0x30603c128e47a03218f8,0x882305a661709090e812,0x1ec004c4401882006602,0x870020807020b9084187,0x8704e902141464088186,0x82e2a4288420050a8743,0x6148123c1e2916838230,0xd8306058830ca060282c,0x10370300100190d83b3c,0xecc0b256c69b0d6bffaf,0x86bb4ae2eb59acdeb0da,0xb9aabdaa7aa77a95ea37,0xa8729fba78e9b5a61e96,0x1a4e2917a3ce8cfa2ae8,0x88a196846a05e7f19f2e,0x7a39dee7589cc27099b6,0xa6ad9a3e66f993262798,0x25d596a257f953e5159,0x3be4cc928a47b9132422,0x8fce3b28e223578c9e30,0x8b5e2a98a1e25b88c22,0xb878a1bf866a173852a,0x11c83c60c5824206880e,0x20097f85fb47e19f5e7c,0xf5f167bbdeca7a99e807,0x951e2577a9db37639d62,0x74c9d0c73c5cce72adc7,0x770fdc136f79bb66e19b,0x526c79afc6b75aaf6a45,0xa6568a19f667319a9661,0x9964650992063f98dc62,0x9d86f60e980d5f857bd5,0xe4d76d5d057125ba96c5,0x5a91680593161157915b,0x7563d56254e5508538d4,0xb85251475516142b5005]) else (word80 [0x377aaa882,0x448af36c91154b5f5f92,0xa10913e42cc7c891b999,0xb66c0a8985df1ced9058,0x978e723a8bb8ff3d14d4,0x8ee1f55103388ef4e42c,0x109723e4d02387db14c8,0xcf67f9c220a67d1f294,0x915f4649952fe8ae123,0xf7d55132f7d55132d2f8,0xe265e2605235d8712afc,0x64e1920943ffd8ae0824,0x576b524acc5fe8b48166,0x697d1132ed67ce9234f5,0xc4ed234f5c4ed2327a78,0x22654f4f044ca69c1c0a,0x7e330a1202549ff4494,0x8f27fd12523e7fb04113,0x367fb0411332f9112647,0xb75ca08d2cd3f4c90291,0x4ede6e614cadbca3ba08,0x2d0be4672292668e9407,0xda9dd65efcf463330eaf,0xb09048bbfcc2d86527fb,0xf039142a0ff3b0c89490,0xeff3b03895d25e127660,0x1626238fc20823eef80a,0x470e7f9c220a957c889,0x3241fb75ca08d2da1bef,0xe30ca47d72d6352a48ff,0xe0942327a0513a09fa64,0x814921dbcdcc29966ff5,0xee8a1a49fe67928280e,0xb804c033eef422612094,0x38ce27234fc67841324e,0xe460e84449cabe46723e,0xf9062439243ed4eeb2f7,0xe7a3199b63fc48923ed6,0x7e2449226bfe62622483,0x4ff0f8205469fe5c8205,0x735ff31924324bbf6de0,0x6629bf7ed33b222b5fe3,0x590900937ff76140527e,0x76c84602ca79db21180b,0x6fdb74ca8a87b13348d4,0x9e8106d9870606b1240f,0x689d512392c14521473c,0x27804803fce278048d87,0x3d2060097bfd873d2050,0x1367e39aca42402637e,0x430899b7f5d0264924f3,0xf89f08e8ae79b0844480,0xc97a4d1fa733596be1c6,0x3328ffb81a9ed1254fd6,0xe1629ed1260f34ad6d12,0x52fc79a56b6892efd248,0x298ad7ebc42818926ff3,0x9d248298b57ebd720304,0x92cf4da3a299d36588fb,0xff94491124ae646e8a69,0xce5414c5b3ff34c84901,0xa24e5fcf802068928fc9,0x220a62c0f68164ca1ed0,0x2c9953d29c2654f4a709,0x95b42e72656d0b9c9973,0x29712655fcd2b4848926,0x5ffe54f7d04d168ff272,0xc42449317f4d3d4a492b,0xfa47e42090d0fd02ccb9,0xad90b2eb3d7b8718ccd3,0xfe4e1a00922bfc9c3401,0x2963c78d291e7e3c6948,0xc5b5323652da99d16618,0x934af8d004c9e312695f,0x1a009bbfd0ac3004958e,0xc7882524b7ae9892b30f,0x1ff26c41207dd6b4b88e,0xbe6d5d75504a1f8c28e2,0x36eeaf841049dce91904,0x8390e584eb5559459ffc])))
def g251H9 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (word80 [0x2876e88c,0x1540002020d20003dc47,0xb24b852438300021cb4c,0x970b40cad2dbb0213b56,0x882164000325b44b7031,0x4a68000c7e04198b710f,0xccab6be400011af00030,0x4220ecb6e0000000c59b,0x854deac598a38b4400e,0xd8c82fed9dcc62400000,0x104e0b40b938aa00000,0xa8c00052284734c5e265,0x138e000228286830f,0x500020d68be81c990852,0x9968f886b48762fc0c7a,0x1880003b6c12e0000531,0x8000d09a9564b33036c4,0x8a0a4522c00000003670,0x11040005010000,0x493092943148d9000220,0xa00000000a894cb8382a,0x6c638c0d3c508000c61d,0x2a49176a55000219dc42,0x82a9cf3e41311a425c00,0x3458128c00000024bce,0xae716aa9bd0e4c18e43e,0x69c1c48c01d45f000131,0xb0002c40466d285278d4,0x2400022450000a970002,0xc8200000000000000ca0,0x34a9d2dd302113a19eef,0x8a138000000000000009,0x1704390000000d0ba418,0x445000048300000003bf,0xc00f0000000000002003,0x454b151f043e435ec4cf,0x26884680000f58000a51,0x400010cf341866400000,0xc7bc17f0000000c,0xea0000000000000024ae,0x290e8cb000019,0x102cc88a000000000000,0xac1400000012052c1c,0x8b24000cc8f10daf3,0xc00000000000c3000000,0x1d90a951750000000c,0x7400000000006990000,0xc32f1eecaf6140000000,0xc14400083d800000002,0xc681d4000000218a8268,0x474b38000001ab465,0x6100e026bda530740f26,0xbb3cb318737000000006,0x1e1477000117ad2eb30d,0xd29d0ec2da445b000292,0xa27e54bd217031f4e8b3,0x6c45f7bb80000000d2ac,0x24a40e42e80000000c8d,0x80009153010486800000,0x2a78cec0000cca1790,0x97b0bf000333dc8a23be,0x2c0b137000023,0x967e81aa40e815f85ac0,0xa4ec000af673e80001,0xbecb79adb0000000000,0xe32643600011b400,0x22370be044cad42308c,0xbb823b0e230060000604,0x240039f0e040810c5078,0x2000442e0004a8002041,0x130004850e042850c40,0x3220c0020208102041,0x703463c0000214e8c06,0x8295068c01900080820,0x41c18306942010208000,0x8604001858d300810,0x904046840804a2c0c180,0x21000204180800004,0xb0000000010010003100,0xc083000480402045142a,0x80120a0848018046851,0x8003002831b0a10105,0xc081860024008140c00,0x200005000204b0002043,0x68e0c00e20080810640,0x8600000810400089081,0x60a84280001c28502,0x40002080001e907851,0xe0139d04141020258080,0x14003000c18f082420,0x3001000400004030e1c0,0xd0a1458304014000004,0x4833600000001c000020,0x42850000080221800502,0x14200061810116000860,0x41458602141080800490,0x10086080200100083828,0xc0a0c18b060400018387,0x3000c20100002020600,0x8022180020a005800a0,0x41210410310001088600,0x18180222810400043050,0x850516000000208106]) else (word80 [0xc8854000,0xc6504320001420000000,0xc228000000000010a80,0x25c4ec00000031fdaed4,0xaf1aff00024518f6,0xc4050003094e9e0000a1,0xb4000000047c26791b64,0x8c81ffec4c157cf2545e,0x34d08d9810e000000,0x827a00b09123,0xac923043067c04ac0243,0x8c00000002f7d016000,0x108d24eb2f6a93e414c5,0x8000007f88d0a315355d,0x1990b76dbd13c2814000,0xe99c00080d33d70ec61e,0xbee9b076919311f91e11,0x800031df308a3658e11,0x22147a1070c271c588c1,0x70c400001580001b9d00,0x2bf9c25c0000002cbf0,0x1165ecb800061990b5,0x8db4000c1f60e5cf0549,0x9cbd130400010c1e8ffa,0xad2f781048bfd0daacf3,0x22bc47400c0002231000,0x19320000a16aa4411921,0x9c00000032df00000000,0x33d90003484ca30000,0x1a440003a18000128,0x4035c000000000000021,0xdd0000a6943dc1680003,0x3d300031d40000a594e5,0x400001c8161b2e62ca00,0x830c00000000008,0x73d2e385c829c8bc236f,0x2e8068ce24000000237,0xea4e4000e40509b00000,0x13ec0001,0x213911c00047d4000ca5,0x80000001a930fd000000,0x349311813010003afe8,0x7100000f7c000016f196,0x100cc7c441a0bd413c00,0x4ab11be00000,0xcaff24100000000000,0x328f000,0x30eb09923ae84a000000,0x11b749e53eb0f8300a0,0x215e000125a09458d2,0xcb66b1500019e9e0e800,0x639000000011d08d3c8,0x5100003b9c08a14f5252,0x2d70000000872831d000,0x373000000000033564e,0xf6312cda33c2e9412be0,0x1870000000021c8000,0x136400000004c503a,0x90000000d13c4530000b,0x452a5800088931b80f44,0x8935bd503b408b814,0xdc0a2eea2d6cffe07f8f,0x8ba564ac0000d2690c03,0x2368f78b54113c5dc335,0x226fa9f11d7000000,0x112c00000012,0xe900010450003c210002,0x1e6a65e31c000294688f,0x7a60000087763541568e,0x8000800801e700b3d50,0x3050a0cc00005c44c7,0xcf622406309bea87c800,0xe98b1b00d513de0087b,0x3e12270e804471760000,0xe8dfbbb637b09fa34,0x432663f12d3a7adbab23,0x8746c871c00002b91204,0x7a63490000448456c342,0x8ae800000000000002b0,0x49f311821d19,0xe1908c000d0dc0000002,0x857a1c5a680ebd212000,0x4ec848e8f1000085,0xcd147000215900011da4,0x7d89ea267d2564670218,0x2a6000087500038d,0x60000000000000000000,0x6ca800089840c70001,0x492510184a0003311482,0xc00000011e200023a7ae,0x6aa2ec3d201f0a6f2290,0x1bdcc09b1270000000,0x13cc42ec000000000,0x108300024,0x4d000000000032030002,0x5900034710000000000,0x2023000232e00,0x9e8cce400000002e2a,0x3613dd0001a98297c000,0x47380000000000cd4800,0x69b4000ae3c000d2601,0x8289dc000000185911ca,0x40146c61ed4fa8000466])) else (if j<3 then (word80 [0xf0000000,0x498f3fd0a,0x18000000204790b242d6,0x7930b8527c000ceb4000,0x321f9e00000000000032,0x2c74c000000124900000,0x40a80000000,0x2143e20,0x1369c6b40000d2a23ab2,0x2ac7d4a600000002b710,0x2488000292bc9820af,0x651d45a4d383438de6c0,0x1278a02fd300c4367781,0x530eda16ec3ed27d818a,0xb2b878c000000c1ec8b6,0xa4c3826131a4822be886,0x9c00009402738220000c,0x39d044cd303e4e8982bb,0x217f3c60002491000000,0xd308000293ba1400032,0x5f4df484ec48c000476f,0x99d0002ab80001a5d0dd,0x800000000000d8e88900,0x120e000321e0002096e,0x4c0222c6300000000000,0x32ab4e1c000c63400,0xce4bacf000000000011,0x860374000000010249b8,0x2089e9e741e4d1,0xf4ad000013f000227502,0x1019acccd47aa8900000,0x6484b34a1d85d000142f,0x6f422e58d6ea15000224,0x600032880b1dc20ef4a2,0xe7452000047804420002,0x8ca45101ac02854b4a6c,0x2bf8d3301cda80930b8f,0xeec23cee000091173aa8,0x79f4a2add7037c714000,0x4f90ab527248,0x6ec0713a0000000c67c3,0xf0000000d1c0292e7dd,0x2f12c2206a4cf2c4712b,0xc000e9aa377c00403020,0x302dd00011c18ef010c0,0x22eb4e7a11c0256444,0xc88daaa0e2e0e20000a3,0xaa90b1f42f6000000031,0xa900003f3e1122270003,0x3a14610a610001129000,0x24bbcaba88f00000002b,0xf20a2000000000000000,0xa440000003c95,0x311000033f1000000,0x10244c58000d0540,0x210100000000000,0x1a5a000130e01d,0xc00000018c642380000e,0x6a093cbe400021b816c0,0x80ad8f00000000,0x8cfc0000000000817e4a,0xa529822a4d4400000000,0x5bc00087200000003,0x9e600010efc10791f699,0x639c80270a74e1800046,0xa0000000000000022978,0xf1c074806400089c4000,0x20a80b80201000046,0x8cb2000000033214a840,0x20c913900000004cf8,0x512bbb90000431850,0x50430000000000000086,0x9785a454000000022590,0x33bb4fb834b,0xc29435f084524ea11400,0x485c000028f1c2cae00,0x47600034250000,0x91c000a9fa9dd8de,0xc0000000a73264f18b00,0x2004000000041813f00,0x326c404a38d054509d,0x3225000234d833206,0xe00023c300000004e7c0,2,0x8bde96f3620002496083,0x6c0024cc0000003bd600,0x32548,0x58d04ba283210cd6a146,0xd18000c12400046983c,0xec328000000000000029,0x350000000052b1e40001,0xbc865e85e000214ee87,0x90618000000edc986592,0x6d329c0b61eac803467d,0xf3331111ac5a48f039b,0x5206181861429e029a47,0x540720d010ff00504144,0x3a06ce0ad00000000000,0xe8f000083c603e000,0x29bf09ec27a4a2400000,0x1a92cb2c0008a50000f,0x22c000c90b02e8f6a46e,0x8c431fc8fb702]) else (if j<4 then (word80 [0x81cc0000,0x92e528d834410b92c0b,0x3c4562144f2a2ce6134,0x2e10000000d1f400011a,0xe457000203209559ed00,0x4bc80000,0x2680000,0x50680000000000000123,0xf000000000033c852540,0x4175017f10a0d50574,0x40a00001f1000,0x21d1883c0dc41a69af51,0xbfc81c5c3c740000000a,0xbf680f000030312d8000,0xc59ca7d00033ab000000,0x1a66819c0000003b,0xe5000000000000000003,0xa5200000000000000000,0x42a7397000000000,0x4c544b2870f4520,0xc3c012b,0xd25e22,0xc24b0000cdc800000013,0xe571a400092364100000,0x53380000000000cdf,0xc0004424000ca0c00000,0x4c844b800000033240,0x23f5a7bc00000001de,0x8179487c9a4000000000,0x14566a540,0x911281a1b51971e1c1b1,0x10f918aa540001b6d40c,0xc0008fc800085721254b,0x63336000234043ea9f20,0x143dc6e80000000357,0x49b601ac6d51bb8a5531,0x900011830998000523e4,0x9d6a6b353a2680000000,0x2a57c4f64a5000,0xcefe2208a8000000,0x3fec77004c00031d80,0x20ea00000000000000,0x898b0990001a9,0xc00030b9054a4a8440ec,0x9300000000000000205d,0x98700000000b5000045f,0x8226c218000000105700,0x304800000000,0x4a100032b6,0xc054000000000,0x4608d000000000,0x121f0000,0xcaa,0x9082c6002afc68400000,0xe67305800000001,0x18f0c688bc0000000000,0x238f0000359000308,0x1e7b80000000402d3154,0x2b0000000e39619349db,0x2e48da800050e240c000,0x1310003860000000000,0x33fa00033a600028dac,0x12817b00000000000000,0x1b702b68000000000,0x14854f8c0000d232,0x9f8edc00000002fbc9d3,0x4c4aa64000218f49e015,0xa1f49ac000000000000,0xcd33b448d6c7e0,0xe40000463c0000000000,0x8fe59c00003a7a41c705,0x20000000000000000000,0x10d732f0002,0x8238c18b6b4bb0000000,0x298d9f58364000c1,0x378860000000c0238d7d,0x2404cd081f98f509e309,0x5b505551e400,0x45a400000029fb04d00,0xd0a400000000000000,0xa4600004cb,0x10c9000337169473d00b,0xc51400000000005,0x1b60df00028f80002219,0x13fc00000008cb400,0x11400000dad86f00018,0x8b0bb400044b0000c7ef,0x29000000000f7000001b,0x6a5e8ae52d1000120200,0x862000000000020790,0x8360852,0xd29014dcaceb9e000390,0xb0640000000000000023,0x6e2a500000ca8000a9ac,0x27243ff85b8d70c3f8b1,0x20130000000000000000,0x3c06000000010204430,0,0x9600000000000000000,0xb4b31d400000023,0xb0ce9738aae580000ba9,0xb6a02b0459403c2cf000,0x11fa000246a000000046]) else (word80 [0xc04583104901351324,0x3f7c41c2488b9,0x8000000007c0000000ec,0xec0e1033c05c12f81b9e,0xef447b87e5174ca042b7,0x4ce800000000000d6000,0x5003a9f000000000000,0xa9dd1a40002a6e0f84,0x434845d1e50003112000,0x9072040000029300,0x30b1502741dcad4000d,0x1272fd40374b1000026a,0x81e38610000000000000,0xf9e86c000000000000,0x1056000141690a0,0x41e8000000041f000,0xc82702700010db04,0xd91a300020fdcd100004,0x34b35040e023ef07e08f,0x8bcc000000012f93290c,0xd0000000000000042813,0xa4894fc5b4ca328a0002,0xaa80a2c000104821c120,0xd391ef9c000000000008,0xb800087000000000b3a8,0xbf80f38e751ccef8743b,0x50440000000ad0105fbb,0x600011b2868b47e8d810,0x6b323f2ef8ad18c06cb4,0x455c3503078fd8407056,0x80e3a1cf320000340b08,0xcf2704f170f800022528,0xd7611b0001a0fc06200e,0xa19000000038ff449a32,0x7000212100008f6908a9,0xe5000015500021300000,0xa3000018f9000,0x2461c6bb2574b4800000,0xe66c00045300008,0xc2a3a383b811602a8000,0x295d000382f8de01f,0x700000004e4d39900000,0xa9732f500031620003,0x8d300001c641918fd000,0x12436c2c0b200013a000,0x23f8ac2538cc93e07e9,0x33fb3f0974c49b2f8000,0x3361cfa726728f433,0x742d800080fca2c00000,0xd1fc0000b3527f0c4f,0x858b1173ba4c60000000,0x30c892d729d000000050,0x380000000000a7f40000,0xcc00000000000881b2c3,0x419a33886fc000000020,0x4cecc00047569dfcf4ac,0x8c452c0002e661d64f52,0x23840a339649fa8f5c86,0xd374016a3c0cb0a2b20b,0x4c8e0dd400047cdc648,0xbdc0001034000000306f,0xe8eda21821c000000000,0x6a8400001ec00000009,0x5c000341b00000004339,0x398d01aa538638474000,0x10730859a5845f0000c4,0xa84820f351bdc3a40004,0x9e10dea7cf1780000000,0x3035000000048c00b,0xce5000000034bf00018,0x34000000000000fe0001,0x1b00000924ac4000ec3,0xb014030b06500010f2cd,0xf00000002c6a04cbca40,0x30e60e14000,0xe8d90290000000000000,0xe3043e68fbc8e7c8b53]))))
def g251D10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x40cf7f82080,0x40cc7f000c1bad822f80,0xc84eeb605293680c3b30,0x80c19f01efe240605577,0x80828b9d7a00a4eec130,0xa9c0077001cf21c04ec,0xd4077bfc4042e00419ec,0xfbd055fc3404ef3db480,0xb29210c1c0b09132a2d1,0x91b2b250203181d04102,0x2c810f010e83820d050,0x6956388a60c7c9d570,0x1a46217253530438ea36,0xc62a4941dc630fc2100,0x364991641925455054d8,0x561d4551d05414c76058,0x350543405013048110ff])
def g251H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x22dc02843d7974243b4,0x18822f5b84ca5651f061,0xd0ff2b26895d220e49f5,0xf64208dc50006c1b86d6,0x13f4fc84f2dc38280800,0x45b84da7242544451,0x589355175de7ce57c70e,0x3e750e04c1c088890734,0x87855189128274284745,0x8c05655631a6301ac570,0xf617203486a3ad1742f,0x38e31ee8d61e82220168,0x284b096a4a02d091a0a0,0x4ed6f080387c7f373000,0x583474e3f10b61611300,0xfc26a7880036ca05a39e,0x6cc84023f1d85da36936,0x62cc36260e07c52895c0,0x52d75b41f81469267be,0x5b466c4532fb68586000,0x23cd6358380060268c53,0x561f35ee29184b578005,0x8cc08827968e2421a08b,0x64842c3888840ce7b43,0x397e26fd59341b59f21e,0x6e42022140758da1e195,0x362694922d0a46f02861,0x9156639379c156593122,0x67846e3d108211800000,0x73c7708580026ae4fd1,0x1c7db87261600e1585f0,0x12b82e7101b11d15ce45,0xc5596a86bf7dd58c87e4,0x8561a89e8623be9507d4,0x9643200857b52be49651,0x11383783fe7fa92d1486,0x922be74778a4780028eb,0x6a654000465e1482a009,0xa40410a3c60620935258,0x9b5421063d80193aa306,0x65219e5ec3727982720a,0x80073788aa3328f95500,0x47685f87e88a25d40d8,0x8f08bc7505e40e844800,0x228e2e02fa4d15680045,0xaa29c8180000037b8002,0x46162e51c21e4b800013,0x31294100007c28cb9000,0x46869700002a80076b0,0x8548911000000028e560,0x80007961c80380002ee6,0x290840d0f761217c533,0x80f8d26b000652053a1d,0x80021680024e57847063,0x4683c72800586c4ac7aa,0x6667580047e426000454,0x858263a1d24f353d8966,0x7385d5e241050a628000,0x8307660e056b84158000,0x22583e80047368101805,0xc16042324340d62b669c,0x4412432a9436405c955,0xe2c40ba3560b04c68766,0x4524f6ff5011fe11624e,0x35c77c5a06a26260c385,0x471a3a563c4887a26db8,0xfa6ed5fa93c59841e314,0x30e6c234800242f09858,0x8003903800022b00000,0x3a0c000c401759941118,0x9c412bc01b50840c5b,0x14c1e273b80c081f0013,0xc0a7160c0c9e0e091750,0x601148601213000682c0,0x4520310002018480c020,0x642a46028e4224d200,0x40f6a832820001d1b864,0x14058a80e030004010,0x56060043202028080002])
def g251D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1010027f
def g251H11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xb32e8fc88983440157,0x8014c9c00ac000024be,0x1628065920d61a5001a8,0x3d9973db80298b64b,0x33923801a31e10340001,0xd00fcf40c308564f0080])
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
