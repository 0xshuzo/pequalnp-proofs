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
def g137Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0)]
def g137C : List ColumnInfo := []
def g137A : List (List Nat) := [[],[115],[48],[48,112],[112,48],[112]]
def g137D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7
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
def g43D3 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xf
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
def g141D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
def g165D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
def g47D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g59D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1f
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
def g109D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x57d4d10
def g109D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc1a0fd20fd10
def g109H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g109D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x23440bf
def g109H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x25f804c0000480c40,0x80000002,0x600003b5c00000000000,0x2a000000000000])
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
def g155D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g167D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g171D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5bd4940
def g171D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc8404fd40
def g171H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc
def g171D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x2b2a0bf
def g171H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
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
def g173D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4e09f
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
def g174D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
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
def g179D4 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4fd5130
def g179D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x4088,0x480e140fd40ff30fd30])
def g179H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xc
def g179D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x18989f
def g179H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x17000001110080
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
def g63D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1ef52
def g63D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x222317f
def g63H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
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
def g111D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
def g123D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xafd9110
def g123D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x683fa61fd10
def g123H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4
def g123D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x34ad11bf
def g123H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x84000000003300,0x14030e500c4000000000,0x9c00000000140000000,2])
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
def g159D6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
def g175D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [4,0x224928a82,0x7a726a625a524a423a31,0x2921191109000e1de165,0x8560a5980926030b82d2,0xe0b8b82a161ee77542e1,0x993855321c6d5417e149,0x18737614eb750a5d43c2,0xd8b19c5ad8b1ac39e272,0x8e63585d76d07505db53,0xd077259741d8f4154176,0xd05501955450d7019543,0x5946550d75d05205c341,0x4826558520d055048161,0x5412050d504814350120])
def g175D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x290d216d8400,0,0x168200000000003415a,0xa6c2000000000000000,0x341a42bd42d41008000,0x401010099086c3283282,0x100b21008009d08b0,0x3602c0400708480c5876,0x827811c5848190440280,0xc51570610251030683b1,0x52159256f57d4f4fd2f4,0x7d0f3fcef364c329c972,0x1c7719c5711c3709c170,0x1bf6f9bccef3ace738cd,0xf362d232cc730cbf2ecb,0x72ccaf2aca4a7c96a428,0xc220839fe7a9d8701a46,0x3174591525092a461083,0x98ca2d09e2386c1603e0,0x90000dce012e0c0b727d,0xbb2a27dc9046e0835653,0x4eb91a85c0d8eca7c465,0x3ebb91e6dc0f16e48137,0x41bb2a465d1236e8743,0x72687b83435d9b1eeac8,0xb7275cb2391551c1aecf,0x1575780ba2ef5c5704ec,0x980764e2aa26fd8d57ec,0x6a0d7658abaacfd8d662,0xe0b0373305b918ed94a7,0x2ca55b702a4aa17650cb,0x5ae039f73196b8122dd8,0x4aaa80e370055ba8b099,0x4556ec1a976214ba90bd,0xd029ea814d540b1b9858,0x50c2cae2165610b2a885,0x9d0425eea02d7502eaa0,0x1dc9a4ae04514303f1f,0x2f579bc7e2ed73b8fb9d,0xae9f2f7cbd5e6f176b9d,0x9ebb3e9ecee733758354,0x59353d07505935050f50,0xd4f415974158341d8954,0xd8d50d05505855054550,0x50d50d4d439954359543,0x5514354d431954359540,0x5414050d40d5120d0520,0x99520595205852055120,0x545205412050d2050120])
def g175H5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x24133372000400,0x688388280233e9269601,0x3e300000009402680033])
def g175D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x90,0x3005aaa19cc467889120,0x6c81180863c0887de482,0x63f20917810d681c7312,0x2e213603cd84017a4200,0x3988f2c2b55288788920,0x617420ba136c0d6aa511,0x31d639bc21d64c4d023c,0x44807429f90ac84735ac,0x8b5e031d9c238e11f69,0x8a3249365344d284bf4a,0x1c6c8d5b60a5e564bb55,0xa89364226cdd0f72a1de,0xac902901ca03aa430220,0xc963d241108e442062c0,0xe11b0d58ac0011040483,0xd7f2bc2eb79be237bdb3,0x60d1f2ac5300bc6ddb36,0xbeac2a8a5a8e9f26f95e,0x488ee2a866087c1da715,0xb3699936097057d434b5,0x1a424f8390ce2fca9260,0x831ac530f42805400358,0xe8d60a3d8daf6263d818,0xd6493d91636528994a16,0x528194a360285808f652,0x3594995428d4ca1532c5,0x4d33537c54dcd6484552,0x21438cd060f6434d50d1,0x5438d8ce1433c584f151,0x3cd04cf651359459541d,0x5406e650b5942d640bd5,0x2d5401d89955422d810,0x96572581c3633550c5d4,0x309584255109d0429500,0xa5003fbf7efebe7dfcfb,0xf9f7efef6eedf54d4f50,0xd055454d515414350120])
def g175H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1152,0xe96540011a4100000011,0x28a6e00033408017699d,0xd4881d045f27c00a6844,0x44638a006816e460a877,0x5a029e4936a000003f61,0x1b09c240186d50d0733d,0x108018400a1803520000,0x1255b44,0x3651c8c4ac010b626300,0xd78035d03606167e2,0x31380335ac8387831ca9,0x9f2d50401c00441c0018])
def g175D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [3,0x480cd2032803200a0055,0x65006002a010f8812d,0xd084ade031fe416e8248,0xc004dac50e808428b308,0x821ddcbbbada09080736,0x64f39281200f54d54f53,0xd53d43f50d50d4024314,0x3951b41520910fff7df7])
def g175H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3807a80,0x3900000200,0x12f200000000000000,0x16004cd880002b8000,0x2d806e000000,0,0x798000006f8057,0x8000003b000050536280,0x48418000000047800000,0x7444002680670000,0x18000000,0x2e8900000000006d00,0x57000000110000000000,0x64806ada004b00,0,0x200000,0x50000000000000055ef,0x6a0006000000000061,0x36d18033e30020807080,0,0x348029b56c0005804880,0x800401000])
def g175D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x5a02013f
def g175H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x201c000a0001,0x12c0c2603a3799c00004,0xc0000000034000000143])
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
def g183D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
def g187D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
def g190D7 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x7f
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
def g235D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf624c3,0x25fba2c5a9cbf745953,0x29f6e0b2a656ddd15254,0x67abb6a598db77454b31])
def g235D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x2908000548402008f8,0x902f236d81d24561130,0x13c0899100c449cacce0,0x4a08eb2926a3e15ed9d5,0x510d8a0743c012c596c4,0xd2c75ec896c696ca12ca,0x22a62aa432a476a532a5,0x6c88acb3f7efdfbefef,0x6bf53d4b3154d5254532])
def g235H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [8,0x100000000000000,0,0xc000540000089])
def g235D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x8350ec33a4d430c,0xa69530e3baca540ce935,0xc338e5430d950a25849,0x38291a0b007fd4ffaa7f,0xf52fea97f4cbeaa3f731])
def g235H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x7009c80395,0x3202586303aaed580c50])
def g235D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x688817f
def g235H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [5,0,0x8000000000000000000,0x181da00000e000000000])
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
def g237D4 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x30d095539259171d49,0x10c7060f915c87254110])
def g237D5 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x92184aca,0x8cbbe0c712b283509541,0xd9caa0d88e6086130a41,0x2d7517a6aa0bd550c59a,0x70ea83b93561dc9aac95,0xd149daeaa63b935196ba,0xa850e444a32ca269d931,0x192ba084a5d03e82ca1d,0x17850d8ac286cc5d4369,0x2ca1b31740d0acbb29ce,0x5d91e70ec8ef836394b9,0xb145e0d86a2a6c32d526,0x5c986475d82ff07d0f,0x91ec3cc794f25e33c377,0xeb1d53a6745e35c5b78,0x6d8da5b33556a6d35a5b,0x46e78ce99cb3665ccb58,0xf31d636c6b8cf1762bc4,0xf87b0ee1bc2f7a2f25d8,0xba974ae65cab656aad1d,0x9ab2d63ac6d78ae5572a,0xd53aa734da9ad33a5d4b,0x695d27a2f3d26d4ce967,0x2ae4dc7c8f51ba1f43d8,0x770de17c1f60b7358750,0xe0974d4e205d164d4e20,0xe0974d46205d164d4620,0x61f54586206037255220,0x6137654e2061b7454620,0xe0954542206037355210,0xdd16454e1061d6454e10,0x6037154a1061b7454610,0x603725461061d6454610,0x6056454610e0d7154210,0x60564542105d16454210,0x59153542105d56450610,0x551515061020172d8550,0x61972985506017298550,0x607629495061f6294550,0x99373585505937358550,0x5907358550dcc6258550,0x60770549506047054950,0xe056218950e0d6118550,0x5c9521855061d658c520,0x60271595205c47159520,0x61b735452054a5154120,0x54a31541205497154120,0x1c97154120d8d5254120,0x54d525412059171d4910,0x59170d4910e0964d4910,0x61d64d491061d63d4910,0xe0d65d01105cd51d0110,0xe1953c811060552c8110,0x5cd51c811054d51c8110,0x4c951c81105c550c8110,0xe0d65989105974290910,0x5957190910e116590910,0x61d6590910e055490110,0x5895290110e095190110,0x5515190110607548c110,0x607528c110e0d658c110,0xe0d518c110551518c110,0x615218c110549218c110,0x60b735951020b7359510,0xe017259510dcd7259510,0x1cd72595105c87259510,0xe0964589105d47558910,0x61b7454910dd36454910,0x60b645491061f6354910,0xe0d7654910e057654910,0xe01765491020d7654910,0x61070549105d87054910,0x5c47054910a077454110,0x5d3715411060b5354110,0x593525411058f5254110,0x54a51541106064254110,0x54a42541106063254110,0x54a32541102156454110,0xdc96254110d4d6254110,0x21562541101c96254110,0xd915254110d8d5254110,0x98952541105895254110,0x1c95254110dcd5154110,0x54d51541105495154110,0x54d32541105493254110,0x5c872541105487154110,0x5d621501105522150110,0xe0d655011020d6550110,0xe095150110dcd5150110,0xd895150110d4d5150110,0x95151501102115150110,0x54921501104c92150110,0x61d654c91061d644c910,0x5d1534c110595534c110,0xd51514c110551514c110,0x54d514c11054d214c110,0x4c9214c11061d6548110,0x54950481106197510910,0x59573109105957010910,0xe0d6510910e096510910,0x61d6510910e0974d4c20,0x5d164d4c205d163d4c20,0x6137654c2061d6454c20]) else (word80 [0x26c201,0x28328200000000000000,0,0,0,0xc04000000b61,0x4058080301000000,0xb210,0xb210080017e,0x250000008b080006d040,0xc8580a6,0x8240400000f220000000,0xd41000070e800ae0812,0x1069048002c2e0210003,0x41591010160608b33e5,0xfcaf93f23e3fc6f8bf13,0xe1fc2f83f03dffbef7be,0xf3ddfbaf73ee3dbfb6f6,0xbed3d9fb2f63ec3d7fae,0xf5beb3d5faaf53ea3d3f,0xa6f4be93d1fa2f43e83c,0xff9ef3be73cdf9af33e6,0x3cbf96f2be53c9f92f23,0xe43c7f8ef1be33c5f8af,0x13e23c3f86f0be13c1f8,0x2f03e03bff7eefbdf3bd,0xf7aef3de3bbf76eebdd3,0xb99722e15bcb716d2d85,0xacb51692d059cb31652c,0x858cb11612c057caf15d,0x2b856cad1592b055cab1,0x552a854ca91512a053ca,0x714d29852ca514929051,0xca3144c8790b20e4007e,0xf81e63b674ce41c0370,0x6c0d41a0330640c41802,0xf05c0b215c2a8530a213,0xc26049c8f9082003e078,0xe31b634c630be16c2b8,0x5309e12c238410760d21,0x702a04c0780d01602403,0x80400400003ca4e325cd,0xe45f270233947b88c93d,0xd649e83728f64d94842,0x3ca4194e4e0dbb0b0409,0x987f29c93f14e49f4173,0xf8be847c5ec23e19641,0xdd9f0ef00b93806bcb4b,0x76426c8f25341391950,0x5c9cb87642648f25300b,0x939482b249b6dc5d4273,0xe807947303ca3b20645,0xba1f06da6d936f87c1b8,0x3f619c9fb0ce2b165042,0x3c90194e48082722024b,0x910062b24912e46409b2,0x122c5648f05c9c710e4e,0x308f2518f5858b62b246,0x93e4218ef2d0a7596853,0xdcac4a2e4a226b270f01,0x648a21ca27902513cab2,0x29c07944f5fc2262f211,0x30153096bf844b6839a6,0x83e6128132ebe0398486,0x1ba2482e4da44b2ad4c1,0x746a05c9b417e49b0c72,0x4d6bf84435fc2202de15,0x9770a82d0834105c9a3,0x926451986e88a0794440,0xbcc1f315d8fc47307ae5,0x843d76c19e82e4d6c532,0x4b887935e25ca2e8fe4c,0x2817260a09970756ba83,0xac5d4181730124f94082,0xdc98418e48200f282a03,0x951434ca9e1c648f1032,0x464fb633a74c1919ce44,0x8cfb265efb833040c918,0x2364cb9072472f983384,0xc916bee0cb103245891,0x94294cc994a8644a5332,0x65683932a7fc1953f618,0xd622a46cfd863388a91a,0x3e61895fb0c493f63243,0x8491dc46088a23046f45,0x623777c1944adcc9e82c,0x64f138226a2b1132ce14,0xc4132ecf21546610cbad,0x475d565c70eae2197586,0x8438fc0e10794b2630a9]))
def g237H5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x1c
def g237D6 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (word80 [0x16118550,0x5486154175d8d205c763,0x48176d4d205c35348363,0xd4520d875148176d4520,0x5c3514816598520d9651,0x48165945205da3148165,0x8c520546314837359520,0xdc56548370595209c565,0x48173595205c56548071,0x59520995614816558520,0xdd9534837454d20dc553,0x4816554d20dd95148373,0x54520dc1514836554520,0xd8d5148361545205d951,0x4816554520dc95048371,0x54120d91504836354120,0xd855048353541209c550,0x48261541209495048251,0x54120905504823154120,0x5d15048173541205c550,0x48161541205515048153,0x54120549504815154120,0x4c55048072541201c550,0x481654c5205cb6544175,0xd8d105cb6344175d8910,0x5d36244363d4d105db53,0x44172d4d105c35344165,0xd4d10d935244363d4910,0xd8b5244176d49105d352,0x44171d49105c35244164,0xd491058f5244171d4110,0x5935044162d41105cf40,0x44171d01105974044151,0xd01105434044353c8110,0xd432044265c81105d720,0x44171c81105972044153,0xc811054b2044151c8110,0x5432044132c81104c720,0x44173989105966244365,0x949105c6524416594910,0x59250441629411055250,0x4436590910d0a4244176,0x909105d6424417190910,0x596424415290910d5240,0x44352901105d64044165,0x9011058a404415490110,0x54a4044151901105da32,0x441758c9105c63244165,0x8c91054a32443548c110,0xd4a30441758c1105d230,0x441658c1105523044152,0x8c11054630441218c110,0xdcd654437259510dc165,0x44272595105cd6544172,0x595101c9654437558910,0xdcd62442755891099562,0x44175589105956244164,0x589101d5624437654d10,0xdc9534417654d105c153,0x4416554d10dd95244374,0x54910dcd524437154910,0xdc1524436554910d9152,0x4436354910d895244354,0x54910989524417654910,0x5955244164549101c152,0x4437454110dcd5044371,0x54110d91504436354110,0xd89504435354110d4950,0x4434354110d095044274,0x541109c9504426454110,0x98950442545411094950,0x44251541109095044232,0x541105d9504417454110,0x5cd5044172541105c550,0x44165541105915044162,0x54110551504415354110,0x54950441515411050d50,0x44142541104c95044072,0x541101c5504404254110,0xd954244363509105d542,0x44165509105494244365,0x50110d89404435250110,0xd4540443505011099540,0x44251501108854044165,0x50110589404415250110,0x54540441505011048540,0x443704c9105d93244165,0x4c91059132443544c110,0xd4930441754c1105d130,0x441654c1105513044153,0x4c11054930441514c110,0x4c930441214c1105d920,0x44175481105952044151,0x48110541204436510910,0x5d84244175109105cc42,0x44170109105944244175,0x8110544204412108110,0x5d35308164d4c2058f53,0x8373594205cd6508275,0x58c205d5630817458c20,0xd4d610815358420dd953,0x837454c20dc15308176,0x54c20591530816354c20]) else (word80 [0xaac0ff06,0xb078b9ac2aea6b0aaa9a,0xc2daa4b0b6992c0fb0aa,0xd78baab6d2a6adb6a92b,0x41f0eb31fc1acc8704b3,0x52b2ad1d2a4b415c3ac0,0x530eb060baadcf304b7a,0x8a92dcfb02b760baabea,0x2a4af3fc0abde2e2af07,0xc287457021c17c00701b,0xe1b1fc186c87041b52b,0xb06952ec19a8a9065e30,0x21278ba84407073b03c3,0xc552ae71526c2468a307,0x1a2ec0c68170f1044b26,0x483b019201c1e1dfac77,0xc2ac1398d306d62ac2b8,0xcaf06d983b1b660aa4e7,0x40b280d1ac8034cb180d,0x1ac97746b25d91ac9734,0x6b25c5eac9507ab2521f,0xac7487ab253deac94782,0xb151dfacb3e18c2b3936,0xc6cb01c1b180706688fa,0x985fec65e7eb19220ac,0x44701c19444f0e969eaa,0xbce706897eb288a92a6,0x20b09907973021213c38,0x4572ea1164ba045b2e61,0x172ba84162ea106ab984,0x3f8fd3f2fc3ecfabdcf6,0xbd6f53cef37ccf2fbcee,0xbb6ed7aeeb7aceafa7e7,0xb9de6f9ae5f96e3f8edf,0x37ade778ddb75dd370db,0xb6ddb367d7b5dd735bd6,0x357cfb3dcef37cdb33cb,0xf2ecaf1fc7afcbeaf6bd,0x2f3bcaeeb7adcb6edab5,0xaceafabdaeeb7abe9fa5,0xe7e9f67c9ee7a9de6f97,0xe3f8f63b8df7458b50dc,0xd62d437158b509c562d4,0x17358b505c562d437458,0x750dcd61d4372587509d,0x161d4272587505c961d4,0x170587505d35388170d4,0xe205935388174d46205c,0x35188164d462058b5188,0x154d4620dd1658837359,0x620dc56588174596205c,0x5658835458e205516388,0x35458620d49618815458,0x620549618837655220dc,0xd548837255220dc55488,0x176552205c1548837654,0xe20dd1538817654e20dc,0x5528837654620dd15188,0x372546205d9518816454,0x620585518815454620dd,0x95088353542205d15088,0x173542205c5508816154,0x22055150881535422054,0x95088151542205cf5484,0x171d52105c35484170d4,0xe105935384171d4a105c,0x35284172d46105c35184,0x164d461058b5184154d4,0x610dd16584373596105c,0x56584275592105d56484,0x173592105c5648435458,0xe10d49618437655210dc,0xd5484371552105d95484,0x37654e10dd1538417654,0xe10591538437154a10dc,0x1528437454610dc95184,0x37054610d51518416554,0x610591518415454610dd,0x9508437454210dcd5084,0x35354210d49508417454,0x2105cd5084172542105c,0x55084164542105515084,0x15354210549508415154,0x21050550841755061059,0x14184154506105454184,0x3544c2105d530841534c,0x2105d36254173d89505c,0x76254274d855094b6154,0x174d85505cf6154172d8,0x55058b615417198950d8,0x66154352985505ca6154,0x1629855054a615436294,0x9505c6525436494550d8,0xa5154361945505c25154,0x37358550dc1615436258,0x550d4d61543525855099,0x16154262585505896154,0x15358550549615407358,0x55018961543705495058,0xd525407054950dc15154,0x3635455054d515417118,0x9505886254174185505c,0x86154164185505886154])) else (if j<3 then (word80 [0xa4b25c1,0x12cc70a4b24c3159a6e8,0x5669ba124ff024916c21,0x8cff024f24c21825ee66,0x24c1180c3045ea7b992,0xc70448aac0921c6e648,0x96b19205d0e5c16c3970,0x930c5c1743915c6e6459,0x7b1914ff02453ec0964f,0xf024e3342108cb08423a,0xc1909dae4423ec090893,0x85f55ba17cc30a573ac,0x195e270a4a8842928970,0x84a55ba12897064a89a9,0x92a22a64a99b912a60e4,0x4a31c292986e85d89b21,0x7622c85d30c197626c65,0xd88b197626c45d88b117,0x4930c5530c295662c455,0x3ec095586e84789b211e,0x22c84731c191e26c6478,0x8b191ea6e447a83911e2,0x6c447a93111ea2c447ab,0x4091eab024798b111c5d,0xe5b16c396c930c5b24c,0x314cc30a53a8a914eb68,0x4533ec094c930c44a8a9,0x1105d0e4016c3900930c,0x4030c2900eb06403ec09,0x930c5230c294aa2a45,0x23ec0948930c4330c290,0xe5ec643a6a990ea2a443,0x78ba188fb066278b998a,0xaaa6623ec1189e4e462a,0xaa9188ef064d3ec1106a,0xaa44179ba1526ac8543e,0xc11526ac454aaa9151e6,0xe6469bb191a6ac646aaa,0x9918ff04469bb111a6ac,0x446aaa91193f065107c1,0x1447f064c1bc292c6f0a,0x4a51b912a12c44714c11,0x881f0ebb42baaec7708b,0xb1fc1aed3acabd62aa2f,0x54acabc66aa2f0570eba,0x14c3ae97aeabaa0aa2e9,0xbae6ba60baae4cf08b97,0xb9ae5e2e2b978c0a6d5,0x70e9a97c1a6897049a24,0xc327582ea9d3ec0a7582,0xea983fc0a60970a9954b,0xaa645b0e9c24c327182e,0xa9c3ec0a705f0e9724c3,0x25d82ea9798b125de2ea,0x96abaa25aaaa8963fc12,0x5a6ac49624c10e8cb083,0x554438ca4f083292420c,0xa5f063296418c8970432,0x25c08ca6f023233c20c8,0xef063224c28e552ea393,0x3c20c45b0e3824c30e18,0x2ea3832c20e0fb023817,0xc38c182ea3016c38dccb,0x8373ec28d1e6ea3478b,0xa8d1e6ea2f78ba8bebf0,0x82fae420beaea82faf2a,0xbebaa82f3fc18bde6e6,0x2faba98beaaa62f3fc10,0xbe6ec42f33c20be8aa82,0xf3ec28cde2ea339ab28c,0xebaa83378ba8b66eca2d,0x9ab28b6daa42db6990b4,0x7708321fc18ca82a82f3,0xec08d8930c2e3fc08b85,0xf088e55c3a325f068c54,0xb2a345b0e9024c3240fb,0x29016c3a2da2e88b3fc,0xa2c5b0e8f24c323d82e,0xa8f3ec0a3c5f0e8a60ba,0xa29e2ea8978ba226aea8,0x89aaaa226d706893fc12,0x24ff0a883ec2a21e2ea8,0x89ab2a22daa48817c209,0x9c7062679c089a5f0624,0x9bc08905f0a2554b2895,0xe7022516c38a0930c283,0xac18a0fb022816c388da,0x2e8233fc088e5aca2270,0xba088ef0422b4c08885b,0xe2724c309ceb06273ec,0x89c5f0e2170ba87e5ac,0xa1f70ba07de2ea2078ba,0x82aea820aaaa082d2a6,0x203fc1082d264203fc28,0x78fb0a1e78ba87a6aca1,0xe78ba07ad2a61eb6a907,0xada841e17c1ad5e302b5,0x16c3ad8f304b617c3acc,0xef06b33dc12cc5b0eb83,0xcc12e0fb02b816c3ac89,0x70cb270b9ac9df0eb13d,0xc1ac5dae6b1b6c0ac4f3,0xaae76baabacaa6ae78b]) else (word80 [0xc0595230,0xf707cc2dc122e9701ac3,0x5b9f2c96e42b2dc922c9,0x7217c05c942e56f54b25,0xc552c5711bc25581b0d5,0xa4943d55230f557d42d5,0x5f30b5590c0d5526e955,0x1ac355df2c9571bc3550,0x6b0d547cb25501b0d594,0x2b2d6522c95916c05645,0xb095817c051122eb431d,0xc3508730d4286b2d0642,0xc941a0aa504ff014124c,0x254c93075324c154c5b0,0x75225c3538f7054e92c2,0xd2a4b074a92c0d2a4ae9,0x4a92b25245b095125c35,0x364ac94d88b254226ed4,0x888b25224ac94896b1d2,0x970d4c92b253222c34f,0x89bb51e4ac94798b151e,0x4ac94b3bc1d2e4ac9469,0xab0d1a4ac94555c34fc5,0xf093f16c3d00930d403a,0xc1d025acb3e07c234d3f,0x4874f4121d3b04874e4,0x121d3f00874ec021c1b0,0x48797c021c97008306c2,0x2181b06864fb9a1938e6,0x861ec1a113ee68451b92,0x108b028424c021077088,0x21c422087f06824fb9a0,0x938e68223c0a08970082,0x4fb9a0542e48124c2214,0x93068597b9a1658e6859,0xbb8a153ee68571c021dc,0x6e68579b8a153f06d207,0xc13481f0ad107c23453f,0x6cd07c13360706ca4fb,0x1b305f00cc17c232c1b0,0x4784fc19d81f047655c0,0x1da07067489c01d07f06,0x7406c31dc53027716c01,0xdde2e27507c23401f0ac,0xf42baaac7f06ab21c12a,0xd3acaac06c1a010eea7e,0x22c09f87f067c23c09f1,0xaea791ec19e41b0a7f0,0x6c21fd0eea7d20c11f50,0xeea7b1fc19ec87047b21,0xc11e81f08c607c1b193f,0x6c64e41b183706c615c,0xb141b0ec907c3b081b0,0xec248ba3088704c206c3,0xb201b0ec14eb9b046b0a,0xc753b23114ac8c415c1b,0x114ec6c452b1b114ec4c,0x417c230d56c8c354b230,0xc5f06c355b1b0d52c6c3,0x55b130c8304aa1fc1aa0,0x8704a853b2aa54acaa90,0x6c21cc1b067306c01cd0,0xf0a6807c19a13f06684e,0x419a01f026853c09a157,0x680bc21a03706681dc,0x21a07f066820c11b87f0,0x66721c119c1b0c7214c0,0x9c81b0e6d49ba1b48304,0x6d07c3998c3006a06c31,0xc453027106c39b13ee66,0xc20c11b06b0a6b36c19a,0x45b007055431bd56ca6f,0x54b29bc5b086f16c19bd,0x56c46f79409bde3026f1,0x4c09bd54ec6f54bb1bde,0x4e26f78b89bd52ec6532,0xc2194eb066578b89941f,0xaa217c02841b0ea407c,0x3a7c1b0e9f1dc227c7f0,0x69f50bb27a36caa38cb2,0xa8d4ecaa052b2a81d2a4,0xa007c30f45f003d06c38,0xfc1f0e3c1fc18f01b0e3,0xe9caa0ec1f0a17434305,0x90b0c1660c00581b0e18,0x42ba8601f0e1306c384d,0xaea131fc184c8704134,0xfb28553aca1555b28515,0x2ca1407c2a545f009407,0xc3a481b0e921fc1a4942,0xec913dc02454aca9374a,0x924c1f0a2b07c20ad570,0x2b07c38a81b0e2a1fc1,0x8a81f0e2906c38a48704,0x2916c28b05b082c54b20,0xb06f0abf1bc2af942e4b,0xe52b23005704c052b130,0x1570ea768ba294ff02a5,0x55c3a985b06647940991,0xe302643ec0991a6e85a3,0xac1968fb025a3dc1140f,0x104503fc094093046130,0xc2960eb065889c292e21]))) else (if j<6 then (if j<5 then (word80 [0x2e1325ab,0x94bc8b053386a94cd26e,0x9231ec1c8d3ec9284f32,0x4a13ac92871c04a13ec9,0x1e4eb24795ee72557b9c,0x8206c7204fb9c993ee72,0x251b94893ee7210743c7,0x475091d1cc24747b071d,0x4fb9c74250f2457b9c91,0x5ee71f5bb947dc6e7277,0x39c9c5b011407c3c488,0x7051216c044c1f0f115a,0xb943d4f0f1095c1c414a,0xe51006c3cb01b0f2b50b,0x94ac8b092a22c14aa1aa,0x52a55b24a582a5294fb9,0xc6206c71716c24645b07,0x1960a9c645b051960a94,0x641b079f06c0e7c87059,0xc06c26781b099d1fc1e6,0xc1b079406c0e501f0790,0x51c16401f039006c364d,0x22c99316c064d430d925,0xb2e4843039276c06494,0x2ed928cb2648f3019206,0xc36445b019177b963c1b,0xf9a1ec1e6893019a21c,0x16644705a706c3e9522e,0x9a554b26981b098e07c2,0x6301b0d8d06c362c1b0f,0x9822c0e6093019823c0e,0x588b039724c065c97019,0x511c16901b0fa248ba68,0x9f2c9a006c3e8552c9a3,0x54b168c1b098a07c261d,0x3f07871fc1e1c1b0d894,0x9ba619f2c98416c06221,0xea98586aa6154ee58524,0xc260c93078324c0e0c97,0xd813dc16064ac97d3dc,0x15f4970d8088b260a26e,0xd7c88b25f25ac77c98b1,0x5ec970d7f55bb5fcef07,0x7f55ba5fa26a57e88a95,0xfa6ac37a06c24001b030,0x21c13f09700fc06c1bf,0xd4ee2fd24c03f47f06fb,0x25c03ed4ae2fa24c23fa,0x66e4fe55b8bf9dee4fe0,0x7c0c381f0b0d07c24301,0xf030c17c242c1b08f706,0xc0bdc7f06f406c33d843,0x4f606c33d44304f542b,0xac188f030643babe50ee,0xaf807c1c201b0f0a1ac2,0xc245f090755b241d56c7,0x760a9c1d56c30722c0c,0x148f030406c1bcc3706e,0xd1fc1bb48b02f023c0bb,0x1b0cf206c3bbd3ee6ef,0x22c0bbc6b0aee10c13c4,0x1f0b0307c3c081b0f021,0xfc1c094aed0107c3b50f,0x704df24c0ba5a6e8db3d,0xc13789302e8a7b9b6aa3,0x4da76ba3acf306eba8a,0x9baea10ed9a9c1b66a30,0x6d9a9b9b66a2e6d93dc1,0xb6666c6d9a8a9b66a2a4,0xea3cc1396a2a4e53bc1b,0x74f704dd7639376a2a4d,0xda8a935666e4e798a939,0xcc30ae4a8a9390c70adc,0xa8a9370930ce2a8a938a,0xa2a4d824c3384930ce0a,0x8a93829aa6d7a8a935ea,0x700d9a8c03646b080c1b,0xc202e27000b06c20307b,0x80a1fc20265f00091fc,0x28213aea0842b283c470,0x40f48c38381b0e0e48ba,0x393ae80d06c20141f08,0x206c30110aca0449438,0x5230e018ac180526e80,0x14fba001530c0354b280,0xd52c80354bb00e22ca03,0x92b200e5ac60322c201c,0x8f080606c1db41b096c1,0xfc1dac73076a1cc0da87,0x707691dc0da4770b6848,0xbada0770b6748bad9d22,0xc97948b25e01b076407c,0x1d841b0d6348b258c5b0,0x16348b25885b016206c3,0xd987b076624c0599230f,0x7506c3dd522e97554b25,0xd81b096007c25781b0d5,0xf16c057d250f5d48c3d7,0x62b075d49ba5750acb74,0x48b25d10acb5c48b2571,0x42c55c16c0571530d5b5,0x4b2d6d52ed5b88b2d6e6,0x2c55b06c3d948b036524]) else (word80 [0x68959456,0x3157b55cd569556d54f5,0x50153854c151c545150c,0x54114f753bd4e253594c,0x852f54b152a549f52454,0x8851fd47551a145f5151,0x44850e543150a541d505,0x540b4ff53f54f9d3df4f,0x453c34eed3b34ead39d4,0xe4938a4dfd3774db5365,0x4d753554d213404cd532,0x64c793164c293024bdd2,0xe94b752cc4b092b74ab5,0x2a54a7528b49f927649a,0x125c493524548dd22c48,0x9121c483520147d51ed4,0x7951dd47551cd46fd1b1,0x46a51a14651189460517,0x445b1164456514f45191,0x3b44b9126446510a4409,0xfa43c90e643790d0430,0x90b2427908641ed07141,0x9d05c414504841010314,0xa501e40450033fd0fe9,0x3f58fc73ed4faa3e84f9,0x93e2cf803ddcf633d6cf,0x533d2cf3f3cdcf2b3c7c,0xf173c2cefc3bd0eec3b7,0x8ed33b10eb93aacea33a,0x58e8b39d4e683974e523,0x900e3438b0e24386ce12,0x3820df537b0de03758dc,0xd36f8db036a0d9b3638d,0x8635f4d7535a0d5a3548,0xd3e34bcd263468d0e33f,0xccf733a0ce0334ccbf32,0xdccaf329cc9d3238c863,0x1e4c6d3168c513124c3f,0x30c8c253074c153034c0,0x2fc8bea2f70bcd2efcb,0xb72ea8b9e2e44b832dec,0xb6e2d84b572d10b372ca,0x8b162c18af92ba8add2b,0x3cac72accaa42a30a7a2,0x9b8a60294ca4628e0a30,0x28a0a202834a0527e49e,0xc27789d1270c9b026889,0x9a263097d25749542530,0x93f24c491e243090223d,0x88ea236c8d3231c8bf22,0xc88a3226c893221c87f2,0x1dc86f219885e213c847,0x20e883220a4821204880,0x51fd87e81f787d31f2c7,0xc01ed07ac1e787961e30,0x7801de07701d847591d2,0xc73f1cdc72f1c687101c,0x106fc1bd06ea1b606ca1,0xad46ab1a8c69b1a38686,0x19e066a1988653191063,0x5188461918105eb178c5,0xce17105bc16c85a3166c,0x593162c57d15d456d157,0xc552152853c149c51b14,0x344fe13d84ee13984d71,0x3204c012e04af129c49f,0x125c48f121c47f11b846,0x116044610e843210a84,0x1c105040b100c3f60fb8,0x3e50f6c3cb0f0c3ba0eb,0xc3a40e503880de43710d,0x9034c0ce83280c5830b0,0xbf02ed0b942d40b142b6,0xa9029709f0269095023,0xf08d0227086820d07f41,0xec076c1ca06e41a70654,0x18605ec16e0584159052,0x413804b011604380fe03,0x840d3030c0ac024007e0,0x1b005a01200360090012,0x1b07b406c0ed01b0,0x9b306c0ecc9701b006c2,0x6c81b07b220c16c49301,0xb11dc26bc1b07ae06c16,0xb88b03ab06c26b41b05a,0xd06c26b01b07ac1ec1ea,0x88b03aa1dc26a47109a9,0x1fc1ea01f073d07c0cf4,0x1f093c07c0cf01f093b0,0x7c1ced3f073b4e41cec7,0xf073b0dc1ced46c53451,0xc3c5487031578c04585b,0x11620c0cb946c52d2dc,0x146cc3091c30c1c72a6c,0x51c30c0c70c50d1a30c0,0xc685b091c16c1c705b03,0x1c1ac2ce87b073a24c04,0xe81f073807c14e01f093,0x707c14dc1f093607c1cd,0x957013654404d8970136,0x6c3ce497013550c34c5,0x6b0b3151b24c5db01312,0x3c0cc0230f325ab94c98])) else (if j<7 then (word80 [0xda7b67ed,0x97b63ed87b5e6d71b5a6,0xd61b55ad4eb4fed37b48,0xad13b3fecf7b396cd0b3,0x22cc0b2e2cb0b28ac94b,0x21ac78b192c5cb152c46,0xb0e6c2bb076c12b02abf,0xcafc6be9af6ebd0af22b,0xc0aedaba8ae6ab90ae1a,0xb77adbeb60ad4ab3dacd,0x6b2dac82b12ac16afdab,0xd6aedab96addab56acda,0xb12abcaad2aacaa92a9b,0xaa4ea8baa0ea7ba9cea6,0x6a97aa56a93aa42a8d6a,0x2da892a1ca852a0ca812,0x9fba7ce9e9a7869d5a73,0x69c1a6e29b0a69e99ea6,0x5a98ea61a97ea5d696da,0x59695da546948a502934,0xa4b2920a45e908a4028f,0x8a3a28dfa35e8cba30e8,0xb7a2be8a4a272894a232,0x880a1e286da18a85aa12,0x2840a0e2830a09e81ca0,0x428089ffe7f29faa7e29,0xf667d19f227c09ee27ab,0x9e8e7969e3a7869dfa77,0x69dba7669d7a7559d267,0x409ce272f9c9671d9c56,0x70c9c126fc9bca6ea9b8,0xa6da9b4a6ca9b026b69a,0xba6a69a7a6959a3267f9,0x9de66f999265b994a64a,0x990a63598b6622986a60,0x797fe5f797a65e197565,0xc796e25aa967a58595da,0x563953e53694a651e942,0xe4f693a24d9932e4bf92,0xc649e924648391e24709,0x18645590e242c907e412,0x901e3fc8fbe3e78f6a3c,0x78ee63ad8e9639c8e423,0x848df23738dae3578d2e,0x3438cde32b8c8a3168c3,0x23048bee2f38bae2d28a,0xfe2b68aba2a68a7a2968,0xa3628489ee27389ae263,0x896e253892e24388ee23,0x288aa222884e20087ce1,0xeb878e1d987461c98702,0x1b886c21a3866e192862,0xa18285ea17185a615f85,0x5e148850213784a611a8,0x44610984060f983c20e8,0x837a0d6833a0c582f60b,0x829209b824608982060,0x7881c206881820588142,0x4780fe03280aa01b804,0xdffe7fd9fe87f55fcc7f,0x11fbc7ed1faa7e6df937,0xe2df827de9f727da9f61,0x7d51f4a7d09f347c99f1,0xe7c59f0e7c19efe7bc9e,0xea7b6ded37b01ead7a89,0xe957a35e7f79dde6b797,0x5e507915e3d78c1e2878,0x71e0f7801dee7799dd77,0x731dbe76c1da87681d98,0x7641d887601d7875c1d6,0x87565d517525d3c74c5d,0x287481d167439cff73d1,0xcec7391cd67335cc572c,0x1ca5725dc897201c7771,0xbdc607161c507109c347,0xa1c207045c036fddbe8,0x6f81bd86f41bc86f01bb,0x56eb5b986e39b866dedb,0x736da1b546d1db3e6cc9,0xb296c7db0b6c0dafb6bc,0x9aea6b89ad46b31ac46a,0xe5ab16aa1aa06a61a906,0xa11a7c69cda6a6989a59,0x6941a486901a3468b1a2,0x4686da13682d9ff67d19,0xec67919dc67459c566f5,0x9b266a99a2665d98a660,0x197365a1960656194d65,0x1593964b192064619066,0x3f98f663b18e3636d8cf,0x63058b962c18a7627d89,0x7623d88761f987661b58,0x616161850612183d60d5,0x82d609581c603d8075ff,0x17f35fad7e15f657d15e,0xfd7b55eb57a55e757905,0xe0977a5da17605d41742,0x5cd972a5c5d70f5c156f,0xd5bd56e95b856d95b456,0xc95aed6b35a8969a5a49,0x6885a0167859c1668595,0x964e5919632587961258,0x195f857955cb56c95aa5]) else (if j<8 then (word80 [0xc06c84,0x18080003019a0a03161,0x6020000c0402c87ac364,0x200bc2100002020100d4,0x1b604000201000000000,0x80007504020000c0400,0x396100602010040,0x400007a424040000022c,0x30c0800f48401a2849b0,0x990990e3d82004040003,0x50400000001361008d31,0x2020000000098b10,0x61aa183841590d90d,0x6447ac8c5e0a83841f41,0x80004b0201a74200406b,0x22d41070200011f4c400,0xb4100cb0d90d302c,0x75040101a6040201407,0x2c2016026424e040000c,0x8401012d8400b61002d8,0x4b610000008d85808030,0x10040400000068200c05,0x1c080004a0805218d84c,0xb748480b014040002b0,0x621a08016c32831c8800,0xb6160200000e04c84c84,0x3610d84000,0x22c2c0403ac20000c050,0x100b011a08045855c080,0x4a08063038c0c8a1,0x5a0c16078b1b01405016,0x2c0402000e040180c58,0x4b613c44c07b0b10381a,0x85898080403361602018,0x7e820000009410094194,0x100941270200001b0b01,0x8702c0436100eb0b01ce,0xe18f682c0580f70c5a82,0x100a025d18803a8,0x2808072d0db02019619a,0x80004026838c08013a4,0x16b81009909908b81001,0x70201561cf8620000004,0x45c0805584c853cb100,0x40101ab0cd0400000268,0x36c0805b022e06d8100c,0xb0990cd06361001a0cd0,0x5014f2c43419a09b0c14,0xd210d04f114d0618100c,0xf262b70299e4c754b119,0xc3033419a0c30200000,0x10f60800c86683ec08d0,0x53618d2c4db08026c3f6,0x863d8561940201341860,0x53cb1370c480990ea0d3,0x8100d41001a093810000,0xd4100000000803b81009,0xa08000401dc08d069c08,0x6c280d2100a42642016c,0x80203a8200007888033,0x61d410000660c1203a82,0x80d42c52c0ad8d0d,0x100009a08056c21b080,0x3b813c454e05b6d88009,0x37044c348300166c1202,0x808381000000cd8400,0x23611a08036c22cd823,0x216d865c08000001b813,0x70200000100000000000,0x8d3106c201d83119080,0x66c20001001a080005,0x19d420000b016032284,0x6424e0403683896d0724,0xa1c928724a1d216702ce,0x4009a47310a4a149886,0xb411fc92881bc8c1cd04,0xe682a43161eb0f58779,0x956844d232691aad0a4,0x9439250ee91521eb0f58,0x400790abac4605b2a220,0x2f21365861923615e42,0x1ebc879cb4cc9bf216fc,0x85bf216fc85bf216fc85,0xbf216fc8486118850aa3,0xc1d0d192112838ca40c0,0xac148917308336462c1,0x484a1a2c8a488360a88c,0x8c00ba96034121e04181,0x8a04001e0d0589026810,0x4c1810c3c2a024a040b0,0x480e4108888061501018,0x200500803029c087015c,0x37005bff6ff5bfb2fe4,0xbf72fd4bf32fc3beeefa,0xebe9af9cbe52f8bbe0ef,0x7bbdcef6bbd8ef57bd3e,0xf47bcfef33bcaef23bc6,0xef13bc1aefebbbeee4bb,0x62ed0bb0aeb3ba82e94b,0xa1ee7bb9bae66b97ae56,0xb93ae46b8fae36b8bae2,0x6b87ae16b832e03b7eed,0xf3b7a6de1b736dbeb6da]) else (word80 [0x2c84,0x20000000001,0xcb0802020001000000,0xb21000000d410000,0xda08045a16036420,0x1cc0cda1ccec52835619,0x41da0800000000000000,0x2020100004040,0x31a6099c08045a100000,0xd6040000029080738,0x100a22d133814658200e,0xd58b9d90400000001711,0x4b032c0cb032cd040001,0xac0d587581d605808016,0xc2c0403581a42000080d,0xc45ac0a0280b38100d34,0x3ac0bbb2080002ac25b0,0xd5840000000000000002,0x10000000000,0xda0800000590ed040002,0x10040403504,0x3504020001008000000,0x4000002c840201a82,0x1a8201f342000047420,0x10094100941006020000,0x128200c058080070c40,0x160364200015a0,0x800000400020001b4100,0xda080000000000000007,0x50402000140400000200,0x808000000000202808,0x4039610000602,0x1008000658401808054,0xb620000ad8402507981f,0x7035b0ca0a7e018e0d0c,0x6562371820c35b1ad058,0xc65629305116c3ee04b,0x613210d869991ed04361,0x60201d684c84bfd90c96,0x43b41ab0b01603b4100d,0xa0ce443680ec84000364,0x3642000100cc362b2100,0xb21b2100d90804000100,0xfc031f47620080000,0x402010000000000,0x80006da12e0c,0x53410000008000002000,0x3410000800000004010,0x10038440001cd851c080,0x40000000200808000004,0x683a82014040000020,0x1001a0801c,0x2200961c10066c32a608,0x2000000809b81000000,0x800000007ac280805303,0x4c080000000004a08023,0x810095304db589808d04,0x2b6100941ad87ac2c04,0x368201283d61b2441c3,0x10013816034c0d6c2000,0x12e040,0x32c348402008080138,0x1a4200012c0804001db0,0x5486581b604020100e34,0x200011b0c6c2642012e0,0x6361321db42000000000,0x148403dc504808052100,0xa433328756100d908050,0x1f748200000080004b02,0xc040002000001642,0x10080004020001a82,0x10000d416020000])))))
def g237H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x170982760a941e806144,0x630b6000311701aa2121,0xf00644049311c27d2a8,0xd1310010208034809321,0xe420e03be1d508bd0b31,0x22889504802190370000,0x9004000885,0x3e000160b000203de0,0x4000c18b02d00005100,0xad90de46e81c207f,0x805a37741f8000847502,0x42dc00002cd21a807b4,0xa0d1a00af02a00150003,0x153808881e103000044a,0xf0ac0134000000203148,0x9c000000212a00000000,0x140200000000000000,0x84000042d4000c11702,0x30000000428500f41a60,0x76000140a02fc00008dc,0x1098426e209000,0x314a5c0c01c02a90baa1,0x38000000105100000008,0x7c0000000324c8a473f,0x4267154000173d010b03,0x6c19f28c000000000000,0x7c91180638cb92000001,0x17000073ec258095884,0x508441c405fd03c11300,0x25cd82400096b008d0,0x6873a526f04c,0xd1bc0000000000000200,0xc046909c803800000980,0x502644580500000000,0x1760380000000c0a,0x61230000000014c00081,0x680028024000000204f8,0x2ed09484e505582d1007,0x1092029f10981ec01,0x3903400051d7052d0200,0x57c28a05983040000000,0x901a119c0405094c8,0xa0a0898c000022601b41,0xf6111001208841cc2260,0x20500000221,0x52f080bc0b903a803746,0x6e26c0000003234425e0,0x460003416010c00002c0,0x69fc293415402b0bc82a,0xc0008101601000105c58,0xc000423908fc0ac0000,0xa03c00054cf228,0x1028000341e00ff06,0xf000027d41dc00012fb0,0x7448cb21f000000041d7,0xc09d0112dc16f204c13,0x80000001039c16000001,0x78259829444282f64670,0xcd006c087121,0xc104000000022241b301,0x8800e0794230000c2c80,0xc1ac000c1804328e32,0x4744b0019cd4f43b605,0xa326d2f506e000373b8c,0x8c02f000000012930320,0x527c1b4c5d4000,0x9c000c15303502e30a,0x6000000000010a3827a4,0xbb613631f54480788c9d,0x8a4204444821e090145,0x364ac21528a11a50725c,0x1000bc01509191c4407c,0x11095a0c830684969513,0x82ba080cc7443040b10b,0x94077025055646500020,0x2a0000000c24c0088128,0x419400040f0000000,0x309a000006d0000056ce,0x28958019a405012f2238,0x4704942f800082c444d,0x20305039441f9dac0,0xc17400583841010d001,0xc00101524c7c50460910,0x80014041c00c4440183,0x1115c4ccb0d10050402c,0x58430111871480041410,0x104058010880d0003c1])
def g237D7 (j : Nat) : Nat := if 6 ≤ j then 0 else (if j<3 then (if j<1 then (word80 [0x905766ab,0x6a2d41dd9782bb2c1d73,0x5852e0b015d9990b9382,0x9756856e8b92d91725b1,0xae5f535cbaa6b9edc973,0xc392e5f525cf4a4b9e54,0x9725b0ae05765c46e4b9,0x5549719b98931731266e,0x224c5c4483b989077112,0x7cea20f5d441eba08057,0x61862ca30e99061cb20c,0x3d63180eec1815d8318b,0x2863a640c72c818f58c3,0x15b8064753148aa62919,0xd43a2ba8747530e8aa61,0xc15d8598b28b3e63167a,0xc62d1584583bb0505760,0xa62ca14f98c29eb18545,0x610a0ee9541dcea83b95,0x53a75a872eb50e5cea1c,0xb8d40576b472c968a5c2,0xd03bb510576a272c9441,0x5dac98b2d93a64b272c9,0x64a5c2c83bb500576a06,0x2cb40e99281cb2503d63,0xa00aed60c596c1d32583,0x964b052e1601dda782bb,0x4f31659e74c93ce5927a,0xb14f2b709e62cb5ce99,0x2b9cb2572970ae62cb38,0xe99271cb24e2b709c72c,0x9312dda695ba4d49649a,0x56e735258e6afa9cd5d5,0x39a92c5357d4a6aea94d,0x29759692cb2db54e594b,0xad67952ac0ae4ac1dccd,0x9fb99b3c73360ee46c1d,0xc0da5b81b1f73360aeaa,0x815c9502bb283165507e,0xc6a0a5c1403bb1905763,0x262ca64f58cc82baa905,0x74523ae6881dd4d03b99,0xa05764e4ae29ca5c1382,0xbb215752424ae2841dd8,0xc02bb182b70300aec445,0x9d088aba111d73224ae2,0x44a5c0882bb1f67423e4,0xae27c15d88073a900d75,0x203ae640a5c0802bb1d2,0x5713a0aec50adc0a12b8,0xa629754052e881259102,0x4b1202b742e96c85d259,0xb95b9974b632e92c65d,0x7d4cbaea9974b622e92c,0x45d7d48baea91783712f,0xe25e0944bc0a897057,0x62e4ee25c75cd292b8a5,0x29753c92ca78a5d0f24b,0x11e81513c96ca552594a,0xa5b11582512b02a25608,0x84ac0909529753892ca7,0xa5d0e40a89c81213852,0xea4d2594994ba136d532,0x6da644e05449c0909329,0x754852e691e54923c992,0x481514902629095c5202,0xbb1229751f02a23c1dcc,0x103b90205760862ca101,0xdd8082bb013165027ac6,0x415d8198b2830776000,0xaec00c594020b1005152,0x5c6ac9340dccd84ba8f1,0x1741e32e63dd4847ffbf,0xbfcfdfebf1f7fb7bfd7d,0xfef777b7dadfefb7bbbd,0xbebf5d9fbfdfafb7bbbd,0xdadf6eafd7a7f3758b50,0x58750d5220d4e20d4a20,0xd46205962058e2058620,0x5522054e2054a2054620,0x54220d5210d4e10d4a10,0xd4610c82105961059210,0x58e10586105521054e10,0x54a10546105421050610,0x4c210d8950d8550d4950,0x98950985509495094550,0x58950585505495054550,0x1895018550d9520d8d20,0xd8520d4d20d4520d4120,0x99520985209452094120,0x8c520595205852054d20,0x54520541204c52014520,0xd9510d8d10d8910d4d10,0xd4910d4110d0110c8110,0x99510989109491094110,0x90910901108c9108c110,0x595105891054d1054910,0x5411050910501104c910,0x4c110481101491010910,0x81105885058450d4c20,0xd4420984205942058c20,0x5842054c2054420d4c10,0xd48105941054c1054810]) else (if j<2 then (word80 [0xae89535d,0x16e4ba25c9745b8ae8a7,0x15d12e2ba21c574530ae,0x89615d14a2ba25457452,0xae89415d1462ba24c57,0x26b2ae7d525c5ee2b935,0xcc4a6b8892d74189ac83,0x135d8326b2862f740c9a,0xc81a2dc0326bb054d650,0xa9ae95535ceaa6b9554d,0x71aa5ae768b5c6d26bb5,0x14d65a25ee744bdc68c4,0xb8514f54a69aa94cb5d2,0xca6b2594d76a09acb40b,0xdd2826b2508970a05ae3,0x6135da7a6b2cf2f719f1,0x6e13d3d4a916ba574d64,0xaec2a95cb5caba6b1574,0xd659c5ee9393592731aa,0x4e61549c5ee539358a71,0x6bacc4d6598d2a932154,0x6644ba4d89549b12e736,0x254e6c4b94d89529b12e,0x33625466c4a0cd8b5497,0x12a92cb5c91a7b99b4d7,0x3369ee46d39c8da6b91b,0x4c72369ee06dcdccd97b,0x91b8b70365ae4a135d8c,0xa6b2992f723312e064b5,0xd5126b2a24f75349cea6,0x935d4d263a9a4f73349a,0xe668bdd4d27329a4d653,0x45ee8693590d16bb272d,0x744e9ec89d3591396b9a,0x74f634e9ac69d3d89396,0xb8a72d704e5aec84b5d5,0xa7b2a14d6542fac484b,0xdd8c273b182d76309aec,0x613d94c26b2982f74309,0xec8613590c31aa186154,0x305ee6613d8cc26b1984,0xf6230fcc461f588c17b8,0x988671310ae260bdc0c4,0x5b8188870305aec44b5d,0x8f96ba9f4f653e9aca7d,0xf548f96bb162d752c9ec,0xa593594b27b1964d632c,0xfaa458b5d8816ba904f6,0x5209aca40b5d4ea6b29d,0x7d523a9aca513590a16b,0xa264d644c5ae49935893,0x30a92689544112a4822d,0xd0bc53a1789742f10e85,0xe2990bc4b2178a542f12,0xa85e2dccbc4b99789532,0xf16865e250cbc5b9178a,0x722f12e45e21c8bc5311,0x789622f14a45e2548bc5,0xa1178a422f12845e2108,0xbc5191789322f16e25e2,0x5c4ba6b2972f742e9ac8,0x5cbdc8ba6b11763522ec,0x2a45e1544b96baa54d65,0x4ad2a89615452c4a8258,0xb543d12a87a2d48f44a9,0x1e8a652b12ca562588ac,0x5a91589522b12645625c,0x4ac5a89589512a9aca56,0x1544ac5a81589502b16a,0x8722550e45a91c895239,0x16a84e25509c5a913895,0x22712844e2995244b2a4,0x8b534912a690b5d5226b,0x2a47d52490aa2922d412,0x44a8242d75249aca49f5,0x48942a8928950249ae60,0x935c8126bb014d65029a,0xec013594003ba680773d,0xee3a01dd3383b9e707,0x72ce0ae92815ce502b8c,0xa43628e2ce8fc55d1f8f,0x39bf1d737e82c4fc99c5,0xf92b8bf0d73901aeb150,0xd8a294b8455f7082b8e1,0x4adc2082ba490573926,0x6a724c54e482b9492272,0x8c42e5191d8630fb9c21,0xc73848ac2f91d86214b8,0x442b708082e23915d06a,0x2b90d0774c40ee7881dc,0x7102bb662970cc0eed7c,0x15daf9cb25f2372be0ae,0xd94c597294b8650776bc,0xaed78c596f1eb1de316,0x5c852e190c596e95b85d,0x576c652e18c1ddae02b,0xb5c4561b896ed6cadd2d,0xa4b25b4963b6bea76d75,0x4edafa95b5d52b692c36,0xc15c5e83b9b20771640e,0xe0c92dc1902babc05717,0x80aece885c9d14b83a07,0x76600aeaec15d9c94b83]) else (word80 [0x950e5401,0x4e953594b9529549251f,0xd46a515d44450c541e50,0x394024fdd3eb4f7d3d14,0xef53ad4e6538b4dd135c,0x4d4133b4cbd3214c192e,0xb4b5d2c34aa129449e52,0x5e490d22a48391f34769,0x1bf469918d45c515644f,0x512244350f2435d0c042,0xa508e41cd05f412d0314,0x710073fc8fde3f28fb0,0x3e6cf883dc0f5c3d20f2,0xb3c38ef33b60ec03a90e,0x9139e4e613914e31388c,0xe0837c0de5373cdbb36c,0xd9535f4d6d357cd5134,0xf4d263448cfe33a8cde3,0x328cb33288c8f3214c70,0x3154c4330d0c1f3010bf,0x32f60bc42ec4b952e0cb,0x782db4b562d28b3e2cb8,0xb232c60b042bc8adf2b3,0xab52aaca9329dca6229,0x50a402898a1327ec9ec2,0x75c9c426b899b263897f,0x25b095c250092424448f,0x423548c122b489121fc8,0x6a216083c20a480d1fc4,0x7d51f087ae1e6877f1db,0x47551ce47211c186eb1b,0x606bd1aa868e19d465f1,0x94c64318cc61a18045e7,0x17545c016c45a3163c57,0xd15a855c1524532146c4,0xfe13784c712c049511f8,0x465114844610cc418101,0xc3ed0f843cd0ec43a50e,0x243730da435d0d083310,0xc7430f0bd02e20b1c2ac,0xa4827d098824d08c821,0xd08301fb07a01d707101,0xad065817f05a015504f8,0x12704400f703780c802b,0xc09601f4064016004400,0xcc02200440004d74d09a,0xe7a139c7426b8e84d70d,0x9ce99d35d33a6b9e74e,0x72ce9ae59d35c33a6ba4,0xa4d73949ce32935c6516,0xba4a2d73945ae328b5c6,0x397ba432f73869ec70d3,0x58e197b8c38b70865ae2,0xfd858e430b1482d718ac,0xed058d8e0b0b1c16370,0x82c2e1053d8e097b8414,0xe74929ae92535ce4a6a9,0xc94e72929ae525394a4a,0x6a9492d74925ae725358,0xe4b0a9c92d72929cc525,0x358a4b0a9492d748c9ec,0x918b5ca327b1464d628c,0xc6a519854a317ba424f6,0x4849cc9093592117b9c2,0x737384e0e7093d8e126b,0x1c2635384c2a708bdca1,0x27b1424e62849ac50931,0x8a131a94261528516e10,0x8b5d1f26b23e2d727c9a,0xc4f98549f16ba444f648,0x85ae5113d8a230a9444f,0x6380c2a700bdca027b14,0x6152805ee10135d3126,0xb9e24d72c49ae388b5cf,0x316b8e64d76be9acb7cb,0xdcefbfb95f2f71bf12e1,0x7d3d530a6aa612d74ca9,0xac99535daf26b2de2f74,0xbc9ac978b5c7226b2dd2,0xf71ba9ea9813553027a9,0x604d52c05ae98d35931b,0xaa632d72c69ac58d35d,0xae26b2dc2f74b89ac971,0x8d52e30aa5c2f72b912e,0x96e2552dc4b9db8953b7,0x12e56e254adc4b8db895,0x1b65ae2dd3dcd926b9b2,0x4f71649ce2c935c59263,0x8b24f70645ee2ca2dc19,0x16ba3a2d71749aecc135,0x95817ba307d72605ee2c,0xb5d5b26b2b62f75629c,0xcac53595896bb392d737,0x29ec6e5854dca7b0b92d,0x70725aecd4b5d5aa7b2b,0x54d656b0ac2d4bdd97a7,0x3b2f2d765e9aecbd3d95,0x7a6b2af2f735e9ec6bd8,0xd4d7b0a9af4f615f0cc2,0xbe1585797b82f2d76585,0xaeacd35959c2a8b34d65,0x5a5ae2e22545a45ba2e8,0x9745d12a8ba2dcd744b9]))) else (if j<4 then (word80 [0xb020d2e,0x311a858e11170a8c3c28,0x3b0f0690ae182e888f15,0x119436085214850d9108,0x91040c24660295020460,0x8304c041020881c14,0x5c58941848444057d07f,0x3cfce2f34bcc1f2d7ca3,0xf23fc81f1cbc63f15fc4,0xcf0f3c29f053c00ef93b,0xd1ef0fbb4ee83b95edff,0xb6eed5fb46ecd7b25ec4,0x3b00ebbbadaeb17abaea,0x8fa99ea27a7fe9d7a6ce,0x96fa49e8d3a1ee8279f5,0xe7939d2e7139b7e68b98,0xfe613972e58b952e50b9,0x30e46b907e3cf8e0e34b,0x8bee2d3893e22787ae1c,0x385fe13783ae09f80ee0,0x37f3df937d1deeb7a7d,0xe63780ddb775bdd27734,0xdc7f702dbe36e2db2b6b,0x5da8368ad9e3667d94b6,0x40d8bf623d8275f7d78b,0x5c9d6d359ed623572d57,0x354ad4d3522d4474fbd3,0x9b4cfd2f34a7d24747bd,0x197452d10f432d08740a,0xcfd73decf2b3bcce9739,0x4cdfb364cd5b345ccd33,0x23cc47305cbcb2e7cb73,0x2cfcb0b2afca8b292c9f,0xf272c983251c91b23bc8,0xa7218c81b1f8c7a31d6c,0x70f1b0c68718fc5fb170,0xc567148c4e3129c45f10,0x5c3cf0ebc38f0ccc2d70,0xa3c24f07dc19b058c107,0x2ac07700abfe6fe9bf6,0xafc8beeefacbe76f91be,0x16f73bd86f4dbcd2f20b,0xc26ef9bbc2eddbb0eeb0,0xba86e8eb9fee73b9a2e5,0x5b90ae2fb87ae0cb7d6d,0xe3b75adbfb6aad98b5fe,0xd68b54ed45b4e2d1eb43,0x6cfbb3aecd3b2e6ca0b2,0x3ec7bb1a6c57b10ac2cb,0x6ac08afcebe1af2ebb3,0xae7ab88add6b65ad46b3,0xeacb2b1bac26af5ab9ea,0xd4aafeaaaaa4ea7fa99e,0xa53a8f6a2ea852a00a7c,0x69dca7229b2a68298ba5,0xfa96da55e944a4c291ea,0x442901a3ca8e8a34a8be,0xa2b689aa242878a1a285,0xea11283aa0b681ca02a7,0xfc9f927d19f127b49e86,0x7979e3277b9dae75a9d2,0xe7409ca27139c0e6ef9b,0x7a6c99ae66a89a5e6869,0x9da6649942636989261c,0x982a5f397725cb96d65a,0x5965658495de56795465,0x3a94b251b943e4fd93b2,0x4d593124b0926a48591d,0x6465915a44590b241f90,0x3e4038fbe3db8f0e3af8,0xe7e38f8df23698d3a33c,0x8c9a3178c0e2ef8b6a2c,0x38ad229f8a36278899a2,0x53890222788362008796,0x1cf86f61b3868618d85e,0xa169855613f849611384,0xa0ef83760ca82c20988,0x21206d815603a809e01d,0x8011fef7f61fc27eb5f9,0xb7e15f737d85f4f7cfdf,0x297c71f077bbdeda7b15,0xeb37a75e8479cde62790,0x5e30787de0b77c9de177,0x41dbf76b9d9c7631d767,0x57dd4974f1d237449d02,0x73b9cd67305cac7255c8,0x71d1c647149c4270a5c,0x177001bf06f79bce6ef1,0xba66e59b826dadb566cf,0x9b266c45af96b85acd6a,0xc5aa56a31a796985a4e6,0x8e1a2068359f767999da,0x67399ba66a598d65c995,0xc654994864ad91363e18,0xee63698bd62bd8a5622d,0x876617d84860c5819601,0x57ef5f5d7cb5ecd79b5e,0x97735d7d7515d197305,0xc717115c056f55ba56d9,0x5b056ab5a5d68259b165,0x58e962e5885616582d5,0xf457a15d856f55aa565d,0x57a55995575511534547]) else (if j<5 then (word80 [0x17c2871a,0x858f7f0439c1a1970c54,0x5c31d42c49c311ec47a2,0x84bf921d88bb30c7b4e2,0x88b11431a8a1e70c51c1,0x31ee84512ca476523c95,0x38932cc50a62847c647a,0xb594498a14c50a628531,0x424f588cc88733430b70,0xc6877a1ac0908e689be4,0x2b322cf8620f1b631a8a,0x1cf050e707a1aec50cc8,0x6cc88c3235d42d55ca20,0x66479e218ccc8bb0623c,0x22ec188778433c22db84,0x3daec8819924d11d44d0,0xb944b671268aca26d702,0x217c121f6ea13101ee34,0x112e412279131dc824ae,0x118d3c898ee4125f7048,0x7205203203d8d4339029,0x78e0322913845a7c0900,0x200af86384c9e44c737d,0x6910028f2624b781321c,0x440117e00c6ba8438e44,0xc71c898e39131ed70225,0xe01253e049b5c088c049,0x6bc89b5c0899f8663cb4,0x378048c81803bbc892f0,0x9001d911901901b9026,0x7b331d3e049380876ce2,0x4a7c0931bf09907c8436,0x23018030077f009080d,0xc8127ae0225e1232f247,0x7c31c26ba12432457848,0xce88cf5a065b03680ccb,0xc925e123be1c6134c421,0xd9e233ec471ac633ec46,0x7d88cfb11d9e23530420,0x3a42406406d018f2219e,0x114e821a4087984903f0,0x49480ee904a4069818ef,0xc0441df80887e0467e04,0x6bf30110fc08d0efd222,0x1dfa4453d7489bcc044e,0xa700641cef4892aba44e,0xe364c8b59a44de602275,0x380320e77a44955d2275,0xbc264171412139f44427,0x3e895c498eb8931a1dfa,0x4443bf4887e0467e0463,0xb3a248e90e4748723a4,0x33f0233f0231859d1247,0x4876788f6b8112f0092f,0x2090b2e6cc859736648e,0x204c837f49136b811239,0x75992f211a5af226d702,0x2674c3325e0123207bcf,0x912cfc89001dde44978,0x4800f79e12259f91259,0x11a606981cee21adc444,0xbc824ba124bc8242039d,0xc435b8888f303bc24601,0x48e90d3aa9321e046f00,0xe474869d549929c46baf,0x49126a10ef211c71a032,0x1e04600c01dfc0242032,0x3720400640b7090ee12,0x3b9049a690c74d22203d,0xde4c67dba84d6ce248c8,0xa3ad8b7e9a44b64496ca,0x4c70109ab04f7012a7e,0x24d34876223c45a690ce,0x88e7fe1110fc8cc96d91,0x21f6c309875cc2a2de21,0x23798277902325c24718,0xe638c5883d31992e0921,0x75a23277902327790232,0x5c124bc1246f3049ee38,0x897091ef1622175a2326,0xf86224f71c449ee38884,0xe8927fa9225b22484f22,0x641f192219e048a04744,0x674473b5144dee0226f9,0xc2887811ef010cf11380,0x63e4867811c532418112,0x3830ff043df80873def2,0x459ef68146b6604abf01,0xda2bb327722632f0931,0x9f0235023f44718e0991,0x7484bd50a228107f1187,0x9432281772833219e04,0x8012812738264bd11e8d,0x219c44bc469107a425fc,0x4889ce099178c244d58,0xa1837d964d58a1837d96,0x40f1920e90af4464e890,0x74857388f39031dfc824,0xdfc887bf910f3a316720,0x63ce40c61e918c7d0888,0x3e84449f110e7c20893e,0x10445e22221730498012,0x3ad8874843a421d210e9]) else (word80 [0x1b,0xec87318871e6237038e1,0x1ca0878c5b1486711072,0x27806c0480af088fc11e,0xf810f7410c7fac111b6b,0x15a44648a1820980c69c,0xc71c23df3087bc428e11,0xc8a10f210ee08ea962d8,0xd431e421a02ab60c6016,0xc2100401007708558314,0xe610f4f8431e021cacc1,0x3f00c9c23cd87682be84,0x3e6ec5484b323bc22934,0x2bc225cd09a3c63cc6c5,0xec504cdd88e224ef6240,0x70e7ef08a80bc03406c6,0x467c11cbd828e8c49ef2,0x63a489604b80d38312e7,0xb43378460e06be3c91be,0xb16f0851991ad610d2e6,0x8614db064406b4c633cb,0xc244b9a189e10e39063e,0xc18a3847bf0430bd0a72,0x84c04beec22516c56c18,0x28a07a26f810c72343c3,0x7d0d40f431c8d0fb0621,0xde10c2f429ba15538c63,0xa5430a96c73850f66287,0xbf0a1c690c6a07a1ce14,0x35702bd422991aff0439,0x1c21b69c633e3236d869,0xadb1ce50a3906310be11,0x21818d314708e6a84dc3,0x14a087c62404c06ac356,0x1bc2475613c22cc2c4b4,0x1a958a4a130160235a16,0xf1086b422c8b550ac323,0xcc2c45e988e110d6841e,0x23e606b00b1ee10a450a,0x4a15b6476d91c6646000,0xd8f18f232b1db647968,0x51a631d74c636d844f7a,0x1d601635a0d43245ca14,0x8a149426d58aac306864,0xa14a0b016fc85bf216c4,0x21ecb3d107910e63c219,0xe11005a3b12fd2889995,0x8ad9154324b645283486,0x194143282865051c230e,0x988b12b1f60c4e022e06,0xc717743ec18abb60c790,0x2d8d66e871b0b8093db0,0x639c21760c47844bd608,0x89e05b1b7a718e7085bb,0x8745b1516c5be0431c8,0xd0c3b62a2d8a2ee87d83,0x10ef0869816c6b374355,0xe10e6ca19e116dc21c9d,0x435cd08a64745b12dba1,0xf6c32750d60686b85436,0xd38c7872865a42c65b6c,0x594cb1c9422f22d8d3c1,0x88dc0826e0acf08c2f84,0x3ec18b2f086b413591af,0x428658588b2d883d6286,0x66a13c034057b843ef2,0x629d21729820090bad8e,0xf089016fd218d01b1156,0x1887a42ac89bd898e299,0x20d04e88c9d1220240ab,0x6471e447623dc854843e,0x818e78c874a4731c8758,0x621ea21d911d4c8e7284,0x3842af2224c8e6050d79,0x81448cc8c02b8626b7cc,0x785e18f628556c31b381,0xb381ef50b2c33c859a43,0x1f74863b88aa64664319,0x91af5087a0a25b48e575,0xc73343ed431d7915791,0x1322d8a14e61d126833c,0x846434d1040f305c9f0c,0x7ac5053c855e4544c927,0x921afa724524c8d60f43,0x9a855b6c49e6c5b31438,0xd42c64c8a70687dc316c,0xc50c93232e0c59c98966,0xee8937c0a2588b7ac0a2,0x7610c69c310043d210f9,0x21b7262cc314ac21d752,0xc6a3d6a21e0467623a86,0x486191b4f0458d4510f3,0xc927190cf3b121e6192,0x77508642c2c4016fac11]))))
def g237H7 (j : Nat) : Nat := if 7 ≤ j then 0 else (if j<3 then (if j<1 then (word80 [0x4ecf,0x200c5126a00003222e06,0x36803300000000000008,0x2d20000406d47283385b,0x615a40d4c054a0000000,0x6af6c00000000000000,0x301e4204380dcc6564,0x4d400004203a0043228,0xf0106c0d2ec93c03a492,0x14519300000000000000,0x202840000412b,0x180380000000,0x1905a80f40000000000,0x681821e0000000000000,0x33301f0000000001120,0x70000001bb64a0000040,0xb0c0607060c889042118,0x22e901bb89a2805580ff,0x45a224d340,0x920000608fe071706b48,0x1d00000408c001a983d6,0x816d80491010b03a181e,0x2c0e01230881eb000060,0xc9d034188af417266427,0x2d49aed000000000000,0x959c071505b173b000,0xc00680000044a00000,0x139460074,0x80000000000008195607,0xc0000190d61447800012,0x24c000000000000220e8,0x37500000063f739202f,0xc41b7c02e80000000000,0x1b18720350,0x8703cb406d8000,0x8c6bc04c400,0x5c9cc079d009e0,0xd4434080c000188d8,0xe4e0de403850148000,0x4891a04f28345000060,0x9f6064b009a485b80146,0x81511b51cdd80000511,0x882678c67009b0000183,0xd00000000206c991959,0x2130422802e783d70000,0x22d8000101728029ca1,0xe00000000081bb401960,0x1d831900006045f0074,0xc02940a5511a280b,0xb182880000025e021dc0,0x31800010567013800a08,0,0x2063b08b0086dc447b05,0x8040dd21100e7400001,0x3a00000000203f20208,0x3011406090c0c010003,0x111050723000d060729,0x703080c07010005030d,0x9b061243060000070203,0x20a0012010108000a0a,0x121200020e0c021d0a01,0x93300070109091100,0xb0504000406110a1b00,0x8160518000c01020f00,0x100050102000301000c,0x2b0d020e000001040001,0xf0b020d0a00050c0b0e,0x40f0500000a19040d00,0x1401010020042f01040c,0x32d0d02031d13000600,0x501110a0000180800,0x705080a07060601,0x30000060800002d0005,0x1010004090b17022501,0xe0f0306060704011f00,0x3020009010c010c0505,0xb010910020001050104,0x2020b01150302000100,0x905020e010100021320,0x103030402000100021b,0x9090502470201030102,0x7050a001200030a0600,0x7040203,0x1500010003030900013f,0x1202030000000c080301,0xc01071e000100000412,0x312040f013700000000,0xa070a02060002000601,0x50106000f0306070e02,0x10501010001030f0d1b,0xc13020701040f00091d,0x5020005010901060101,0x3010e0006000e000d00,0x61708081001000a0c00,0x30000080a000a02,0x3020e00000205090218,0x401000d030300010201,0x110500000a0404000504,0x4010006000902080c01,0x9120004070e0f010200,0x30a0300010501040002,0xd0402000f05010b0702,0x205020003010a020000]) else (if j<2 then (word80 [0x16960000,0x819a000000001027b007,0xe00768231e0404000060,0xc50042f8a8b0000202e4,0x347010481054622f42d,0x882c7803d0004a05b810,0xc2821a00000409600c68,0x17ceee06046200000000,0xf0000060c,0xac000000000000204523,0x1ba00000000000000000,0x3b0000000000001242,0x985f5800000001837e00,0xa9c49940001023300000,0x20a872b10004d0af401d,0xc0000000000000000000,0x103a000000000000000,0x890e0ec0069e0000,0x80778000000019911055,0x2c114542d60000c8c900,0x2e20000000000003,0x3c0c16b000000c23072,0x1ba328191c04fc04bc00,0x45e0514006481ed0,0x207fa01c3030b41cf,0xff01cf092391bf480,0x9904dd0098000000d8b6,0x4b2043900000023d0729,0x2a000000d500001112,0x94c678035c0001289800,0x40c7d0294028201072,0x255827ae00d9801380ed,0xa21958330004a0000000,0x33a8034c0e2a06cc0,0x34b04932340,0x19da0134000198c1805,0x96228d257290c7805ea0,0xffe21720000413b60ef0,0x134082ff00000000203c,0xc0000811a0000306ba00,0x15b940390000181409,0xd5c2290000181035194,0x30324810d40af004,0x1085400004857000000,0x3c180bb8000160a4,0x209c0b300001217c000,0xc1f1c0a9c06a3211c00,0x525300000000024a5e,0x87b1355ea35c00000000,0x562f08ab01f8c0adf73,0xc903de411d602ff25040,0x8556635c8185,0x41d1610bb030f811f000,0x11269000000,0x15b8021000000000,0x20b64000,0x18893c82a08b7546f892,0x5cc8752092f071ba1a80,0x2fa0b08000002575ca4,0xc093c00000000c00fc07,0x848176205880cec06700,0x2898303c1dba06ee05ea,0x65807e32304abf,0xd000020f9743de088940,0xbf4a235017d838b01530,0x108ed82110000,0x22562000000006a22b50,0xfa000001458000024fe1,0xfec12c8050e016d31b0,0x544074c00000000c14,0x3c024704d60000944b00,0x104c6000015b6e08db,0x4f4821f9c9f40ab1466,0xe203f813420248004681,0xc8000040b2831a4098e8,0x22464f60000190550000,0xf9906f6000040fa800,0xb401ee00000000405954,0x6b4000041c6044080001,0x905901c3c4350078c000,0xc1fb0000103ca000005,0x53e63350402000000000,0x81d841326031,0xe20ad839f01a58000200,0x8b02990000409f800000,0xe5e20000000000067,0xa,0x680000060e0000000000,0x92d0000040a4a,0x214200000000010dd054,0x4a16f408380003101a00,0x3551600000,0x3018a834a0000,0x494000c,0x9331b900e64da4c64150,0x3510377000040a140000,0xc02b009f301cb03d,0xf188dc0142042b81b700,0x205d2412750380,0x2212591121cff446d,0,0x408b044b503632,0x97d41e900303034f205e]) else (word80 [0x207002e0,0x1f2813b000050472008,0x20760000681cc000002,0x52c0a30000107d18a240,0x649bf02b899948004,0xc267921d0125418dbe49,0x5e7394280ac228400474,0xc20000101b800030330,0x9872847a0cdb00000899,0xa000046328037a807240,0x1243f502de004e01308,0x44f80211821000004043,0x82219b07f0000205d400,0x1ce020d800031355c,0x982000000cd7062ea066,0x2158415c000080c880e,0xf809dc20f60000000020,0xe6301c1801500004ed00,0x90b8000000932019,0x839da820980003066220,0x13000064457010703ee4,0x2510d5c068400004956,0x8000108520000847fe03,0xb400000000000020e0a0,0x63400000c3e608121456,0x96cc8aa07a9133b287,0x98150c09180553204148,0x32800000000a32b00000,0x5ef052603cf402be0cc,0x80001018a01766414322,0x98818000000000007f20,0x30604a047,0x8c5fc4acf03d083f3000,0x44240000000060,0x1cf02730037000000002,0x7e913da0000208e3079,0x8000000002a1ec011000,0x66418000182aa4,0xfda08ed8139015a90b8,0xc81541237a04851bc0c8,0xa832cb80548099205a65,0x20000048470809c0000,0xa139c1ecc04700000010,0xc412d4635804de843b00,0x84c0000000000000,0x40f3050200000000223d,0x4406c00009022e112825,0x5800008221000011685b,0x9e1c0ef00001185482b2,0x100de000091a,0xfe113f73618265dc2e00,0xd13377c0000000064300,0x13ad4c2c08ba649,0xd0301508c224100001a3,0x62446080003235481330,0x20400ca6351a00000000,0x10010a000019bc49,0x6a00aa810a907d0cd800,0x1008940078879f11e2,0x121a80bb4475e12ca000,0x3dc413b274d006004,0x7c80000000003a6c04c8,0x8e02113e012c0014e24a,0x4000102adc0878000200,0x26394a00000000124020,0x268b400000000,0x108f3000,0x20,0x5b80000a0300c6de2881,0x2388000080330000004b,0xe0000c07980002006c81,0xb6814f00002083824284,0xacc41b060bbab460000,0x103fd0000010,0x57070ca16ed111643172,0x4d80883c194643320226,0x416240fae0813043,0xc87e00002077b114200,0x7b0824000040948,0x30610894d13c23c,0xa444c0000000000f7000,0x1209dc21e8000172780,0x17d0000087c2056b18be,0x17a428200d70179c09,0x764f6c06d40000000020,0x710000182fe48be80229,0x88f4071180862204000,0xa09a000030850049d83,0x50188000004470a0310,0x1076588d3005b,0x80003219a01d601a0a06,0xb2067e80ced89c00b194,0x5b190ee0000441240001,0x36d9c9f8e7780001990,0xd0000007900000000000,0x209000001013d414ba,0x8f00000000000000000,0x23a4c02d40ac431,0xa80000cd178000000008,0x3158405f0c9912b7220d,0x8051a6340224a1328483,0xe60d9c00000000000040,0xa3c00000000409822648]))) else (if j<5 then (if j<4 then (word80 [0x3e880f1c,0xe0622b401458227000e,0x60a91809fa33ec88f800,0x8856800610,0x70b08f0c93d4058c0000,0x4e816058a837,0xa0000246cd07da821600,0x3bb00000,0x102500000c44920eb,0x682379263d0fb80bc164,0x3a82a084d0ce6f006990,0x3db1003049a0010e10c3,0x5c9ea0455034802325c9,0xde0c78000110b1802368,0x6b1429e000025e3a0d78,0x738302ce40dc00000000,0x103e2011360a40053400,0x10b2081600000,0x2e73d235b009e8075,0x232720f40000c15f000,0x6890c0,0x7c82a8a00000624a0044,0x81d91c13800000001204,0xc0165800000072000000,0,0x105758994c067c0be,0x9038d98d884800000054,0xb00000c0362094d42c00,0x684980001b854,0xc092e10840000000008f,0xe00000250a000040e080,0x305c6844d006ae02d2,0x245029f40b86438a117,0xd8967000020306408810,0xe9000001080000000000,0x60f0a4084127000c3,0x20873209e0168c07f803,0x8e2134000050f90e75c0,0x5d8456202c403a9,0x82190000007e8000082e,0xb4047402bc00008090c1,0xd9a0f2a000c03ba0084a,0x1d0083b81620d5960cb,0xe014d9051c8080000300,0x84835600000000000018,0x9f022612f2202400000,0x80e64203a33620000419,0xf206a9011a88d4009a90,0xb2205920443000000000,0,0x12b6e8111c23400000b9,0xbdc894426440000a145c,0xc7200002055680fd0000,0x818000000000c1f7a04,0x98000102b9000044b460,0x29600000000000000000,0x834d446b80002213f00d,0x84718000207ef809c00,0x1150,0xe5c000000008196c041,0x7055181f6401600bb495,0xde8084495920983377e8,0x3e900000000000008298,0xc20140b41202a49c3c20,0xa87a400000000407f20,0x90c000009a341ac60120,0x6e50f12c,0x40000000000000000000,0x416420378011800000,0x600b8000181ca40c4,0xc14d8cc,0x93219039380000000002,0xc71279808e8000000b1,0x899b40896c16f80ed042,0x8044a000000001828e81,0xaba0fe211fd01ad5199a,0x9c00001c06c1ca10000,0x1088504538013014,0x3a80f8043f609d000000,0x98d1c2ee633305a21197,0x88cc210ca0374233f086,0xae423f00bc18da8c61e4,0x1e724cf30508064e87cd,0x3b982888131282ed43d,0x5828a483e80000218800,0x805a8000211fb82838,0x829885a704cd80b3a4c1,0x80000000111410000000,0x184560000c16b404d80,0x1023f0000000000001,0x82550000000001800000,0x600f0000083da00,0xabb90c5ac,0xb30059a494dc17c1085,0xe03d298c9c1a30000227,0xb3c8725186a0ce203ae8,0x8b3c4440261301d80000,0x91bd4104000000000d89,0xce443c00000000816d64,0xe524c0000041e269090,0x1407364c08432d015,0x80000ccd2800011118a8,0x7a413c608f4000000004]) else (word80 [0xaf00,0x83c0000014a000000000,0x40a75068f83a,0xbc1ad8000000000000cc,0x6a84ad80000840001f3e,0x634403fa01fc91bea097,0x70000a89300000000104,0x89007c810c0000006d60,0x402a64232099f,0x416f0e6ff1117205780e,0xd800000569903d000000,0x744000083dd000000000,0x8870e0bdd035,0x3111bd10a242aa07ea00,0xa13e80000000190e78,0x808443a2201a33b41ea,0x4086b067801ee4220603,0xa000000000c1c4000000,0x1a900c1280e4,0x808c800000000000,0x40aee227800000000c9,2,0xb8400010395c84a60dc,0x5864e998f41678000000,0x102b0000001870,0x19700000000341360000,0x40c84230391a6000,0xc1f500,0x222140000000000001,0x213c0000092480000065,0xc88ddc450a064c00c802,0xb0000000000000000000,0x44e0000,0x24780000082df0000000,0x1051881600000000000,0xa05f0545000030178,0xa42180ab030180000b3d,0xb0000000000000000000,0x2e7f605b0842d00006,0x4a100000000000000000,0x901cce52103,0x20a00890020000107638,0x2c081160000000000000,0xe136800020424000001c,0x48000305df01f3801200,0x83fa045480002,0x16900000000028b4803e,0x201b00805800f47281b9,0xd281b9c669a47ba00000,0x1be80efa232d00fa0186,0x207688b82000000c,0x342e1835f0c60605540,0x81ef800d200940001,0x2050038622b90866036,0x1846440bf74472831311,0x9ca090604fe0360c217a,0xe4ea004c0000089fe0f4,0xf20d3c274d4c42075506,0x86817a8c85a0abf0242a,0x32fc8786096207520000,0x50f58000306920174c11,0x8018507248275820a40,0xbb8436a822f000002334,0x43dd034e4024c83ec000,0x1914b000000818000000,0xd19d00000000000000,0x206d0001,0x86ac7036508ef0000401,0xf8000000000000042fc0,0x102bbc452ea242071e,0xa32301d2e2d100000000,0xbfc02740292112048,0xa06e4d6080d03d0cc872,0xf901a682a3d0b5204b,0x4000000000000008a000,0x234c0d0000c2a767f9,0xd200000000000000000,0x41b908cb603e80000000,0x1005702bf40f662,0x2880001804109b1c43b4,0x8e760f56079,0xa0000421fa0dfc069002,0x3e8c69a4468000111270,0xa38000221cd816b41cb,0x210140000c01ac08,0xd4075e007f5031003580,0x6ca8399015c4438d06a0,0xb944000000002079c01a,0x2000020950219e80a500,0x20efc000088e4486f8,0x107a2000000004812,0x9002e0000000006f3000,0x18e5cdd00003739d1,0x25504ce0e717113003ac,0x847700059087013aa000,0x60cda04a3022081b800,0x2a19b9208680cd16,0xe200cd020280001074,0x80000d4c340032062504,0x17022340613005140700,0x1b604a04000000000000,0x4223d247408f7c0cd800,0x100da000000004230d4])) else (if j<6 then (word80 [0xbe014f00,0x2e6be219c289101d3a,0x2180000a0758050a071,0xe01bec39c00002908c00,1,0x2830000083d2088802f3,0x46e604680000b077000,0x3378e0000000000,0x41124,0x40ca0000340c,0xe841f81ff40633048580,0x7800004e70e510e83e18,0x21f40ba823bf3b3a8088,0x864400000835c5032108,0x9102f00000c023c20437,0x3ff4bc1415b463100000,0x816c817b0000000010b9,0x40000000000000000000,0x89b100000,0x198c200000000,0x1100c00500000000,0x1a34a00da0000000000,0x3ec00000000142bb02d3,0xc17d80002626e2046201,0xc8026c000003fbc17a42,0x21202311a2e000000002,0x14540000519e080cb01d,0xda98481aae444f084a11,0xbe0093ea22005c110c60,0x845f033ea1f6c14b,0x4801e0356106a0000402,0x55040588b5e076e109b0,0x74780010000689030582,0x827201168cce8211a81b,0xc00000000217d800008c,0x6308840000083aac0416,0x40f80001818280188000,0x200fa0000c10dc007505,0xbb04030808c23f107380,0x8107e0a35081e0000,0x206f80000c10,0x64421800019295805760,0xd67040fa897091c44948,0x61c0000000020e06029,0xd0102e04ec6367036780,0x20d108c042d06d283160,0x139a078f233200001915,0xe28bc049a280918ab481,0x3c1104831c847c000000,0x1088b,0x12170000001d40000801,0x9000040a70212a88c7c0,0x8d8a60301ed024788778,0x15510020081dc6088,0xa0256024a00000000232,0x28a11e0003a0c980000c,0x74046f80cf5119800ca,0x15ea41c922bd0427c94,0x6a818c035f10eb000000,0x231803b5420c00003,0x3218039180ff810f1032,0xd82e6000050d3e0622a3,0x5bc87200003078000000,0,0x4103002f942d20000480,0x1706729190406e0816a4,0x4790152c12d804f3078e,0x4061000030787006,0xa4ca2800002182000049,0x3e81104000018c8c1bc0,0x164000008f600004470,0xc0000000080180000000,0x40e780ea308220,0x3c8885d2067800000000,0x839b0d3563080000421,0x8d02680000ba04000000,0x10501111c01b180000,0x10286404be0478000,0x81a1c114c03ec000000,0x40df6091606e88318c,0x969000000000000a421a,0x80000000001510000000,0x1a09c81c2000004,0x1e5aa4dd1a4c03ad07b1,0x2074000040206318e000,0x20017815800,0x18b12,0x82c0000000080e188d4,0x80000000080d70000205,0xcf0271420b2854000011,0xbb0002c230204a188db,0xc0c48000000000000000,0x305a883834108c0,0x7340000000000000029c,0x11a5843a00000000002b,0xf206ec54f80000000181,0xf2c450000000001032c0,0x8f58000100144025,0x806560100025c59b5807,0xdc60a7a1e6000044abf0,0x5e583b980b3803d7236d,0x22b0936800022014815,0x7c84864ab8061f82f100]) else (word80 [0xfcb3321,0x4280c83c610d8000083a,0xe00000000080eb807640,0x880000123ffa065c1242,0xa44024788aa80340112,0xc000083685ceca055102,0x7d88bc8601a0590031a0,0x893a622a203160000,0x409a0688164a90199490,0x1c0c2504d2000010aa00,0x89355c5a33d810a00002,0x3211409941cdc464d46c,0xc01a6000000000000000,0x83208,0x580000105af4bc50000,0xcc5ca08,0xe400b6297e0000405b40,0x14bf809b621ae,0x3f001b7010670834000,0x608364132094500,0x608de216a000000000,0x300368322c02e0000,0x1809300004036800,0x1819100002469726a40,0xc1cd2471e4618990f,0x8c850000001b08289845,0xf80000000181dd000060,0x29000000000000020e4c,0x793a1e80000601e4000,0xa889c09b80001466400,0x40ada23e8000110774,0x8c3206fc131292640022,0x1464882e80000407,0x2c00000000493bc49f80,0x3c402d5910f80e394077,0x2e5102ca04a8018802e,0x24157603440000000044,0x53405300000000014476,0xb0c000100aac0cd0000,0x30068900902120000247]))))
def g237D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd2418f6f20c,0x64c895f6920eda483df2,0x3111483818fc38584e70,0xb094fee014286f83821f,0xa76e03c34b93d13185c9,0xe8a2e4825b9de08286fc,0x416f9581141b92129c99,0x2427bf3844afc410dd98,0x35cc3484a07d00894fc2,0x252e5369a533f60442e2,0x9a134adfc016dc2487f6,0x40cdf882b6a20f1b9213,0x5e378214564243f8c213,0x5efa2630bdf44f72412,0xdcef04145e1125f2e044,0xf5c9096f1982142fb402,0x2c1ea408cb6048dc484f,0x78dd04295f40221fc048,0x733a27a7e11290394e8,0xa4fc009697c22603b7a2,0x73fd9031ce02537c0098,0x6318114f3ca213df8092,0xfc0497e02439c04b3888,0x772fc0935e1125f2e044,0xf7f388944f7045480633,0xf224bf02352419a411f9,0x20a7ce284d7f8891806b,0xac035f48225fe2243f,0x2048900cf8823e208804,0xb8890ff08901053af02a,0xfb8221e846b00ac035f4,0x8225c8896f90244806df,0x410efc88e63811348e04,0x5bfa092fe8243b015fa0,0x15e808c6053f010f5c09,0x5f80679704b530923c23,0x3e89132ea21bd2084029,0xf38148053e91132010f9,0xc0a5984872ec90b3092c,0xdb242cc24bf660958048,0x1c6993030b96088e186,0x6521088b1208226840a,0x22a900054a44910c46c2,0xdc16bfdbe7bc7bb6b95b,0x7eb5cb42b1aaffadeac8,0xaa8a92a73a5ba3ca21a0,0xe9f79d69bd9a49819689,0x4292e9199018eb8d58bb,0x89b88886b85083181b7f,0xb7e77c97b27937777597,0x4872d70c6f36dd6c06a7,0x68666e65463861f6085e,0xe5d25b359e58957455d5,0x4952b5174f94de4c44b4,0x49c48847646645143541,0xe4114013f43db3c43ad3,0x9d38b37936c35a342334,0x31f3072f52e52d82bf2a,0xa29428426e25a2422282,0x121fc1ea1d61c51b41a2,0x18a17916114e13c12310,0xf0fd0ef0da0cc0b30a60,0x9107d06605203c02800e,0x9d896662595896462,0x59949655259d85666159,0x585646159945655159d5,0x1e55479d4de55379d49e,0x55279d45e55179995256,0x549d4d25534998525614,0x9d452651495452451498,0xc5253149d41255049d4c,0x655319d44655119d51a5,0x5469d4da55369d49a552,0x69d45a55169505a66539,0x594e7533954ce6623958,0x8e75239948e55239148e,0x64239508e442398c8e53,0x239d40e55039d00e5403,0x9c80e52039d4c255309d,0x4825520558a556195596,0x156285586176257d495d,0x5255d855562255849565,0x75591d56375589d56178,0x541d76545595176345d8,0x522504854115651558c5,0x5611559595646558d956,0x265585a150684c1a3206,0x5d94d56535d8cd56335d,0x88d56238940e15038900,0xe140388c0e13038c80e0,0x20355941563055881b50,0x839888d6224984916120,0x99441651298c49631498,0x451611199185646fffed,0xfdebfbdbbb7af9fd4250,0x88210541204405008010])
def g237H8 (j : Nat) : Nat := if 4 ≤ j then 0 else (if j<2 then (if j<1 then (word80 [0x8115003d,0x36ca18103ed00e894eb,0x1091a0668cc60b520597,0x83e6443a84a78a82054b,0x809d020603ce016323ba,0x84f2934b83650461801c,0x4e5038c047caa03,0x2be80ca824c818e1063,0x823a0000000181408267,0x217f80480000142080b7,0x93b209dd024800011c6e,0x4b30a728dee00000000,0xc8039304591303a1c5,0x85c8828f236185c581d7,0x10790399acbc000183b1,0x24c29d7d804f00ee05a1,0xa19d24e4000121ce28e2,0xe1192c703f51d7a033e,0x931a0000088e034b83c7,0x26ea1ed8adb81fe80b8,0x1e5ba843501858522be,0x859200420df0841292d8,0x8566025600000099,0x4b581e112e185370bfe,0x80aa00000000854c0b55,0x1df811633a710990ae3,0x1a8366000025010b56,0x85b885c0000144a382de,0x42020d00000,0xc4de000004be0001ba0b,0x811b039e01eb063c0000,0x34084ee935c8846,0x83348475a5d8,0x1802381ce90878464,0x80fa38a4012f81be0065,0x23f21a200013b2403ba,0x832e089c0357b402,0x29c0000850e02f40000,0x569985743b684ba03f6,0x912b130c860400000001,0x84fd055d830c4a448328,0x84c2860a351321b08b49,0x8343853f04c880fd819a,0x5e4bb6a02d581e71968,0x94100d3c2deebb710afc,0x2958b5152504827a203d,0xc3ad1704ac43a624cc,0xcc58556a4e110720000,0x416000d017502f00001,0x26a855a0000bb7bb8a7,0x122d3d8549008d0512,0x299e013481aa81291a4d,0x38a8219a83ac0001016c,0x31c808e0541a1e5,0x85e609e4020b8ae80642,0x181199430a84b13e6,0xcc11af403000000a22e,0x80dfa88610f02493bb88,0x860308601340805a0001,0x85ed82c13b2a82388afb,0x146000003a5018a0000,0x233002c403a12609a034,0x10350047203c44220,0xb050600380486260a8,0x203e00008443a2204010,0x8205c010649b1280400,0xe1a04c844e239a4a600,0x60a0004d0581034ae01,0x810140000b48019c1803,0x80e1d17b248c12331481,0x41b0f01c023500854580,0x10501056ca921a0b8651,0x1810021b1e804007c059,0x7c9401198045062180ec,0xe15189584c950887800,0x58600e2900808325c,0xd94c20121800816a012,0x83c520f0b0e800104c80,0x2c87078d400cb1b8080,0xe07009403c0c01048380,0x251d81a060d80c20110,0x304c8a32008248c10052,0x38000d218180e0000828,0xa9f0081c7820000b936,0x9068040016020299600,0x13014020a0409c0e0404,0x18b00f0081c40b01980,0x4f600030082c00098000,0x2010201409000b03e0,0x503070aa120000032000,0x1004ca0107804e63d018,0x241a220380002051d818,0x2540b09078110001002,0x1058000206022b83809,0x2c42002f00c1e2f18,0x482800100002a020406,0x4006e80c1a430086c0,0x20000000020600800460,0x403008c8350888cd0050,0x48101010118082a2d000,0x3402091b8043a0201804,0xe050293c0000130d81e,0x36008000c1a000a00816]) else (word80 [0x35c0000,0xa614835984ca81890021,0x235a0c8bbb40aee8279,0x21a8825aa3b7830e80bd,0x8649884f13c5006da90c,0x15d0562042a940388ed,0x824a0c9f822b8d3f9442,0x18106044a037d1321,0xd18842c000191f9091f,0x218c832b005682030595,0x8bb121c8063804808aea,0x21e785af38c022cb8bd8,0xb2038b6614a6885d039b,0x22c9a18b1342884aa453,0xa1b3a2b744cd2ad80000,0x1ab44203085a5062a,0x1031682b68dd20000,0x14132c011369827193f7,0x85140000856f830a8215,0x82e1044e0000000103b7,0x13640000000002da84e6,0x5200000001202cbbc9,0x5108440a1d59c3d0408,0xaf403618054112c847a,0xc2a0001a5200001,0x1c378479214313bd04d1,0x84548559051e92a9014e,0x843e816504c704d2bb6c,0x925c048708879d4610fb,0x22c20dc48a1a0000c4d0,0x84f483fa10c701c3,0x83bcb3d200b10243004b,0x92e80000829f00f493db,0x59e0000000104760001,0x23ed802c000104f983f2,0x92cb00922c5c13e48e0e,0x833aa27c8575235b813e,0x627bb2785d121f78233,0x82a581b2840f002783a8,0x84d4838982720302027e,0x37b109c24ce93d21593,0x16a84dc82e984ae0001,0x2c9404ec807cc3d33b6f,0x28c000109da05f2b8af,0x62800fe83bf091b886a,0x22088ad4000083c292b7,0xb3fdbad235182567a606,0x8113032c105b88758031,0x4b42806a8123925e102f,0x20c290470917106ebbd7,0x284a610800408948290,0xd6007b04fa826085a6,0x803783320af6140e05ee,0x861f01319870843b04b9,0x811d061103e983770434,0x284482fb00e34d88048b,0x94a934de1b0e8e180323,0x80812107839138bd137b,0x841808e5057181f5bbdc,0x40a80ba81b401d482dc,0x849101ef04a48c1c2316,0xe4c7b00ed84d70451,0x85fac4cf812a862221af,0x83f092cc04e228480add,0xa568944e0484134fa424,0x84cd20c5a214863ac1e9,0x860c80c690a3034484b6,0x819080960dc8000912ce,0x806885d6064102810227,0x1b600018498853a906a,0xa4e2a27e000183528d42,0x46e035a01480a710b47,0x84249b4b85820ade09e2,0x8ad602ca8383063f83af,0x857c14e7825800011ae9,0x850c000000000001985a,0xaa7103e103c001361328,0x9053931fa09600000000,0x101fc00f983100492,0x194c8000129ff0156,0x17d83260000ac1d8251,0x50182a84545846204b0,0x22b92841036a82c38320,0xa429fd24af089bbb8e,0x20001a0000001248473,0x5250aed0c2ea4b885e1,0x8646908d93a70cbf84bc,0x4940000831b02d9a2c4,0x20cf141f02b484d880d2,0x190169c4b82178066,0x561203b303603b4042f,0x806002ccad1b015a0000,0x90a8902a00d80b1e9d56,0x81cb82f90b0200000001,0x2ff85c303fc000001ac,0x13a83d408889b5ca1a7,0x1535bd188b5802e7833d,0x84060000000101a80000,0xa1e1a5e6104885cc0000,0x82b9a3960000826da104,0x82cf834702ef053d843c,0x9c70000000010294,0x8449aa3eb8ada45502e5])) else (if j<3 then (word80 [0xcbc24fc,0xb36a014210640001836f,0x54321d2b8a1bb7293c6,0x83b8000183c505048309,0x80148632a48a862e38b0,0x104f8003904113110244,0x5ea018538b2839d0415,0xa19503d0336992ed8078,0x805f93d592eb03d2235f,0x15e83df852f85078489,0x80dd012783eb05992518,0x12b0000000000001,0xe40001818d44e48324,0x46d03fe10f9bbac9d40,0x239902a1838482af,0x857e841c821800b38b1c,0x103140001,0x814481bc0000820e0000,0x85473b84056c00500000,0x93fa000005f185090578,0x5f40001a5b400018445,0x8dae01f923ea00000000,0x101dd13c8885e0001,0x81c7b8be051baadb84a8,0x828692ee0000000080b5,0x83b285b2143738cca530,0x21314f89c2d4d81045d,0x81b9044c112581f20001,0xa53813d8017f91220001,0x3950af929da04a200f2,0xc082532d1f00c4,0xc5988402954901e8a39a,0x19035059c1c33,0x8193824f0427049e0000,0x8ad2000000000000821a,0x471b8360dff80a0adff,0x2ba0001886c81eca846,0x1a4a7041e,0x8b0000000001861c,0x9aec00018e09b03288e2,0x2b410318a48e82e30534,0x8033018680e005b6bbaa,0x8de2000080280230132b,0x19a39d85bd80d591f7,0x85c690441001105c81a3,0x348019f9860850a0000,0x1a5052d804d8b4a061b,0xa04c00000000000112c2,0x1bb1810b808501d8,0x110e80001a394,0x16000000000,0x5ac0044105984aa23c9,0x5dba1ca9027001ea0d2,0x4c73807400012c8c986e,0x110000102ea0000,0x180460000852b8195,0x24a9856b8ba706240618,0x23da565c5a200011aeb,0x104a954c0338185d808a,0x1b0b02221cc219230304,0xbbae0001aa180001,0x81a7848c159400160000,0x13b784a00600249f8cc2,0xa0000015081218071,0xb51a81ae1bd800018429,0x14fcbb76064b84c103a2,0x645022fad74930805be,0x132130b802404118a19,0x8b4c01b189cd810c0095,0x833703e20000450412fd,0x17180cc000000010306,0x82c82c68000083e58573,0x91eb0dc20001909f0169,0x25038167885b82ac0577,0x809e12d3013c01d01419,0x8da505fd21c6000105de,0x220a83da1103955b122b,0x21124ab843895980001,0xbe2135a49818588502,0xa8e4136b825585528297,0x838f01020e2200000001,0x85a328e9a2bab4a023ce,0x938a0000932e207e2bfe,0x8371051d85f704db04fe,0x8dc7885781770063943f,0x34cc05d323cc0914404d,0x82b30180042200000000,0x1a20ea0bb022982d2,0x807f9b08058c837281c0,0x93a8a19215a7a8e722cc,0x31f13b08039252f936e,0x81e33b7d8b0505278528,0xb2f3890c802f81988d9d,0x6311406017b2d198433,0x46b22c7134d003f83f9,0x85981c980d10378020c,0x91ef80a601f68a209345,0x4439aef02c603620220,0x3c80001841a000044d2,0x80ae000185238863014a,0xb8ab24a42914845b8158,0xdd494a4839620d620d5,0x8274944400018bd3b0a1]) else (word80 [0x810901bb83d60000,0x18100086410101089,0x3a8586a007019da4c8,0x14c959c0000bb810452,0x1817981820c28,0x21c834c000194040293,0x849d8531231383ca05b0,0x18c1a85aa888b84e8,0xa2bd0082856401731c79,0xad6c85cb05e8022c821f,0x36905a80312029841ec,0x58b02fc3b8a03a7c448,0x240ad9b104d91f28331,0x4044d7f959712fa0518,0xbb2d809b858881398225,0x9b0c04df1d8703dd14d6,0x9af7864d0848a8e00606,0x29b038a85d432010007,0x82bd0387901224ac8482,0x24d78154045e2278a1bf,0x23793b980e6854e1450,0x2c299304885286348381,0x80eb106803d9b1fdac1a,0x80cea0cd03aac0f9,0xa5a922338612403f0354,0xb51d80f00867a2302c89,0x92e385e380732dc30456,0x4e085bba2c1834f8544,0x18b7d005903cd816f,0xc554811f92d1b08a0000,0x800000019c1f9546,0x2ec000021ea826480a2,0x5f82c61249d02b100ac,0x1035f825e0000138c,0x8854000004ea012c0001,0x11f080a8239e13fd0614,0x204804120b8843185fe,0xa0820000037544e105b4,0x860985dd24d108510617,0x82f3037e8637057a260f,0x2bfa8ad8858ea27a805d,0x84ce059092bb00da82f7,0x43c491f402a604668621,0x847e840084f1a0ca8551,0x855e05ce806e84969033,0x8276852003ef01fa0533,0x60e85398d9b059a0000,0x8087028290f7245a0d40,0x82a3210f807710939b06,0x5d8028a0000a90913af,0x10e106184c40ae112da,0xf62038000025f784f7,0xb4402630105b8b60000,0x4b2f01c48034862d840d,0x202a8288140b85808197,0x855412f1046881d28c2d,0xb325108b827c20a20001,0x4360001a1a400018268,0x8088a8ef2004000082d7,0x24de000002aa81cd2524,0x3b290010825d0153802b,0x1ca502d10246943da60c,0x140c851701f1849a8091,0x1350903e8afe00000001,0x848f203f01da04470209])))
def g237D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc0,0x900180012000900085,0x801000096003a00129a8,0x82488a20610204c43bcb,0x42ba39a1189006a1282a,0x284409004108220087f])
def g237H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x303581e8000c1,0x6c00000000000000000c,0x98873900025128d64000,0xc4e0249000007c019400,0xc0c300581b000000010,0x2d9d3e571c13b13781d9,0x10a55c024e955a25b159,0x110981a1006444b02f00,0xe1f400011160570,0x115c20c0000003025,0x886400044fb079c08c00,0x1543000101400000,0x347700000000000,0xd20c0000001555000,0x2087997c00049,0x6b180000387500e40690,0x14510001004,0x204000011c000110526,0xd803054244bc00041900,0x267991d80000003,0x2160000000c18b1865d3,0x22c16100a884316700,0xf106e000300e00000860,0x1e100004fc41059e0000,0x41e000000000eb44,0x2874061f21800f72,0x4b80dc00000000004469,0x53d1c00000003135597,0x9777d046579818216609,0x136104a826b1d3b97b8,0x4e800081d00290003466,0x146826a919400041de24,0x7c9400000000000c0810,0x3b817000059c57830615,0x3e010202b5110000000,0x776c1415780d1d04f00,0xfc360000000001fe97ac,0x1100160001751000007d,0xc94727d491807180cd04,0x3c4ef05f000301b00038,0x5bc079211000067041ef,0x11686100000000000c1f,0x8011015a0545d0604600,0x240400000008,0x800081c800084b4000,0x200b0000000c47f37,0xbc034000c05685a00010,0x1aa58400000200000000,0x812c000c00,0xd136000301f004874001,0x78000000000080700000,0x206f81080000000000,0x41c237a418c000000000,0x196091a721590a50,0x8000ba05a90b145d5d74,0x5d372174157073c1a,0xc000a1a474b417701000,0x220d000321200001830,0x24670000000000124a,0x302c0000075c92117,0xcc104000819d02711484,0x5c81a800000020520000,0x210000009,0x304c8124000842c000c9,0xb117fd0e475c00010664,0x20903245240000002051,0x406000091c4000d13c00,0x547f4500964001444f0,0x2a45f506101280000000,0xc90404d0000000000,0x12130002252557c000c0,0x5d048000000000000000,0x2530001009000124f,0x407400,0x520000000203880d00,0x135994000845c0004114,0,0x4420000000311c00,0x55e000200f00030318,0x9912000000000002181,0x85c085275119212,0x9000313900012451d4b4,0x68199217e509f1820001,0x26340a0000816701950a,0x80009d40000c95303695,0x9506d901621444f1007c,0x9132740020043441c10c,0x21e72d30001821033030,0x800015815002803c0080,0x10100159a00404c4400c,0x1030420800403450412,0x3404060880801c3005])
def g237D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x3f
def g237H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1a360e00000144612,0xa2460086b99e0ca40009,0x100009869148000004c0,0x4200070e24c2249001b,0xa8000000023d04000131,0x38d2a94d044cc4000280,0x143062004060062b3,0x3e0a014a104085380a28,0x910b000e2924cbaaee59,0x9000a988b33110928094,0xa94398840022420c9061])
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
def g243D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x4fb7059653
def g243D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1002628,0x401413142f3185b400bf,0x59653fed8153d7d4e53b,0xed8153bd58453be58053])
def g243H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x8
def g243D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x190e,0x6a1474365a981d90ea61,0x47888807f94ffaa7fc53])
def g243H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1400100000,0x23880000000001024029])
def g243D8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x468817f
def g243H8 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x98014e
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
def g246D5 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x104085b546031d,0x1d771591318f7815d954,0x4c795d915354531b5585,0x50d514c7c55514354531])
def g246D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x2ac20000c0580c5840,0x20080802020000,0xc076833415a080000040,0x280801d22d410000a420,0x381195900690130a869,0x90e0403043c16773395c,0x822b08803e1e0e76fb55,0x9ac35dacd509b47204f2,0x713417caa4d1f0c85422,0xb83c002bab4b7560ae9,0x1dd9c9b9bc57450ee88,0x15d523ba9db753b0ea79,0xdc4e5ba9d77138aec67d,0x90a9ba8d1751beca3759,0x478aa0f7711cec849590,0x96aa1354321ee8b8d896,0x2ba085750aee200dd4f4,0xa993ebe7eef577bbbdbe,0x7efb77b7d7e7f1fd8d51,0x5815150d51d854358543,0x54540d9531d913159531,0x591315513154d3154531,0x50d31d9510d911055110])
def g246H6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1900,0x25c1000250092000008,0x60000048000000001100])
def g246D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xe068772,0x6121396128e84a22fcb9,0x5235c3090dcc24af0620,0x171ea2301fca44dca439,0xe90bbc263be223eaf108,0xbfb92113dff38009d4d8,0x4adf80392dc028f1425,0xbfb34270fec309978c1,0x47a4645a5fc494a17203,0x91422227064c51e02603,0x23083402f2c4464c2964,0x90c68008860954a28107,0xc3e6f966418a6097d1d,0xe729a96397a5a1525092,0x6414e4334b5270861984,0x80d01a0026c362c362c7,0xa287a2c1a2cae2c8e2a8,0xe2c4e2a322a2a282a2a2,0x62a80ec34ec78ecacaca,0xcec8cac8d2a6d286daa2,0xceca0ec806c53fff7def,0xeed5150d404c53048110])
def g246H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x221c6a060,0xa808e8021f906930,0xfa138b78e000380020e0,0x41c0023685c228ae0c0,0x4219e139fc3a2e00001c,0x5800000018ee24028348,0x8010249e86800000000,0x4320c405a,0x8c3c43026e8414000000,0x18a28bc2a44530020])
def g246D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x1258602a230,0x32071959238a01412473,0xc39648a004a2650a1292,0x16592188818b1e584930,0xa16502422204a1e40e45,0x4210a830007f50ffaa3f,0xd31fea07f4c3fa41fd10])
def g246H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x71,0x32f0f84800014e0055e1,0x987a5044151589aac000,0x60b4600000002000c,0x30030a005cc34002ec06,0x980198e7811878e00e50,0xa00001ee216007209391,0x190b02000000058c00d5,0xb624800000a503b00440])
def g246D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xa4188201bf
def g246H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xd088a0000010b8f80,0x40000580c00000,0x25000003200000000,0x8800000,0x26000000000000000235])
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
def g127D5 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x306e98e1c8259465
def g127D6 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x80a02e02008000400,0x290b0100000000000,0x985a128,0x4e1585d5c5b5a595816d,0x5341311f0efeeed8c2b2,0xa2928272625242322212,0x7c9be78370530d9e0d,0xafc90dd9218b243ae5c5,0x5c389f8710f2e17e1c2b,0x4c02b8703f304ae4881c,0x92039261f24b4e4551c2,0x243928872502658c1c91,0xcb962b70e26e1c1c6f39,0xe67c3f86ecdd75ae74ee,0x8fc7b61f64d418758b50,0x60372597725c1651c970,0x59585dd1605977358154,0xdcd60dcd6158187d9552,0x61b7154372d89505cb62,0x441655c865e1d6519782,0x59465609651948259465])
def g127H6 (j : Nat) : Nat := if 1 ≤ j then 0 else 0
def g127D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3014d86b4,0xd89361000000008044c8,0x8c869229412d87662180,0x2e684001e44013417702,0x7c45196c434100a42000,0x80800e213015702,0x80803783147c62270201,0xf586e1100002736200,0x40401010040401013213,0x2100da0ed07683db0f6c,0x280800000000000521a4,0x25cd880290ea0804c843,0xa421b0800052158a11,0x90d72626023e42000000,0x19a100000056c211b1,0x190afb19118080007b0e,0x614d24549141cc25005a,0x8791000059080400000,0x2c8675080000003b0e,0x613b0f0508c188110c1a,0x20102cc4e270f83c0e37,0x1413410721f84c041006,0x84480a86700080d8601e,0xc20d50c010701052e85c,0x5b6f68ecad8db0b5f6ba,0x56aab753ea0d35a4f452,0x864fa9e538a6d4cd97d2,0xba4d48d90b1ea3946a8c,0x516a284488710b60f414,0x818fe1f2bd679af11dbb,0xa8740e61c2b7d6e6dadb,0xb5969ed1d9eb3164ac7,0x5883035ecba16d2d0590,0xb015c2b0550a814aa8a4,0xee9bd322584a08f51aa2,0xa438851062013e0790e8,0x9c636a6b4d299d32a610,0xbe1742d8578a614024e4,0x708a0f01c43505e8b515,0x260480880f81cc35863,0xb614c2383705e09c0f8,0x3704e284138a700de8,0xc037650ed0cc136a6e4d,0xa839365f06d59c135a6e,0x4d683935bf0402ec100a,0x7050b3c13fa6c5012c2a,0x87300a29c126330ea58c,0x1297300a52c327cf0491,0x9c124770094cc32ac705,0x17041458acb18cc3c492,0xeb12eb2c4c704bf0412f,0x6704bccc2b33304ceeb2,0xac9acaca6aa32330ac62,0xb2b19ee6baeb2ab9ee6a,0xccc1309ee6b4dc13ca70,0x4f28413c330ef8cc3bd8,0xaecf4cc3ba8aeceaab93,0x9aae2e4dc11f6b02859c,0x11e6f0270cc323a6e480,0xcc322570874dc11a6704,0x64cc29baee461ac09567,0x4499c11196ea39bc08e,0x630a530b2946308532b2,0x8d670a2d8c28b330c5a9,0xb1165708419c110d2843,0xebb88fd6c4334a10c330,0xa28cc10a37041cdc3063,0x7041a5ba84670410cc30,0x9330a24dc305a2e422bb,0x903dac20ddc302aee409,0xfc380b70402c41007aca,0x4bc0413b0b0ecb2c31f,0x4987c13c2702ed1c2b9,0x17067c7c11f2702685c1,0x9323025e1bb141b04285,0xc1870f0a141c380ff3fa,0xf6fbbe7f9bdfb7bddf5f,0xcff3bc7efebf6fbbdeef,0xb7edeb6e7f9fa7d9ee77,0x97e1f5cb605976054b60,0xd8b525db525cf525c352,0x59752d9350d8b505db50,0x5d35058b50583505da65,0xdc965dc1655c1651c965,0xdd160dcd60dc960dc560,0x59560589605856055160,0x54960dc152d95529d952,0x995525d9525cd5259552,0xdc950dc550d9550d8950,0x5d950595505855055150,0xdc9405d5405954058140,0xdd120dc520d9520d8920,0x5d920595205912058520,0x58120551205492054120,0x50920dd910dc910d8910,0x5d9105d5105c91059510,0x58110541105c86559465])
def g127H7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xf3403,0x30053239e201140000f0,0xd6d8d731bae000004100,0x3a80e0025000147b3b2,0x40000069e40004898204])
def g127D8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [2,0xca47dc4b1f78314cf78b,0x8d18016c9d2d883802d,0x907190c30592ecabb90d,0x73e524599ac7108cb5eb,0x48858e0c73ac88a461d7,0x244b87a25af218cebe24,0x83e243f5e896696912cf,0x762583d12d7c4675e894,0xfdae25a5848bf0161153,0x9498e0fe124e10b42e91,0x6ba43272189a2e90cfb,0x871293ce24d8c219f0e8,0x4b3c29137a428c18abbc,0x40842b0658289fc08a15,0x46d2630bbbb3e962b015,0x7639a380abb1cd1effd8,0x1627aef80210af690a31,0xce1185579749d0a36b80,0x151a0f429af6912373c0,0xb1498dcf02c54664f094,0x33b949a36d52996fff02,0xa279f596411cdfa05075,0x411ffd0a24f6e504bf81,0xc6fc21bc40a38c288b5,0xd70633ff006138e33111,0xe258397c731bf8a60f1f,0x64631e46922dfe012273,0xc3410175c44684c206f8,0x222b79031af54b88abd6,0xa0446d8f8112fb8048a1,0xf9f86826bc831872620b,0xae2269ad045217c92ad7,0x41127f601b88f9751114,0x73b611557e2442ef8898,0xbbf04b98c18cb3e11317,0xd8126bec104fb1f0226e,0x63822987f79308532a32,0xf88a3aedef44103ae0e0,0x91b19579847111e1c232,0x117130d104320c4c3c01,0xfc5408312c1c2c6451b0,0x588032200461d0b44821,0x90e86874118480f02161,0xa80421504010a0c07088,0x50914bfdbe7bd3bb1b95,0xb82b66b52b31b1eb00ad,0xdac1aa9a88a70a58a42a,0x2ca189fe9e69cc9b79a5,0x98e97496194292a91390,0x28ea8d48ba8a688b8748,0x5f84582e81c80a7e47d0,0x7ab79476874371e6fc6d,0x66c66a167e65e64c6326,0xf5e95ce5b259257054e,0x5385235014ed4d64bf4a,0xd49147845743e42740f3,0xf53dc3bf3a038937035a,0x33f3273092e82ce2ae28,0xe27726424b2302171fe1,0xd91be1a218816e15513e,0x1231080ed0d30b708d06,0x704c0250009dc9e57279,0xdc1e570799d9657659d9,0x56565595cd6552b9595a,0x55469589a55269585a76,0x499d8a656299d9525654,0x9d912564495512762495,0x89276149585255149594,0xe55239d94a56529d90a5,0x6429550a76129584a551,0x29d94656519d88656219,0x5484976825ce0972825c,0x20b7277dc9dc7272dc1c,0x972025c00976a5596897,0x3a7d8a8970a2dd949765,0x5995556552dcd4b70525,0xd6d165b25d2c972b25c6,0xcb7564d95916562dd19b,0x7362dc98b71625da4974,0x925ca4971985824b7642,0x5d90b7442dc90b7142dd,0x4c97532dc8e16032dd88,0x97622dd4897522dd0897,0x427d889d52275088b712,0x8580a15022dd8497612d,0xd4497512dc8497218580,0x615013d96017381dc9cd,0x6500dcdbfffefdfdfbfb,0xfcfdfef777d8352d4265,0x59560549505012044065])
def g127H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x10800,0x474003db0d000325,0x23b75e000000004631e0,0x2f000000061603b20000,0x3296283801ac0000000,0x1000000,0x6a000e0800000000b44,0x44000000000000000000,0xc5e00166be109a00,1,0x8d913000953370000790,0x1b27731040020880,0xf62d0001e60013d,0x6cf7e80061d000000,0x1f740cdb8000004975,0xecd627500004937a1900,0x620012b800000,0,0xb692a00e00000006e0,0x800cbe000000008528f,0x91296d00159a1600052a,0x7b0004ee001f9000e,0xde001b00004cd8800023,0x8ce80031d06000107c00,0x10d000458415117,0x1201e0011b9007599b79,0x9000000dda0000000000,0x69c000000018fc00000,0x31c800000000000,0,0x77a00000273f5a6ee00,0x1398000001a8d8e27000,0x30b0000,0xd800000000280000007d,0x40000000000000000000,0x2ec8b9000000,0,0xda0000000339c,0x4bb00000000000,0xefc00007000000000,0x16dc87bb5001769d,0x80000001240000000000,0x1db00000000375800000,0,0x3310008311b80,0xd4aa0c92b8d900000228,0x8004068ba2dde0000000,0x4b5000000000000000,0x11393e04700,0x82510800bf604c00000,0xbc9070000005c8002,0xfa00000000000000fd90,0xb8000000000053500113,0x13e9b8055,0x4c000422000000000000,0x7b8000000000000,0x7e718db0a5d00183c30,0x800c1100902e50416000,0x271000000000000010,0xb4004760340000000000,0x205edcd3bec00000,0xf613c00000000000000,0x886594000008280000,0x423001118006da00000,0x4c000001d6c00042c83,0x9c00066589194c000004,0x78000000590000000000,0xf4915b15800000972bb,0x667000000182150db1c9,0xd6800000000000000000,0x32a00000,0x2e104102093005,0x57031061115514104011,0x24c31030142104000])
def g127D9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x3ff300494033fc60091,0x803bee700ee003bff001,0xd900cef300ee71021f90,0x75e203840664f221248,0x78e3a18d158a082c2291,0x8407ecdcc1b096846b5a,0x422b1500995651975254,0xb60583505414048110ff])
def g127H9 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x82da,0xa74cc5194a9f00000178,0x40000000000000000000,7,0x3200000000000d7edf00,0x29880000000142,0x800001838005e6001940,0x802000007de0000,0x90000000014aed9fb,0x8000007d40000de0f0c4,0x531880040f6d88ec6fa,0x13000000004cd07e0011,0xac2e0018400000000150,0x25800c040038b800000,0x42b3,0x372e4000087a59b40076,0x1cc200000000001eac05,0x3d00000000894bccc074,0x104f043977e230004ac0,0x553cb31a9d880000,0x1d6c0a00083018c0b800,0x56200102000000000000,0xc632aa00000000,0xcbe000000000019b,0x800000000cb000425000,0x640000000112bbc,0x12000000003a711c0006,0x7ad60022780000000000,0x7c002e972e000,0x2028000d20,0x3ce000000dbd2c00000,0x1ca298006cdaad35800,0x238000354006,0x31d5528d02073b60000,0xd8000000000000000000,0x1f000000,0x348a4187bfc3f40000,0,0x1980009c00000,0xdca00000000c188a8,0x2670000000,0x52b0000000000000,0x22b800,0x250,0xaf8006270000000,0x716b40000000000000,0x1263e2000,0x57000033e220000,0x1b90800634c580000024,0x900005800000c472cc00,0x2d30001778900049a000,0x58c00000000cd00,0x10680006f00,0x30aec00910e800000,0x640032d800001754000,0x442cf0000000000000,0x4060001800000084800,0x1e2ef6c0001c9264000,0xa4e51001746ed0000,0x168418000012d33800,0xa6a00000000000002b4,0x5624aa0000000008a000,0x996b02d0000,0x2864bd8bc0000000,0x65400000000000,0x8d80046c0000030c8,0x1480000000000000,0x10e4000004867b,0xc00000000000000e84b8,0x430f,0x80f83d62d840400f0b71,0x22011400100430100000,0x51010141050001002])
def g127D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x430a1ff
def g127H10 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x100,0x55000000c24700000b,0x73004a00530000000000,0x54900c3007500,0x920000a8000080f40021,0x6056002300000000,0xc6d491e600eb0000,0xa58800c46700,0xf100b6000000a40081])
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
def g191D9 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
def g239D11 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
def g247D10 (j : Nat) : Nat := if 1 ≤ j then 0 else 0xff
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
def g255D7 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x22c20001b412f2200,0x321a644000148402,0x90d21d41a42809010000,0x5808000000,0x401004000000c050100,0x941b213857c4,0xbbc400cac1c05f037c,0x36c19c198b5c188a1a84,0xa0a809fa7c9ea789da74,0x9ca709ba6b5a56759060,0x1785c1685714d5153d4c,0x92a47d14420fd3c8e737,0xcd733cc72fcb72b8a326,0xc9322c811dc6d1945d15,0x44a100380c0280801803,0x238153ba7a5dd3d0e,0xe9e7874f33ba795ddbc6,0xfe9e45f52f0fc0801e14,0x40f0a11b8160dc0adddb,0xd85702c2b815b5c0b9bd,0x95a2f0df17878b3b3c18,0xe1e4c6cf217857ffa762,0x7d3affe9d6974eacfa75,0x27dba54e9d3976e8cfb7,0x42ddab56f15bb76ad9fc,0x2751e1381f099af6e74f,0xb7323e11b1f08fc76e56,0x7b7277da937ed4917864,0x7bb52fbdc672edc7b76e,0x30bc30346485c3202578,0x4227c30d5e1026f085e8,0x6f71ada6b65ad66b55ad,0x4eb51bce6b35acceb273,0xc96f23bc6eb17ac5cf15,0xbc3eb0f3c2eee5ab95ad,0x5ab54eb5aa76a95ba3ea,0x8f39d6a4faec9a65d560,0xd43b26a3935da656c3a2,0x66176997a2681985da65,0x663a364176997b26a686,0xe01756c1a9a1b805d7b5,0xe8996e0175e97a265b80,0x5d7a7e9792619756cfa5,0xe49865d5b0e979261975,0xed5a3e49865d7b068f92,0x61975ed5a0e49865d7b3,0x6839261975e95a0e4986,0x5d5b8a9b9060d756e296,0xe41835d5b9e898660d75,0x6e7a2619805d7b268d86,0x219756d97564e655c1b6,0x5d59099570ec9a6e4175,0x5c3b0e89965d5706dba0,0x5d5655c3a6e979261d65,0x6cfa5e4987597a6e5792,0x61d65ed9a0e4987597b5,0x6839261d65ecda0e4987,0x597a56839261d65edba2,0x64187597b5e899061d65,0x6e7a05d765583b0e8995,0x5d9606ea96e4175583b5,0xe89985d560ec9a65d570,0x583b5e899759560ec3a2,0x65d65581b8e899759560,0xedba266176543b0e8996,0x5d5506e975d9570541a6,0xe19755c15065b865d570,0x543b2699755c15069986,0x5d570541b8e899759550])
def g255D8 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (word80 [0x6955db60,0xe89955db60e899759760,0x6a69661f50e89965d750,0x659865d750a998758350,0x6998758350a997558350,0x69975583506599361e65,0x6599061e656817661265,0x6a57660e656597660e65,0x6997560e6568d7560e65,0x6597560e656997560265,0x6a3935da65e89985da65,0xe81985da65681985da65,0x661935da65e8d905da65,0x661905da65e81935d665,0x659935d6656a686e0175,0xe9596e0175e8996e0175,0x68196e0175e8986e0175,0x68186e017568d95a1975,0x68195a19756a190a1975,0x69590a1975e5f9561975,0x68f95619756839561975,0xe9f9261975e979261975,0xe8f9261975e839261975,0xe5f9261975e579261975,0x68f92619756839261975,0x64f9261975e959361975,0xe899361975e819361975,0xe959061975e8d9061975,0xe899061975e559061975,0xe499061975a9b9060d75,0xa5b9060d75a1b9060d75,0x69b9060d7565b9060d75,0x61b9060d756a29660d75,0xe898660d75e898660175,0xe8186601756199021975,0xea58621975e8d8621975,0xe89862197568d8621975,0x69995e19706a575d9570,0x69997a15706a196a1570,0x6999799570aa19699570,0xe1993995705d59399570,0x5d590995706997599570,0x659759957069b9061570,0x69b905d570696965d570,0xe89965d570e81965d570,0x697865957069b8559570,0xe999859570e959859570,0xe8d9859570e899859570,0xe819859570e817559570,0xe617559570a197559570,0x66175595706197559570,0x29975595706a576e0165,0xe5b9561d6568f9561d65,0xe979261d65e839261d65,0xe579261d656839261d65,0xe4b9061d65e999061d65,0xe959061d65e8d9061d65,0xe899061d65e559061d65,0xe499061d65e419061d65,0xe958760165e898760165,0xe818760165e957660165,0x2957660165e817560165,0x683965d565e1f905d565,0x69b905d565e99935d565,0xe81935d565e59935d565,0xe99905d56569576e1560,0x69597d9560e8175d9560,0x69d96a156061d94a1560,0xe8d87a15606a576a1560,0x69d969956061d9499560,0xe8d87995606a57699560,0xa979361d60a579361d60,0x6979361d606579361d60,0x6549561d60657905d960,0x6a6955d960e89955d960,0xe81955d96069b985d560,0xa63905d560a5b905d560,0x69b905d56065b905d560,0xe89985d560e95965d560,0xe89965d56068e655c160,0x5d6655c160a99755c160,0xa15755c160699755c160,0x65f9059560e959759560,0xe899759560e819759560,0xe8d87595602958759560,0xe8175595606a17559560,0x69997e19506a197d9550,0x61d90d95506a176d9550,0x6a575d955065d75d9550,0x6829661d506589661d50,0x6a3955d950663955d950,0xe99985d950e8d985d950,0xe89985d950e81985d950,0xe89955d95065b865d550,0x6a6965d550e89965d550,0xe81965d550659865d550,0x65b865c150687655c150,0x5d7655c150e19755c150,0xa99755c150a59755c150,0xa19755c150699755c150,0x659755c150619755c150,0xe899759550e819759550,0x6a587595506a17659550]) else (word80 [0xd5c7b075,0x6ee95d5c3a57471e89d1,0xc3b57771ec9dc83b2822,0xec9fc59b57e42ec9ea0,0xdb079816d9f20db67b5a,0xe9dc577a77061e99c18b,0xa66f63ed9b997b56e63e,0x99b997a56e67e8db993a,0x66d66e95b59bb0730cec,0xdc911b06b40ecda50bb2,0x6944ec1a4fab96740ecd,0xa111b66c56ecb318fb8c,0xb63ea32ccfb2cd7aee32,0x9eba8ca63ee3298fa8ca,0x1a6d8fc6bb63d1a6d8f8,0x6bb63c632e0e1afb7387,0x4ec0e1afa7386ce9cddd,0x3a23780edcea1bb23a07,0xec8e4cfb24a23ec91d5b,0xb24423ec91137b23656e,0xc8d97fb73165ed4c5aba,0x7306be9cbdcba52f86ec,0x8cc9fb23380edcca17b5,0x3286ec8c89fb23223ec9,0x248fb24356ec9008fb24,0x7a2e09dffb72784ed49,0xd5ba52784e949e1bb027,0x85e949a1ba2267ee5ca1,0x8cb82772ed49dd3b0277,0xfe5c9dcba52780e5c99c,0xfa52674e8898c6b92462,0x2a4963b972385ed4a61b,0xb2294d6e09d67b02759e,0x8898b7b72236ecc88dfb,0x2228eed4aa3fb22a45ec,0x8a937b2c965ee32197a8,0xc837ecb1e33b2c53cecb,0x162fb8c391ecb0d1bb2c,0x312edc846bb3211cec88,0x47bb02147e9c5d33a616,0x4ded85537b5154de9855,0x3ba6145ae9c5d7ba7166,0x2e98597fb71563ed8557,0xfa71563e98559fa31560,0xe9c5193a61409edc6437,0xb21912edc6073b218636,0x184d94b8106eedc41d7b,0x106ee9c41c3a70f75e8,0x83cdfb21238ec048dfb2,0xe07ec8451fa70e1cec8,0x384bb7201cec880abb71,0xe33ec87893b21d836c07,0x135b80359ec00d67a202,0x2aedc00cbb30033ec800,0x33b3000dec800efb30d9,0xec81a25a60a896582a2,0x5a604446d42513b50645,0xec819c1ba0b19ecea06f,0xb2a85069e9d3fa7a248e,0xa61411ba901d6c6406fb,0x28d03ecac00fb2b90aec,0xafc2fb0bf7665ef8d3b2,0xbd2bedeecd7b0bc18ecd,0x816fa7634be8d641bb27,0x80fec9dc55b57d3d6c19,0xcf5b06a3dec1a007ba3b,0x176d0fc63b23d026e8f8,0x5db43e18ec8f009b9451,0x7ecd180fb236046e8d41,0x5ba34056e52009b94117,0xecd08f5b52c3ded4a8f5,0xb62b3f6ccada5a62d6d5,0xd4b80fb2c9296df18c1b,0x8c43d6df10c3b8c349e5,0x86c03ba1a4be8c544fb6,0x1f02ecc040fb201436c4,0x2507b2062c6e020ffb30,0x50e6e81d0db107506a42,0xd71a80b6f5d433f35f5a,0xf9d7c7bda7ebaf4f7a6f,0xcbde5bf0ff6ebb3dd9be,0xaf756faafd3ee9df47f9,0xf5cf3e6df2ef8fdc7be2,0xff0df7b5bbadcf6e6f6f,0x5b5edae6d6f6adb3ed9d,0xec7f63dafad79eb7b5b7,0xabed5deadf53fa7ed3de,0x9df4bfa5ed2de8ff3f59,0xf3cede6ef33f97ecbde5,0xdf2bf95ecade3fb1f78f,0x7c79e2ff17d8bbc3fdf6,0xaef575ebae5d6eeb5757,0xbab5c7ee3d6fab7b5bce,0xdcf6deb6ddb5edad6d3b,0x5ddaded3f69eb3f59eec,0xbf65eb2bd8fec7d5fcaf,0xd57cebbd5dbaddd67eaf,0xd57baafd3fa9f94fba7d,0x53de9ed4f3a73d37e9af,0x4bfa5f51fe7f53db9bd4,0xd7a5f72f797b4bce4ff1,0xfe8fdc7ea37d0fe87dc3,0xde1bf0bf69576617606a])) else (if j<3 then (word80 [0x5f62bb12,0xd87ac35616b09583ac0f,0x5ffafdd7cebdf5e42ee1,0x754b9a5c92e156f0b635,0xa52cd564cb19588ac255,0xf6aeb56e2b3958cab755,0x7aa9d53ea97547aa1d4f,0xea77537a99d4b4a4d521,0x28d9452a1c50a2831408,0x9f54f6a7953ba9cd4e2a,0x6c93409934c2a5cd2d69,0x5e4a7a50d26692b48e24,0x511fc8e846e23251728a,0xb44ea25511087b439a1a,0xd0c6846417a044fde7dd,0x3e09eb4f2c78c3c11d6c,0xe7873238a9be0ddc6c33,0x4999eccc663c31017f8b,0xb85c52d4967cb0655f29,0xd14989e84cd258124c8f,0x846222290ec8424061f7,0x8f5076a38e1ba0d64652,0x2fa1680aa44ee24c1210,0x8984001d60d986a433e1,0x950bc05b82c813608903,0xd81980b1041817c06400,0x1fedea87fb7a91f6c29,0x94797a551e5e9147979a,0x53e5e65539798206c28e,0xba7a2246ce8891b0a25,0x3e9e8483b79d53e9e749,0x3b59d27ec2754fa7a057,0xe968083b79c53e9e7093,0xb59c57e96709bb39c206,0xc27dbba7a282e5e8a0ba,0x79e246ce7891b09e82e5,0xe7883b79b24ed66c9fb0,0x9b51e5e5d47a79452e5e,0x594f979557e56554fa79,0x357e964d63a3934aece1,0xd29b3874aea61853b984,0x4aea610abb78433eca11,0xebb9857aea615ebb2880,0xdeca3135b98b67ece2d9,0xfa38b1e6e24885b79225,0x6d648a1b19221ede3c97,0xb58f27eca3c79b590086,0xea4095b590286c641e7b,0x78d7deca349fb28d086e,0xa4479b891216de4495b5,0x91286c64487b78e25ed6,0x389fb28e3ceca3479b0a,0xf4ded6b935b5ae4de96b,0x9a1b0ae68e8ab547a7af,0x256c2bd35b8ae53edeb9,0x5fb5ae53e9eb95fa5ae4,0xdecac139b0b0686c2b0b,0xfb7ab38ed6ada3a2ab4d,0x6e629a3b08a68e8a2473,0xb2c21cecb0537b0b84d6,0xc2e137a2b71aeced873b,0x2b64de8ad931b3b94dec,0xae473b2b51cecacc31b8,0xb44c662d17987b424eca,0xc59986b239ecf0237b2b,0xd37ecaf4dfb2ba61e599,0x71b3631c6c18c71b662,0x1c6d58937a5621ced980,0x73b5604de9581f3b3607,0xde818223a7638ae998cd,0xdb3631c6cd8471b06188,0xe9d862ba6618ae5984dd,0xb3615fe9d8997a5622ee,0xdd817fa76033ed980dfb,0x56065e9580ebb3607d6c,0x17d6ba75e5de9d7587a6,0x5d61e99697ba75c62e99,0x717fb75b63ed96d97b55,0xb65e556d7fa75b63e996,0xd97a55b67e8d6de3a759,0x4de9965eba6594de9565,0xefa5597ce8d65f7b0596,0x3e996597a55967e8d659,0x3a65866e9561f7925887,0xe1d9577876455e599213,0xa663246cd8d5fa56223e,0xd98093b56057e95809bb,0x36088e1d8e13a661246c,0xd8623876184e59856b87,0x5e5de1d7557a65a5ee1d,0x717f875b57e556d5ba65,0x957e956563a3596ae1d4,0x5ab874e7ee1d31c3874d,0x446c14043b24f6ae1d2d,0x83874d07ec93ccfb2667,0x7e5d5da3b05678e5d59e,0x7975568e8955fb975487,0xe1d508ab95331ae14dfb,0x975351e5d520f975289e,0x1d484bb7831aece0c73b,0x2831eec20c83b2811aec,0xe0073b28059ec9e047b2,0x78706c1d97cb8756eed5]) else (if j<4 then (word80 [0xc2011618,0xb080000007c06992489a,0x2072906c80d7c8ac2672,0xc51b5b2c86f9051c158c,0x200a9bbc00042ae3f00,0x4500a4e0014607880a30,0x8bff76780330077fd29,0x8033a78031a78031829f,0x8000851ebc04497e0002,0x121f800084ae00c73fe0,0x88010dfe022069b7803,0x2879e000198fe0140ffc,0x5fa00492f36e000cd0f,0xc0083268f141d700638f,0xc018c5a3c5060147e00c,0x60278a0eb8031d750064,0x51fc008a4f160002163f,0x63013c5063fe178d80,0x921ff2e180019e7febe,0xc004702fe2000cddf2f8,0x33000342797f10006600,0x97f00115beb600066cff,0xad800198bfb000328040,0x10040fc008300802027b,0xfaae41243f2a0019aefd,0x9abf1ed00066bfe804,0xa04f7f55c824ae3fe002,0x367eb1d80019c001be5f,0x62068999d18a630fe1f9,0xea5b850509462434401,0x60b415c2b703e08e22c3,0x88351782b8068091401e,0xe12a43b41f4250aa0e0,0x9e8591d51e4882900f24,0xec0548a82c0e0285a03e,0x727e2708b0ff0c8b9168,0x2f03fc300a3956180f21,0x1c2284ee292000b22624,0xa0768bb0c25dc3386474,0x6594ba8008562588910b,0x1582823e80e102ae1312,0x6e18e3e47c9444688817,0x50e624a48c9786e1f633,0x8383a8741001383d8170,0x3ac899030461ac008200,0x50f000e8647bc2e86d8a,0x856e2015983d140720e0,0x22d0cc591b22a702c1bc,0x1d8906ce44cb78809f81,0xa1bc8a0740dac1781e0f,0x831c1d83707e0fc0f85d,0x73eb5f56faa7d46e9f74,0xc7a49d16e85740b9e7cd,0x6e6572f795dca6e49721,0x38ebc6de2f715b89dc40,0xe15707b811c00df8efa7,0x7b7bcdde2eef776bba8d,0xcdee3b6ffb70db46d6b6,0x99b44d98ec5b617afcd7,0x66b875abac4d5b6a7f52,0x1a84d3ae99b4bda48d15,0x6867423a09cfde7cf3d1,0x9dccea67333819b2cd26,0x67331d980cbc659f2bf9,0x51ca164d323f904c7e63,0xbb1cd8cfc5f62c314588,0xec38616309b842c12e05,0x30097f4bf35f7af9f7ba,0xbd95e9ef37784bb0dd36,0xe7972eb935c56e0d6f5b,0x72db76d996c4b5e5ad2d,0x596a4b4c5a42d01673b3,0x5d98ec99636b15585ec1,0x7603afdd7bebc55daae7,0x56ceb45596ac4d5f6ae3,0x564aac5502a5b51aa83d,0x3f29db4daa67d3129734,0xa6a4dd24290b47aa32d1,0x76891440a15d0567ff3f,0x49f4cf7a7a73c89d94e9,0xe73f3979c24de26cf35b,0x9a7cd0a66d32a98c4c42,0x61130097acbaa5c52d59,0x5ecac25432929454a0a4,0xf526a931494648123891,0x3c87e42f20c8fe47963b,0x51ca8e146c635319c8ca,0x46323091748b645822a9,0x14389bc4be24f11f8844,0x3c21d10d586142ce1430,0x8d83ec1b20c1054822c0,0xd202effe7f13f69fa4fc,0xa7debec9f4ef9a7c6be1,0x5efaf757b6bd95ea0f40,0x7983c8de24ef57743b65,0xd92ec175cbaa5d3ce937,0x45ba0dcdce6672f3959c,0x82e367173899c3ce166f,0xfb7ddbceddb6e3b6edb5,0x8d986c6b605ae8d676af,0xb53da7ed37697b47da1e,0xd0367bb38d9aecc76593,0x29992ec8f640b1e58cec]) else (word80 [0x29d0807584,0x6823419604c84019c0,0xf1fa4a8cc85683ee0402,0xb2d8a581f70201ee0400,0x2581ce958cc864c8a20,0x670201db0f6c2000000,0x3411a08d075c0eb81000,0xd8436100ee8c52fb1a0d,0x80fb815e42a436431bc1,0xb607968614381b21e703,0xce04031f3822b62e68e0,0x7820001db080301b2100,0xb21ed87b6100ed87b6,0x1007de0805b03b686d81,0x60c14bd138300b60402,0x27b613af06d81b60490e,0x8cf220a353e0a2602c0,0x7edd1346cbc1aba1a3a1,0x8d84038d0db06080180d,0x90eac4c2032ccd5499c6,0xc4abc18d84014783b685,0x3782e742015a62000000,0x32100c3a15a08000,0x61cba2aa2688c8732b11,0x908000190ad0400c855e,0xe941ead08c8568264264,0x2b4132103e0a2ce8c59d,0x18b3a3130117039d18a9,0xd21a43d858a90d21a43,0x48618b04010c58200862,0xc101c54417451521a434,0x8580b010ba2898080006,0x6562321d5a1190990ad0,0x4c84c87a562000000602,0xc040068277a144341d70,0x3ae040000020e8400f78,0x273c10035e08000301ab,0xa1ad8184c068e8400b78,0x2011610000007ba100d4,0x1d4129e0ea08000007d4,0xba200efa200c7505ea60,0xa9c0cf685ab304388433,0xc1d41d4197022bc1a7f3,0xa41b7d758fedaaa8c000,0x683486908d0468200,0x12f9829ba19ba,0x1da08cd08043e147b41c,0x703aa840000bc8548690,0x800075a2880000005d50,0x5484000000034e551007,0xee0ea0c7f316a0db818f,0xe62a43643d61ab08045d,0xc5d080007ce0c1d0ea0,0xea0c7f316a0fae08baa0,0xac872d08053020015b10,0x590d302000000019b,0xf8e0803dd08055caa25,0xba1a607a704022c31612,0x5c924b82a0d5f1056e06,0xac20000db0f2e0ec426d,0x84025c08000000000000,0xd04683486c84,0x68234100000097020000,0xe742018ea0a3562ab0,0xe6c337a1004d066d0ea0,0xf0e0804b8100063e0818,0xf82d4180ec4b7434c0e6]))))
def g255H8 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x266068e83b040a,0x4468835b610aa858ad1c,0x34c00006c306000027,0xc223598a061b1e4044a7,0x400d700001d30e000000,0xa013130000000000,0x4000000932f3983c,0xc800040000233a99a000,0x6ee56960005001,0x989780000274a8024600,0x47c2f370548000000092,0xa30a000001816e01d840,0x64000000502080409a])
def g255D9 (j : Nat) : Nat := if 9 ≤ j then 0 else (if j<4 then (if j<2 then (if j<1 then (word80 [0xf462a0b,0xa2159dc3034e6181bf7b,0xf6fefbeefe7fe7bdfbde,0xfd7fd7bcffcfbc7fc7bb,0xfbbefbdfbdbbbfb7fb7b,0xb6fb5faffafbaefadfa7,0xf9ff9fb9ef9df97f97b8,0xff7fb7f77ef7db77f77b,0x77776f75f6ff6fb6ef6d,0xf6bf67f5ff5fb5f75ef5,0x7f57b55f4ff3ff3fb3f7,0x3ef3df3bf37f2ff1feff,0xaff6ff2feefdefdafbaf,0x7ef7af76f6ef5eefeefa,0xeeeedeebee7edfedfadf,0x6deedded7ecfebfebfab,0xf6beebdebbeb7eafe9fe,0x7fe7fa7ee7de77e6fe5f,0xe3fe3ee3de2fe9561f60,0x5d985d82955db6065576,0xd81965d76065d65d8296,0x61f5065987d419761b50,0x66176d42965d75065975,0xd41865d75065d60d4187,0x583505d560d419661e65,0x64d879959061e65e5d86,0x9979061a6565d8699590,0x61a655d9849959760e65,0x659839957660e655d583,0x99576602655d58099795,0x5da65e4d76997905da65,0x66176995935da6564176,0x995875da65e617599793,0x5d66565975995935d665,0x64175995865d665a5b83,0x5d686e0d7561b835d696,0xe0175a1b805d596e0175,0x61b805d786a197565686,0x5d590a1975e5d865d795,0x61975e4d865d79261975,0xe41865d5936197564186,0x5d79060d75a59835d686,0x60d75659835d58660d75,0x219835d6866017561980,0x5d48660175640865d586,0x21975657865c196e1570,0xe17655c191d957064365,0x5c175d9570662865c197,0xa197065e855c196a1570,0x61a855c3869957065e65,0x5c19699570652655c193,0x99570642655c17599570,0xe4d865c39061970e4185,0x5c28661570619855c390,0x5d570a59755c2865d570,0x659755c1865d57025975,0x5c39859570e19655c385,0x59570a19655c19859570,0x641655c186595705d565,0x5c187e01655db8059698,0x9d565e55875979261d65,0xe41875959061d659d980,0x596756016565d8059587,0x601655d9805957560165,0xe5975597935d565e4175,0x597875d56564d7559590,0x5d5652597559576e1560,0x65f6558187d95605d765,0x58196a15606528558193,0xa156061e8558176a1560,0x65a65581949956064e65,0x581909956061e6558176,0x995605d6655839361d60,0xe41875829561d6065587,0x5809561d6061d8558176,0x61560e5576583905d960,0xa5576581955d960e6175,0x583965d560e417558385,0x5d560a6175582965d560,0xa1575581985d56065975,0x583655c160a557058285,0x5c16099570581955c160,0x61570581755c16059570,0x58390595609d56558197,0x5956061d655817659560,0x5d56558197e195066365,0x54197d95506476554190,0xd955061f6554176d9550,0x5d76554195a195064686,0x54187a195061a7654186,0x9d550e41875429661d50,0x659875409661d50e4186,0x541976195061d8654398,0x5d950e5576543865d950,0xa6176542865d95066176,0x541955d9506197654390,0x5d550e1975542965d550,0xa1975541965d55061975,0x543865c150d957054296,0x5c150a1970541965c150,0x61970541755c15059570,0x543905955065d6554187,0x595505d9655417559550]) else (word80 [0x530055a5,0x8032d04015e95f8b746f,0xc67a07e32d3410c69a5d,0x6b3128cf859676bacb34,0xe1655e2eb2ab5978e1ad,0x2c739ea621cb2d10c386,0x8b63c34534e1a24234ef,0x825a07c09d3bc07e8de0,0x4744f027a0781fd1bc10,0xe89e06b4af651a7793ed,0x3c9fe81d8634cf58fa6,0x75c6533ae3a19d71b0ce,0xb9ba075ccbabb836a780,0x5b4fc031a6e01ed1f005,0x6a7786351bc51a7de3ad,0x1ef0cea374f745babba8,0xdb83d16d8cea36cf745b,0x631a64e5fcaa70e69138,0x7b469c49a04e19d3268f,0xe8d3487449a4ba04d5ec,0xaa631e95418d4aa0c5a5,0x506252a831e55418d2aa,0xc59550624aa85ee8142,0xf7269f27a05093c9a7c2,0x68124fb409231a84738d,0x2239d68d1cfb408e7ba2,0x463fd02342655216b2eb,0x237a5591fd1ac85e9d71,0x730eb815a9586ccbac30,0x61d6dfaecb6c5875a80b,0xb2d2de5d2c7f4696db97,0x4a06d32285699146b4a8,0x217a63e0fd19f08e88f8,0x6f4a7c3fa33e21d11f09,0x68110db4a806fa53d16d,0x3a11b698fd0b467ed2a8,0x43855321c26990da70a8,0x6d29843854b21c26590e,0x1340bebba95eabd1af36,0x65d74ff40bab597531bd,0x2a98fe8d4c2f4eaeb987,0x570ad4a93665d49f32ca,0x2c187567ebb2b3161d56,0x2ecab11755568c3aa42,0x5d9523aeaa817a5327dd,0x29941e88ca174064db97,0x323dd1191fe80caa74a6,0x350a531abd198d7e80c4,0xdf4a6277a331375499e3,0xe5cbf57405edb972f3fd,0x179f69cd2132e69a975,0x3411d11909e80c86f4a6,0x23fa3316dcb981be94c0,0xff406025a73484bb1a47,0x5d4d093507665a73b3ed,0x31d9fe98e0cb4e747da6,0x3a4cd21d2768ce8cf4e6,0xf92a636c8d31b52e14db,0x350a6d998536c8ba9e09,0x6a4e4cb4e727da639ccb,0xa9ca6690e53b46739175,0x35ccba9a836a7685b4fb,0x449a0da21d16c90e8b61,0x9745ae43a2d71ad46b15,0x69f592341ac37a8d545d,0x16a92ea34d274ba69fa3,0xd3af53695769b4b554da,0x3a9a6d15dcb100d69480,0x8b424049a0201bd28f8f,0xe8c7c87443e4ba01f5cc,0xb0f34e5885a32c42b597,0x2419d31206e9c997b0e4,0xccd87251bd28e0fe8c70,0x8744384ba01c24d38ead,0xe5c6c674c36bba92306d,0x28d0669468634c2eb7a7,0x1507d30aaee98541f4a2,0xabfa51563d18ab2e8855,0xa7402a1ba5150fd18a88,0xe8854674c2a3fa31521d,0x10a8b69c60db4a2d37a7,0x13afd0098be9c4c4b403,0x2bfa9221ad4082368441,0x2340208ba20e49d00706,0x6a43cab4e1e8da10f9fd,0x386dbe8034af4e1b6f86,0x12b6c3090be9c35a30c2,0x40fa72d19d314ae660a1,0x7b304ee5972766c395c6,0x5d4ada30e5509762a8eb,0xa9508e880c4f40060da9,0x219d30139e5c004b4e0,0x90976048eba82126a028,0xcb4e1491a50a49d28427,0xe8c20cb4e1291a50954d,0x84d2e9c1ccf4e0f9ba6,0x6cd5303666981b314c0,0xd9a9606cccb0366a181b,0x330c0d49860612d48592,0x6a02f32ea16a9a10bccb,0xa8280ea6681745600ba2,0xbf03d1c981e8e61baeb1,0x4e17589c4ba9a82e8b5c])) else (if j<3 then (word80 [0xce29a067,0x14d33353e1d8d6740c62,0x9a665a7c3b1586a5cec7,0x4ae773a574c1d13a6be9,0x5cd074cd697a56b51d1b,0x5a9e89ae9f2ed573a56a,0xc1d13561e81a9ef2ed4a,0x7a26a59d03520aa5b72f,0x2ed3afa569d652b4bde5,0xda52f4ad296a96ccfcbb,0x46fe81a1ef2ed0b3a068,0x6ad34cbda9a45eb4d22d,0x5a89098d0482c69a14d3,0x4b026ba57fcfd2bfe8e8,0x9ff4f40fef5a99496c2c,0xb3d69a35ad511931a08c,0xced3441a69df16340f94,0xfa778b1d33c5ce95e2ff,0x46f183a278c3d03c1ae9,0xde14746f0a7a27859d03,0xc13695ed4746ec4da67a,0xcfcc3ae7661d73f4ceb9,0xd8675d3d3bbe95d5dec7,0x51bbb3a2ddb0d2efece8,0xb72c751b7b3a2db26d32,0x713e99372f4e8db3a246,0xdbd0230a6a51c9b508e6,0x9a74740d323ac6811d4f,0x448cb3a046b0d2b04369,0xd721b52b197a73dd7d29,0xeece88f54f447b31a643,0x98cb21c36957e1b4eaf0,0xda95287d2996be94cb67,0x4465b7a032b05498cae8,0x8ca674064a7a23259d01,0x913e94c6ff466283a530,0xb8d417efe80bd67405eb,0x1a63b59d31c69698db4a,0xea6b83a2d9c1d16c60e8,0xb5ee751abbba2d5b8cb6,0xa6169b4b7b4da2d5a62e,0x27d30da5694689b4c2ed,0x7a615a7d38a93e9856c7,0x4c2b7fa315c1d10ae1e8,0x5547462aa7a215a7d38,0x99ae9c4dab0c3331a019,0x26d40cb566066c30c32b,0x1a019b0c30a29e885167,0x40299fa70eddd1076fe8,0x3ae32c2371960d14d48,0x81a69c412b4a2097a50e,0x53d1073565835ab50592,0x1a52c98d016586a0a35b,0x4a5121a92791d281cae8,0x80e674006a7a20359d00,0x193e980ac35003afa501,0x26d400a5e94070b2c19a,0x6a606d2d3030c682b837,0x475a1ba0ad68d4563c69,0xeb23b4b5819a3aa0cd05,0x539e5ea9d74f5117a5a8,0x75cbd445e56a17753355,0xba29a5cc34d8b69ed46b,0x4b6a45a1b524d05a836a,0x6d06b4b6845a1b424d05,0xa10e8acd772d4435a5a2,0x22d0d112682888745400,0xea99f69c35234a1a91a3,0xd48d086a422d0d932e8,0xac087456023a2b006d4d,0x891686c487455ebb969e,0x22d0cf10e8a741d53384,0x3a2d006d06690e8b2c1b,0x4f98cba2bf07d05f90e8,0xafc5f477819a3c206d46,0x836a3016b0f8035a3bb,0x1ad05da2e8ae46f476c3,0x7a0b65ec35d0dea2e127,0x417037a8b71dd1e48ee8,0x3247f4d903fa7c762cbe,0x38fea7187b538d4197c6,0xaacb630fe831acb4d8b6,0x596c5b2d0628fe8f1acb,0x478a0da37106d038d4e5,0x9c46b46e2cba57065d03,0x832681c28f4ee16ba570,0x65cab85ae55c19724de3,0x3a66e1bd2b70fe8db887,0x44dccb926e9fc3b8bee5,0x9c62f4ae14787708bcab,0x80668dc8ab40c98f8767,0x36d0339baa184db40c26,0xfa6637dcb31a4e818cdf,0x4cc42da0640ad03390e8,0x9d16f2ed443a26a0b54b,0x6b6e5da66f0ed21aa96c,0x73cbb44fe1da1a74132c,0x7a39309d2c949e821c4b,0x4b0d27938663d1cc0de9,0x63c7f471ebb96841fd1c,0x18969a15a30d0a55a581,0x30d0c09968204af4afe5,0xfa27f33d03f99681f423]) else (word80 [0xd72b7a56,0xa0ad05587aae7557caa5,0x5531aa345402a72d4d12,0x9775288a45d46d28a750,0xfaa13141a28094fc49e9,0xd3b9274c4e169bad3602,0x6964ccc98e9307a5e24b,0x7096352ae252a49e8932,0x9257a48c48c8915121fa,0x41547c88ec91c1a36546,0x708c3517a22c4453089b,0x511ea21243da87150cea,0x175429a849507ea0de41,0x90828503d20504060803,0x8fed9fb93f027db0fab9,0xf273df47b0cf441e5b3c,0x667810eef1dc33b32761,0xeaa1d3d3a5a7400e719,0xcc8393a71b4e259c1a37,0xde6f50dd49b7d36a26cd,0xd8a9aec35846a48d3a9,0xa4a342867c8ceb99b433,0x2865c8c99991831e2631,0xcc4f1877309c6060bf61,0x7be2f445de4ba297292e,0x165bb0b6096a62cf4597,0xcb1495fd2b965660aba9,0x5562a605448a7694c429,0x2e521ca2b942e28204fa,0x9de93a526ea4d2098f1,0x2f1258a4a8893b124a24,0x4048088eb91a82300457,0x88a1111321d042f08489,0x66206840407f10fb51f,0x203db07a50f191dee3b9,0xc76a8eaa1d363a047390,0xe561c6a38046f70dd51b,0x5a35ec6a90d301a08336,0x6580c8418b430e860b8,0xbec17682e385ab8b2d16,0x22b705610a9714d628f,0x450a89f313ae26ec4d50,0x97b12a6249047a08c311,0x38219041688050fac1ed,0x83c887700e921c9c3810,0x6de0d741a6833c06560c,0x5418242f305c40b4815c,0x2a3051809c412c023b0,0x44708240f601d6837606,0x920c7418102d2053c09a,0xc11e821303cc06f00c88,0x160024a03c8064009300,0xc400bc0004868eb64341,0x5a69a0ab14d1d567e5ea,0x92b475495a0aa7bcbd49,0xae9e99ef2f4c97a5a653,0xd1532ce829a574b512ba,0x3a894d1d44ae82a25341,0x51a3a7a8d1cbd46ee96a,0x2572b51bb95a895c9d44,0xa64ea1ef2f4f2395a795,0xc9539ae9e95ef2f4a97a,0x5a591cad2a8e8e954f45,0x4b2b92a5b1d1cd5868e6,0xa9f4f6783a2b326d4519,0xa69e8d2b4b46ada1a335,0xd3d0a5e96854f45424da,0x5a24ad2d12868e895b43,0x454fa7a0bfd1d060e8a8,0x1474740a7a2a09953524,0xc69a92650d493186a499,0x4b524c65a930b0d48d7a,0x5b0c1d15861682c1ef4f,0x6123a5b095d15853e9eb,0xee74b5f83a2afc2d0579,0x3696792b4b3cada19ea7,0xd3ce93e9676e74b3b83a,0x29dc3d04ea5e96754f45,0x3a4fa3d0c1d1683565b3,0xdab2d9d83a2cb27d0659,0x3e9f29af417ed5a0bfc1,0xd15f93e82fe9b47794da,0xbc6acc5f5361ef9ab31,0x7b4d87bd51d1dea5e8ee,0x777457371a3b6b8d05b4,0x865ae2e30d717186b7ba,0xd1e4dd68326e34d8b85a,0xc4b8d3619368dc49b40,0xe383a570c1cab860e81c,0x30340e0d7956fb9cab7e,0xe49be9f4edc4fa66eb1,0xd33713e95bae74add739,0x56ebfd1b760e89bb0724,0xdd87906ed7cb38a568dc,0x6574ae12ba07094d0386,0xee95c2572ae1bb9570a7,0xc3b7c8e55be5724df4f8,0x76e41d33725e95ba472a,0xdca3a36e53d1374ae49b,0x92b46ce95a067cfc3b32,0x56999b3f0ec697a66391,0xcb31efe818f3f0eca95a,0x665cfc3b125e99885346]))) else (if j<6 then (if j<5 then (word80 [0x3c2f077,0x816ee7dd97baab74d6e7,0xfdcc7b93f71b6e16dbf5,0xb79b6e7edaddb1bb5b36,0xa1ed1fda0db3b766c6cb,0xed94bb2476396c5bd88b,0xb0bb60c6bfbd7cbaf175,0xd76b94d6e1ad7759c6b1,0xdd5ffab8755fea9fd4ff,0xa97751eea1dd407a78f4,0xe0e99cd2f1a57349ee91,0x6d1e3a36b459e897d0ff,0xa1bf428e82dd02f9fe73,0xeee7c7cf639e473c1677,0x3cea39cb738d6703cdcd,0x9b37358e698cd0199a73,0x296635cc45981f2f4e5c,0xfcb6996832c4e571caa1,0x94bf28de501c9d3931b2,0x54e489c8d3911f215640,0x3c7c38f0f1cbe374c6c5,0x8cfb18d62fac5a98acb1,0x4de283c4dd8957117621,0x6c40787b30eae1bcc353,0x86430bce15bc27f84670,0x8060e3c18b82df04c607,0xac09f80af0095ff8bfbf,0x7f22fdadfa2bf137dcaf,0xac5f2fbe297bf6f6fdeb,0x8bd357a3af395e55bc7d,0x788aeffddf3bbb97702e,0xd65d96bafb7596ea15d2,0x5ba1573bae6cdcc1b95d,0x725ee45dc73b8b170eae,0xe5c02b7d16f3eddc5b9,0xeb6ff6d8eda85b30b62f,0x6bfad74dad0b57f6a7ad,0x44da74b4bf690ad0fda0,0xcb3e56762ce059a9b30b,0x65becac593cb23563fec,0x7358dab1776242c3c585,0xcb08560dac0fd802afcb,0x5f32bd85794aef15d92b,0xa7d72fae275bfeb70d6c,0x6ad1f59ceb28d63fac4f,0x5856afa55e2ab9556caa,0xcdd586aadf556aa9d552,0x8aa2353daa7154cda973,0x525ea415462a89950dea,0xd53fea7c34efe9cd538,0x5a6c34d02995d314a5ff,0x4b9a96352b1a5394a229,0x39d255a46d48428fa51e,0xa38946a28c3516ea2af,0x44f2890d111a1fd43b28,0x6e50c5a157425a840506,0xca0ab40fa81550139fef,0x3f6e7e0cfa69f173dee7,0xb1cf429e673c4a7784ed,0x49d733a4e73cce5e9c91,0x38c670c4df89ba136d66,0xcecd869ae5356669acd1,0x39a0133a665acc9698ed,0x31966254c35984130325,0xfc4bd197852e865c94b7,0xb96a72cc25884ae89581,0x2a5a535ca41942d27764,0xdd499692e7253249348e,0xe919d22b6446c8719093,0x208e403c7eb8f871e763,0xb5c7478e411be235fc68,0x28cc518da30345d58b41,0x15e22aac52e8a1513aa2,0x61449588e3110620543e,0xa876d0e461aec33685f7,0xb72154427c84ab08ba1,0x241d9834b060e0aec12,0xb820d036e058c07f80b5,0xba0013fd97f44fdd9f,0xa5bf1c7de0fb11f4ebe6,0x87c68f811ee8bda37ada,0xf4f9e94bd0a79caf2f9e,0x503c8178c6f0dde0cbbf,0x1779eeea9dbb3b527654,0xec31d7bbad4756aea3dd,0x36ba427462e815cfa39d,0x37356e5c1c9b390b71c6,0xe2e5c44386d706ce021b,0xf0b7af6efadd51b8fb6e,0xd6d96dad9b4736746ca4,0xd8c1b04b5d96b7cd669a,0xbfb5506a5ad3d9a65b4b,0x6904d15da15341567d0,0xcef59cf337766baccdd9,0x88b2dd6560c9d1925321,0xe63f6c74d8dc318e62be,0xc4d9887b0fa61c2c2f58,0x483069608ac0657f3afb,0xb5f16bd6d79b2f105dd0,0xbb457552e795c86b82d6,0xf52dc55b2ab5b96a5ad3,0x65a0cb369662aca4591e,0xb1b162b2c2c580aaf895]) else (word80 [0xfe21c008,0xf3fd7040048cffe2bc15,0x81a2bfa5900019c63f7,0x88e0048b9ec0269ffc81,0x2387ff1be8800345cf,0x6013193d804f667b009e,0x73fd74002419ec0269e3,0x3584004933d804d9ffc5,0x782a1034274fca000338,0xe57f1d88009431ff1911,0x1297ff000234fe0004,0x62e3d40019afe1c226df,0xd090123d7f4300099d7f,0xf70280490c00c5ffe6c0,0xcf4d8f500067df880,0x1156bd7d0091c7fbf530,0x23afdc034be96500004,0x3abfbb00002197ffb340,0x4757f760000432fefd9,0xa00246fd0f82464ff620,0x67cfe362200679faf,0x3a001217f200454f8be8,0xcf3c7ff19009207ff,0x3a0011c3ff840273f1c0,0x26afc0a58000d0df9e80,0x19e9bb34900a1a3fd8,0x33f7d3a000067c7f,0xe25420021c7f940011e4,0x71fe26004899ffe05012,0x44f334801217a938011c,0x7d6a02466ffd3b500133,0xdffe0004ea00ce80337f,0x75000067600b7f801290,0x61fe00445fa800234bf,0xc301000043b91067fcc0,0x337fb10013377f5ff0c8,0x4ce9ff6200266debc00,0x1199f36c000219abfe08,0x99d39fc00019bbfc00,0x19ebe95000067bf2f,0xc026cfe0000cb1ff1900,0x19ddff8000000022271,0xd700047aff9ca744400d,0x23f5f9c0023ce31faa01,0x246fc6d0011dffe0068f,0xc6a0000ce2fb3a10010c,0xbf9f1c000246ff8da002,0x3cf8e8008d43f804d43f,0x804cf0055fffc3d00090,0x379ea00091bff6fe7001,0x22dafe8000021e1f8340,0x10e37e3800122bfd3,0xda93c801a1df99528440,0x440f5539002467f9719,0x67ad5fc028ef32801,0x332fc98011b6ff280024,0x6f5e0008c3fe000047da,0x8f200471d76e0047adbf,0x80283f9e1009cfe37402,0x82fe10400067987f0023,0x61ffc00469f4380118f9,0xe1009d3ff25c95801a0b,0xb7110006718fde238012,0x3f8ffaca000686f3b7f,0xa0001a1bcedf48420006,0xaeffc9d0000d1dfefe9c,0xa000686edffa7214001a,0x43fa6500033a7b7f0892,0x69df78c9a0024cff9,0xd74002437dd807dfff66,0x8c00494ffc972560068d,0xfff668480095cff02000,0x4337ae21c04ceaffb69,0x28650b7eb801209f30,0xc000430107fc18001a2b,0xfdbd764c000348c7fc74,0x24004aafc2080099c3e9,0xe3d28000d01faff82002,0x67cfd689d0000d3bef19,0x39001295113243350ab3,0x4d5310c44d0903d00551,0x194c099123185042090b,0x1c041444b30e5281e125,0x189252e8521a089281c4,0x1e0d927c6854549442c9,0x4c4d03c2e3289d07e052,0x1d14e0b039181432e0fe,0x2085a0c9784047d04053,0x278750d8454bc4f0c124,0x5c9e414484542521081c,0x5053a4cc471e91605c0c,0x3c5a0ad4443c88106177,0x214109247d1c8da39930,0x5f44d2185c148e02045b,0x2007174220b4c561f115,0x168746c9151e88c3a456,0x211347b13b181624d833,0x1ec447420e1707922137,0xd48839c6438c18782f0,0xab08b0c11321c47161b0,0x4f43d1911a1828846c10,0x382361b06e0ec507a1d7,0x41509c1d0874506f86f])) else (if j<7 then (word80 [0xa1eff6,0x12e3ec064a5002888ff,0x48480019e3ec58003357,0x4fdba4000d02ff480800,0x43c7ef680019eba7f7a,0xc4000d24ff263000043c,0xfd78008cfb0065ef8fc0,0x47bfd00967d7c00465e,0x7f0011a1fc4c0142e781,0x5768003447e4226807fe,0x463f9804abfff4d480,0x122f9f2001427fe61d3e,0x20068efd4ac000cefbdc,0x1f36fd0c00268afed4c,0xceb3fac6200487d80,0x333f90000021b39f2b00,0x33dfd9002717c300010,0xb5ba0138fac44008e33f,0xe00023abf9320000043e,0xbb38620021a3fd83ab07,0xc801a56bfa5e00475aff,0x25e00489f5e0008cdf96,0xccfbdc01cfe7fc80,0x2957cdef00810dc5fcf,0x66985fbc008edf006,0xafa013475d001331b97d,0xc600a185f9000142eff5,0xe0023643d7a800339745,0xedf8004d09c3960000ce,0x9febe80000ce9fdbcac0,0xceb7ebc004719ff000,0x11c7f88000121f74034f,0xf3c0004787eb20000043,0xe7ff9420c000d027e3e3,0xcbc800963e3000465ff1,0x8002313f5780000436bf,0xc800085be79e004eff00,0x5aff5e100006777abc80,0x867f8028c7c80919fc,0xd147c8091dfe006df9,0xbe4809207ff900023afb,0x8f824687f8661004087e,0xfbf5f640006895ff3a00,0x12080377f83e08000d03,0xffe08048e3ff58800471,0xfe632012467ec3868000,0xd019f97d00019c3fa0e1,0xa00034678827c28000d3,0xff3000085cfcbe8000c,0xc0fe180800021e1e3670,0x10d1ffe01ec3600069,0x27f674600010ebb7c7e0,0x2447ff9d580019edb00,0x9a3e1f5000338fdd7000,0x474ff87546e4040d2dff,0x3a374000689fcce0011f,0x3fff3a56104004d43f54,0x8d9f97140019d7ff35,0x47efffcc400267cf4,0xf8900067eff600000ce9,0xfd3a0000678fc4000019,0xe31fa800033e7a7f4e80,0x819d1f8c3d004087f7e7,0x46980002203c3f900066,0xfc844d3f99801193fe0,0x199c015ba00fbff0b,0x80023c78f0d88009a19f,0x3e020000874ffec04004,0xcf7f9801347bffa80019,0xd3ff94001333fe60187f,0xebf0000120a5f8400019,0xe91bf8000338d7ffe000,0x24265ffa000666f8e00,0x33043ed80033043ed80,0x33043ed80033043ed80,0x33043ed80033043ed80,0x334faa00467ec01a1f1,0x400042c7f8000066cfc9,0x540019e7f00011b7cc00,0x479f7f2f7cc00926ffe,0x139bf8d5200000443b,0x801dde00c3ffd6300009,0x2fd5200408647f36a0d,0x8111dff93b788c001a,0x53dbc46000cf94ff4000,0xcd5fc5470001a0716de0,0x48afd804dbff5180023,0xbdc01a3f6c830009a2f6,0x12b0036ffae8480920e,0x4f804c3fe0911bfe2000,0x3397f95b4800338f938,0x8fdfffc400006787d9,0x400010cf7f801ebfa000,0x33f7fc4480033a07f8,0x339c9f009aebfc01,0x3efaadd001207e2af400,0x484ebf20c00268393e01,0x337fc40000679f7f2c7c,0x980128ffdc00277dfc00,0xf33c98011ee3e7009cd6,0xff8028effe3921336000,0xd4df7601e7ae870023ec,0xff5d000913ff18800475]) else (if j<8 then (word80 [0x216bfb18,0xe38f51903f4063602ee8,0xc70f26083223f341b7f,0x418e30fb1925f7320e5f,0x7320f5b2085c704411e0,0xaca8eb9707ad904b6790,0xa327a0e640747c844b0b,0x11187351478fc5a4425e,0x846016ec75991f601eb5,0x96f42300b763cf7663a9,0x6cc719c24cd1ac64e082,0xa72512842e988328b19f,0x1c325b5d82e51c15aec1,0x243e4d0cb43324779248,0x84b0d096c3849de68d64,0x97d4a8357fba4193d746,0x909df0426866ab192f7f,0xa17432f7e998194e6849,0x9a358c9c1054fa683a72,0x49684270413bb60ad760,0xb11704244e951a7ed286,0x4261db256152f6ba8ed7,0x60b0cda68f0cda68dbd2,0x44165afd8632f5ac6b5d,0x6d13dfeb41b701cad822,0x4c8ecc883d431aef2689,0x2b782a79209be98bba03,0x1f740636fa62ee80c774,0xd81476418d478fe04193,0xc9c83279390627435e0a,0xc68f8d12849b42087e15,0x84245f856139f2720e51,0x62c1fb1f16110bed5e41,0xca2c5838cd0942bcb1e7,0xd818e36d12195df16c52,0x2175e8941a76e31f6586,0x38cb62d64b41a58af695,0x2122fc2b096cc8f2b2b1,0xe3922f73802c3c7b7a86,0x4779248845c213babc83,0x2704103b60b0ce08d2e0,0x8986e824c2b38103bf4a,0xc2338162aec789bd73d9,0xb4fe2522123e000194b,0xd3c800198bd3c8001993,0xfef6000662c3fec000cd,0x1d3fc800337174e50006,0x717f969040000445ff99,0x8027cc7c302656c78604,0xcb9ec70c0999bd1c3026,0x60efff6042000691ee34,0x246bff6c013d9fe60131,0xfe6012e7f51280332bf0,0x10a7f9804a7f9804b,0x9fd44a00ccafc000042d,0xbe9ab880050e09f8604c,0xa1ebac0019aa1ebcc019,0x9dee02bf0000110cf71b,0x88dc400289b3fcc026f2,0xbf580008607c1ed80008,0x6ea7b4bd0003437d39f3,0xf0001a33fa89401997c7,0x1a12317f10e02662fe21,0x265b3fcc026cfea2500,0x66a707e2001434f1cf00,0x230780f51280341bf450,0xdc400288b3fcc0260cfc,0x387a1026855df9002387,0x7fc352081340f7bf2004,0x704fe387a10804d4bfc8,0x11413f8e1e8409a0dff,0x50000218ba728003354b,0xe500066ac6dd00019f2a,0x5f2800339bdc0e8c0004,0x38f3c4008c1c3d081336,0xbe2c0200010e38f84004,0x7c7e6800010c5fcfc000,0x33001fd5000010fbf9e2,0x46c1bd48c4086c1bd4,0x8c4086afef4800333bf5,0x74328000888f83970006,0x7c777400010d1ff77a40,0x19e9889e00021812abe,0x2181cfc00042c7fc5,0xc108001a59f5609e0002,0x1fde3e1400021cdf0ddd,0x438baffd00010cdf,0xeda97a000342ff1c7e80,0x487bc028efe0045ac4a,0x1813368f7af0247debc0,0x9163e18132478604c9ba,0xa3ac784911e181320f03,0xf5812387a6000cabffc8,0x46b7fca42000087dff,0xa90246d7839002855f58,0x115ed00cd8f0c09963e,0x1813237478604ccbfc20,0x236f0bfe40048340377,0xafbc00033b201b7f8800,0x8d87bff0008f5ed7e7e7,0xe0001a403ffc2f440006,0x9c35feb00091bf7f2800,0x8f9afbc00033c3eb9294]) else (word80 [0xbc288346ad107bfd6089,0x4b26f5846e03a7c4106c,0x5fc0c88f10592f063c55,0xe0d84e60e08344f622fc,0xc6c5c56db2f634adb2d,0xbf123613bdd415b6cf47,0xb094d49ec4d83f626c1a,0x33608d17383e8edb1d3a,0xc11dada9a3df8687db43,0x1b43763ef818c34936c9,0xdf031cea6b7a297e063a,0x78c20e413c0069238315,0x7f18f819798b041cdad2,0xb460fb10c209c1c6148e,0x838c308ec78c30827071,0x8523a0e30c23b1e30c23,0xb44b06ee315d092f81cf,0xc238177d5a151ca10821,0x55f0820d1b2d2c24b03b,0x8e585702efab42c48dc2,0xf1aef8a10a6e60f075ed,0x2c71b83156ea51a5eb52,0xa522f90868edab420dd8,0xc22af9086be4218a0fab,0x421c223845cfedab4229,0xe75005206b628b56c715,0xead644c3831adb3551a6,0x1c18f1a5d8eee05145ab,0x638af56b24576200d74c,0x91e7b4b24e6868801ad5,0x91bf18a2e7a197f031ca,0xeec61199f05550908b04,0x6e9741c710b1f9194d5a,0x4a2e62d193ea59423be9,0x9c4263ece5508f603ba3,0xa7ba085b0a0e8e144276,0x94f0c80d84a77690d2f5,0x70ba124f420327b17a44,0x38a17aa4c775488427b0,0x44a6175f88c88488e0c6,0x5fc0c78cd82f626c1cbe,0x4a64d85895b63ec2c41f,0x18e304b1e38020fb831,0x638020cbd031a65c20c9,0x92ee0c86f2330042db04,0xa0e4e0034747820519c0,0x65fee0190b9f5a6497c9,0x4ce950ce7b094d498f4a,0x83353aa0f1e95061f018,0xc3f3146d620fb831a780,0x63df821128e2b8e4d4ab,0xf821123a531d0078b46e,0xd14eaba153e96164d418,0x458f83bbe00d1a9e9a25,0x79cf8391eda7749a835d,0x218ede20e0fda60ac3ba,0x2cfbe31d4cc6139d1001,0xa4a30ab51fbd0e8387d1,0x583ed431e191d107062b,0x195846429796883ef2d1,0x313fa564c4fe95905e52,0x83170820d5b4b0777028,0x85e9083c0f22ec916e5d,0x469e188bf842d911c4b0,0x70f488376bc1238960eb,0xc51f3d186588ab1e3c2,0xa22ac6b3e0b45d62f93,0x90934d0d767344c784a0,0xd13ad8fba0b1bbfcca84,0x246684a58e58f3e30191,0xdd3d508427267067a8f2,0x5941b4da51084ff66214])))))
def g255H9 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [1,0x600000000000016d4dc0,0x4400000000000000,0x3ca00000000000000,0x111400345a1cc5a8,0x76c00,0x36dc0016d348c00033f6,0x8c0032fe3113162f6630,0x6f45fd0793c92c81e000,0x325fd4b2c00022a40001,0xb766000053d1b0139680,0xf430a06d65730355e6e,0x558b77000020c7600000,0x344d82f8be0a4179,0x18000204c00000000000,0x3008001dcc0000014300,0x1185aff,0x5e000000351864933020,0x80d66740020866422e76,0x92d9d48753630c000b01,0x151f74b64145602c45e,0x446f38c0005517400000,0x3da42585222f155b0d1,0xc09cd35480006500046e,0x34680014c80ca12805c4,0x1236b2a95c25900024b3,0x5760403c000034c0021e,0x95140023980020e541c6,0xf062150e1c018c003578,0x6011c75de29e5ac12,0x460856821b7380006361,0xfc0000000000000011a0,0x316c5100036ed28800,0x21b800262c0000013200,0x580000000000015442ac,0x63a1f80000039ab55400,0x23cc0000000000016,0x4e4fc00000335c0003b8,0x59ca9e35662960c002cb,0xc00309d095d880000000,0x14f0000000,0xaf239c06b58400000,0x3c7554fda80034800000,0x15273580005e958c,0x1555a312caa2dd645,0x44a919503d280afa65c0,0x169c00000121f3f3c01,0x1b53800005000135000,0x274d4b80031,0xed4ac17156f67e3fc52c,0x3121d5d45128571,0x1932e904823e4c65b62,0xb4248dd10737013773a5,0x2d966f2b800000205747,0x631b1080039a67511aa6,0xbf75a25272a1a74644d5,0x5963fb4dc00137000222,0x351c0024432662392,0x2400026c00000276a15a,0x3a800039059a70400211,0x34280004e128c32c0001,0xcb7195b00012426e8001,0x43f4cd94800036c0033e,0x45c534400066400008c0,0x361800000042531f2fa,0xc7256c7d0fe2a35323d,0x410f3f70e1cb00000000,0x34d829800201c0b824e,0x73fa8c0000000000ac00,0x32e306560400117f3,0x292cf5fa0920754a4002,0x6b00000027491be61f87,0x15a702e5f64936c40cd6,0x940000000020ed0606fe,0xc134a22b2312040eaa9,0x80000031e40100032140,0x1cf216823524637c,0x358303057c6da1d314,0x64721325f27086b80000,0x3d00012d4002448002,0x37800071f0246b70f91f,0x734001c803e82b34,0x1b10575d5c80000002bc,0x4c000000000000000000,0x33b333a72d45e1033,0xd965b21000000311c000,0x24093400016ac3bfc2,0x22ec0034f46cc6880,0x34bd960394000757720,0x108000000000000000,0x10bc4440000006,0x7a4376682766f92612dd,0xdc00150800042357000,0x10b000c2000103103206,0x10320234b34021200904,0x42570506000821820006,0x4d31020c0412411850cb,0x901441010410450de94,0x404034b10004008e6020,0x40033450413ce090031,0x1d600208528000004104,0x400010100004130e1802,0x890430c620510c340180]) else (word80 [0x27c0014ee,0x4e86c17173b64d2c6a11,0x96700012921d74a21de6,0xcb3064061af2d2134000,0x33c40006a800,0x247b19927000000219c0,0xd402a614e7028003732,0x32420214113e1dbd463d,0xc00118ad397256102796,0x985ee5bd4970d80ab3ad,0x366297aee0a00006855c,0xc0000026a303642d3340,0x3615b0749c,0x294e48836000000146,0x20b6d0a5d776463d40f3,0xe3af414c001745098003,0x5295b80033885daba417,0x400000322c0023a00000,0xd2c0000000035d0000,0x11500023853ee14800,0x15e5075000000030230,0x7d70e624003542167380,0x30f34f800326a6466a,0x40000029380000000024,0x3956400347c038000000,0x149800000000208800]))
def g255D10 (j : Nat) : Nat := if 5 ≤ j then 0 else (if j<2 then (if j<1 then (word80 [0x22f9524f,0x7264a0e40937ca906e95,0x20db2a41b254817ca902,0xd972ca30e59b5d8b17cb,0x91518722daec460e4089,0x6cc142d9628eb0a50be6,0x7a94c0f2d981ea3303c,0xbe587b74b0f6d961ea70,0xa3dda147bac28f83901e,0xdaea5cb65c9a8c3936d7,0x626eaea4dbe5c6b6cb8d,0x6d871adaea34be5c696c,0xb8d51871adaec35d9d46,0xbaba8d82951d032a3a0a,0x14740c28e82651d02ca3,0x94a59fa8cb3f51977ca3,0x30f54619ebb4b3c75967,0x9032eee05d9da9cb0652,0x960ca32c194258317cb0,0x683900c5b2e25461c4a9,0xcb8551970a5f2e15461c,0x2c1c8052d9810db0c20b,0x654417cc045298085b30,0x114660229c3046e8608a,0x30c11b618217ca847796,0x6ed2c0dd6581ba4b037,0x68606eb0c0cbe581a8c3,0x32d9714a30e29b5d853,0xaba8a2f97025b2e05461,0xc0b73b016d7602eaea06,0xa58140cb02828605030,0xc0a0d94140b2820b9374,0x1720e8264d904c832378,0x65e2b2abc9645794c82f,0x17955c4724b8d619584c,0xb312b905a132cc02e4dc,0x85c8390b97701720e026,0x61a18c3b41795687f30c,0xcf61998bc9b341766e8b,0x2ed91659b22bb363d756,0xc7aead42640f85ca9c3f,0x95389724702e40e19c39,0xc2392382d3074564cead,0xc39a679634c92c685e4c,0xd19c39a139634132e78d,0x9d8f1abb1e3e753c7aea,0x782e40004caaa09984e1,0xb2e9ca64138fc9a42b90,0x48132ca42661306cba62,0x9904c57208d7e41104cc,0x282591505320a0266128,0x6cba559754a332894764,0xd294c8250b9842b2ea84,0x2661006cba0299040172,0xb144e56185cbc4357688,0x133118465a31ec2c60b9,0x884133108f616109cbc1,0x1197826b0f0599d60b2b,0xac1099532172a491e4c9,0x27c8121f9324232a544e,0x54835c8102b9020132e6,0xd5d8c08cb1619942c3b,0x26582660a08cb140b981,0xe57203c465cb9ac39711,0x962633284c764c994c81,0x313971a232e34de1c69a,0xc38d66751acaea35ae40,0x695c80d4f851cbaea39a,0xd94734b28e0b967e172e,0xf8266201ac3402990801,0x730f42661e9ac33d3d86,0x789b0eeda9d9db4bb3b7,0x17576132c302e58327c8,0x60997162b2a24964448,0x5cb854f900a133020d61,0x8405cc040998086b0c10,0xf61839fc3033d8606e72,0xcae40184cc0a259114,0x532028ae400a7c3024d8,0x604baea08e5d5b03c91c,0x39324aaea0bffffeff7,0xfdfeffdef7fefbcff7fe,0xfdd7faf6ffdfdbef7bee,0xfdbfb5f5fe7fbff7fafe,0xdfbbef7beefdbfaff3fe,0x7dcf79d76061f6061760,0x5db605d760597609db50,0x61f5061b505db505d750,0x5835061a7561e6561a65,0x6126560e65602655da65,0x5d665e1975e0d75e0175,0xa19756197560d7560175,0x21975e1970e1570d9570,0xa1970a15709957061970,0x615705d5705957019570,0xe1d65e01659d56561d65,0x601655d565e1d60e1560,0xd9560a15609d9609d560,0x9956061d60615605d960,0x5d5605c16059560e1d50,0xe1950d9550a19509d950,0x9d55061d50619505d950,0x5d5505c1505955061c65]) else (word80 [0x7d99ede7,0x979dd274b9caa70b9b8a,0x6bf9a7267e9956643986,0xa60997e25d896d25a596,0x52584956653294264de9,0x3164a5922245b90ce40a,0x8f863ba8e5e3748d3233,0x38c5e2ef8b362b08a862,0x8c89a624688861fe8776,0x1ba866e16e853612a83d,0xe0db830a09781d205b80,0xfe0197fddfbe7e89f757,0xd19f217c39ee27af1e99,0x79d1e5278a5e01775ddc,0x976e5d957619d5c7539d,0x287411ce6732dcac723d,0xc707145c2f703dbef6f4,0x5bac6e39b6c6d19b206c,0x45aee6b2daa569f9a5b6,0x8d5a1067a99c6665d973,0x653992564018d262a987,0xc617583a60697fb5f717,0xba5e257755d557345c41,0x6eb5b2d6a95a11660591,0xd62e57e55d656dd59555,0xad53b54554e753114995,0x1a944f50a54034f913be,0x4e5d3714d453324c3d2e,0xc4b01297499d23748351,0xe8470d1a3460515f44d5,0x11843a90cb428d081418,0x103f4044fec3f28fa63e,0x3cf633d30f213c00ee13,0xad4e8939b0e3f388cdff,0x3744db63668d7e3580d3,0xb341cce33304c9031b8c,0x373024be72f68bab2e3c,0xb732d20b372c98b192c2,0xaed2b34abe2a80a8029,0x80a5328b0a1a28289e12,0x7389a625e495b24c491e,0x23d48cf22c889d21bc84,0x4206c7f61f887c61ee07,0x8d1dac7471c706f31b34,0x6b11a60670197462e184,0x85e817305b1162856514,0xf4519142c4fe13784cf1,0x2b848d11a444610dc412,0xfbc3c30e343790d4c33,0x30c7c3010b602ba0a5c2,0x8409c4260090421c0820,0x1e707081a0061015704b,0x811103d40d302bc08d01,0x90042007c00087955d0f,0x26ba164d743c82e85905,0xd0d2cb616596c3432d85,0x865b0d0cb21619642c9b,0x48590690f2a721e40e42,0xc81c8593350b206a1e5c,0xdc2cb9b8587370aec6e1,0x5d4dc2c2a88798430b30,0x8616190c2c2a18695210,0xb2a4216587c2cb8d8575,0x1b0f30121660242c3048,0x795090b2a121a581c2cb,0x38597030aec05464dd2,0x8c83a519364a320c8b64,0xd916c8322d955e5b26bc,0xb6417b1cbae2f955cef2,0xab8be4d73fc92e2f905c,0x5b26acb6415a94b31519,0x6625b2cc54a198a8c331,0x2f965aa70cb54a196a8c,0x32d50865b0720b54a598,0x28cb302d9660a50cc146,0x19817cb2c538658a50cb,0x14619628432c519672a3,0x26e54641ca8cbb851907,0xa330d0be4da17c83475,0x9666eb26cdd6419a8bb3,0x651766aa3207cb640fa9,0xca9c539038a32071de54,0xe3fc91c2f9038ef2c69d,0xe4cd3ac99a779034eb20,0x68be58d17c99a2f9034a,0x32e7945d8f28ba9e2d97,0x3ca30e79b5d8f3aba9e2,0xf9736a70e6d461cdb73b,0x1b6d7636ecea6dd5d4da,0x8c8002d954e5f2a91ee4,0xd241c8242d964ca30c98,0xbe591a94323518647072,0x8d8e591314b22619644,0xc12c898a19130c3222d9,0x850db0ca14e15430baa8,0x2d984a5b2c954e19297c,0xc215298425b308546610,0xa9c3216e8642db0c854e,0x150b0baa18190425b308,0x14a562a8cac56e9586db,0x2b0d465e228cc426d968,0x4a30b09b65e0b6bac153,0x9524a52a4946549284a9])) else (if j<3 then (word80 [0xc0006867,0xdb011df6a0003377da80,0xcd3f10011bbf120006,0x6bb7ff50052b97e40024,0x65f500232fc8004627fe,0x10051bfee00119b967ce,0x8019e2f9fc4008e17edf,0x8fc00909dbeb70000d13,0xf7e5400246fcca00120b,0xfcfd005197d4008db5f5,0x230d37f048e67e4f82,0x152fd001157fc69bf82,0x48bffd004dbff348008f,0x35fa00231bfe9009cffe,0x9004f3cffcc400244c7e,0x10011cdff480283fec88,0x297ed00c27f85880092,0xfda0187f8ca20024cfee,0x1183f78013dfff7078,0x148fff72800241e6e00,0x9fbf2822000d079d804d,0x7e61e00507ffd2d78015,0x5de00273e3c0263ee402,0x63c39009cff346005205,0xd7a69a040d37633b8052,0x77bbe8056ff0b3280012,0x8b39e00291b8ffeba0d0,0x9535feb8b0024063a78,0x52005dfe1670000937d,0xc004f5fc004f3ff0b180,0x11de00af0050029801cf,0xc80135fcc8013a006bff,0x80098ffd0009cffe0009,0xc00bbf88000120600860,0x63fffb00014bb0063ef,0xe590029dff955e00241e,0x558051df12b00033ba00,0x7127f200024dcfbf5805,0x4fac0275b803d9fbff3,0x40055bfc6a00012177fc,0x1d008ed9f5000667a007,0x7ffa007401578b4be002,0x4dff9a004f7fe8a0053b,0xfc6a0001217ff06d008e,0x9f08800331f2e0133f58,0x22e7ffa800a5b0039fe,0xcfc8d002b7fb60083ff2,0x7a800aafae009efdc013,0x5e5feb40297fb6cec051,0xf3f95a01487f2b401520,0xa005dfc00046400d3de,0xc00475f8800231fff800,0x13dfff80027000e4df3c,0xc0283bfc9804fb8af404,0x933ffe4dc5100253d8,0x31f6672005347ac8052,0xee00cffaf0040efe9784,0x11ce7d00273cf970050e,0x801dd003bc014fec8013,0xc9fd000121e801df7ef2,0x137ff8900283cfd9009,0xcfd9009b7d6b90000923,0xfe97610473d2e0139f3c,0x13179ce80505cf2d005,0x47f0b20140fcfea0011c,0x69bf82471cef8008e7f8,0xf00985784a0309065a4f,0x45c9259251613b82a20b,0xba9423090251b2a4142,0xd1d4964c4ac0288500a5,0x283a14200d0bd0c1e22e,0x2b0e290fc194c10c4038,0xb789c3178a88b0863e21,0x828e48a1f0f4711f1a27,0x64424e9028872189015,0x23b218d11c2d18262107,0x444e1e62d143a1bc370,0xb81c1f36fcbbf257c71f,0x133c27eff7bceee93b7b,0xed43b23ebcbad5ead3a9,0xe9aba47e88f9fae74f9,0xbbe69397be58f93be453,0x8f0e30f8a2e1fb85de11,0xf82fe0237ebdf3b7aade,0x17767dd1f728dc036e6d,0xb3b6b5da2b66bd903617,0xd7ef5ced687577d50f51,0x3d3cf4c9d27f485d1774,0x37d0773f0cf03389cd7f,0x32dcc072d1cadf29dca0,0xb268c907220c7eb1d4c6,0xbb185c56312dc4330e4c,0x2f3092c1cb052c08aff8,0xbf4afa2be06f68bd0ef1,0x7bbf6ee4baeae89b986e,0x36b82edd5b6b6d7db54a,0xd28b412cedb302c99b20,0xac59b0b6bffaf86bb6ae,0x5ab7fad82b49acc2b0ca,0xbaaabfaa7ea82a986a3d,0xa872a00a78a9c3a65297,0x2a4f691aa3fa8d9a2e68,0x99a1ea857a0de8199fde]) else (if j<4 then (word80 [0xcff1c002,0x3efe59000914f20132fc,0xfc0e0012036c3a74001a,0x17cc0ff81c00254cbfc6,0xc00905d3ffb0f2015aaf,0xef1c0024266805f80034,0x53c804d4f20133bec808,0xa79009a3f0a0003336e7,0x7e0263f8c0006679acff,0x602de5b3fd80bdffe190,0x2387fdfe1200aa73c7c,0x400243f7d660246ff110,0x1217fe550011caffffa,0x8029dc6a0046dc6a0046,0x51f5e204004a9ba3fe00,0x122fcf71c0285d738f22,0x49a79660141fa0098b,0xfcfd005057bffc90054f,0xe4c045cd0098af7ffd80,0x299fc28d3fc1249ff9d8,0x201487fdff48029afd20,0x8000cebe7b35cc40025a,0xaafdc00246e725444002,0x587fdff48029afdb5000,0x19d57ee0011dfb4030ff,0xf0b100122fff2cc0143d,0x4808dfe2a200240fbfe6,0x20024495f8a88009478e,0x6013cfe54c400497ebd6,0x80976d00e7d2600a1bb4,0x3ad5a0267d560011ee7,0xdc0028ddf949400927bb,0x7804e795c027bcfe0013,0x9f0f7801430fff4028db,0xfc0217cff008a3c78051,0xbffe3c800120fd9e0028,0x1ffe6b20000255e1de00,0x293ddf008bfd8780145f,0xd180145fd18014177f00,0x273ef9fa01567dc0050b,0xa7f00559dfe004f7e780,0x13597fe004f5fb800516,0x5f7c00a27515e0009113,0xcf0028bf8e004f3e1770,0x483efdf8014efd8fa0,0x28ff7d008af3c0000339,0xc00f5e78000067700318,0x1cffd0009dbfffa0029,0x31801d001f6eb81800,0x24de7df900285e3d6000,0x246dd7030004967d8041,0xeede0139e57009cbf6cf,0x4000cf73fde2005373fd,0xe2002a8fff718014a9fd,0x100048be4fa00517ef34,0xa0607e400121eac012,0xfd6e0117f9f96005079f,0x2e013bfde80210030e80,0x267d600023deffb00273,0xffd900144e75000475fa,0x800235fff60027bfec00,0x4ebfeeb5000485fa8002,0x35ffeb00275fff6183c0,0x92dfba010fdd00799f8,0x1c000937ff1400a1fbe0,0xcdfec0117fa7000151c,0xf1a0052bfffcc2800004,0xb6ff6008bdfce1000165,0x3f777c5002cbff820014,0xb60073ff27a0002b9899,0x980120bf0b2014cf57b0,0x122fe168029bcb9cda0,0x155e5efb40152ffc7400,0x8e00320039fff80013a,0x65ff8e80011c0063b9,0xc9300a4eff8300a2c7f0,0x277df600f776400a2cf,0xe004c6be400a28f1e014,0x5ebfa005067da0050fff,0x2c0127ce8013dcfc9000,0xa4ff770083cf97009eff,0x7d8002933ffb000a1003,0x6ebc000479cf80008f7e,0xdf88014cce7c000489e7,0x80008e6737f80145fff6,0xa0c7fe70028cbfc00,0x472fe8340000d173be4,0x5373be2002abfccf70,0x14afe940011d7d76fd0,0x49bfccfb0028dfefa9,0x1263f280140efd750,0xc5ffe5009bfb400515f,0x9000a17ffe400a3ff853,0xed00163b003afff3004d,0xfd8000a6ef32f00a2cfe,0x55805373ce804f73cb40,0x1497981d00a8bec3a00a,0xa3f004d1f8026991ffea,0x5c00251ed5fd80a1ef00,0x8c7dde401436b86a240,0xcf5f8b6a2000d1b97e40,0x244ffd056384907fe12,0xa07fe16400241708fa]) else (word80 [0x27,0xac608b4187c0ca5a262f,0x8330ffb8d82346bbc841,0x9a3215df2cc1485073cb,0x3e4ac0141fa6810b877d,0xd520b1e02ad4ce3fa204,0x795223841e5e58ced2f2,0x82e64168df81822c7d02,0x19729ff8a118b4ee0fa,0x66dae3aca8c9fb0290cd,0xaa6bcc3d488eb98490ce,0x3c8288744c963fc9a154,0xcd0eb1070566b7a29023,0xd4450d1c7eb6155183ca,0x909f82ce3f220146afff,0x203271f9100a31e86499,0x8eec70540c8fd1f75e42,0x8a5068f645c6fe0146e0,0xb7ab5332ebe028bb53c0,0x28cbd0f85177fd4d0011,0xd77e807be4025bd20136,0x7fcd400067bdb480501f,0xffdd200a73f4a2000cf6,0xb3804e3c4ff8400482b9,0xffe1201505abf9000923,0xffeea99000953f13b563,0x84937acb0052a7ffdc00,0x23afffdb0008f4f20134]))))
def g255H10 (j : Nat) : Nat := if 3 ≤ j then 0 else (if j<1 then (word80 [0x28e88b93,0xd61eb4c400010347d394,0x600000043d04a7824000,0x68a566530e180e03a623,0xe8108e67440012cf4a62,0x914d1200000848be5446,0xdb680053f4dd8b7c3047,0xe95c1eb39650983bd72c,0x3851e3251fd9480000ae,0x713800000063940002ba,0xcbe0894000143cb068bb,0xb0f8610002a3d1c107b5,0x166a8526ea6cc71c8710,0x2e000d9580024410bd00,0x26ac22800096b219a32,0x289f46c408d1ae000000,0xd4f8138df22a0390,0x502039000007e8ad9,0x9e82f6314c5ca9f15d2c,0xce57728eb00e00000000,0x102a80500035fed7c00,0x1112000000,0x126782f64e8000e88,0x346a00000022fc,0x1e40004,0x76800046e2d0d1248f40,0xb13d5880031d016b44,0x683eb9956d204300011a,0x69ff44c265a63a000000,0x62106a27fcaa898c000,0xc60ba09c72100000002,0xa04000000080015c0000,0x91f472c0002c800062,0x452cf0aa41fe94400092,0x6d1c9ab124000d0f800,0x1aeb957d7ce24c000000,0,0x1abc00029e0,0x2acc0000000f00000b,0x5ae77013000300226f00,0x26582cb13200020e,0x331831803cc0011f86c3,0x22b1cb4c3a800162e,0x22d03500000019ee75fd,0xbc37880c509a45c5c80,0x414d79886400000000,0x333a000000493e61200,0xa7f0000000000000000,0xc6f8000000afb,0x14b858107572e228,0xbda0858f96c0a09e0008,0x8df9e7245a1100005403,0x4e00000000000011fd00,0x291f3920000002b3b55,0x200014b02382ef997549,0x6635c5fa5f000000335e,0xa85522044dbc799f2fe4,0x7280009ae00050d24ea0,0xa1ece800061817609b43,0xf043d4c96f7800316191,0x554c618e0c9a7dd33296,0xf3ce2d5000018b168000,0x88000341cec356e8000,0x18ac57460f75492849,0x9415040011d253a13f32,0x8d11a91c6c3e0aa6a600,0x492f09892d000650641,0x51a9d2c800235925a0be,0xac865b15fb8b20000551,0x86d000443a9739a8934f,0x88800188847dc0e521e0,0x61530140530aed3,0xe33b0000cad3ae041128,0xac02000000000054744f,0x92eb14431f87349a7a09,0x58b0bd63a68f8af0c3f4,0x2abc0009720,0x53b37600000000021,0xd200098d008b16200000,0x4b4b42b2f0c41485d09,0x7e01d13f0a9364043000,0x5a39f51ef97e8001880,0x4289852508004003440,0x104380780e018852030c,0x891304012060d6816810,0xb880044403040c182020,0x2060041401720838208,0x103880a2438300201930,0x9cba1040819200d0804,0x340c480180c68042100a,0x8005810b180040106042,0x1518085291c240900484,0x30302280080e1839f021,0x8a960000d893c4450306,0x1c102043050600300800,0x405011e140211a04710,0xc480030028303061800,0x20618a02020000406001,0x1c58806080010834,0x69908146040200200006,0x82000048005124060900,0x18032003030a044800,0x20809202000090a0c081]) else (if j<2 then (word80 [0xfe4a8f6,0x478e6c94692b20c00000,0x49e41b680d000000040,0x2000832e2e0001a1d482,0xa1dd47e02c0000000001,0xae387b2254000aac92a2,0x97030a0e7000415a0ba8,0xab00005944900008db78,0xe8a3ba4004249265c3de,0xed35c60b088c47501d45,0xd15f10159266e84040f9,0x194c4874dbc2d0000000,0x1e3d4687b113e20000,0x433c000173183a8c83,0x81ed3000609632631500,0xd8000000af3000378b56,0xa00000000000009ed04f,0x2a035b75fed904868584,0x8c1abac0001aa0002,0x5649f6b2ad6f2224001a,0x26d6bc73b863e2b8d8ca,0xf603b008000232156429,0x40000000000dffd64eac,0x320583a28de58c1522b4,0xc63e5c73c42d95840000,0x1d489425e41700012aab,0x45e754476dea2f800000,0x1879086984001ac5d9,0x167cc37e1c5d53f5dc5c,0x5aeacda8002620a68cc0,0x42b511ea330000001516,0x2d3270c94aa8336d6,0x5295121a304ba8002fee,0x42f54b50c5e4b2f0362b,0xf9d56a9586e8bdebc158,0x100000013ae000000675,0x3141079963a4e5032076,0x6658001dbab1985d0c78,0x9f6921a4a8cfc8c0c,0x6d000000000055dcbb00,0x82c78ec000,0x580e9fed66350000000,0x191e0000000388000a87,0x2a1c001e414418682c00,0x1314f20626b531c2c91a,0xead196ad1b6bfe1898,0xf06bd00a3164011d0da7,0xe5430000000009c3d600,0x5db05f82c85a,0x52c313c00063c7042aef,0x2bc86b64160160004c2a,0x38f1db906213b148af65,0x2e97b2c5093f859a07c0,0x18684986c143832c409,0x30446638014801000000,0x1058c4e8000668000000,0x15fab04001,0x25787100000001700cac,0x7c31379b389649f80002,0xfc000000000104d00000,0x326800017300038f82d,0x3a52676442d1e883a053,0x560600046f00004ab0dc,0xcef60185e8a2a2becb6b,0x6170d5c70e95905aa821,0x4680022be93200000032,0x69780e325271a40a2d4,0xd800134c608183036400,0x12996000030ce133000,0x60000000950000024a,0xab6000000000000093c4,0x4ee867ebd49700021760,0x87268051456fa9c51e49,0xec000000cb300024830e,0xe4004b53519848000000,0xc8c104000000153fa73,0x85f288b2f599a00000c9,0x2a984a0ef84923ba127b,0x56a848000d120a5e5880,0xa9fb46532524d01,0x7e7b04b000000000e008,0x219e1186a74000000000,0xb73370000ec24c001a3,0x9b400003583b981c0004,0x6800000049ab58c0000,0x21c000103c41b0c,0x4b432000b2504f597400,0x48a260905b701000,0x472a9a0000508000000,0x17880000012520bce200,0x2cc5970c942df2bcc,0x37333c00110900030c05,0x22000cb63ab000124c44,0x8476a14c000000668a0d,0xeb33c28ca5ec86ecb486,0x8000001b0dcd20794ccd,0xece62e9b52b05a07d0a2,0x3516608c301d81030132,0x908dba43000191800023,0x2905619087782d73ee05,0x81f70ba526081000678,0xc0686c1453bb461338ff,0x8b6cc6f0249fb0c60000]) else (word80 [0x10c5b5e000323b1,0xead02c3380012cdcae03,0x84579d692f063e12c00,0x41175f518600f474,0x818000049d250,0x476000000185ac23ccb7,0x66a7249c22f0000000c,0xd282964420000b726661,0x19b270c5daba28111f52,0x168374ec92b00041fd16,0xc82ecff06f606f072d38,0x64285ce12f00026632ac,0x95200061cd15ced50004,0x83d9f2ab891a011bb0a0,0xcce466c2a750300000,0x2134000418c1af085e2,0x64078000001078c34daa,0x80006ca0002330000ad1,0x860e3d6196aad0004af9,0x54d2c600000000004a99,0x5580033ea0000000003b,0x18aca8800000110b00,0x6b7c64c0004c72a1819,0xb04900026e6d85184000,0x4a95462000cc08be39fa,0x59f923000239f9e10000,0xc7c4471e9c3e46c1c778,0xeb08b0001662000d32c9,0xdc001aae94cc1f41ee80,0xb8ca6687d6d2882f4473,0x32fc000c8c80ab3cc95e])))
def g255D11 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x2e2cc028bfcc,0x598052d3ef010fcf9c04,0x13b3009c3f71b300a9bd,0xf38086eb35e02efc33c8,0x293f880853fe80847e2,0x29bf5c03b74f8086b70,0x8be81c00a5adc0209f4,0xd400a8fd8d00292fb1a0,0x54ffcd6a016eb70087e,0xf801ddba009bf0b000a4,0xfe780145e00effc3c025,0xf3e0087ba740165e00ee,0x5a012ffec00e7ff40096,0xfff6b0050e00f7f78300,0x297fd6008be5f400056e,0xe90050e00ef8e0103fb8,0x7b8f9009d7eec03a7de,0x1d6fec03adfd80767ea,0x20fa60219fa808b0fb0,0x9cfe7c039fc40446f80,0x273f88086fea01dbf4c0,0x41f880827d2013bcc01d,0x7a00e7c700277ffc0043,0xfbf0021fb401df34021e,0x801cf4010fc00cf800e5,0xa0105e00e5a0107c2e00,0xa1f80087eb0073e8022d,0xc920143800edc0081c01,0xdfd3c021e0066801cf93,0x401407e6e3028be7d402,0x743142d84238e0a18171,0x59321280f0627051e874,0x688851bc61d1311470ec,0x54807084586c2c1c0924,0x8fd8e18c38a687e86083,0xe8188007e47ca7af7947,0x7c75a74271e6fc6d96b5,0x69c6826686466296155f,0x65dc5bd5a95915755585,0x335214fc4e04b949f48d,0x47545c43e42340a3ef3d,0x43ba3a238836a34f3373,0x1c3042ea2cf2b829b286,0x27125423721a2021ea1d,0x61c11ad19918517115d1,0x3e1281100fa0db0c90b4,0xa208607406204302000,0xfc32fa197b0cbc865fc,0x1af60d7f00bd805ebb37,0xe1cfb0e7d753fc01f600,0xfd0c9d864f42a76153ec,0xa9e654eb2a71953ceb3d,0x759ec3975d8bd0a5d852,0xf3a975d4bcca5d652f3b,0x475da3b0e3e861ec30f9,0xd87aec3d751fb28f5945,0x30ce98374c03ae195706,0xab8054c3b2619aaeac98,0x364c032e1cd30e76753a,0xba9ae00d30e098005c32,0x2e151aea898798bb4a61,0x662cb2b8724c3949d8a2,0xec4b8529b294594b2e04,0x98784c3455d632c10b87,0x14c38ae18530c36751ab,0xa8e5c04308c5836ffffe,0xf7fbfdfeffbdeefd8350,0x9d6655d5705956054065])
def g255H11 (j : Nat) : Nat := if 2 ≤ j then 0 else (if j<1 then (word80 [0x244d034b,0x2bca50001af50868e58c,0x2b0696f9561b89361ae3,0x4000001cfc000914b3c,0x25600117102706,0x3179aadd2a0000000000,0x116400000181f056,0x89832284aac052c00021,0x1ed537eea023e84ea691,0x51a189c706c37ba3d286,0x56db2bd27b461be00134,0x200187f36ec8acfbafe8,0x432fcdda00021fb7089e,0xf660000d535eb61d720e,0x8b729900019170bea991,0x302cc31a4be9bb3660eb,0x20807a425b4e0d1c691b,0xc1c021d2335642d291ba,0x6f2d7260c23a8a1c21e6,0x33998929e97f35b113b3,0x1241180f6cad400005d1,0x3c01a161a20aaf09d6db,0x6c422be9735303d1d8b2,0x98ae001b0f4728de07c0,0x1c920c0000019c4910,0xbb86010a0002aa00,0xb213758220000000000,0x12f059616c36292a001,0x95c9efd62aee24e00000,0x1a07d30aa40162,0x42746c2a8de8c90c58f,0x17727bb0d0099f400088,0x1ca00183f24699b1eba,0x72354812b0876a8676c9,0x24cb1834c0000012d828,0x6d68c4001d6b239621d,0x6fb11e23c1312736c000,0x8a0f59ebbb2c1d6000dd,0x8000c4a000001106d84c,0x1016a0009b22bb264314,0x26622e0ee0008f5a37a8,0x233bc94a9d13a1950a4b,0xb2034b7351a25828000,0x10fee60a5c21786aac,0x21349a5a896a6031a2de,0x1c9a883a31ca96001949,0x2011aa0001b70b25142d,0xac1520ab32000b48a31b,0x789b11cf8ce001900000,0x9d41e580400024800,0x949030f69468844a5b,0x8000095a464000000cd5,0x36a001124aca2b192873,0xaaa308a7320000009ac0,0x198b26a88999dd05a9b,0x1320001a6e369d1909a5,0x2dde0ac9e980cec79438,0xf237d9fe4748708e68cc,0x8780b0ab60011192c92f,0x60004770258522e569e1,0x388bcb6930200000150f,0x2ea2cfb5785858803400,0x1a26b77add0380000012,0x6c8b986f744000001e94,0x12de0000019d3141c2,0x800102e0002e10da0000,0x1ab4001c8d9f7aa6000,0xde6a588010509de00200,0x114400133e1a10720f0a,0x54168a1a00005e000065,0xfd90e04684183709a00,0x82a19781407435dafac,0x900010a28c01f24f6f65,0x17a001ab812c69200081,0x1ad0000a4b3448a79520,0xa5b869a92001af3a45,0xaf8b00000000b1600000,0x8e3a23b6495f6,0xbe235d68897890000213,0xb344a32432840000000c,0x80000000000d98924bc8,0xcb9e3b1e00117d17488d,0x1052b20f9eae182a5fa7,0x102c20f1590188d2337d,0xf018618e2c5312a3b94f,0x2ec2950aa99ea910c600,0xcf49b4a6348f12e0,0x27cddd98c000,0x94a01d9fd5711fa73,0x14276572a911e94c1,0xdd80e9e18ed97384409a,0x13065480242b45035930,0x1f4c653211e04c898a0,0x10040e2806b0204,0x1c1583abd5841e302002,0xa5c38504449051200089,0x111083247098c090438,0x41c317830048494003c2,0x302a420500080030c00,0x5810a6958d1200b84600,0x33928305022a0858402,0x3578226ac2040a040010,0x20c38016702010204182]) else (word80 [0x1d17a284c,0x364132f1f9c6a0b4000a,0x760001f02c6f38000848,0x9db9554219841988e1e9,0x82a113e9200000008763,0x400000009931a20018d7,0xe428b6a7821512200000,0xa9ec161f38200108f4,0xd200027e821abe358b26,0x180a5e42e28dd03296,0x2a8f84c6249ec6d8883f,0x4874bae62e9f6811c75a,0x5134ee0018fb16600166,0x51cd05400000005a807b]))
def g255D12 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xc00e60077a004,0x2003a003b50040007700,0x10001d8008084c88e0b1,0x8345101e0c2813b18eec,0xeae86684224013aaeb32,0xaca32ae1b02c1a82a1ff])
def g255H12 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0xec400421540030e868,0x2d001481124eb30,0xb700000c9000000,0x400000000000000000,0xc98000000000128c13,0x2b0008f00000c1400134,0x8e000b3f,0x7d4c0000000d0400b2c,0x1560d8f143000,0x4b0000023a000,0xb2001320000000225d08,0x1c002370000000146000,0xee0006380045c00000,0x1c500000d4800000,0x10b00000464008c7,0xbe8a9910000000000000,0x336000000014a002,0x2f00000000850014c003,0x1f000000000000000000,0x12cec00003,0x1d4400b0c0000150000,0x1d0000000000001,0x1b00000000c200000000,0x11100000850,0x878000000000000ebe,0x92858008610c05400000,0x10f0000048800000,0xe800000295080,0x89c564b857b28,0xb600000000004ce348a7,0x90fa97d242327c00001,0x24c24fc0f3d4d400c84,0xa0000000000000,0x678000000004caed00,0x21012f4500000000,0xa70000000091e3901b,0x3f00000a4c0041003056,0x220f031140171011020])
def g255D13 (j : Nat) : Nat := if 1 ≤ j then 0 else 0x146042005ff
def g255H13 (j : Nat) : Nat := if 1 ≤ j then 0 else (word80 [0x19c37,0x1f08803400839a90ba00,0x52af652100200003e092])
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
