import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_49539.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_49539
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xffeefffffffefffffffc,0xfffefefeffaaaa00ffff,0xffffffffffffffffffff,0xffffffeefffffffeffff,0xfffcfffefefeffaaaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 0 && x 4) || (x 3 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 0 &&& x 4) ||| (x 3 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,6]⟩,⟨.or,[7,8]⟩,⟨.or,[0,1]⟩,⟨.or,[5,6]⟩,⟨.or,[1,2]⟩,⟨.or,[7,12]⟩,⟨.or,[5,7]⟩,⟨.or,[3,9]⟩,⟨.and,[13,11]⟩,⟨.and,[14,10]⟩,⟨.and,[15,4]⟩,⟨.and,[9,3]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 5, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 5, 5, 0, 0, 0, 1, 0] : List Nat).getD i.val 0))

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
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low9 : Lower true (varsX 9) (graphGoal 9) 1 := by
  have q := @lower_count true (vars 9) (graphGoal 9) (proper_of _ (by decide +kernel)) (graphPairs 9 3) (by decide +kernel)
  exact q
def K9 := extendKnown [] 1 [(33,[83,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V9 : Known true K9 := extend_ok (m:=9) baseKnown low9 (by decide +kernel)
def g25Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g25C : List ColumnInfo := []
def g25A : List (List Nat) := [[],[67],[48],[48,64],[64,48],[64]]
def g25D3 (j : Nat) := if j=0 then 0x7 else 0
def g25L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g25D3)
  | _ => emptyPacking
def g25I (_ _ : Nat) : Option (Nat × Nat) := none
def g25 : Forest := ⟨25,3,fun i => g25Y[i]?.getD (0,0),g25C,g25A,g25L,g25I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25P3_0 : block g25 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g25B3 : block g25 3 0 1=true := g25P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25T : checkedTables g25 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g25 0 0 0 = true)
  · exact (rfl : block g25 1 0 0 = true)
  · exact (rfl : block g25 2 0 0 = true)
  · exact g25B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g25G : graphValid g25 (boundsBefore K9) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low25 : Lower true (varsX 25) (graphGoal 25) 4 := lower_forest (g:=g25) (i:=0) (hints:=3) (before_sound K9 V9) g25G g25T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K25 := extendKnown K9 4 [(25,[]),(88,[48,16,33,66,98,82]),(137,[116,84,101]),(145,[67,115,83,101]),(152,[48,16,33,66,114,82,101]),(161,[83,116,100]),(162,[16,83,116,100]),(194,[16,99,116,83,84]),(200,[48,16,33,98,116,82,84])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V25 : Known true K25 := extend_ok (m:=25) V9 low25 (by decide +kernel)
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
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact g43B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K25) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K25 V25) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K25 4 [(43,[]),(51,[67]),(75,[96,16,49,83]),(83,[96,16,49,67,84]),(99,[16,99,67]),(105,[48,81,33,96,66,64]),(106,[16,48,32,82,66,100]),(113,[64,81,33,99,32]),(114,[16,64,32,83,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V25 low43 (by decide +kernel)
def g57Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfd5b8fff83fffff3fa,0xb71fff07ffffe7f56e3f])),(BitVec.ofNat 152 (word80 [0x92410820802000,0x1248210410040000249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3bac71fffc0fc7fc77,0x58e3fff81f8ff8eeb1c7])),(BitVec.ofNat 152 (word80 [0x818d24921241124103,0x1a492424822482063492]))),((BitVec.ofNat 152 (word80 [0xc6b47e3ffff007ff8d,0x68fc7fffe00fff1ad1f8])),(BitVec.ofNat 152 (word80 [0x16324924208a24802c,0x6492484114490058c924]))),((BitVec.ofNat 152 (word80 [0x64f803ffffff8000c,0x9f007ffffff000193e00])),(BitVec.ofNat 152 (word80 [0x264f6db8430c070a4c,0x9edb7086180e14993db6]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g57C : List ColumnInfo := [(32,0,25,0,4)]
def g57A : List (List Nat) := [[],[67]]
def g57D4 (j : Nat) := if j=0 then 0x1f else 0
def g57L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g57D4)
  | _ => emptyPacking
def g57I (_ _ : Nat) : Option (Nat × Nat) := none
def g57 : Forest := ⟨57,4,fun i => g57Y[i]?.getD (0,0),g57C,g57A,g57L,g57I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57P4_0 : block g57 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g57B4 : block g57 4 0 1=true := g57P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57T : checkedTables g57 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g57 0 0 0 = true)
  · exact (rfl : block g57 1 0 0 = true)
  · exact (rfl : block g57 2 0 0 = true)
  · exact (rfl : block g57 3 0 0 = true)
  · exact g57B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g57G : graphValid g57 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low57 : Lower true (varsX 57) (graphGoal 57) 5 := lower_forest (g:=g57) (i:=0) (hints:=3) (before_sound K43 V43) g57G g57T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K57 := extendKnown K43 5 [(57,[]),(90,[96,16,81]),(139,[112,33,65,48,49,81,101]),(154,[112,16,81,101]),(170,[112,16,49,84,67,100]),(178,[112,16,49,84,99]),(184,[112,16,33,98]),(195,[112,33,49,100,80]),(225,[112,48,84,100,67]),(232,[112,16,33,100,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V57 : Known true K57 := extend_ok (m:=57) V43 low57 (by decide +kernel)
def g89Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf1fe003ffc0f9f3f1f,0xe003ffc0f9f3f1fe003f])),(BitVec.ofNat 152 (word80 [0x241e49248a2142a241,0xe49248a2142a241e4924]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe750fc7fff01fffe7,0x50fc7fff01fffe750fc7])),(BitVec.ofNat 152 (word80 [0x400012491042040400,0x1249104204040001249]))),((BitVec.ofNat 152 (word80 [0xff8af1f8ffffe03ff8,0xaf1f8ffffe03ff8af1f8])),(BitVec.ofNat 152 (word80 [0x800024922084080800,0x2492208408080002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x19fe00ffffffc001,0x9fe00ffffffc0019fe00])),(BitVec.ofNat 152 (word80 [0x959c924c308103095,0x9c924c3081030959c924]))),(0x0,0x0),(0x0,0x0)]
def g89C : List ColumnInfo := [(1,0,88,0,4)]
def g89A : List (List Nat) := [[],[67],[96],[96,67]]
def g89D4 (j : Nat) := if j=0 then 0x1f else 0
def g89L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g89D4)
  | _ => emptyPacking
def g89I (_ _ : Nat) : Option (Nat × Nat) := none
def g89 : Forest := ⟨89,4,fun i => g89Y[i]?.getD (0,0),g89C,g89A,g89L,g89I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89P4_0 : block g89 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g89B4 : block g89 4 0 1=true := g89P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89T : checkedTables g89 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g89 0 0 0 = true)
  · exact (rfl : block g89 1 0 0 = true)
  · exact (rfl : block g89 2 0 0 = true)
  · exact (rfl : block g89 3 0 0 = true)
  · exact g89B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g89G : graphValid g89 (boundsBefore K57) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low89 : Lower true (varsX 89) (graphGoal 89) 5 := lower_forest (g:=g89) (i:=0) (hints:=50331651) (before_sound K57 V57) g89G g89T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K89 := extendKnown K57 5 [(89,[]),(163,[33,49,81,116,65,97]),(169,[48,116,84,101]),(202,[16,99,116,84]),(209,[67,115,83]),(226,[80,16,49,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V89 : Known true K89 := extend_ok (m:=89) V57 low89 (by decide +kernel)
def g153Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0)]
def g153C : List ColumnInfo := [(1,0,152,0,4),(8,0,145,0,4),(16,0,137,0,4),(128,0,25,0,4)]
def g153A : List (List Nat) := [[],[116],[67],[67,115],[115,67],[115],[48],[48,116],[48,64],[48,64,112],[48,112,64],[48,112],[64,48],[64,48,115],[64],[64,112],[64,115],[64,115,48],[112,48,67],[112,48],[112,64],[112],[112,67,48],[112,67]]
def g153D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g153D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g153H4 (j : Nat) := if j=0 then 0x13 else 0
def g153D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g153H5 := limbs80 #[#[0x2b9010071801448,0x2c00052fe1c40]]
def g153D6 (j : Nat) := if j=0 then 0x3904f else 0
def g153H6 := limbs80 #[#[0x2082000010a000000050,0x12000000058801]]
def g153L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g153D3)
  | 4 => (3,2,2,0,0,5,0,g153D4)
  | 5 => (1,1,2,0,0,0,0,g153D5)
  | 6 => (1,0,2,0,0,0,0,g153D6)
  | _ => emptyPacking
def g153I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 2 0 5 1 0 g153H4
  | 5 => lookupWord 2 23 2 9 2 3 g153H5
  | 6 => lookupWord 1 23 0 9 0 5 g153H6
  | _ => fun _ => none
def g153 : Forest := ⟨153,6,fun i => g153Y[i]?.getD (0,0),g153C,g153A,g153L,g153I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P3_0 : block g153 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B3 : block g153 3 0 2=true := g153P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P4_0 : block g153 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B4 : block g153 4 0 3=true := g153P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P5_0 : block g153 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B5 : block g153 5 0 1=true := g153P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153P6_0 : block g153 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g153B6 : block g153 6 0 1=true := g153P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153T : checkedTables g153 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g153 0 0 0 = true)
  · exact (rfl : block g153 1 0 0 = true)
  · exact (rfl : block g153 2 0 0 = true)
  · exact g153B3
  · exact g153B4
  · exact g153B5
  · exact g153B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g153G : graphValid g153 (boundsBefore K89) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low153 : Lower true (varsX 153) (graphGoal 153) 7 := lower_forest (g:=g153) (i:=0) (hints:=3) (before_sound K89 V89) g153G g153T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K153 := extendKnown K89 7 [(153,[]),(216,[48,16,33,66,98,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V153 : Known true K153 := extend_ok (m:=153) V89 low153 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf007ffff87fff007ff,0xfffffffa0dce40f83ff])),(BitVec.ofNat 152 (word80 [0xa05014011000a0500a,0x20100082201824108421]))),((BitVec.ofNat 152 (word80 [0xfff801fff87ffff800,0xff87fc03373b3f00000])),(BitVec.ofNat 152 (word80 [0xc261582a010ac060ac,0x40a109082171b2739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffe00007fffffff,0xf0007ffccfd11c007c1f])),(BitVec.ofNat 152 (word80 [0x80608c2223048230,0x4c22200c2c118a5294a]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb058130444c0904c0,0x9004c100d26c14a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc0601c000700e0700,0x8e0470211a86098c6318]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,2,25,32,5),(2,0,57,0,5),(8,0,51,0,4),(16,0,43,0,4),(32,2,25,0,4)]
def g59A : List (List Nat) := [[],[67]]
def g59D4 (j : Nat) := if j=0 then 0x57d4d20 else 0
def g59D5 := limbs80 #[#[0x460e140fd32fe20fd20,0x4088]]
def g59H5 (j : Nat) := if j=0 then 0xe else 0
def g59D6 (j : Nat) := if j=0 then 0x16a09f else 0
def g59H6 := limbs80 #[#[0x200500da000000160200,0xc]]
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 1 13 0 7 2 1 g59H6
  | _ => fun _ => none
def g59 : Forest := ⟨59,6,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
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
theorem g59P5_0 : block g59 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 3=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P6_0 : block g59 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B6 : block g59 6 0 1=true := g59P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact g59B4
  · exact g59B5
  · exact g59B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K153) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=83) (before_sound K153 V153) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K153 7 [(59,[]),(122,[96,81,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V153 low59 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc01ff0ff0ffc03f,0xf0ffffff24d65b0000ff])),(BitVec.ofNat 152 (word80 [0x282a140a202282a2a0,0xa2820820048653999999]))),((BitVec.ofNat 152 (word80 [0xffffe000fffffffc0,0xff0ff0c6353900f000])),(BitVec.ofNat 152 (word80 [0x42b098ac45402b030a,0xc4142242823539777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff000ffffff,0xff000fff39b5260f0f0f])),(BitVec.ofNat 152 (word80 [0x80c0203001840c0403,0x184080383100222222]))),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x300c0c0860830080c,0x200304034828444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0301000800c03030,0x8c08c084480c4888888]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,2,25,64,5),(1,0,90,0,5),(2,0,89,0,5),(8,0,83,0,4),(16,0,75,0,4),(64,2,25,0,4)]
def g91A : List (List Nat) := [[],[67]]
def g91D4 (j : Nat) := if j=0 then 0x5ed4132 else 0
def g91D5 (j : Nat) := if j=0 then 0xc8404fd32 else 0
def g91H5 (j : Nat) := if j=0 then 0x90 else 0
def g91D6 (j : Nat) := if j=0 then 0x23468bf else 0
def g91H6 (j : Nat) := if j=0 then 0xa else 0
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (1,1,3,0,0,0,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 2 0 4 0 0 g91H6
  | _ => fun _ => none
def g91 : Forest := ⟨91,6,fun i => g91Y[i]?.getD (0,0),g91C,g91A,g91L,g91I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P4_0 : block g91 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B4 : block g91 4 0 1=true := g91P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P5_0 : block g91 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 1=true := g91P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91P6_0 : block g91 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B6 : block g91 6 0 1=true := g91P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91T : checkedTables g91 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g91 0 0 0 = true)
  · exact (rfl : block g91 1 0 0 = true)
  · exact (rfl : block g91 2 0 0 = true)
  · exact (rfl : block g91 3 0 0 = true)
  · exact g91B4
  · exact g91B5
  · exact g91B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g91G : graphValid g91 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=16777315) (before_sound K59 V59) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K59 7 [(91,[]),(121,[96,81,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V59 low91 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ff87ff007ff,0xff87fffcd47c560003ff])),(BitVec.ofNat 152 (word80 [0xa4280a201120a45214,0x81102080501c1694a529]))),((BitVec.ofNat 152 (word80 [0xfffc000ffffffff801,0xfff87fc35353a20ffc00])),(BitVec.ofNat 152 (word80 [0xc0302c40a002c06058,0xa01010a425122318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x140b002c20b008060,0x2c220a00a741086318c6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0x982c08b044c090481,0x30004c100d22c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xe03000c00700e0701,0xc044702118a6118c6318]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(1,0,106,0,4),(2,0,105,0,4),(8,0,99,0,4),(32,0,75,0,4),(64,0,43,0,4)]
def g107A : List (List Nat) := [[],[97,83],[16,99],[16,48,80,96],[48,101],[48,81,96,16],[80,49],[80,97,48,49],[96,16,49,83],[96,81]]
def g107D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g107D5 (j : Nat) := if j=0 then 0xc1a0fd20fd10 else 0
def g107H5 (j : Nat) := if j=0 then 0xc0 else 0
def g107D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g107H6 := limbs80 #[#[0x42000000c57a00,0x4eeb000000,0xa1000000f700061320]]
def g107L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g107D4)
  | 5 => (2,1,3,0,0,4,0,g107D5)
  | 6 => (1,0,3,0,0,0,0,g107D6)
  | _ => emptyPacking
def g107I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g107H5
  | 6 => lookupWord 2 29 0 8 1 3 g107H6
  | _ => fun _ => none
def g107 : Forest := ⟨107,6,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P4_0 : block g107 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B4 : block g107 4 0 1=true := g107P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 2=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P6_0 : block g107 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B6 : block g107 6 0 1=true := g107P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact g107B4
  · exact g107B5
  · exact g107B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 7 := lower_forest (g:=g107) (i:=0) (hints:=16777299) (before_sound K91 V91) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K91 7 [(107,[]),(115,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V91 low107 (by decide +kernel)
def g155Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0)]
def g155C : List ColumnInfo := [(2,0,153,0,7)]
def g155A : List (List Nat) := [[],[67],[48],[48,64],[64,48],[64]]
def g155D7 (j : Nat) := if j=0 then 0x3f else 0
def g155L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g155D7)
  | _ => emptyPacking
def g155I (_ _ : Nat) : Option (Nat × Nat) := none
def g155 : Forest := ⟨155,7,fun i => g155Y[i]?.getD (0,0),g155C,g155A,g155L,g155I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155P7_0 : block g155 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g155B7 : block g155 7 0 1=true := g155P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155T : checkedTables g155 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g155 0 0 0 = true)
  · exact (rfl : block g155 1 0 0 = true)
  · exact (rfl : block g155 2 0 0 = true)
  · exact (rfl : block g155 3 0 0 = true)
  · exact (rfl : block g155 4 0 0 = true)
  · exact (rfl : block g155 5 0 0 = true)
  · exact (rfl : block g155 6 0 0 = true)
  · exact g155B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g155G : graphValid g155 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low155 : Lower true (varsX 155) (graphGoal 155) 8 := lower_forest (g:=g155) (i:=0) (hints:=115) (before_sound K107 V107) g155G g155T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K155 := extendKnown K107 8 [(155,[]),(248,[48,81,32,66,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V155 : Known true K155 := extend_ok (m:=155) V107 low155 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(1,0,170,0,5),(2,0,169,0,5),(8,0,163,0,5),(32,0,139,0,5)]
def g171A : List (List Nat) := [[],[80,49]]
def g171D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g171L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g171D6)
  | _ => emptyPacking
def g171I (_ _ : Nat) : Option (Nat × Nat) := none
def g171 : Forest := ⟨171,6,fun i => g171Y[i]?.getD (0,0),g171C,g171A,g171L,g171I⟩
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
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact (rfl : block g171 4 0 0 = true)
  · exact (rfl : block g171 5 0 0 = true)
  · exact g171B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K155) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=83) (before_sound K155 V155) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K155 7 [(171,[]),(179,[67]),(203,[96,16,49,83]),(211,[96,16,49,67,84]),(227,[16,99,67]),(233,[48,81,33,96,66,64]),(234,[16,48,32,82,66,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V155 low171 (by decide +kernel)
def g185Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fc7f807f8ff1ffe0,0x7fffffcfd609000ff0ff])),(BitVec.ofNat 152 (word80 [0x80801010100200041,0x2040080000011111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc007fff800ffe1fff,0x80fe3ff1cdec00f00f0f])),(BitVec.ofNat 152 (word80 [0x109112121222404482,0x240889040cac22222222]))),((BitVec.ofNat 152 (word80 [0x7ffffff0001fff,0xff003ffe31e30f000ff0])),(BitVec.ofNat 152 (word80 [0xa12224242404848904,0x8511200b14344444444]))),((BitVec.ofNat 152 (word80 [0xffff80000000001fff,0xffffc0003b98f000f000])),(BitVec.ofNat 152 (word80 [0xc1c038383847090e08,0x30601c293b9866666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x20040404008001010,0x40802000000088888888]))),(0x0,0x0)]
def g185C : List ColumnInfo := [(32,0,153,0,7)]
def g185A : List (List Nat) := [[],[67],[112],[112,67]]
def g185D7 (j : Nat) := if j=0 then 0x3f else 0
def g185L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g185D7)
  | _ => emptyPacking
def g185I (_ _ : Nat) : Option (Nat × Nat) := none
def g185 : Forest := ⟨185,7,fun i => g185Y[i]?.getD (0,0),g185C,g185A,g185L,g185I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185P7_0 : block g185 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g185B7 : block g185 7 0 1=true := g185P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185T : checkedTables g185 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g185 0 0 0 = true)
  · exact (rfl : block g185 1 0 0 = true)
  · exact (rfl : block g185 2 0 0 = true)
  · exact (rfl : block g185 3 0 0 = true)
  · exact (rfl : block g185 4 0 0 = true)
  · exact (rfl : block g185 5 0 0 = true)
  · exact (rfl : block g185 6 0 0 = true)
  · exact g185B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g185G : graphValid g185 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low185 : Lower true (varsX 185) (graphGoal 185) 8 := lower_forest (g:=g185) (i:=0) (hints:=3) (before_sound K171 V171) g185G g185T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K185 := extendKnown K171 8 [(185,[]),(218,[96,16,81])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V185 : Known true K185 := extend_ok (m:=185) V171 low185 (by decide +kernel)
def g186Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffc00ff87fc3fff00,0xffffffe257e300007fe0])),(BitVec.ofNat 152 (word80 [0x20a82a051048802a2a,0xa12004a546306318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0007ffc3ffff,0xff1ffd9276c00f801f])),(BitVec.ofNat 152 (word80 [0x42308c262110088c0c,0x4c0444811226ca5294a5]))),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c130480261113030,0x10588900e8d114a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c070438221c040,0x60600e100b98d8c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80200800400020080,0x80801000000021084210]))),(0x0,0x0)]
def g186C : List ColumnInfo := [(2,0,184,0,5),(8,0,178,0,5),(16,0,170,0,5),(32,0,154,0,5),(24,0,162,0,4),(34,0,152,0,4)]
def g186A : List (List Nat) := [[],[67],[49,84],[49,81,65],[65,49,83],[65,83],[81],[81,67]]
def g186D4 := limbs80 #[#[0x9bd89544426d6215110,0x31826f625474]]
def g186D5 := limbs80 #[#[0x7c54443f2808857d4d40,0xfea8885f95110beaa221,0x7d4d40bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201161080d176b,0x8118204c10001]]
def g186H5 := limbs80 #[#[0xc0000000f10000286200,0xc900]]
def g186D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x2150c8543]]
def g186H6 := limbs80 #[#[0x1d21c581000000009055,0x114d97002d4705c77091,0xc19490000026400b0c2,0x10]]
def g186D7 (j : Nat) := if j=0 then 0x1605f else 0
def g186H7 := limbs80 #[#[0x58a5001c4004,0x20000000ba0078000000,0x40044801240000764000,0x2c200002b25]]
def g186L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g186D4)
  | 5 => (10,2,3,0,0,7,0,g186D5)
  | 6 => (3,1,3,0,0,6,0,g186D6)
  | 7 => (1,0,3,0,0,0,0,g186D7)
  | _ => emptyPacking
def g186I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 8 2 2 g186H5
  | 6 => lookupWord 4 23 4 10 4 2 g186H6
  | 7 => lookupWord 3 31 1 9 2 3 g186H7
  | _ => fun _ => none
def g186 : Forest := ⟨186,7,fun i => g186Y[i]?.getD (0,0),g186C,g186A,g186L,g186I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P4_0 : block g186 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g186B4 : block g186 4 0 3=true := g186P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P5_0 : block g186 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P5_1 : block g186 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g186B5 : block g186 5 0 10=true := (@block_merge g186 5 0 1 9 g186P5_0 g186P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P6_0 : block g186 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g186B6 : block g186 6 0 3=true := g186P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186P7_0 : block g186 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g186B7 : block g186 7 0 1=true := g186P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186T : checkedTables g186 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g186 0 0 0 = true)
  · exact (rfl : block g186 1 0 0 = true)
  · exact (rfl : block g186 2 0 0 = true)
  · exact (rfl : block g186 3 0 0 = true)
  · exact g186B4
  · exact g186B5
  · exact g186B6
  · exact g186B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g186G : graphValid g186 (boundsBefore K185) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low186 : Lower true (varsX 186) (graphGoal 186) 8 := lower_forest (g:=g186) (i:=0) (hints:=269697104) (before_sound K185 V185) g186G g186T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K186 := extendKnown K185 8 [(186,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V186 : Known true K186 := extend_ok (m:=186) V185 low186 (by decide +kernel)
def g217Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f01f9fc07f1fc7fc,0x7e7e7f1fce000f000ff])),(BitVec.ofNat 152 (word80 [0x122441489122489089,0x105052241ce444444444]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffe01fff801ff9ff,0xf807fffe66800f00ff0f])),(BitVec.ofNat 152 (word80 [0x204082010204010010,0x20808040000111111111]))),((BitVec.ofNat 152 (word80 [0xf800001fffffe001ff,0xfff807ff8160f00f0ff0])),(BitVec.ofNat 152 (word80 [0x408104020408020020,0x41010080000222222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe000000001ff,0xfffff8000bbf000ff000])),(BitVec.ofNat 152 (word80 [0x8306080c18308c24c1,0x820203094bb444444444]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x40810102040100102,0x4040400000888888888]))),(0x0,0x0)]
def g217C : List ColumnInfo := [(1,0,216,0,7)]
def g217A : List (List Nat) := [[],[116],[67],[67,115],[115,67],[115],[96],[96,116],[96,67],[96,67,115],[96,115,67],[96,115]]
def g217D7 (j : Nat) := if j=0 then 0x3f else 0
def g217L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g217D7)
  | _ => emptyPacking
def g217I (_ _ : Nat) : Option (Nat × Nat) := none
def g217 : Forest := ⟨217,7,fun i => g217Y[i]?.getD (0,0),g217C,g217A,g217L,g217I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217P7_0 : block g217 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g217B7 : block g217 7 0 1=true := g217P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217T : checkedTables g217 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g217 0 0 0 = true)
  · exact (rfl : block g217 1 0 0 = true)
  · exact (rfl : block g217 2 0 0 = true)
  · exact (rfl : block g217 3 0 0 = true)
  · exact (rfl : block g217 4 0 0 = true)
  · exact (rfl : block g217 5 0 0 = true)
  · exact (rfl : block g217 6 0 0 = true)
  · exact g217B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g217G : graphValid g217 (boundsBefore K186) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low217 : Lower true (varsX 217) (graphGoal 217) 8 := lower_forest (g:=g217) (i:=0) (hints:=50331651) (before_sound K186 V186) g217G g217T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K217 := extendKnown K186 8 [(217,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V217 : Known true K217 := extend_ok (m:=217) V186 low217 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff83ffffffff3422b,0x8c7ca80000000fe03fff])),(BitVec.ofNat 152 (word80 [0x805090080804034022,0xc4c0842850a142850a1]))),((BitVec.ofNat 152 (word80 [0x3ffc1ffe07b50c,0x5cbc20003fff0000000])),(BitVec.ofNat 152 (word80 [0x5610050404823a00c,0x50bc20e1c3870e1c387]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8c8,0x93211e01fc00001fc07f])),(BitVec.ofNat 152 (word80 [0x118002608110009088,0x912114142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f4,0x691ab3fe0000001fff80])),(BitVec.ofNat 152 (word80 [0x260004800260480444,0x2012a32850a142850a14]))),((BitVec.ofNat 152 (word80 [0x91713,0xa28774000007ffe00000])),(BitVec.ofNat 152 (word80 [0x380227011380881711,0xa28034b162c58b162c58]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0xc00438021c01044913,0x4a4000c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(8,0,115,0,7),(16,0,107,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,2,25,96,6),(0,32,88,3,6),(1,32,88,2,5),(2,32,88,1,5),(33,0,90,0,5),(34,0,89,0,5),(64,2,25,32,5),(66,0,57,0,5),(3,0,88,0,4),(3,32,88,0,4),(9,0,114,0,4),(10,0,113,0,4),(17,0,106,0,4),(18,0,105,0,4),(24,0,99,0,4),(72,0,51,0,4),(80,0,43,0,4)]
def g123A : List (List Nat) := [[],[67],[96,81],[96,81,67]]
def g123D5 := limbs80 #[#[0x4c930483b2595324c120,0x483d254d3254120ecb65,0x1cf72595208ef825d953,0xc185b54f0333]]
def g123D6 := limbs80 #[#[0x26fb9aca907c9324c120,0xd7ec8992217edc13244,0x837db2a60906f9654c12,0x20fd6e4a8241fa4c9504,0x4837cb1aa09077953541,0x520bf6e6a8241bed8d50,0x2483e6a9a64906df634c,0x4d20ddeca99241bb5953,0x634827fbaac6904fd765,0x59520bdee4b2a413f5d7,0xd6548377b92ca905df73,0x359520dbee6b2a41b71c,0xd9325427eb9eca904ff7,0x73d8950bbee6b12a13f9,0x5c3634867eb9ec090cfd,0xf75585329faebb02653f,0x1a8c85e2810858260057,0x6c32978ae50249087638,0x2e9446a2906803c9c8de,0x1084b056aa94ea450a69,0xc1a20710042019c0e0,0x4041c206941050400000,0x100594100003040c1100,0x28810000304010040,0x30810000]]
def g123H6 := limbs80 #[#[0x3e088b1002c0a408,0x2a40101018005600]]
def g123D7 := limbs80 #[#[0xe54120fe4c120afd9110,0xd8d20bf58d20fb4c920f,0x8950bfd9520bf59520bf,0x132bfd8d21bfd8121bfd,0x20ff4c520ff4c910bfd8,0xff54d20ff58520ff545,0xff4c940ff59520ff58d2,0xfd8950ff58950ff4c950,0x58532ff58132ff4c941f,0xd47f0b911214814800ff,0x50a7f49087cfb1b83024,0x36c6a2cbd86af9592ad5,0x1e00c1607be6796ec1c7,0x84b0872440423842e3c4,0x94209c14046310c31a20,0x40728488070c14201804,0x9080c0065070c100e546,0x4a1018120395201c3250,0x5801c304038e2a220386,0xc384003088a101a81844,0x44187081c30503910141,0x203244230d0c10626144,0x2885091046216201111c,0xa880141110a0e195208d,0xc306140220ca90468840,0x4b0908c5091084805442,0x4c886]]
def g123H7 := limbs80 #[#[0x244440b81005,0x1c2400005707c914c64,0x44c00000281c0,0x3c6000146cc6b44000,0x0,0x87921000000343c0000,0x382000142f07,0x0,0x202b05d0100744480000,0x718c0f45000245800000,0x1110000003c34001831,0x0,0x148372c00151800000,0x39618000000c00000000,0x3a24000000002d,0x43b52c000003c1400,0xe1c002c1b804000000]]
def g123D8 := limbs80 #[#[0xd21fea87f503fa41fd10,0xd210c024007f4cbfa83f,0x10882448e230f161cea5,0x2258e22891464009648e,0x99023071638a4221300,0x18030898e22cc2058c18,0x1c652592]]
def g123H8 := limbs80 #[#[0x92ca702015810121c00,0xd5468c30005b88780000,0x6113e6488795fb0c,0xe4200000231905b1d848,0x460024b800cc4eb741,0x11145b4c001a60c400,0xe08006000006884b0000,0x5d42b6003c100078c428,0x287614003a9893001d6,0x1098000009220000]]
def g123D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g123H9 := limbs80 #[#[0x94bce100006005,0x7a400dc0000000000,0x8000000025d00020b460,0xa00036200000031,0x14a006080]]
def g123L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g123D5)
  | 6 => (33,3,5,0,0,9,0,g123D6)
  | 7 => (26,2,5,0,0,11,0,g123D7)
  | 8 => (7,1,5,0,0,9,0,g123D8)
  | 9 => (1,0,5,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 4 9 3 2 g123H6
  | 7 => lookupWord 11 113 2 12 6 2 g123H7
  | 8 => lookupWord 11 67 5 11 5 2 g123H8
  | 9 => lookupWord 3 41 1 9 3 2 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 5=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_2 : block g123 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 33=true := (@block_merge g123 6 0 2 31 g123P6_0 g123P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_1 : block g123 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_12 : block g123 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 26=true := (@block_merge g123 7 0 1 25 g123P7_0 (@block_merge g123 7 1 11 14 g123P7_1 g123P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 7=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P9_0 : block g123 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B9 : block g123 9 0 1=true := g123P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K217) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=16777299) (before_sound K217 V217) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K217 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V217 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ff87ffffff98c2,0x903af000000fc0fc0fff])),(BitVec.ofNat 152 (word80 [0x4050051004001018c2,0x80006041041041041041]))),((BitVec.ofNat 152 (word80 [0xfff80007fe1ff83b0f,0x3485500003f03f000000])),(BitVec.ofNat 152 (word80 [0x806056202841213a0f,0x140551c71c71c71c71c7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x79312000fc000003f03f])),(BitVec.ofNat 152 (word80 [0x48118013084400015,0x7931028a28a28a28a28a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x90260024009824628,0x2869514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038043810e044100,0x63e88618618618618618]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400040010000000,0x820820820820820]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(1,0,186,0,8),(2,0,185,0,8),(32,0,155,0,8),(8,0,179,0,7),(16,0,171,0,7),(128,0,59,0,7),(24,0,163,0,5),(136,0,51,0,4),(144,0,43,0,4)]
def g187A : List (List Nat) := [[],[67]]
def g187D6 := limbs80 #[#[0xe5c5243e0374d5354932,0x5]]
def g187D7 := limbs80 #[#[0xf54d52bf59532fb54932,0x42a00ff58d52bfd8d52d,0xc70187cb1570186ae8a5,0x481c5cb15308c82071b2,0x81c60d4c72c071]]
def g187H7 (j : Nat) := if j=0 then 0x90 else 0
def g187D8 := limbs80 #[#[0xa3946061a403faa5fd32,0x1e851ca301c]]
def g187H8 := limbs80 #[#[0x0,0x410000000000000000,0x9800000000,0x4200000000,0x830000c4,0xa00000]]
def g187D9 (j : Nat) := if j=0 then 0x5432101bf else 0
def g187H9 (j : Nat) := if j=0 then 0x1c8f5 else 0
def g187L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g187D6)
  | 7 => (5,2,4,0,0,8,0,g187D7)
  | 8 => (2,1,4,0,0,6,0,g187D8)
  | 9 => (1,0,4,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g187H7
  | 8 => lookupWord 1 53 0 8 3 1 g187H8
  | 9 => lookupWord 1 3 0 6 1 1 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 1=true := g187P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_4 : block g187 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 5=true := (@block_merge g187 7 0 4 1 g187P7_0 g187P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 2=true := g187P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P9_0 : block g187 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B9 : block g187 9 0 1=true := g187P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187T : checkedTables g187 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g187 0 0 0 = true)
  · exact (rfl : block g187 1 0 0 = true)
  · exact (rfl : block g187 2 0 0 = true)
  · exact (rfl : block g187 3 0 0 = true)
  · exact (rfl : block g187 4 0 0 = true)
  · exact (rfl : block g187 5 0 0 = true)
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=83) (before_sound K123 V123) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K123 10 [(187,[]),(250,[96,81,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1ffc01ffc3ffffffe4,0x1b4332800007c00003ff])),(BitVec.ofNat 152 (word80 [0x4829148289040820c4,0x1b031225294a5294a529]))),((BitVec.ofNat 152 (word80 [0xfffffe0003fe1ff047,0x2c4bcc8000f8000f8000])),(BitVec.ofNat 152 (word80 [0x2b0182b1028424243,0x2c4b4c9ce739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffffc001fff38,0xf46918001f0001f07c1f])),(BitVec.ofNat 152 (word80 [0x80c0200c0030808038,0x44480808421084210842]))),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xaa846f83e0003e007fe0])),(BitVec.ofNat 152 (word80 [0x30040300040030400,0xa0046590842108421084]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x11ba877c00003fff8000])),(BitVec.ofNat 152 (word80 [0xc0180c021810c0804,0x11b08221084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x4514407fffffc0000000])),(BitVec.ofNat 152 (word80 [0x100201000200100000,0x42108421084210]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,8),(2,0,217,0,8),(64,0,155,0,8),(8,0,211,0,7),(16,0,203,0,7),(128,0,91,0,7),(0,2,25,192,6),(10,0,209,0,5),(24,0,195,0,5),(128,2,25,64,5),(136,0,83,0,4),(144,0,75,0,4)]
def g219A : List (List Nat) := [[],[67]]
def g219D5 (j : Nat) := if j=0 then 0x2f8e017354921 else 0
def g219D6 := limbs80 #[#[0xb73b1aa490f655354921,0x19f6e0b2a65d354d524c,0x4b7db82ca997e5735492,0x471eda9652017edc1635,0xd03f211a0ae02790b61,0x2c98f971104f0e4204e,0x1602]]
def g219H6 (j : Nat) := if j=0 then 0x80 else 0
def g219D7 := limbs80 #[#[0xdd8d21bd58d21f954921,0x59532fb54932fd54d21b,0x8d52bfd8d52df54d52bf,0xa379688a331205400ff5,0x479122141e986448d388,0x3298479122e0a64388a,0x41656246580c52a4e191,0x6386450a5942e3864a46,0x16520408a]]
def g219H7 := limbs80 #[#[0x8090000402c95b8e,0x257a000]]
def g219D8 := limbs80 #[#[0x88a4b807f54bfa65f521,0x1ca38c24818273568384,0x2a851c612]]
def g219H8 := limbs80 #[#[0xf280000d30031c01a8,0x460000000c30018000,0xd3480000000000220800,0x5]]
def g219D9 (j : Nat) := if j=0 then 0x5430211bf else 0
def g219H9 (j : Nat) := if j=0 then 0x12a400c802b19 else 0
def g219L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g219D5)
  | 6 => (7,3,4,0,0,8,0,g219D6)
  | 7 => (9,2,4,0,0,9,0,g219D7)
  | 8 => (3,1,4,0,0,7,0,g219D8)
  | 9 => (1,0,4,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g219H6
  | 7 => lookupWord 2 13 1 8 3 1 g219H7
  | 8 => lookupWord 2 29 0 9 4 1 g219H8
  | 9 => lookupWord 1 7 0 7 2 1 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 1=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_4 : block g219 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 7=true := (@block_merge g219 6 0 4 3 g219P6_0 g219P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_3 : block g219 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_8 : block g219 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 9=true := (@block_merge g219 7 0 3 6 g219P7_0 (@block_merge g219 7 3 5 1 g219P7_3 g219P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_1 : block g219 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 3=true := (@block_merge g219 8 0 1 2 g219P8_0 g219P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P9_0 : block g219 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B9 : block g219 9 0 1=true := g219P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219T : checkedTables g219 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g219 0 0 0 = true)
  · exact (rfl : block g219 1 0 0 = true)
  · exact (rfl : block g219 2 0 0 = true)
  · exact (rfl : block g219 3 0 0 = true)
  · exact (rfl : block g219 4 0 0 = true)
  · exact g219B5
  · exact g219B6
  · exact g219B7
  · exact g219B8
  · exact g219B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219G : graphValid g219 (boundsBefore K187) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=16777315) (before_sound K187 V187) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K187 10 [(219,[]),(249,[96,81,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V187 low219 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe007ffffe1ffff9164,0xdc16e000000fc0000fff])),(BitVec.ofNat 152 (word80 [0x44510a204404101144,0xcc00e249249249249249]))),((BitVec.ofNat 152 (word80 [0xfff800fffe1ff8318b,0x3c89500003f000fff000])),(BitVec.ofNat 152 (word80 [0x80602c028040213083,0x3c0140c30c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0x80300b0881400a39,0x31110186186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x902404c0009824628,0x3861514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe038070110e044104,0x42ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100400800010000000,0x820820820820820]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(1,0,234,0,7),(2,0,233,0,7),(8,0,227,0,7),(32,0,203,0,7),(64,0,171,0,7),(128,0,107,0,7),(3,0,232,0,5),(9,0,226,0,5),(10,0,225,0,5),(33,0,202,0,5),(40,0,195,0,5),(65,0,170,0,5),(66,0,169,0,5),(72,0,163,0,5),(96,0,139,0,5),(35,0,200,0,4),(41,0,194,0,4),(73,0,162,0,4),(74,0,161,0,4),(98,0,137,0,4),(129,0,106,0,4),(130,0,105,0,4),(136,0,99,0,4),(160,0,75,0,4),(192,0,43,0,4)]
def g235A : List (List Nat) := [[],[97,83],[16,99],[16,48,80,96],[48,101],[48,81,96,16],[80,49],[80,97,48,49],[96,16,49,83],[96,81]]
def g235D5 := limbs80 #[#[0xa0221dc1744c9214c110,0x5248540443f028699242,0x34bb2a4a8240887c8551,0x8221d617154950c8110e,0x248530443d82ca992429,0xc2a6490a60887705d53,0x221bc3854c9214c110de,0x54530443ca2caa9a4298,0xba2a8a8a60887545d153,0x21e5391595534c110e98,0x46304438b2e8b2aa6982,0x1aa8a8c60886745d7835,0x1d3174551518c110f88a,0x540443ac242baaa51822,0x6a6a8a80887585d55248,0xe33625515150110b98ca,0x4044366704aa2a2a0221,0xa8a8e808865c55387546,0x157355151d0110e98b82,0x443cc2c4a92a2a8221d,0x528aa0886d8e09525455,0x18254a5154110f30b12a,0x4434b30ca9a64a8221b6,0x212a08869a6195250950,0x8654a4254110db0c0aa5,0x434d706b12a4a8221a69,0x92a08859ae4d62549504,0x160c7254110ba4c9cc4a,0x3692a4c18e4a8221bc12,0x2a0886b2589831c95044,0x6107254110ce4b930639,0x652a4c20e4a8221ba121],#[0xa08869a58982d4d50443,0x97454110d2db1b05a9a,0xa2e2c18e0a92219e3712,0x48866c5c5841c1524433,0x5534c210c5cbb308382a,0x328b1aa6a8421c597459,0x878664d6454d50842cb,0x5150610b1acb2a8a8a83,0xca9462a824163796551,0x69a61952945504834d3,0x254120b34c8ec6a92a09,0x8c16a6a82419c97160c7,0x63ae5980dc9548834d2c,0x54950e54a82c9b92a910,0xb9ac4312a1b619260470,0x3354b835c76254319f02,0x5c00c6729706b8ec4a86,0x59208a421f8f07236198,0x631980ba5a2b950a24e2,0x27e3d9e0ea72379b0d26,0x1329649a411a8a43a110,0xad162ae55aa14aa24fa7,0x67b3192c661b017aba5b,0xea73b91c2de6db61aad2,0x48819061606590224044,0x2a820]]
set_option maxRecDepth 16000 in
def g235D6 := limbs80 #[#[0x48420443705cd2108110,0x443785d52108110d6175,0x5d15108110dd17354420,0x8110d7175544204436c,0xd71815d4204427ce1d51,0x54530443f04c9214c110,0x44396595534c110f5153,0x5515150110bd38354630,0x541109f38754640443cc,0xe69625495044237e0d76,0xd4d504439658d5354110,0x443acd076454110e5b63,0xe0d76d49108df835d952,0xd4d10cdb635c35344237,0xe596554d308429761763,0x549508439a5895254210,0x8438e5935254210e3964,0x5915354210e596354d50,0xd4610e3964d4d508438e,0xcb9645c3528432e59170,0x5c3548432e59170d4e10,0x833658f7054c20cb964,0x5977054c20cb964dc153,0x54120e6952d85504831e,0xb6b83549504839ad8d52,0x1c950482da6165254120,0x882da60b5354120bc983,0xe0d7654620e596354d50,0x552209e980dc95488237,0x8f787584615432b59372,0x1c152542dc6047054950,0x542ce6107054950b5983],#[0xe1d6218950ccd7358862,0x481108df835c7625423b,0xf695254320443da54950,0x4c7204435e5d550c8110,0x4427e61f53c8110df175,0x54d214c110fe14248530,0x4c110df17448530443f4,0xfd13254530442fce1521,0x4c930443dc551514c110,0x443dc551518c110dd974,0xe055050110d797554a30,0x50110f355454540442fc,0xfe15248540443f84c921,0x54540443bcd952150110,0x443dc54d5150110bbb84,0xe116550110f735354540,0xd0110df17154340442ee,0xd757554740443cd55151,0x94550443dc5495154110,0x443d654d3254110f7152,0x6144254110bf18110950,0x54110af98610950442de,0xf6952509504427e61c42,0x90950443da54a4254110,0x443da5895254110b7985,0x6165254110f6a6254950,0x54110b798598950442de,0xbb9841c950442f660c72,0xd4d504427ea1f4354110,0x442fa2097454110b7982,0x5515250910d79805d442,0x54910bd9831c152443cb],#[0xb7980d5152442ee61070,0x59153083cd5515150610,0x483375d57458c20e9d83,0x54d3154120f69524c550,0x54120f69528c550483d6,0xf695294550483da54951,0x54d508839e5496154220,0x5439d5516154620e7964,0x5d55108110cdf641cd61,0x48110df1815d4204437c,0xcf576545204433e5d950,0x5d9204423f6157648110,0x4437c5c550c81108ff85,0x60750c8110bf38154320,0xc8110f6952d4320442fc,0xd7975d4320442fa60b50,0x547204427e61f50c8110,0x4427de1d51c81109f587,0x59571c8110de5525c720,0xc8110fe1524c7204433d,0xbf1854c720443f454d31,0x54720443f84c951c8110,0x443dc54d51c8110fe152,0x5cd51c8110f735354720,0xc8110bf383547204437c,0xfc9534cb204437c5d551,0x4cb204437a5d532c8110,0x443f860552c8110be985,0xe0d52c8110de97354b20,0xc8110deb8754b20442fa,0xafb8654f20443765cd53,0xd4f204427e61d53c8110],#[0x442fa60b53c8110bf181,0xe0d65c8110beb8259720,0xc81109fb8759720442f6,0x9f98799720442fa60a65,0x5d7204437c60575c8110,0x443f8549214c1109fb83,0x5d5214c110ef16548530,0x4c110bf185485304437c,0xfd15354530442fce0951,0x54530443dcd51514c110,0x4437c5d5514c110df174,0x5d5324c110ed9654c930,0x4c1109fb875493044376,0xbdb8254d30443f460553,0x54d30443765d1534c110,0x442fce05544c110ed965,0x61d544c110db97455130,0x4c110df3815d1304427e,0x9fb855d1304433e59574,0x59530443bce05654c110,0x4437ce05754c110edb83,0xe11754c110ddb835d530,0x8c110fe152486304427e,0xdf17548630443bc59521,0x48630442fc615218c110,0x442fce09518c110bf385,0xd51518c110fd38354630,0x8c110df17454630443dc,0x9fb8754a304437c5d551,0x55230442fce05548c110,0x4427e61d548c110db974,0xe0d658c110cf9655d230],#[0x8c110cfb8759630443b6,0x9fb845d6304435ed4975,0xd4140442be6195050110,0x443bc5952150110bf181,0x5522150110df17548540,0x50110ef16588540443ec,0xbf185885404437c5d621,0x54540443ce5515150110,0x442fce095150110ef362,0xe0d5150110df37354540,0x50110fb15454540442fc,0xf735454540443ec95151,0x54540443ec2115150110,0x4437c5d55150110fb384,0x5d65150110df37554540,0x50110df375945404437c,0xbb984d4540442fc61651,0x549404427e61f5150110,0x4427ee1d5250110d7975,0x6135250110bf181d4940,0x50110d7975d4940442ee,0x9f987d4940442be61b52,0xd89404433e5d76250110,0x442f6e0d6550110af985,0xe056550110ef38159540,0x50110afb8259540442be,0xedb8359540443b620d65,0x59540443ae2116550110,0x4433e21d6550110ebb84,0x60b6550110bb98499540,0x90110ef16254640442be,0xf715454640442fce0951],#[0x54640443dcd515190110,0x443ba5895290110df175,0x6195290110d797554a40,0x901109fb8754a40442be,0xd7975d4a40442fc60752,0xd4a40442be61b5290110,0x4433e5d562901109f987,0xe055490110afb8558a40,0x90110d797555240442fc,0xd7975d5240442fc60754,0x59640442be61b5490110,0x443b6e0d6590110afb82,0x6057590110cfb8759640,0xd0110dd973543404437c,0xd797554340442eee1150,0x54740443755cd51d0110,0x4427de1d51d01109f587,0x59571d0110db5545c740,0xd0110d9d545cf404433d,0xc7d655d7404433759573,0x549504427d60b7154110,0x4433b58b7254110e6d62,0xe097654110a7f8559150,0x54110cdf835d9504423f,0xef36254550443bc58951,0x54550442fce095154110,0x443bc58d5154110f7153,0xdcd5154110ef36354550,0x54110ef162945504437c,0xef16494550442fc60a51,0x1c5504437cdd25154110,0x442fc6087154110f7152],#[0x9cb7154110f7152dc550,0x54110bf182dc5504437c,0xdf173dc550443dc54f71,0xdc550442fc60f7154110,0x443da5493254110df174,0x6153254110edb634c950,0x54110af9864c950442de,0xf69528c950442fc60632,0x8c950442de6163254110,0x442f660c4254110af986,0x61942541109fa8710950,0x54110bf18190950442be,0xaf98690950443ead0a42,0xd0950442be61b4254110,0x4427ea1f42541109f987,0x6055254110ee96254950,0x54110f728154950443dc,0xf6872549504439ed8952,0x54950443dadc95254110,0x4439ed8d5254110e7963,0x5915254110b7b8354950,0x54110e7b64549504439e,0xbf181949504435edd152,0x94950443ba58a5254110,0x4439e58b5254110af986,0x58f5254110e7b62d4950,0x54110e7b63d49504439e,0xe7964d4950442de60f52,0xd49504439ed935254110,0x442dee156254110d7b74,0xdc96254110ee87258950,0x54110e795358950443ba],#[0xafb83589504439ed4d62,0x589504433edd16254110,0x4439e2156254110afb84,0x60e6254110e7b8558950,0x54110cfb74d8950442f6,0xbf1811c950442be61362,0x1c9504437a5c87254110,0x442fce057254110bba84,0xe054354110bf1819c950,0x54110edb6350d50442fc,0x9fa8750d5044376dcd43,0xd0d50442be61b4354110,0x443dc60553541109f987,0xdcd5354110b7b8254d50,0x54110ed95358d50443d6,0xedb73d8d50442be60b63,0xdcd50442be6136354110,0x4427e6137354110dd953,0xdd15454110bf38155150,0x54110dbb74951504436e,0xb7b8559150442be61a54,0x59150442bee096454110,0x4439ee156454110e7885,0x6166454110bd98399150,0x54110af982d9150442de,0xbeb825d150442fce0574,0x9d150442fc6067454110,0x4436edd27454110bd983,0x6077454110bf181dd150,0x54110df281dd1504437c,0xcfb8758a504427e60f74,0x55250442fce055494110],#[0x4433ee1d6494110db974,0xe0971d4110cf5625c750,0xd4110cf5645c7504427d,0xcf964dc1324433b58972,0xdc1324427e613704c910,0x442bbe09644c9109f985,0xe1d644c9108fd8759132,0x4c910cfb805d9324423f,0x8fd855d9324423fe1176,0x5c6324423fe15764c910,0x4433d595718c910de552,0x5d9528c910beb8054a32,0x8c9108fd855da324433b,0xcf9655c0424423fe1576,0x5cc424433ed957010910,0x44337d957310910cdd65,0xd957510910c7d655d442,0x109108fd865d4424431f,0xc7e865d4424431f61975,0xd8d424423fe157610910,0x4423f61f65509108fd87,0x5957190910de5525c642,0x90910cf7655c6424433d,0xeaf65d0a42443ab59742,0x5d6424433b5d95290910,0x4423f61975909109fb80,0x5c470549108ff855da42,0x54910cf9761c1524437c,0xdf271dc1524437c5c770,0xdc1524433e5db7054910,0x4437c6077054910cfa76,0xd8b7054910df281dc152],#[0x549109f983dc1524433e,0xcf965dc1524427e61370,0xdc1524433ed977054910,0x442f360e6254910cfa86,0xe057654910cfb805d952,0x549108ff815d9524433d,0xcdf835d9524433720d76,0x5d9524423fe0d7654910,0x4423f6037654910c7f85,0x60f76549108fd81dd952,0x949108fd84dd9524423f,0xcf7655c6524433d59571,0x5c3524437c4c570d4910,0x4433ed8970d4910df231,0xd8d70d4910cf9635c352,0xd49109f9835c3524433e,0xcf9645c3524427ee0d70,0x5c3524433ed9170d4910,0x4437c4c171d49109fb84,0xd8971d4910df2305c752,0xd4910cf5635c7524433d,0x9f5835c7524433dd8d71,0x5c7524427de0d71d4910,0x4433dd9171d4910cf564,0x59174d49109f7815d352,0xd49108fd865d3524432f,0xcfa305db524433e4c176,0x5db524433d4c576d4910,0x4433720d76d4910cf631,0xe0d76d49108fd835db52,0xd49108ff835db5244337,0xaef82595624423fe1176],#[0x59562442b7e0d6558910,0x4431f9977558910c7f75,0x6137358910cdf53dcd62,0x589108fd85dcd624423f,0xc7d50dd5624423fe1773,0xdd5624431fd437558910,0x4423f60f7558910c7f51,0x5957598910cdd655ce62,0xd8910cbd545d3624431f,0x8ff855d3624423f61574,0x5d7624431f54975d8910,0x4423fe1175d8910c7f52,0xe0d6554d10e7b8059553,0x54d10cfb805d95344397,0xcdf835d9534423fe0976,0x5c3534423f60b7654d10,0x4427ee0172d4d109fb84,0xe0d65d4d10cdf635cb53,0xd4d108ff825db5344397,0xced525cb6344337e0d76,0x5cb634423fe1172d8d10,0x4423fe1572d8d108fd85,0xe0d75d8d108ff825d763,0x59510cee62dc96544337,0xddb80dcd654437654373,0xdc1654433798b7359510,0x443b61cf7059510ef371,0x60f7059510edb73dc165,0x59510af984dc165442be,0xced20dc9654423f60b70,0xdc9654433bc837259510,0x4433bc877259510ced21],#[0xd0b7259510cec42dc965,0x59510ced52dc9654433b,0x8fd83dc9654433b94b72,0xdc9654423fe0f7259510,0x4423fe1372595108fd84,0xdc87359510cdd721cd65,0x59510cdf70dcd6544337,0xcdc72dcd65443b6e0373,0xdcd65443375cb7359510,0x44337dcb7359510cde72,0x8cb7359510cdd32dcd65,0x595108fd82dcd6544337,0xcdd20dcd654433754f73,0xdcd6544337c837359510,0x44337d037359510cdd40,0x6037359510cdd50dcd65,0x59510cdf80dcd6544337,0xcdd42dcd654433710b73,0xdcd654433790b7359510,0x4433794b7359510cdd52,0x60b7359510cdc82dcd65,0x59510cde82dcd6544337,0xced625ca6544337e0b73,0x5cb654433b54972d9510,0x8423fe1172d9510cee52,0xe11754c210ed96554d30,0x54210cfb865d5308427e,0xe7b7654950843ae59141,0x589508439e5875254210,0x8439e5915354210ee952,0x5935354210e7b7654d50,0x54210ed95358d508439e],#[0xeb954591508427e61373,0x59150843ae5d16454210,0x843ae5c56454210eb951,0x5496454210eb98159150,0x54210eb97259150843ae,0xeb97359150843ae54d64,0x59150843ae60d6454210,0x8427e60f7454210eb985,0x60f7654210af982dd950,0x50610af984dd950842be,0xeb56454541842fce0151,0x551418439d5955150610,0x842afe195450610abd86,0x6137054610cbd7559141,0x54610e3d64551518427e,0xa7f86551518429f61954,0x59151843ad6056454610,0x8438f6156454610cbf72,0x61d6454610e3e8559151,0x54610cbe87591518432f,0xa7f84595518431fdc965,0x5c3518433e58970d4610,0x8438f59154d4610cf964,0x5c964d4610a7d8655351,0xd4610e3d85593518432f,0xcbd645d3518432f61d64,0xdc1528431f5c965d4610,0x8433e61b7054a10cf965,0xdc56254a10eeb7058952,0x54a10cbf71591528433b,0xc7f71595528439edc165,0x5c3528433ee017654a10],#[0x8432f5c564d4a10cf961,0x60576d4a10c7d7159752,0x54e10e9d83591538423f,0xcbe87591538432f61d64,0xdd9538423fe117654e10,0x8433e59170d4e108fd84,0x59174d4e10cbd8759353,0x552108fd865d3538432f,0xcbf73591548432fdc564,0xdd9548423fe0d7655210,0x8433e58570d52108fd83,0x60d70d5210cf9635c354,0xd5210e3d51593548427e,0xcbd73593548432f5c564,0x5db548433e4c176d5210,0x8423f60d76d5210c7d51,0xe157159210cbd755c564,0x59210cbd755cd64842af,0xabf815d564842afe1573,0x9d564842afe0d7559210,0x842af60e7559210abd81,0x6137359610cdd43dcd65,0x584208fd83dd1658423f,0xaf584d4d61082bde1153,0xdc1530833e5937054c20,0x833e61b7054c20cf965,0xdd16354c20edb7058d53,0x54c20cbf745915308337,0xcbd8759153083aedc164,0x595530832fa1d6454c20,0x831fdd16554c20e7b70,0xe117654c20cfb805d953],#[0xd4c208fd84dd9530823f,0xcbd8759353083375d163,0x5db530831f5d165d4c20,0x82b7e157458c208fd84,0xe117558c20edb805d563,0x59420add849d563082b7,0xe7b805cd650823f61373,0xdcd650829fe117359420,0x483da6015254120a7d84,0x61a3154120f6b8054950,0x54120af98690550482be,0xee952d8550482be61a51,0x54950483badcb6154120,0x483bad8d5254120f6953,0x5855254120beb8354950,0x54120f6a6154950483da,0xf697154950483da1c552,0x54950483da9c55254120,0x483da5cd5254120f6b71,0x60d5254120f6b7354950,0x54120f6b8354950483da,0xde9711c950483da21d52,0xdc950483da54f7254120,0x4837a5d37254120be983,0xdcd5354120f698254d50,0x54120af981d8d50483d6,0xdb954dd150482be60764,0x5d6314833d5d9518c520,0x4823fe15768c5208fd86,0x60f7654520a7d85d8551,0xd4520cfb615c3514823f,0xdea325c3514837a4c970],#[0x5c3514835e54d70d4520,0x4833ed8d70d4520cf963,0xe1170d4520cfb645c351,0xd4520a7d85d87514827e,0x8fd81dd9534823fe0d76,0x5c3534823f6137654d20,0x4837a50172d4d209fb84,0xe1176d4d208ff815db53,0xd8d20cf5515c7634823f,0x8ff855c7634823f61571,0xdc5654823fe0575d8d20,0x4833d9877159520cf561,0xdcb7059520cfb71dc165,0x59520af984dc165483ba,0xcf710dc5654833d44371,0xdc5654833d5477159520,0x4823f60f7159520cf651,0x8c773595208ff83dc565,0x595208fd81dcd6548337,0xcdd53dcd654833750f73,0xdcd654823f6137359520,0x4833d58571995208ff84,0x94571d9520cf5515c765,0x54220ef151585508833d,0xcfb74585508839ed4961,0xd4d508839edd95354220,0x883b654d6354220e7964,0x5c77654220eb95459150,0x54220af981dd9508833e,0xaf984dd950882be60f76,0x585518833ddc96154620,0x8838f5915454620e7754],#[0xe117654620cdf835d951,0xd46208fd84dd9518823f,0xcf9645c3518833e58970,0x5db518833e50176d4620,0x8823f61176d46208fd82,0xe055458620afb8054961,0xd4a20cf9615c352882bd,0x8ff845d9538833d58571,0x5c3538823f6137654e20,0x8833e50176d4e20cf964,0xe095458e208fd845db53,0x55220de950dc954882bb,0x9ed81dc9548837a60372,0xdc9548833b5977255220,0x8838fd456455220ced86,0xdcd6455220eaf7259154,0x552208ff815d9548832f,0x8ff835d9548833be0976,0xdd9548823f6077655220,0x8833e58570d52208fd83,0x58571d5220cf9635c354,0xd52208fd865c7548833d,0x8fd84dc5658823f60d76,0xdd1658823f6137359620,0x5423f60f74596208fd81,0x60b7054550d7952dc151,0x54550d7953dc1515427e,0x9f984dc1515427e60f70,0x5c2515435e5497094550,0x5439d54b6194550cfb64,0x6136194550af582d8651,0x18550cf57258461542bd],#[0xcf78758461543b5e0d61,0xdcd61543375907358550,0x543764837358550dda10,0x9037358550dda20dcd61,0x58550dd880dcd6154376,0xd5d52dcd6154376e0373,0xdcd6154357d4b7358550,0x5433758b7358550cdc62,0xd8b7358550cde62dcd61,0x58550cdc64dcd6154337,0xcde64dcd615433759373,0xdcd6154337d937358550,0x5432f5937458550d5c85,0x54b6198550cbe64dd161,0x98550af582d86615439d,0xced645ca615437a60172,0x5ca615433bd917298550,0x5435ba157298550d6d85,0x5917498550ced865ca61,0xd8550cf8805cb615432f,0xced215cb615433ee0172,0x5cb615433bc8572d8550,0x5433b8c972d8550ced32,0xe0d72d85508fd835cb61,0xd85508fd845cb615423f,0xcdd325cf615423fe1172,0x5cf615423fe0973d8550,0x5423fe1173d85508fd84,0x50574d8550cbf405d361,0xd8550cbf415d3615432f,0xcbf425d3615432f50974,0x5d3615423fe0974d8550],#[0x5432fd0d74d8550cbd43,0xd8770549508ff835d361,0x549509f981dc1525433e,0x9f983dc1525435e54f70,0x1c1525427e6137054950,0x542dea187054950b7981,0xd8b7054950b7981dc152,0x54950d7973dc152543da,0xb7984dc152542de60f70,0xd8a525433bd897194950,0x5437c6017118950aed81,0xe1d6218950aef8158862,0x18950cdd615cc625433b,0xcbd619d0625432f58574,0xdc5625433d5877158950,0x5433d5857198950cf661,0x48571d8950cef625c662,0xd8950cf6215c7625433d,0xcf6315c7625433d4c571,0x5c7625433720d71d8950,0x54337e0d71d89508fd83,0x61171d89508ff835c762,0xd89508ff845c7625423f,0x8fd845cf625423fe0573,0x5d3625423fe1173d8950,0x5432f50d74d89508ff81,0x60f72587508ff835d362,0x587508fd84dc961d423f,0x8fd84dcd61d423f60b73,0xdd161d432fd037458750,0xd432f90b7458750cbc42,0x60f74587508fd82dd161],#[0x58b508fd83dc562d423f,0x8fd81dcd62d423f61371,0xdd162d423f6137358b50,0xd423f6077458b50cbe41,0xc00300008fd83dd162,0x40c005402400f0060024,0xd05d02b8132091842c1d,0x21f20f607503781a40b,0x4889e44b023710f88404,0x6423121818bac5a62b21,0x1dd0e406de35719f8cc0,0x88243b20d10087d43c9,0x226892c091e46e22f914,0xe8a6852e28f941ca024f,0x942c295fcace5612a014,0x824bf45e22e99710b465,0x66c3331980ca264b31e1,0x1b18d6e69f34c9a28cf6,0x7323919c2cdf86e4366,0xd9e0cefa76e3af9d1ce7,0xe7ef3eb9f20f847aa3c,0x35214907482b412a0590,0x1768ac44ea2390fe8794,0x478a3ad1ca8df4682305,0xd22a90f484a40d1fa8f7,0xf49ca4cd25a927490a46,0x8d2ba9574a8a52d28a93,0x874c0a5ed2ea96f4b4a5,0x6ad34a99f4cca64d31a9,0x9cf4e4a70d37a9b74d8a,0xa7cd3da9e74f0a76d3aa,0xaa17508a82d40a9ff4fc],#[0xa8ed46aa2f514a88d43,0xcaa5f52ca94d49aa4752,0x44aa0d4faa77538a9ad4,0x55aaa7550aa6d52aa8f5,0x568ab2d58aabf55caacd,0xd5eaaef574ab8d5baad7,0xf58cac4d61ab07580abe,0xd67ab37598acad64ab1,0x675b0ad6d6aab4f5a4ad,0xe2d70ab7f5bcadcd6dab,0xbaf5d4ae8d73ab975c8a,0xaf4d79abc75e0aeed76a,0xabf75f8afad7cabdf5ec,0xb06d82ac0f604b00d7f,0x8ac3f61cb0cd85ac2761,0x34b18d8bac57628b12d8,0x91ac87640b1ed8eac6f6,0x658b2ad94ac9f64cb24d,0xd9aaccf664b30d97acb7,0xf67cb3cd9dace7670b36,0x8da3ad17688b42da0acf,0x476a0b4eda6ad2f694b4,0x5adacad5f6acb54da9ad,0xd8f6c4b60dafad776b8b,0xb6cdb5ada76d0b66db2a,0xadd76e8b72db8adbf6dc,0xb7edbeadef6f4b78dbb,0x4ae1f70cb84dc1ae0770,0x24b90dc7ae37718b8adc,0xcdae67730b96dcaae4f7,0x748ba2dd0ae7f73cb9cd,0xdd6aeaf754ba8dd3ae97],#[0xf76cbb4dd9aec7760bae,0xddfaef7778bbaddcaed,0x27790bc6de2af0f784bc,0xd2de8af3f79cbccde5af,0xf6f7b4bd8debaf577a8b,0xbe4df1af877c0bdedeea,0xafb77d8beadf4af9f7cc,0xbf6dfaafcf7e4bf0df7,0xafff7fcbfcdfdafe77f,0x14c08e03b017808c02e0,0x9b047820c0ee06b02f8,0x838c1ae0cb05f82cc14e,0xe12b08f844c20e0fb077,0xf85cc2ce15b0a7850c26,0x8e1bb0d7868c32e18b0b,0x7880c3ee1eb0ef874c3,0x4ae24b11f88cc44e21b1,0x14f8a4c50e27b137898c,0xc5ce2db1678b0c56e2ab,0xb1978c8c62e30b17f8bc,0xc6ee36b1af8d4c68e33,0xcb1df8ecc74e39b1c78e,0x4c80e3fb1f78f8c7ae3,0x45b227910c86e42b20f9,0x928c92e48b23f91cc8ce,0xe4eb26f934c98e4bb257,0xf94cca4e51b287940c9e,0xe57b2b7958caae54b29,0xe7970cb6e5ab2cf964cb,0xc2e60b2ff97ccbce5db2,0x32f994cc8e63b317988c,0xcd4e69b3479a0ccee66b],#[0xb3779b8cdae6cb35f9ac,0xce6e72b38f9c4ce0e6f,0x8b3bf9dccece75b3a79d,0xf4cf8e7bb3d79e8cf2e7,0x81b407a00cfee7eb3ef9,0xa18d0ae84b41fa0cd04e,0xe8ab44fa24d10e87b437,0xfa3cd1ce8db467a30d16,0x8e93b497a48d22e90b47,0xc7a60d2ee96b4afa54d2,0x3ae9cb4dfa6cd34e99b4,0x50fa84d40e9fb4f7a78d,0xd4cea5b527a90d46ea2b,0xb557aa8d52ea8b53fa9c,0xd5eeaeb56fab4d58eab,0x4b59faccd64eb1b587ac,0xe4d70eb7b5b7ad8d6aeb,0xbdb5e7af0d76ebab5cfa,0xb08d82ec0b5ffafcd7ce,0xec6b62fb14d88ec3b617,0xfb2cd94ec9b647b20d8e,0xecfb677b38d9aeccb65,0xa7b50da6ed2b68fb44da,0xb2ed8b6bfb5cdaced5b6,0x6efb74db8edbb6d7b68d,0xdc4ee1b707b80dbeedeb,0xb737b98dcaee4b71fb8c,0xdd6eeab74fba4dd0ee7,0xb77fbbcddceedb767bb,0xd4de8ef3b797bc8de2ef,0xf9b7c7be0deeef6b7afb,0xbf8dfaefcb7dfbecdf4e],#[0xf02b80fc04e00effb7f7,0xfc1ce0cf05b827c10e06,0x8f0bb857c28e12f08b83,0x87c40e1ef0eb86fc34e1,0x2af14b89fc4ce24f11b8,0x8cfc64e30f17b8b7c58e,0xe3cf1db8e7c70e36f1ab,0xb917c88e42f20b8ffc7c,0xe4ef26b92fc94e48f23,0xcb95fcace54f29b947ca,0xc4e60f2fb977cb8e5af2,0x35b9a7cd0e66f32b98fc,0xce8e72f38b9bfcdce6cf,0xf3eb9efcf4e78f3bb9d7,0xfd0ce84f41ba07d00e7e,0xf47ba37d18e8af44ba1,0x67d30e96f4aba4fd24e9,0xa2f50ba7fd3ce9cf4dba,0xaafd54ea8f53ba97d48e,0xeb4f59bac7d60eaef56b,0xbaf7d78ebaf5cbadfd6c,0xec6f62bb0fd84ec0f5f,0x8bb3fd9ceccf65bb27d9,0xb4ed8f6bbb57da8ed2f6,0x71bb87dc0edef6ebb6fd,0xdd8eeaf74bb9fdccee4f,0xf7abbcfde4ef0f77bbb7,0xfdfcefcf7dbbe7df0ef6,0x8f83bc17e08f02f80bbf,0x47e20f0ef86bc2fe14f0,0x1af8cbc5fe2cf14f89bc,0xc8fe44f20f8fbc77e38f],#[0xf2cf95bca7e50f26f92b,0xbcd7e68f32f98bcbfe5c,0xf3ef9ebcefe74f38f9b,0x903c2e8cf44fa1bd07e8,0x20903c20903c20903c20,0x3c20903c20903c20903c,0xc2a0f0c11640803c4090,0x541606120c08541e105,0x38200c051000a83c20c,0x400883c204c9420283c2,0x2018401e103c19283250,0x7250804110a04030a044,0x420103c28100c1e14080,0x1088325064a083e4a149,0x4420183d84103d84103c,0x80610042c140804440a8,0xc0a10082810080a110,0xc1e0b001600200501e1,0xa0403088502018442810,0xc10007042d640386110,0x898090430000000081c,0x90219041400201901010,0x1040c240800090418308,0x2022c1150200d24618a4,0x10041040009041000030,0x604211204201000c000c,0x100220888021014111,0x828100000600081c0c10,0x8216141030a010828088,0x808006040c0848221089,0x800704c880094b00081,0x1108200001038215040e],#[0x300]]
def g235H6 := limbs80 #[#[0xc10011090a100051,0x392690a80000000000,0x34d8707301800000000,0x0,0x0,0xd01c000d078,0x0,0x2c26106c00,0x343c,0x14940000,0x0,0xd42,0x2e0000000000043050d4,0x60ac0000000000d0a58,0x20e400,0xe080400000000000000,0xb0c4000d,0x14280000c9200,0x2093d49,0x106c00008250000,0x805481900000,0x2d4c0000000000000,0x208a21528020000000,0x90000000000024100000,0xf5220000000d034000a0,0x50000000384a455a0e,0x3,0x140600740,0x80000000000000,0x391d00000000000000,0x78000000182700000000,0x820f42174],#[0xe134000000,0x29850000000e02c,0x18240000002c3f20f40,0xf4bc0009140000000000,0x1c2f,0x0,0x0,0x837b0f80000000000000,0x1100000000000000f00f,0x390600001,0xd2ac0c800,0xd050000b528000,0xa4000000400024240000,0xc1a14,0x1811000,0x0,0x260b5235000000000000,0x71080000000000000341,0xe178000,0x0,0xc36000000000,0xd4a300e0000000000,0x352100000000000,0x183300000,0xe25c0000000000000000,0x50d0000,0x8d3000000000000000,0xa308000000000000,0x9e000000000000000000,0xd0300004081c2c403c,0xc07c000000000000000,0xc0580009000000002400],#[0x12f90000000000000000,0xe8000000000000000006,0x0,0x608c000000,0x170000000577c00a604c,0xd0000000000000060894,0x214]]
set_option maxRecDepth 16000 in
def g235D7 := limbs80 #[#[0x2ecb9840887e12108110,0xaf2ea102216e5d02044,0x835cb22a1084df735951,0x10ddac4a9021da549504,0x427ebb2a40867d65548,0x810cfacba90213fdd952,0x30436eb1aa6084fd76d4,0x4c109faeca98219f5955,0x530433eb2ea6084ff765,0x594109fee4b28213f5db,0x420443f8a8840884ff73,0x1c81109faec902217e5d,0x4720443f898e40885f57,0x52c8110fd26590221fc5,0x5d720442fcb9e40887e9,0x1514c110fe242982217e,0x654d30443ec99260887f,0xf9654c110bf2e898221f,0xfc48630442fcbaa60886,0x5f9748c110fe2a318221,0x17e5d6304437cb2c6088,0x87f22150110fe242a022,0x21fc94540443f8a8a808,0x886f96550110df6c4a02,0x221fc546404437db2a80,0x885f97490110df2c520,0x2217e5d6404437cb2c8,0xa0885dd73d0110beae3a,0xa82213f5d950442fbb8a,0xaa0887f25154110fe2a2,0x4a8221fcdc550443f838,0x12a08877b5254110ef2a],#[0xa6a8221bed89504437cb,0xb1aa08877b5354110ef2,0x6e6a8221bed8d504437c,0xdb22a0886f96454110bf,0xf2c5282217edd1504437,0xfcba4a0886f96494110d,0xbeae3a82217e5d650442,0x27ebb264885fb704c910,0x9faed192217d5c63244,0x42eeb9884885f9701091,0x10afcea212215f5d4424,0x442fab8c84884fd76109,0x9109faed21221ebd0a42,0x2442fab88a4885f97014,0x4910b7ae829221775cc5,0x524427ebb0a4885be741,0x549109faeca92217edc1,0xa52442fab8ca4884ff76,0xd49109faed29221dbd4,0xdb52442fab8ea4885f97,0x75589109fee6b12213f5,0x5d362442eeb9cc4884ff,0xd6354d109faebb12213f,0xf5d9534433eb2aa6886d,0xf970d4d109feeca9a213,0x9f597534436fb1ea6885,0x4fd72d8d109faeda9a21,0x177dcd654427ebaec688,0x84ff7059510df6e0b2a2,0x21b71cd654427fb92ca8,0x884ff7359510dbee6b2a,0x421fa54b208427eb96ca],#[0x1087d9534c210bf2eb90,0x84217e5d5308437cb2a6,0xa10877b5254210ef2a4a,0xa8421de54d508437cb12,0xaa1086f96354210ef6a6,0x8a8421be59150842fdb9,0x2283086fb7654210bf6e,0xc8a8c217edc1518435eb,0xb2aa3086be6454610d7a,0xac9a8c217e5c3518433e,0xeb2ea3086be64d4610d7,0xdac4a94217edc1528433,0x5f322a5086bd6454a10d,0x9faeca94219f59552843,0x2fcb86a5084ff7654a10,0xd7cc9a9421af5935284,0x427ebb6a50867d65d4a1,0x10d7ac8a9c21b758d538,0x8433eb2aa7086be6454e,0xe109feeca9c213f5d953,0x38435eb26a7085f970d4,0x4e10cfacba9c21af9935,0x548435eb22a9084fd76d,0xd52109feecaa4213f5d9,0xb548435eb26a9085f970,0x359210d7ae2b24213f5d,0xd5648435ebaac9086bd7,0x73596109fee4b2c21af9,0x585510827fba2cb084ff,0xe6354420dbac6a8841bd,0xf5d9510833eb2aa2106d,0xf561d44209feeca88413],#[0xb798f510836eb1ea2106,0x4fd76d4420cfacba8841,0x1bdd4d610837aa9ac210,0x6f67558420deaeab084,0x41bdd4e610837aa9cc21,0x106dd6354c20bf6e0a98,0x841af991530835eb22a6,0x6104fd7654c20cfacaa9,0x9841b758f530827fbb2a,0xa6106be64d4c20d7ac9a,0xb18413f5db530833eb2e,0xac6106dd7558c20dbae8,0x6b28413fdc5650836f3a,0x8aca1067d71594209fee,0xe6b28419f5cd650833fb,0xb92a09076d5254120cfe,0x6c2a82413f5d950482f7,0x5292a0907e95254120df,0xd0e4a8241ded4950483f,0xbca9aa0907eb7254120f,0xdf6c6a8241ded4d50483,0x2fdba2a0906fb6454120,0xbdae5a82417e5d65048,0x82fcb80a2904fd768c52,0x209faec28a41775cc514,0x483bba8ca2904ff76545,0x520bf2e1a8a413f5da51,0x34827ebaec2904fd76d4,0x4d20bf2e1a9a413fdd95,0x634827ebb6a6905ed72d,0x595209faebb1a413f5c7,0x5654827fb82ca906fb70],#[0x1d95209fee6b2a413fdc,0x49508837cb0aa1104fd7,0x5354220ef6a4a8441de5,0x58d50883bda9aa110779,0xb7454220df2c8a8441be,0xd585518837dbb2a1105f,0xff76546209faeca8c41b,0x3f5db51882fcb86a3104,0x67d6554a20bf6e0a9441,0x19f59752882fcb86a510,0x67d6554e20dbac6a9c4,0x413fdd9538827ebb2a71,0x1067d65d4e20bf2e1a9c,0x4417bdc9548827ebb6a7,0x9104fd7655220d7ac8aa,0xa4417e5c3548827fbb2a,0xcb104ff71596209faeda,0xb08a13fdd1658827fb9a,0xac4286f57458450deae4,0x128aa17edc15154376b8,0x8c2a86f76194550bf2e,0xe6b0aa1771cd615437ab,0xb94c2a86f76198550bbe,0xae5b0aa17b9ca61542f6,0xfa9ec2a867d53d85509f,0xfae9b0aa13f5cf615433,0xbc382a4a85fb70549509,0xbf2e1292a1dedc152543,0x2bebaca4a86ef6294950,0xbeae2312a15f5cf5254,0x4376b10c4a85f6711895,0x50bbce6312a1775cc625],#[0x542df3a0c4a85bd74189,0x9509fae3b12a1bbd8a62,0x1d427eba6c4a84fd73d8,0x87509fee6b0ea13fdc96,0x62d427fb8ac5a84ff745,0x481109fee8b16a13fdcd,0x920443faa8a40887f950,0xc8110ff2a190221fb54,0x4b20443faa8e40887fb5,0x53c8110bfaeb90221fb5,0x59720443fda9e40887f9,0x9424c110ff4cb90221fe,0xe55130443fca9260887f,0xf9548c110ff2a518221f,0xfed4140443fca8280887,0x7f95150110feaa2a0221,0x1fe4c940443fda8a8088,0x87fb5250110ff2a4a022,0x21fe99540443fcb2a808,0x887fb5290110ff2a5202,0x221fed5240443fcaa480,0x887f551d0110ff2a1a0,0x82217f5d740443deaa68,0xa0885ff7254110efaa4a,0xa82217fdd1504437eb22,0x2a0887fa3254110ff264,0x4a8221fe50950443fc21,0x92a0887fb4254110ff48,0xc4a8221fe94950443fca,0x392a0887fa6254110ff2,0x4e4a8221fe5c950443fc,0xca1aa0887fb7254110ff],#[0xf2a8a8221fed0d50443f,0xfcb22a0887fa5454110f,0xff0e8a8221fe99150443,0x3fd3a2a0887f97454110,0xff2a528221fedd15044,0x43bea96a0887f9549411,0x10bfae9a82217f5cb504,0x443f6a9464886fd644c9,0x910fdaa4a12217f5d442,0x24437fb2a84886ff6350,0x4910bfaeb21221fb54a4,0x52443fdb82a4887f8705,0x54910fdcc4a9221fb589,0x652443bfaa2a48877d54,0x558910bfae9a92217f5d,0xd662442ffbaac4886fd6,0x7259510bfae5a9a217f5,0x55130842feb94ca885ff,0x55150610ff282a8421fe,0xf58951843deaa283087f,0x7d54d4610efaa8a8c21b,0x7f5d353842feba6a3087,0x7f93154120dfac8a9841,0x1fe50550483fd18aa090,0x7f95154120ff482a824,0x41fe54650483fd28aa09,0x907f5518c520bfae3a82,0xa41bfd8551482febac62,0x29077f5354520efaa6a8,0x9a41bfd8751482febaca,0xca905ff7159520bfae3a,0xa8c41df55151882feb8c],#[0x2c3106fd5258620efea8,0x8a9c417f5c7528837eaa,0x8ea9106fd5458e20dfac,0xc4a8aa1df54951542feb,0xba4a2a877d5294550dfe,0xee8b0aa1bfd9161542fe,0xeb8ca4a85fd7498550bf,0xfae3312a17fdc562542f,0x7ebb2a4086fd6554810b,0xdfaeca9821bf59553043,0x37eb9aca086fd7259410,0xbfaea90221bf5952044,0x43fda9260886fd65c811,0x10ff6a518221fed51304,0x4437eb2a80887fb548c1,0x110ff2c4a0221fe5c540,0x443faa8aa0886fd65d0,0x4110dfac4a8221dfd495,0x50443fcb8aa0886fd655,0x54110ff2a6a8221fedc5,0xb50443fdb9aa0887f973,0x54c910dfac9a8221bf58,0xd6324437eb2c64886fd6,0x6510910dfaca212217f5,0x58d42442febb084886ff,0xd7550910dfacaa1221bf,0xf59642442febb284885f,0xfd7690910dfecb21221b,0x7fdc152442febb0a4885,0x7f67154910feae2a9221,0x1bfd8952442ffb8aa488,0x86ff6354910dfac6a922],#[0x21bf59152442ffb9aa48,0x885ff7454910dfec8a92,0x221bfd95524437eb2aa4,0x4885fd7654910dfaeca9,0x92217fdd9524437f3b2a,0xa4886fd6594910fdac52,0xa92217f5da524437fb2c,0x6a4885fd71d4910bfae1,0x7a9221bf58f524437fb1,0x26a4885fd73d4910dfec,0xeda9221bfd93524437eb,0xba2c4886fd6458910bfa,0xae6b1221bf99562442ff,0xe3aac4886ff7358910df,0xfceab1221bf5d5624437,0x7eb2cc4886ff7558910d,0xbfee4a9a21fe5c153443,0x37ebb2a6886fd6554d10,0xfbee6b2a21fedc16544,0x437e392ca886ff705951,0x10dfce4b2a21bf5c9654,0x4437eb9aca886ff72595,0x210ff6a898421bfdcd65,0x843fcb8aa1087f95154,0x4210ff2e4a8421fe5495,0x50843fcb9aa1087f9535,0x50610ff2e8a8421fe551,0x951842febaa83086fd65,0x454610efea8a8c217fdc,0x9551842ffba2a3086fd6,0x72d4610dfac5a8c21bf5,0xd49618437eb26a3085fd],#[0xf7154a10ff6e0a9421bf,0xf5d9528437eb2aa5085f,0xf97054e10bfae3a9421b,0x7fdd1538437eb22a7087,0x6fd7654e10dfacaa9c21,0x1bf551638437eb26a708,0x87f97055210dfea8b1c2,0x217fdcd54842ffb8aa90,0x86fd7655210dfacaaa4,0xc217f5cf54842feb8ea9,0xb086fd7259610dfae2b2,0x8841bf5d1658437eb9ac,0xa6106fd7654420dfacaa,0xa98417fdd153083fdb82,0x6a6106fd7654c20dfaca,0x2b28417f5d3530837eb2,0x8aa0906fd7359420dfae,0xcaa8241fb54950482ffb,0x30aa0907f96154120dfa,0x2e2a8241fe1c550483fd,0xdb8aa0907fa7154120ff,0xf6e4a8241fe5c950483f,0xfcb9aa0907f95354120f,0xff2a8a8241fedcd50483,0x3fdba2a0907f97454120,0xdfacb18a41bf5953148,0x82ffb82a2905fd761452,0x20fecc2a8a41fd585514,0x482ffb9aa2906ff63545,0x520dfecaa8a41bf59551,0x1482febb2a2906fd7654,0x4520bfeeca8a41bf9d95],#[0x514837eb2ca2907f5619,0xd4520bfaed28a41bfd96,0xf51483bea9ea2905fd70,0x6d4520bfae7a8a41bfd8,0x95614837eb2ac2905fd7,0x6598520bfeeab0a41bf9,0xdc553482febacc2906fd,0xf7454d20fdae4a9a417f,0xf5d9534837eb2aa6905f,0xfb7059520bfae9a9a41b,0xbf1c5654837fb82ca907,0x6fe7159520dfae2b2a41,0x1bf5cd654837fb8aca90,0x7f95154220dfee6b2a4,0x41fe54950883fcb8aa11,0x107f95354220ff2e4a84,0x441fe55150883fcb9aa1,0x3105ff7254620ff2e8a8,0x8c417fdd1518837eb22a,0xa3106fd7654620dfacaa,0xa8c417f5cb518837eb16,0x6a3106fd64d4620efaa9,0x8b0c41bfd4961882feba,0x2aa5105ff7154a20dfea,0xcaa9c417fdd1538837eb,0xb26a7106fd7654e20dfa,0xea8b1c417f5d3538837e,0xfb8aa9107f97055220df,0xfee6aa441fbdc954882f,0x7ebb2a9106fd6555220b,0xdfae2b2c417f5cf54883,0x37eb9acb106fd7259620],#[0xbfee0a8aa1bf5d16588,0x43bea9aa2a85ff725455,0x50dfec528aa1bfd8d515,0x5437fb24a2a85fd72945,0x550dfac430aa1df54861,0x15437eb20c2a85fd7218,0x8550ff6e0b0aa17f5d06,0x61543bfa92c2a877d525,0x58550dfac4b0aa1bf189,0x9615437fb12c2a86fe62,0x358550efaa6b0aa17fdc,0x8d615437eb1ac2a877f5,0x7358550fb8e6b0aa1bfd,0x59161542ffb9ac2a87df,0xd5298550dfcc8b0aa1bf,0xf58a61543bfa94c2a877,0xfd7298550dfec530aa1b,0xdf54b615437fb24c2a85,0x6fe62d8550dfac5b0aa1,0x1df54f61542feb96c2a8,0x85fd73d8550dfac7b0aa,0xa1bf54b61542feba6c2a,0xa86fd72d8550dfca5b0a,0xaa1bf54f615437f396c2,0x2a86fd74d8550dfae7b0,0x92a17fdc1525437f3a6c,0xa4a877d7054950dfec6a,0xa92a1df58d52543bfb82,0x6a4a877c7654950efec6,0x2312a1df58f52543beb1,0x1ac4a87fb7058950bfae,0xe6b12a1bfd8d625437eb],#[0xb8ec4a85ff7458950bfe,0xae9b12a17f5cf62542fe,0xf38ec4a86fd71d8950bf,0xfae9b12a1bf5cf625437,0x7eb92c3a86fd7058750d,0xdfae6b0ea1bf9c961d43,0x37f3a2c3a86fd7458750,0xdfae2b16a1bf5c162d4,0x437eb9ac5a86fe7158b5,0x801600160001bf5d162d,0xe0032804a006e00b0010,0x1a60300056809e011601,0x811a0216040007880e20,0xe00b2815a029604f0094,0x38e06e00d28192030e05,0x8222041e07f00f481da0,0xf0134825a04960900116,0x5860ae01528292050e09,0x830e06060bc017282d60,0xa01ac834a06760cc0190,0x7a60ef01d0838a06f60d,0x8432083e10301f883e20,0x2023c846a08be1140220,0x9be134026084ae093612,0x853a0a4e145028084ea0,0xb02cc85860ae615802a6,0xc0e17d02f085ce0b7e16,0x86660ca61900316861a0,0x2035a86a20d261a1033c,0xe6e1c8038686f20db61b,0x877e0ee61da03ac874a0,0xb03e887be0f661e803c6],#[0x7620a040e88120ffe1f,0x888e10fe21b043288561,0xb046c88ca117e22c0450,0x27624b048e890a11f623,0x898e12f625b04ae894a1,0xc04ee89ce137e26c04ce,0x47628a050c8a0a13fe27,0x8a9214fe29b052c8a4a1,0xd05708ad215862ad0552,0x6962cf05948b16160e2b,0x8ba617262e005b88b5e1,0x506008bee17b62f305dc,0x8e631806268c3a184e30,0x8cc6196e329064a8c861,0x9068a8d0219e6339066a,0xaee35a06ac8d461a6634,0x8dce1b7636a06ce8d8a1,0x7168e1a1c0e37d06f0,0xd3e3a3073c8e661ca639,0x8ef21dc63b507608eb21,0x707a68f361e4e3c60782,0xf663ea07cc8f861ee63d,0x8ff61fde3f807e88fc21,0x60824903a20564070804,0x15e4250842907620ce41,0x910a21de438086890be2,0xc08b09146226644a088c,0x38e46d08d2919222fe45,0x920e23fe47d08f291d62,0xe09349256248e48d0910,0x58e4ae0954929a251649,0x931e26164bf097692da2],#[0xe09b2935a268e4cd0992,0x79e4f009d8939e27164d,0x9416281650009f693de2,0xf0a309452287e50d0a14,0x99e52f0a529492290e51,0x952a2a265410a7a94e62,0x40ac0956e2abe5540a9e,0xbe65780ae295b62b4656,0x96522c7e58b0b0c96062,0xc0b5096922d0659e0b32,0xdde5b80b6896c22d765a,0x97322e3e5c50b8496fe2,0xf0bb897662eb65d40ba0,0xf965ef0bd697962f165d,0x981630065fd0bf297da2,0x90c2a984a307e60c0c12,0x16e6290c48988230e661,0x991231fe63b0c6c98ca3,0xe0cb49956328664d0c90,0x36e66a0cce9992330e65,0x9a0633f667a0cea99ca3,0x50d229a3a345e6880d08,0x52e6a20d3e9a6a34be69,0x9ad235866ad0d549aa23,0x60d849afa35e66ba0d70,0x6b66d40da09b36364e6c,0x9b8a37066de0db69b663,0x30dde9bb2374e6e80dca,0x7f66fd0df69be237ae6f,0x9c2a383e7060e069c063,0xd0e349c5a389e7120e1c,0x95e7280e4c9c8a38fe71],#[0x9cf239ce7360e669cbe3,0x20e9c9d2e3a467450e80,0xaf675e0eb69d5e3aa675,0x9d8a3b0e7610ec09d7e3,0x70ecc9d963b267640ec6,0xb5676a0ed29da23b3e76,0x9dba3b6e76d0ed89dae3,0x30ee49dc63b867700ede,0xbb67760eea9dd23b9e77,0x9dea3bce7790ef09dde3,0xf0efc9df63be677c0ef6,0xc167820f029e023bfe77,0x9e1a3c2e7850f089e0e3,0xb0f149e263c467880f0e,0xc7678e0f1a9e323c5e78,0x9e4a3c8e7910f209e3e3,0x70f2c9e563ca67940f26,0xcd679a0f329e623cbe79,0x9e7a3cee79d0f389e6e3,0x30f449e863d067a00f3e,0xd367a60f4a9e923d1e7a,0x9eaa3d4e7a90f509e9e3,0xf0f5c9eb63d667ac0f56,0xd967b20f629ec23d7e7a,0x9eda3dae7b50f689ece3,0xb0f749ee63dc67b80f6e,0xdf67be0f7a9ef23dde7b,0x9f0a3e0e7c10f809efe3,0x70f8c9f163e267c40f86,0xe567ca0f929f223e3e7c,0x9f3a3e6e7cd0f989f2e3,0x30fa49f463e867d00f9e],#[0xeb67d60faa9f523e9e7d,0x9f6a3ece7d90fb09f5e3,0xf0fbc9f763ee67dc0fb6,0xf167e20fc29f823efe7d,0x9f9a3f2e7e50fc89f8e3,0xb0fd49fa63f467e80fce,0xf767ee0fda9fb23f5e7e,0x9fca3f8e7f10fe09fbe3,0x70fec9fd63fa67f40fe6,0xfd67fa0ff29fe23fbe7f,0x9ffa3fee7fd0ff89fee3,0x31004a00640068000ffe,0x36806100aa012401e80,0xa02a404e8091010a01e4,0xf101ca036406680c1016,0x968121022a042407e80,0xa05a40ae8151028a04e4,0xb1034a06640c6818102e,0xf681e103aa07240de81,0xa08a410e8211040a07e4,0x7104ca09641268241046,0x15682a1052a0a2413e82,0xa0ba416e82d1058a0ae4,0x31064a0c64186830105e,0x1b6836106aa0d2419e83,0xa0ea41ce8391070a0de4,0xf107ca0f641e683c1076,0x2168421082a10241fe83,0xa11a422e8451088a10e4,0xb1094a1264246848108e,0x27684e109aa132425e84,0xa14a428e85110a0a13e4],#[0x120f0a15642a685410a6,0x8608483c20f1208483c2,0x5051110184050443c4a5,0x41111014410444402002,0x41110c5104404441410,0x25104111104095044441,0x4c4031413100c144c403,0x3100c944c40313100850,0x1013140c420444504251,0x143c444120f0854483c3,0x61210483c208110f0c20,0x6120e021848a8415010,0x48006120e0218a848480,0xc415a2640f102190403c,0x884c3c4170f084c44403,0x10f0c5c883c3150f082c,0xc2110f085689903c4081,0xc48444140b220f10503,0xf0c56882c184110f081b,0x1543040610443c20b120,0x3c44315a2240f102c3c2,0x20f0c50103c3110f0848,0x86c513111030443c3a42,0x6151404020f1490503c3,0xa2250f14040192881894,0x66406140d90503c36400,0x14112510941488581844,0x314220f0c2018141c406,0xc143c214250f0c5c943c,0x6051050883c314a50f0,0x28006119000503c40c0b,0x4205110f0c143c443642],#[0x943c4140b22250f143c4,0x4103c411c52a0f105490,0x143c444c5080f1110401,0x42090404c50824101020,0x4949040416082410131,0x1020444030508241013,0x1010201444404c508241,0x51010204494404011125,0x241013044494404c1112,0x3011110204494404c125,0x44030403160c100c222c,0x1444404c111251010204,0x80054945140111251020,0x3c415140402032518928,0x4080403070614401410,0x83c305110f0c5846184,0x4020f0c943c2050f0810,0x1422250f1010083c5c40,0x83c61514250f111a942,0xc41005040f1054509410,0x1018542a586099410083,0x45018100c08604020f15,0x4020f103c10e0a0f0c5,0x3140811101010083c3a5,0xc403c217100f0c402044,0x100c58504440414100f0,0x7140f101050444031114,0x3c30f14100c3c504031,0x45044309c1141110885,0xf0e9430443c40015140c,0xf120c2e96883c422150,0x944220f140c54503c3a5],#[0xc503c2a50f120c2e883e,0x10111014404431101100,0x41411100e9440483a581,0x4011116101050044440,0x4838110a511100444405,0xc94444032511100e9440,0xf102e94403c405100f0,0x4100f1050403c3a51044,0x100f140c105c403c4140,0x310a5440f102c42943c4,0x44440410140f1040943c,0x604441403011110168e0,0xe06944440114110c0c04,0x3194443c403011411128,0x1958d04444650b100f10,0x10044044504634111651,0xf0c0c04445040410140f,0x4043121294483c305120,0x3c314120f0c50483c3a5,0x294483c3a5120f0e9448,0xf0c50483c34043a5121,0x2650f119592083c41412,0xc465120f0d94483c3648,0x828280651311960a004,0xe95083c405a4420f103f,0x5291083c4a544420f102,0x11085c3c41404420f10,0x102d0a943c4a442a50f1,0xf129108503c44442a50f,0xf11942e083c40442140,0x20f0d9209943c4656482,0x14120f0c1208503c4141],#[0x3c41464820f1050483c3,0x4504032511100d920850,0x50444031614011110144,0x4494404110200102514,0x8005040314112510100,0x31425100c5c944030714,0x104411114100c504440,0xf0c5844944041411251,0x312250f0c48943c30512,0x8943c30403150c48943c,0x2518085094305120f0c4,0x71004444031614040301,0x25100c50944030401101,0xf110c585094100440616,0x84041610080444403050,0x31614070403011804445,0x8503c40111100c100440,0x405044316141110102e0,0xc3c5040317140f1010,0x314110818504430f141,0x83c4c205a40f1024585,0x8503c30402150f105010,0x130c584430402140f100,0x4110c405044316141011,0xc414100f0c14403c3101,0x403040f1710105010403,0x40503c410250f0c3c50,0x301111016844438b041,0x4441411080c046044414,0x3c404020f14100c0450,0x443c3030111141010405,0x50e14443c311850f0e14],#[0x140f08530a143c414401,0x143c20ec50f1010543c2,0xf110c3023143c4140f0b,0xf0858501c100c046c50,0x5051404020f10503c214,0x514c3401610600c082c,0x4030540160c581450444,0x14444051411100c5044,0x44504041714051010585,0x105990403c5110f0c20,0x14101314443c30811141,0x411100c2090504040811,0x11010545018100c0861,0x3001510500c044441404,0x20015101008543c4040,0x401101610100c0058403,0xc1830607080c04445840,0x894881830722060e881,0x1830280060c1812206,0xa0a0504a838106220c5a,0x50424481110818882062,0x889040030981410c8a0,0x2c1820b06082c182410b,0xa4a12142c182150b060c,0x2206110c8818443130f2,0x8a0418324060854903c3,0x60c6204901840781060c,0x8225240f0c943c224810,0x60d081a003180608101,0x40580060c32001434214,0xc42581062210960418a8,0x188840681110c948a043],#[0x88894406228164109604,0x1c94201840625220c581,0x1109488503c422250f0c,0x140e14890431685074,0xc60182640f0a0418222,0x50f08302c94184062564,0x180b8541101a14959042,0xc581888341140a143c2,0x183160609081820b1806,0x6061058882800a08602c,0x820d23060c4844208071,0x4106220c581822204341,0x81810807060d0400883,0x441831622060c4811211,0x508201c9430f25220c60,0x888214220a0c58183162,0x8301450c080030209045,0x86000218051204207150,0x820782085c242c318000,0xc94215044410782081e0,0xc541c201041c54215041,0x4281050e048430721050,0x21081c5422105070c1c5,0xe0414481210c8454205,0x100150c602c183164206,0xc005420942180c5c2c22,0x800c2089005044022800,0x849030c4008302c24022,0x622210c182020c240854,0x842021]]
set_option maxRecDepth 16000 in
def g235H7 := limbs80 #[#[0x461030d80071800401c9,0x111208408005eb090810,0x8900b3400c310019710,0x400010820800c000d003,0xc00800071c60060010,0x163d010680a1010400c,0x403411800450401c6111,0x100a3070028c00400000,0xc000100230304108418,0x80022c002004b0c7080,0x2500031440c00140810,0x992850434410c02084c,0xc70c2085113029000080,0xad804470840123000516,0xc01c21c300004b0c048,0x830400000c21101852c0,0xb08135a9010522743c40,0x14514d2c530537f20,0x12820052c4103140014,0x2d5047a525430cb1043,0x1800010051011c104700,0xc48012001021806c049f,0x14811450800c01820400,0x1c40808410c70c578280,0xd2c01102c7006041b68,0x714fb842820232c05c36,0x24c1400c91531141c324,0xe20800940491d61410d3,0x67033840000040070408,0xd3350084320,0x28342,0x80abc00000000000],#[0x343a100000000072400,0x529f00000000,0x10ab0000000000c5e70,0x0,0x0,0xf403a6e2c1000000000,0x303300000a3d240000c9,0xe35426784b4042600000,0xde484900351805b6d2,0xa3400d50507808900002,0x1dc0000b0c794a2b824,0x780ba5c210f097e412e8,0x8e428f00000a345ed20,0xfc218c163e491940a53c,0x915580000209d,0x67bc0000b76b4458500,0x101fb0718f9164,0x13362c14be0a7000,0x606a4000000000,0x973019930ce548c4000,0x7000005b00000000000c,0xe0e47031,0x800000049e90a2000000,0x928ca1b412c4e04720bd,0x103c0d36000003425d32,0xa3c03c27017803a9,0x8a4d1038ac1f38079c00,0xb680be90df4816000001,0x4c680000505760d99608,0xa20eb6838e50d2740526,0x21600000000022351832,0x6193c90d588a27000018],#[0x40942a0f16584d842220,0x922c808d30000385fbd1,0x3b00003c13c0000380b2,0xe0bd10ab80000c22ab83,0x2e032e0000282d827153,0x7090c00e8f31,0x242f70000000000,0x3b310c3c000000000000,0xc0000e05080000072238,0x900000b00f40000306a,0x80,0x82fe000000000,0x484e00ec40000b036c00,0x906c48270b0803,0x828bd08aa09f99082000,0xc000000f4e0000282420,0xc537078d0202809aac92,0xe04c5612f0000087706d,0x90000009424d4336c012,0x4bd8000000002503ed2,0xf017c0000000000000,0x99a1000004d1ea136000,0x2ac2d3d08fc000000002,0x14bcc13d60c240000f00,0x80018b01c10000000006,0xb9000001c56000038a2,0x1418c104e80000000030,0x1bb81fdc044543080000,0x141ff498ce096283ae10,0xceb0e71c26b10b564854,0x421a5068383032236840,0xff91c51008f422af03da],#[0x66c52c7501680000320,0xa4017343c554206c065d,0x81505fd5709d0287804,0x48b80000000034,0xd015644ea0000,0xf0a43854460744000000,0xf9000038323000000000,0x444a7168a03018095882,0x3f88a9192cc428600000,0x53000002623d8182b08,0x341b20000342c37,0xbb98091c0de4000,0x2c27d088b904b3710340,0x520c0a38072f4846d0bf,0xb034fc020a03b80000c0,0x7043381802a50b11410c,0x8fb404e42cd00001c3,0x282ccc2274000000001,0x3d07c000,0xb000000000f068c00000,0x1efa3398000000002811,0x3e,0x3d00440ed800000000,0x280ebe050d105000,0x61da7751c0000,0x0,0x95c897c8292c444e09c8,0xcf50886204ec0000b0e,0x2027cb0dced4b15,0x4fd007828314801a4000,0xb09fc000000003c,0xe8a42570000000000000],#[0x2030ad08ca020630,0x34d074fc810806204191,0x42b7a7246416b0000140,0xab41593044a855f94e7f,0xd22d9a5402b40000d01,0x5b22e388e95082b41cd5,0x81d65057fc5f,0x304f983ab000000,0x1001f0000,0x0,0x309b000000000348a3,0x22700000c306513d000,0x2c29a88be6410b90241,0x248f0118107c21dab000,0x136200000000000d832,0x98740493dc57e06a8000,0x792ed90d43d2ea90d8f8,0x46c0000823dfdda0b84b,0x4030f055491435c94683,0x6b00003557c842f80983,0x840b00000000062d73d8,0xddc03a000038278e024a,0xef6008c971624353105,0xc4079a88d50000141fff,0x404bc000040a7801c,0x15037000000000000000,0x39f84d0667edc35a0000,0x721e00000d0,0xf71540000600200000,0xa295800,0x498d00003434400000,0xbe1d2eca03778157000],#[0x26750c059d103040000f,0xc640000000029d4,0x284db000000000000000,0xef8000010bee41de0000,0xf000252e240570000080,0xcea06e9c4d434745831f,0x422990135080c6077003,0x40af705d00000208e2,0x505f40000000,0x3c1620c28200f4d81580,0x548721d982b040dfac0f,0x38322404724b39d0e366,0x4a342f5355f74332e0ee,0x2c220a0c440a5410,0x5f0091dc00201400993b,0xdc640000201a500c390d,0xce8164165ec000022690,0xac981c9000000000677,0xe,0x408e8000000000000,0x40000441980000000000,0xbcac2650089b0117323f,0x90cc4000062215804730,0xe940326c33f5096c0000,0xc11f0000000000000141,0x3e42dc046402958219d,0x3552c12530602d35b000,0x2c01e6,0x502d341df00000000,0x80e000000a0d380,0x2874d1f60e7c40f90000,0x2094c0000e52df400e04],#[0x80c7402bc000000000,0xd317000000000d009400,0x28036106280000a07fb,0x63c08e440ea18371000,0x440d1e410d00003c1fc2,0x8709c4079d0db9909,0x110476041c0000000000,0x8326a0d9c00000000,0x80a9cc0eaa31270a4200,0x7514b9f002f508398099,0x8a00d22a3188600000c2,0x61c1e273463c40e10396,0x55d485f6000000000803,0xe1105804ea05e9c8e66,0x22340000,0x5c12cb453fddb32466c0,0x9d382bd41329434bc419,0x60074000000003183900,0x2600002c137108b800f5,0x82b1c17de803ee25e221,0xd41af583f4401a10dfd,0xe4800004211cc16fb0f,0x181a4d086fc1d84,0xe23ea9c6700000000,0x505ca214642590053c0,0xad000c40000382500000,0x409200000000038d1a30,0x3042a25af000000000,0x806350f400000e30f400,0x18815428e348d8c74ff,0xc00000083138ca23000,0xc0676001c00b0341853],#[0x86830938403b00000c91,0x1425c0000000000,0x4283c13cc00008770,0x1438300,0xd9000011102982740000,0x283aa5215b01,0xa0904,0xd048c0000000,0xc33b381c80000000000,0x5795770903c700000000,0x7d619019980000000032,0x107e,0x1427b062ac000000,0xe5000028a45c0e328269,0x284801600000302d6c5,0xe00dc000000000,0x55d88073e0b3dc942000,0x1092fa,0x296a014400008276a41b,0x80000000000000000008,0x380cbd02000000204d,0x143b470a6d01d700,0x51d0956c28b921240000,0x40bc80283c0384312982,0x4e91d8e0a89422ba08bd,0xa840000d4020835dd28,0x40000340600000141e53,0x21260b6d02e810f2bc13,0xb850500002112190c718,0xc84ca2e703de0cdf84c1,0x60f240000a0a9a4461f0,0x17113490a55000030d44],#[0x7139800350000342,0x1b400900002c36800000,0x7c9491b000000000007,0x2107bbd06b903c40000e,0xd074980b080cc2410,0x80280d12dc48dc645980,0x26312fd90648983fe0c4,0x70f040000804d4400760,0x94a0d33429290bce40a8,0x402a801,0x86cda2d751782ab1339c,0x23cc0000e0b0a450a901,0x348e250b440000c,0x37c0000360bec0700000,0x42d4804400000000038,0x2b40000c0584c1db903b,0xe0349892411,0x5560c4c0000d0056407d,0xc357923fc00000000188,0xc0a2b811420c69,0x24b80000000000000000,0x22dc00003c0224,0xa3a4b840000f08ec000,0x242f400003c17200003a,0xaa5c850f0626c24cd918,0x1015ba01fe61db50,0x10169a4737c508,0x83b050f35c8423066800,0x1c2c1b04c000e100002,0x2c2d0000,0x4503b400002202c00000,0x43c],#[0x0,0xe3c00000000000000000,0xe0b8443ba43474000060,0xe087fc0c2000038230,0x358b04a40000a0f3000,0x905a211dbc0a5c,0x21c8ff33ac0000000,0x100000254a60d48d1cf0,0xd08cd0a3d30e61ddb,0xcd5810000380b1000000,0x804800000000040ef,0x4055653a000002c2da00,0xc9f0aed00e47054ac2ef,0x12e9c0d0102996261804,0x41260021c000000000,0x9a00000000,0x80d70000000000,0x23d9063bc03010e14000,0x9d00001dd40000000,0x6e400000040000000000,0x4081c000040415402170,0xa700000009a212d9c018,0xa152010482493082783,0xc342eb00003419f00003,0x458c0341e02900000c47,0xaa0c32894970871c0f8b,0x141d8000000002120,0x440d054c4c4c4d814180,0x3fb84cfd0458cc4ff023,0xc76a402354069a8005a2,0xf000024346e031e0279,0x2165000010298f0c8285],#[0x9e61f800a1c0000d06b6,0x28fc41b500000c410f01,0x802ccc8e00000000002,0x196a0a24038763378144,0xd06ec000000001c,0x102110000,0xa9c723d1014d00,0x40254e1f940d518a3e,0xc0270000212080000000,0x5a421477165d1a700002,0x3212e08c2947,0x7f0823c334340e0c0040,0x30500003e2f8105d9050,0x8000000000c0d6000008,0x5841f13010f8ced7009,0x401bf88dfc0,0xc0a380000e25f5d104,0x1830dc161800,0x5287442fd40a34,0x281fa00000c263000,0x95827e1daa801ef834a0,0x1834310e2d654,0x200a680d780,0xc813620000000000000,0x608a34a4b00003a03d34,0xa760e651084f06104324,0xd4bbe290580ba00003c9,0x1280ab6140e816c4111a,0x27f82e45013de1fb90e,0x6033a6c2a8b42f400002,0x3c00002d2eb665464a2,0x3437a5082c00004239e6],#[0x12a4147b08924cd55099,0x2294d52e64133b836252,0xca0000105820000151d7,0xc2d900002038ad249c40,0xc60df500000012bb409e,0x1ed70db48397804,0x40e1a419890dbc00000,0x2ea00000000000000000,0x1c262541f8d2de000028,0x3021900000005b0000,0x1d05100000000000,0x7a000000000c0f024591,0x704e00912805aa42,0x425251356489970ca0,0x1407eb003c818b000,0xc92df597000000,0x4080c000,0x380726110d531b000000,0x44129c00000c396006a,0x30afc00004102a44df40,0xae5064c0000562164032,0x8e810ad9437400002c0,0x50000000000000063387,0x301da841a74254705,0xe0000388cc6428cc8dd0,0x1ddc379c000000002c17,0x4006b03004260000024,0x406d3214d802b0000,0x60e8c00000000344b000,0x80d9d012480b6,0xf03fad031a0d7c00,0x39007e76ec],#[0xf4ac02e000,0xf000000000a088400000,0x2ed534640000f14e6d4a,0x2c5e3000010355000010,0x3844ba0def00c60000,0x90d90c998f1427808800,0x5e30ee6c1a2f0d64c0e0,0x70ef388a4d025b41,0x70000000001c304644f4,0x54241f800003888df8a,0x4333000020291f,0x0,0xa0de00,0x5454042c0cdc00000000,0xb0b58000000001ca4960,0x1448b833e6144200fa,0x913900000e01d800,0xb800008097811e6b52c0,0xc8f20000344de506,0x2c0b7e16ac00001dd410,0x808f8000000001401,0x22933421e800500,0x300c500002c1cea76f,0x810a8000000000000000,0xd9000000000000000000,0x9daf000034186c28a9c8,0x5c000070ca7d99f90501,0x3ee83c6a0514000030b,0x60000083810089781708,0x10a5200000c37,0x141bc3118ac31bd03700,0xa90000000000000080e4],#[0x2916900001c06440,0x105e15d3a4134c0000,0x404865db64046800,0x2508b12114,0x55dc0000000000000000,0x33099c00000000342f0c,0xcee1024e019500001818,0xc088f92e8224320,0xd139400004027,0x300a4000000003c24400,0x9340cb3ca43e0f464071,0x5409b41b541f74037ec3,0x280f4083010382074f2,0x294092620e510cef000,0xb407bc82a550b2612dd4,0x26620b1c00004893141e,0xb4187d0a7e886352d7f0,0xbfd0205000018044d0b2,0x70900cdf402322d40aa0,0x6e020f700d4c0b228113,0xc979b08d9c88800001c2,0xa882e57091704f040ae3,0x20103b29419a1a90d,0x1d00500000907d0,0x1bd00489007018294000,0x3c840e0b19026d733d24,0xdad807c00b7b03180000,0xd13b4c11d2768580bf30,0x25206b221c0000,0x904fe4104209d800,0x140000b459582c5002dc,0x8f1021da0425021580a],#[0xae0100c05d40e7941711,0x37710c2ec3a4f0d9ac33,0x542ade5c0681b300ebc0,0x8eec288c01308086e016,0xb04c902ddc0607c4c742,0x4ff04a848fb60d94c083,0x91ceb0e54034ff3bdf02,0x6482e632862119ea0e6a,0xf2f4d15b6857c190300,0x4f015340eff0634c2cb4,0x2e770db3d15ae0833097,0x40000995e00000d084f8,0x8340000f6043c4e9f288,0xc029c0000300b65db580,0xa0a41e920c1000a0088b,0xc44200000c24d44e7503,0x1e1ed00000206d00002,0x143bbb043ad124000,0xc1c20,0x3b500000000000000000,0x90d1c108c40000000034,0x28273000028672b235,0x6015e04d1c0ce0000000,0xbf580f800752027a08ed,0x5026e0687a0760000110,0x43484ca003381f6a0d72,0xaa80000d04cf81b4d45,0x30ae8000000002c1495,0x1c700001003100000000,0x204eed0d6d44b8000034,0x510000000000888a0000,0x1ecf0398c17930],#[0x2b0edc000040d828175,0x60214c50ee07aac3,0xcc000000002490e706b0,0x60d140000a32,0x650040000000002c2710,0x55c00a7400001197008a,0x381530000340e3350408,0x64882ce50c9d4307007d,0x1432b637c702f101,0x1227dc039,0xa747700040000f0eb000,0x8502ecb0716c1b8503ff,0x26c000060dd5c1b7707,0x4101000000000e,0x102f580d500000000,0x2019c64c5b88ded0c940,0xc2c01b00000593d0000,0xe52d000005005c0000f4,0x78000008115000000000,0xc19700000100082b7440,0x2d055100000000000003,0x16410162000000000e13,0x3036888e130cd7411e1,0x24a7059c000000000000,0xc0000000000000309bd0,0x1bc2fa501b3c24b1474,0x90b4b433cf26774146e4,0xbef0806c388d03f00000,0x1e851639c1e40000108,0x31d3d0000303151073d,0x76b092fce0558c00b000,0x260da6003f000b351588],#[0x19c90207d480f,0x140cd00003c8f6508d00,0xe6e01be3262fc0fd600f,0x50b724cea00000000060,0x70ae741c4705b94108,0x429300002ca470000000,0xd6c50400000c14a6285a,0x25218261802efc38910a,0x1000f408b00001814e2,0x1b6108114361b0a8c000,0xc000020a3142be000018,0xcb50b5e9004c91daa058,0xf05eec4e250419028160,0xace2024ccd0f01998050,0xc0e9908e4000025bd286,0xd08053e04834877f0cbd,0x11a8166a33a00000901,0xa0000140940000204d66,0x62945514400002480,0x400009754f01bfb0b800,0x22a425a64269415a215f,0x70f2181d4301a100d1f0,0x97e13ff40cf42923039d,0x313bc089c0000280,0xad83cf00002c1ca652f0,0x2045c139e020941d0901,0x7001e8c045e8778ca44d,0x2e3f02e0000060ace423,0x500c89075788898069e8,0xcc00003043c000090d3,0x10,0x46c05940000c070ec084],#[0x51e950c5bc4e3140ea82,0x8800a9404b59095d2170,0x159910b42602c19ea02,0x70000000000000182e28,0x83705cc000000002c8d,0x140ac70dc8000000001d,0xc40000030888c22c0000,0xe0,0x7c20ec80000000000000,0x856100002509600003c1,0x1]]
set_option maxRecDepth 16000 in
def g235D8 := limbs80 #[#[0xd58420af99210af59210,0x98c20b758c20bd98420b,0x84509f994209f59420b7,0x850bb58850bd98450bd5,0x10bf58810ded4250bb98,0xfe08110bf59410bf58c,0xfe8c110fe4c110fec811,0xe54110fe90110fe50110,0xd8910bf58910fe94110f,0x9510bfd8d10bf58d10bf,0x210fec8210bfd9510bf5,0x10bf58610fe54210fe4c,0xbf59210bf58e10bf58a,0xbf58c20bf58420bf5961,0xe94120fe54120bf59420,0x59520bfd8d20bfd8520f,0x8620fe54220bfd9520bf,0x220bf58e20bf58a20bf5,0x50bf58450bf59620bf59,0xdf54950bfd8550bf588,0xbf58650bfd8950dfd495,0xf58750bf59650bf58a50,0xd4810ff54810bf58b50b,0x8110ffd4c10ff54c10ff,0x110ff50110ffc8110ff4,0x10ffd4110ff54110ffd0,0xff10910ff8c910ff4c9,0xff14910ff90910ff5091,0xfd4910ff94910ff54910,0x54d10ff98910ff58910f,0x9510ff59510ffd4d10ff,0x610ff54610ff50610ff9],#[0x10ffd4a10ff54a10ffd4,0xff55210ffd4e10ff54e,0xffd4420ff54420ffd521,0xf54120ffd4c20ff54c20,0x8c520ff4c520ffd4120f,0x4520ff54520ff14520ff,0x520ff58520ffd4520ff9,0x20ffd4d20ff54d20ff98,0xff54620ff99520ff595,0xffd4a20ff54a20ffd462,0xf55220ffd4e20ff54e20,0x94550ff54550ffd5220f,0x8550ff58550ff18550ff,0x950ff54950ffd8550ff9,0x50ff58950ff18950ff94,0x2c044000ffd8950ff989,0x1e07a834c16208f03681,0x8343d61c20cc85c02801,0x2d915f0a544e62581140,0x8f0473036f1a68c90604,0xc486235914085c4051f1,0x1159ca7c523280936096,0xb863a30c17d8b9a5a42c,0x9b1c50de46d035019f8c,0x207e73db9e54ef47513,0x47c233d13e87d43120c9,0x13dc9c54d525e92b0921,0xd5722ad1516a54519284,0xed824bcd5d22dd167ab0,0x5469933ed96cc9463930,0x9b5c96e146f5b6b5b08d,0xf8d7b5bcede16ed4755b],#[0x42b611705b8193fedf96,0x31db8dcc64229712986b,0x94bd2597294935c92643,0x23430a004f0a73335b99,0xf15676adb536a86d33e9,0x223c4b54d9e6ca1619a,0x80121e212004020f1480,0x8480021e20104009880,0x4878a480021e20206009,0x526406204428f101000a,0x878a400110a3c5220400,0x20210001488f141000a4,0x894024060a4c80614881,0xa0400f24201243c32600,0x478a8888f0d101264078,0x4a3c5440488f10093244,0x8121e2a24a4478815100,0x64078815101223c52214,0x84049478a149901e2052,0x1e19110403080928f101,0x88f102911e00a1018590,0x64078814041224051014,0x90005088f1428f221851,0x43c50a2c10f102921e1,0x89010280229480a50900,0xa40791102a1224040c94,0x60294890100a5224040,0x102c2223c40a44780284,0x7910c28b203c40a18890,0x84428f0c800284478a14,0x8008082941e306221480,0x18a110a4040400291202],#[0x8091488f0c0010a44a10,0xe29028002911e3068a44,0x8e04b110a4050808a851,0x8414a4442c1412521048,0xa949900cb85069499018,0xc48a9488f122a5444478,0x4a3c78a9488f122a5223,0x684885a51e294848800b,0x52a21e4452715291203c,0x864888e962881e9080d1,0x54b14311104064a8c345,0xd1414a18892207a52240,0x4a3864a4441014116868,0x44a2088f111c3441a091,0x1c2488928f24b25223c,0x1222407091251e3970b1,0x530592224a3c6488928f,0x52a410147911528f1844,0x2044788904251e295880,0x79104825222160a092c1,0x8251e2970b101a44a40,0x22318090d1a582447889,0x50a052921e304868e0a5,0x1a44b08790052921e21,0x203c4480e1251e3170b1,0x1424529014a414201291,0x5292202454b112101e34,0x80950872c8904a4878b1,0x74a4878804ac4490d1c2,0x5488e243430a0074a48,0x204154a3c88894406224,0x1429480c5e20382910a5],#[0x48a5202a14a448091124,0x1e2958805225843c72a8,0x28295085204488892125,0x12901e441424129114b0,0x22224209478a5c2c4069,0x14a44630121c14685291,0xc244560210014d868e0a,0x242001479004a44490d1,0x405488800f28414488a,0x182228f1d222291478a3,0x29215222003ca0c51222,0x48901c1148284b002240,0x84280225080e510c1001,0x88a4480c84a118a40510,0x840110a40a0c5108]]
set_option maxRecDepth 16000 in
def g235H8 := limbs80 #[#[0x7818100000010400400,0x4380000400b48101010,0x1040e040019c1850200,0x5120a380000200104341,0x8b5400f830e6c0000e0c,0x10a00c84002000700000,0x12840800e00081040438,0x8000830800b870024e91,0x88810004302001c1010,0x180140c100004c10006,0x401081c0162001381000,0x8083008914102060610,0x8703830625c0406040,0x18200050868014024c80,0xc000041e00e000008101,0xc011144da820a004031,0xe060028c95080629d14,0x48a2818f32084c081102,0x50e241830c0c0050000,0x9084428f305802604141,0x240b110634004025808,0x408281760c0972850600,0x1380022870b02f000e0,0x7000000b83002c30c00,0x90b0a541103ced70d040,0x5020d7034a22f9b0230,0xa2ebc227101859902180,0x142d0152e18637402850,0x800c011410b07032c009,0x1524f0804001160029c2,0x4001221dc13000c4094c,0x30320e89027],#[0xb780a00000790a940728,0x278f828cc4f600001e04,0x4a428cc1e884dd800016,0xbf5c4c00448d2039f221,0x32ac4000000001203263,0x3b800000000025560000,0xe01900001241aa058941,0xef04496846d2404f93db,0x239c207f8000180e2103,0x698174c0dfd83e6c4fc3,0x3e5059e843ee01b8615,0x164dd401e86149a05fe9,0x35e82b80000160c0c22b,0x983594310d023fc07248,0x657005e000000001e4c4,0x2144fb1fc0057e24e0e0,0x1086709514001630146,0x8627416b3859d233e000,0xd9039ac183c0628010e4,0x6b4d00eda33fa908bc17,0x3b5440000505bf0,0x364a16c8000,0x5cd9600000000020bf00,0x9e000008882b02b60000,0x28798000068,0x78000000000000000000,0x249fe0d45a8e460c3d14,0x3b08a000050233a0d9e,0x5c201cc000000000000,0xa82ef8020000051b756,0x2b7a037203cf414a0000,0x22bae12602],#[0x16168800000000,0xa36b00000a148f0a7200,0xc15480000000000000,0xe0010000020ae000,0x80000000000000000000,0x30885eecbda08e3a03,0xa950a85af2104000010,0x563010c80000000040bd,0x303d72effc10484517b8,0xd5d047e611bb8283a04c,0xc14c00001c21478509a4,0xc40000502466869900ae,0x9406c102c0dabe18f602,0xd8044b009a503ba4f017,0x4e91218c0000403a9c12,0x200001035aa070b904b8,0x505a0358819d6215b0a8,0xc131c33f1211c3c,0x4d84507c542f903f80f4,0x5f8003c80ee7a03b61,0x95007c88166c12a13370,0x1f7a0ed78bcc0000502,0x901058a09b704fb021d2,0x140a72a450075,0x200006822a00001ad460,0x16003892ce000018d6,0x500b1419300000011d80,0x42da9db814971b63e078,0x404ff9858e0,0x5ce0f6281ece058cc430,0x16068382da0000692,0xd800000000483a0c0958],#[0x3842a44b4c85b0216,0xaa90d983bc2223f03740,0x683eb6055c8bc,0x2a71687808048f0e000,0x12b007842f3928e10831,0x61330000000005908c22,0x8604d7b815c000000001,0x81a80000000000000704,0x2ea00004,0x37a80001404080000000,0xf0012babcd410c2826bc,0x822180000816d082f,0x601b0000032007e17b80,0x1835664af908ec0000,0x20812018440bdf902e00,0x526b64008b817680000,0x831fe067f0c86690e094,0x480001894a1238608791,0x51680000000032cac817,0x1681fc824f60e5392faa,0x57400007848c00005018,0xb8520811880000000028,0x60e400000c0d0,0x3a51000000850e00,0x4a28dec1087605808496,0xb8c00000000000000106,0x905ec000000000c0e06,0x864d0096261800001e14,0x436ca85ba0000784f7a,0x1ec000000001a4270000,0x80001e13d34cbd6f0842,0xa600001e4d6000016431],#[0x7036800001054ea0,0x28809d68370810b4055e,0x3417022700000aa56513,0x401ee800000005,0x21052203e685c4000,0x56f0048b198037800000,0xbac00006837c0000085f,0x110916a864b8ac6b6318,0x5b02dee2b700001c16a,0x2a12d11f4f365038b381,0x8940ac338b7715a1144d,0x3b48a0cc89ae7e176504,0x782f54110782f10073f,0x213c540da921ae000,0xe001f0a47d2e2ff83c60,0x16904000016186002c,0x5904c000000000000000,0x5b000000000000000000,0xc0ca0000102190000065,0x2c5b040bbe2886,0x12025205328cd5800,0xa6210400001a50600000,0x3404c000000000a02,0x6128000000000000000,0x818a000050a2,0x9082ba012c00,0x18500a01b725ec4222,0x611e5823000004a42600,0x32a0eb00001a1146b8a4,0x1815980001605a314,0x29470c4e50000064d80,0x9603a19bc02301b16000],#[0x4ed328223a138000018,0x0,0xc0226000000000000000,0x83fc418f,0x28b1e00000000000,0x7847c0000404de,0x13aae154000018138800,0x14029662f4a83fb85252,0x616a85cac4df3800600e,0x8177c0d61408e70481a,0x7f40a4e0d6400000000,0xc0863a15a125fca171e0,0x621b14016800008411,0xae3300001c41a5834e00,0x14441898b2480b8125b4,0x80b400002845f60f794b,0x98000020d07a2b920f06,0xfcd043c8942e8018612,0x26e0d8000140beda2338,0x20b8ed28000101701aa0,0xf102a0000200f0000028,0x2a8000160d18889a6191,0x813a9a52a0015000006e,0x8de1818000000000038e,0x598000000001417cd81,0x86057781248000000000,0x17f582b40000581ac618,0xc24af4823b20e0800008,0x4194c28490260066003d,0x16021c15a7c0cf90,0x4837384fcc14300027,0xa218581e60000621c400],#[0x92c8aa800000000221d5,0x1094b303b6613c290,0x200000a12b1203f80b90,0xa1730863b60b,0x7a12d0000000db784480,0x9dae033a1397e8ace027,0x1143d80f8485dc000048,0x81781376d0f180a52132,0x60ab18c82a020c823461,0x4e24f242583e146f01f1,0x57a20c5e146b2389308,0x700000093a7835d2188c,0x4b70a99fe871a1aea613,0xac02aa10600000385ce2,0x213380000440c980e,0xb142964e9fa52f042200,0x404d402b680000e07e,0xde182ca000012ca800,0x38cb7380001a15718107,0x215600001401ba80,0xbe017289395851800000,0xb37500812b50000016a3,0x64027e06158135e931b8,0x53a0ae0ce5805,0x48549821538426001480,0x29885804116e89e40000,0xe03518051247c0000180,0xf1272e9a03d86f4b81d2,0x122a613e781f5e0ecd85,0xf00001e14ea034cc170b,0x7228000004d463af7a2f,0x1e830e056040f2404252],#[0x1aea14824c00000000,0x4001a000028224093680,0x924c513a217000000000,0x800400001c0db8000181,0xce6607ac01be,0x12941088580000000,0x48000061158a5494b180,0x2c0103c4000061b67c00,0xc0000000000000383d41,0x429ff60430839,0x700fce2770043e000000,0xa8501912eff000000000,0x90e18838c00005033420,0x1c4f8d060200004a413,0xa5120000583e4c41c800,0x6209722c86146da4bc8,0x6b202000000000000,0x1801d0707000080,0x1ed00cd9204dc14b8000,0x80000285fb860800003c,0x480c1415b4a3dfa0ce,0x6e2f501d601289046800,0xa0a6b3b3f437d80001,0x24b4150000000000000,0x5288e4a0ba202872127c,0xaff058d050fa8546812,0x520952186fe8df28b2f2,0x61615042341877104,0x392e8000000000000000,0x1a901f96048b8207e010,0x10338400203319857a1,0x4e280001a37d601a2],#[0x93b80000420d14952800,0x40000000000000140904,0x12b80001014151065a08,0x1607b922b5c4f840291e,0x34a20b5c131821550000,0x3831360838000128ab30,0xb4713d52b611049c0000,0xc0980a1a3a98480000a0,0x6106b3c0084000040d03,0x14883b80d80000484,0xe0000140eadb38600000,0x8fb6841b6190d2326c72,0x8000068610000000000e,0x1620ebf053f0d4f2802,0x800000000480e54d1790,0x58088000000001803d,0xc80c00000647c8000000,0x6200007a1f6000000000,0x822d804780ad60000003,0xa0a0ce00000000002228,0x7213400005091f46d,0x6000000000e01160e160,0x5d00000284fc410d0030,0xd149c0000138a70a8fb8,0x7630420615300000e0ef,0x832100000000040c8040,0x140315bb4fe0fff0d43,0x25f0084885c80000000,0x8c1337602c93d4200006,0x84e78835580990b1,0x400003ac8000005a1a40,0x4922843ca4a600006041],#[0x4a909c522d1017c374f1,0x754033de5109021e8801,0x83856840750e24a8e9c3,0x100caf9103e0cb712e3,0x6cb5000012410000,0x88000000006196800000,0x373885a4000000000882,0x808db00ee0000580362,0x367a12ea9aec00004bc4,0x800012ac4f92dbc10d89,0x713efc03ce21d3e043,0xaa7f00001847dd828e00,0x3e6426501b4411180000,0x655e80001e083000,0x2815420f8f82d9a8d00,0x14f00000000078066000,0x60000793d200002051d0,0x2e3003a00001a071301b,0x800011105f3ac0000058,0x4fc90780000284c2e80a,0x618680001c819d8634ad,0x6f7811c0000401c1,0x0,0x701152d4ae112bc17a8,0xfb00001028600000000,0x40000483b088dd1218a2,0x53842d7402e6a2f8324f,0x80000876480001e023f8,0x3680000000009416a011,0xee2a2403fc1,0x7e00c98c1600000086a,0xa0c80000603980000205],#[0x5056b00340000180503,0xab5c000038ad2000,0x6689f80001603d235420,0xe05c2fa80000e10bf05e,0x80000000078404000078,0xe5692c40000000010497,0x60c100000656a30288e6,0x1c17920452a8d0fa1cf,0x100e0af585d426ca5b2,0x5131420788006b0710f,0x40d10300212e50220000,0xe000028092609674372e,0x2e46008d80b9410ea839,0xb031d40908000102f5e1,0xb4d805c8121085e0e05b,0xa0fa78dd180bcea55cc0,0x1dc3407a60c0efc38014,0x104236ef948e0000782,0x47a36e618e12cd4418b4,0x2fa183a7ee2840073a04,0x16164803f1a139782a7c,0x514202df8641a0028000,0x601ae000018,0x0,0xe0b51827000007861e00,0xea90e0fa4e7602f80000,0x43088c000000000491,0x1028120b3302c2e1247,0x881824511610e8000,0x4412ac10f8e11954498a,0xbd800005105d6427b03a,0x1497070e0ee11679],#[0x503daa151000008872,0x415f080ff32911203400,0xbc0098a904e201c280bb,0x352c286d02640000684,0x4800000000085f840659,0x107f030beebe70542209,0xa244b2829e0000000012,0x1dfc169b00bc437793af,0x48251a08510ac0276418,0x6a715582b6aa92aa6e2c,0x5465906f64f33941931,0xbac024183a34d41601a7,0x630e074285aa204e501,0x70000000007242202b67,0x75dc002ba4d6a8126cb1,0x362bd50517808624d9ca,0x2c0205e60e1d20497912,0x80000c0fe512b8f10891,0x20d500001c43d,0x2ccc7004f00792884800,0x3360b018c61c05280001,0x24d6a0d27085204c7430,0x2b83c28028e82454a389,0x1290945d2730d854b283,0x5411c9057fe10082377a,0x1da00004837b310f3032,0x2b2a0a2da4ea005398,0x3fa0076a168785e3402b,0x216f0000000005adf521,0x4e00000000000007023d,0x594a036800000000224,0x9706122c0dc92c8e0cbf],#[0x18c778820cc52e415,0x1e1644025c00002a6140,0x89030000,0xd85114b3e00001089e80,0x31d3b3261340000080f2,0xa0c8a23c6e6935060b60,0x8f615e0013da5096802e,0x2c760000000014107684,0x4934d605f3030c804a9,0x7500000a22530310000,0xa000010b23e18c802aa4,0xae36085ca10688e02862,0x38444e54a4014ca14340,0xba200d360e1ba2ee217a,0x1b8ae8142984d966,0x1805da23c4000000000,0x26e411700001e8de000,0xe7011600000038a8ebf6,0xd7141c4183403f6482,0x724046a3c9e054e82f94,0x144a0825010964b40802,0x686cc8c1c62b7f8,0x7a98c3d2b5080001a04d,0xa80b00000e08a484d348,0x8f20c6524ff04c5c049a,0x2617aebfe04ca62f9c33,0x52302633f68314c064a,0x38d064400004027c4a1,0x80000603cde9282891b2,0x7400c9b80fa0000511f,0x80000c61c00000000070,0x2890da88218cfb6165],#[0xc02680625eb815a34c00,0x2a038000000001,0x84be613c800004063800,0x838b178103a84ede8eca,0xa430044c00000000140c,0xc64d2880cbe0927bc1a8,0x27d217ea858a6a127804,0x8000180a1393d0618582,0xd81027f200c3816b2018,0x809e00000843c28068a0,0xb3810200000a41680001,0x93c000004260e0000112,0x79422e4f99,0x1108000000004858e000,0xa0166fab6ce86a000010,0x1434211981658007a047,0xf20cdc052601c62903f2,0x45181180000083d2609c,0xea4543b34000030ad102,0x614030b012e000000000,0x2ec451ba20d6000052d,0x5003a412c98309e11d2,0x8cad8158000050ace000,0xb0a3980000000000120a,0x467c4baf81fc60968831,0x72cd32648982a3c4dae0,0x317bb37a4bf204c0a0a9,0x84de1238840468900101,0xe15c702036af980000,0x1b3f331109cce04ef02,0xdca2ae000030ac960e5e,0xfd40867604a00001618],#[0x1695538601a359c3b3d2,0x51e60abc9465a2b10000,0x80001aa11521be221b08,0xa181dc60aa183932061,0x19ba86558142c1,0x6c000000000000000000,0x9ad180868218100b7081,0xd12bb60187053400004,0x50583456b0000102b,0x8c97821c85c15b88ac60,0x38112216e404e,0x3a0d3611500001814b00,0x7e11ef6175c8ae40000,0x84cc2813200004048225,0x88487288556000038376,0x15000002044e915d601,0x15ac245d81a400003,0x1bbf2000000000000,0x1488be052aa0b1b83440,0xa70609e80001608b8000,0x81aba099c1ad68216f8,0x1251a12846c00b,0x673fa1ba200004858600,0x146d780000a05e80000,0x185c4b51003300000000,0xcefde,0x1049062e215c80000000,0x848be]]
def g235D9 := limbs80 #[#[0xd20fe107f843fa21fc10,0xa1fe50fea87f143fc41f,0x19508a379506c1e003fe,0x445103090053009f96db,0x8144f0091440c20403c7,0x510304f0920084051030,0x44f0091440c108045020,0xc20513c5009405103081,0x13c02440c20450064040,0x10308100519010308115]]
set_option maxRecDepth 16000 in
def g235H9 := limbs80 #[#[0x6102010800602000800b,0x580010a0000006003241,0x4090180428800280841e,0x58a0a201021c20202520,0x100040042c000800200,0xd0298109026420012403,0x25152623a10305185220,0x2,0x1a3051804a1057e0760,0x24e0000f078713ce5551,0x1054f04110840000a,0x1169083b00d406e11080,0x7512466c665105600005,0x248d03ee01422500000e,0x24b736100002037555ef,0x4b0000197af028607c8,0x346470f96070180000e,0x60481186613b7,0x57000000000000000000,0x113f074621500000149a,0x708253505db007e740e,0x5430000c07e0000c3472,0x7520000800ad022610b3,0x2c41662063d0090000a,0xf5781187f4053,0x4d874f3024107900000,0x75c00000000804e474c3,0x3013f8441801c00005,0x4071000082417483b,0x8184000040520,0x65e206b11120000c03f0,0xb2462450903502176],#[0xb0590000d67000000,0x808600000,0x78351800000441000000,0x4f9020d00f407720447,0x610000000090664136b,0x87de0260000b445845de,0x1200000106f0000c03db,0x711a00005021c404d,0x0,0x201d725a0000220d0,0x320000126bd37a00000,0x27dc556611790873263c,0x154219d013412f942c7,0x464e10aa244b00b00006,0x467e97b9030d06400001,0x19c033e51a46787,0x13a0000801600000,0x252a038a8699068e2180,0x8740000000000002210d,0x961001f0000000000006,0x55f00000000c564f245c,0x776802f0000e44400002,0x50000d07b0000504cf,0x85a75710000918161290,0x2b82742216f01280851,0x41e911fa047102e1001c,0x49f065d062a4768031e,0x69a138b741000032593,0x74b102330450000d4689,0x80003451405b11676,0x6a00000000000000000,0xc429000051858],#[0x29c5790000024f00000,0x36275d000000000000b,0x2500000471803ac139d,0x452000061099360e6645,0x30060000a671b135f,0x90400000000000000,0x365f0000a0580,0x75000000000000000000,0x542717f324900002148c,0x6067203cb046226c5,0x2144072c008000000000,0x42d2405512a4409212e,0x73524a44690000f05c9,0xd44f00007,0x137a37b307d425b30750,0x2d100200000000500e8,0x17601ea183200c30807,0x43713e3060000000009,0x42a0000574e2081b,0x26d412df039000012540,0x213508200000000f05ee,0x530000702700009,0x5359e050000016790,0x7439000000000,0x26a00003875000000000,0x917c606d00000000c,0xa45c95655411105f0,0x74d00005011c777b51f0,0x2470000f05ab465f0108,0x2110000712a917d00003,0x115100451825275e85b2,0x807f0000e055017ee],#[0x427611c7739d03b74770,0x1b207a0000c02af06c6,0xb]]
def g235D10 (j : Nat) := if j=0 then 0x3f else 0
def g235H10 := limbs80 #[#[0xa98231156208034a0060,0x7a41aa798233dc971,0xc38c3644a880001a2800,0x2000000284213e4ae830,0x5440000006b491,0x2b8883800000000501,0x18a092a4e3973852a8,0x400a3400000000051480,0xa30a9a09f02800019d93,0x850ab1191118881a0005,0x6c2d0a629421000284ea,0x3a8b00000000641000,0x0,0x9460278180000000000,0x238005b283323a800000,0x731799092a]]
def g235L : Nat → Packing
  | 5 => (64,5,5,0,0,9,0,g235D5)
  | 6 => (980,4,5,0,0,13,0,g235D6)
  | 7 => (807,3,5,0,0,15,0,g235D7)
  | 8 => (136,2,5,0,0,13,0,g235D8)
  | 9 => (10,1,5,0,0,9,0,g235D9)
  | 10 => (1,0,5,0,0,0,0,g235D10)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 26 397 2 14 6 4 g235H6
  | 7 => lookupWord 391 2333 6 18 10 4 g235H7
  | 8 => lookupWord 361 1973 7 18 10 4 g235H8
  | 9 => lookupWord 76 457 7 16 8 4 g235H9
  | 10 => lookupWord 15 97 5 12 4 4 g235H10
  | _ => fun _ => none
def g235 : Forest := ⟨235,10,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
abbrev SixBits := Bool × Bool × Bool × Bool × Bool × Bool
abbrev SixRows := Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512 × Fin 512
def readSix (r : SixRows) (v : Sig) : SixBits := ⟨bit r.1 v,bit r.2.1 v,bit r.2.2.1 v,bit r.2.2.2.1 v,bit r.2.2.2.2.1 v,bit r.2.2.2.2.2 v⟩
def sixCost (x : SixBits) : Nat := (#[0,2,1,1,1,1,2,0,2,2,2,2,2,2,3,2,1,2,1,2,2,1,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,2,1,1,2,1,2,2,1,2,1,2,3,2,2,2,2,2,2,0,2,1,1,1,1,2,0] : Array Nat)[1 * x.1.toNat+2 * x.2.1.toNat+4 * x.2.2.1.toNat+8 * x.2.2.2.1.toNat+16 * x.2.2.2.2.1.toNat+32 * x.2.2.2.2.2.toNat]?.getD 3
def crossOp (d : Nat) (a b : Bool) :=
  if d=0 then a && b else if d=1 then a || b else if d=2 then a && !b else !a && b
def applySix (d : Nat) (a b : SixBits) : SixBits := ⟨crossOp d a.1 b.1,crossOp d a.2.1 b.2.1,crossOp d a.2.2.1 b.2.2.1,crossOp d a.2.2.2.1 b.2.2.2.1,crossOp d a.2.2.2.2.1 b.2.2.2.2.1,crossOp d a.2.2.2.2.2 b.2.2.2.2.2⟩
theorem readSix_bin (r : SixRows) (d) (a b : Sig) :
    readSix r (bin d a b) = applySix d (readSix r a) (readSix r b) := by
  simp only [readSix,applySix,bit_bin,crossOp]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem six_cost_binary : ∀ (d : Fin 4) (a b : SixBits),
    sixCost (applySix d a b) ≤ sixCost a + sixCost b := by decide +kernel

theorem measure_live_tree (w : Sig → Nat) (hb : ∀ {d u} (a b), allowed u d →
    w (bin d a b) ≤ w a + w b) {u T k S} (h : Live u T k S) :
    S.card = k+1 → w T ≤ ∑ s ∈ S, w s := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb' ab fr tail ih =>
    intro saturated
    have zU : bin d a b ∉ U := fun m => fr (by simp [m])
    have bound := live_size tail
    rw [Finset.card_insert_of_notMem zU] at bound
    have bc := Finset.card_insert_le (a:=b) (s:=U)
    have ac := Finset.card_insert_le (a:=a) (s:=insert b U)
    have aU : a ∉ insert b U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated
      omega
    have bU : b ∉ U := by
      intro p
      rw [Finset.insert_eq_of_mem p] at saturated ac
      omega
    rw [Finset.card_insert_of_notMem aU,Finset.card_insert_of_notMem bU] at saturated
    have tp : (insert (bin d a b) U).card = k+1 := by rw [Finset.card_insert_of_notMem zU]; omega
    have step := ih tp
    rw [Finset.sum_insert zU] at step
    rw [Finset.sum_insert aU,Finset.sum_insert bU]
    have price := hb a b hd
    omega

theorem six_cut {u T k S} (r : SixRows) (size : S.card = k+1)
    (cost : (∑ s ∈ S, sixCost (readSix r s)) < sixCost (readSix r T)) :
    ∀ t, t ≤ k → ¬ Live u T t S := by
  intro t ht live
  have wid := live_size live
  have eq : S.card=t+1 := by omega
  apply Nat.not_lt_of_ge (measure_live_tree (fun a => sixCost (readSix r a)) (by
    intro d v a b h
    rw [readSix_bin]
    obtain h|h|⟨_,h⟩|⟨_,h⟩ := allowed_four h
    all_goals subst d
    · exact six_cost_binary 0 _ _
    · exact six_cost_binary 1 _ _
    · exact six_cost_binary 2 _ _
    · exact six_cost_binary 3 _ _) live eq) cost

private def wheelRows5Page0 : Array Nat := #[114530269217091,151322437880362,47871881642369,36837959671968,47841699432584,150094074816521,151780017143841,73714576679016,214452065034344,73714574573640,73714576679016,38521579111179,144083320856648,211692496225035,142526344858153,153119933628608,211692496225035,46356257341632,184899013345410,211416544576265,211692496225035,214452065034312,46626840314691,144323840575560,46626840314691,144725368113706,73714576679016,153119933597768,142526344858154,106941481887786,114530269217091,153119935703144]
private def wheelRows5Page1 : Array Nat := #[153119935703112,176478059374626,144323840575560,114530269217091,45634052696200,142526344858146,144323840575560,114530269217091,177575439728673,142526344858146,48001233978242,46901722350466,74225666769281,73714576679016,247678969806978,247677896065154,46226905063521,38212357660705,114530269217091,114530269217091,153119935703144,45527328688200,153119933597768,149842827427849,10204842819849,153119933694144,45634052696200,12382447347784,184859687485569]
private def wheelRows5 : Array (Array Nat) := #[wheelRows5Page0,wheelRows5Page1]
private def wheelRows6Page0 : Array Nat := #[144725367587105,144725367587105,114530269217091,46626840314691,141875672023176,114530269217091,142526344858154,46626840249154,144725367587105,152329773416584,12687509555336,141875672122123,141875672023176,144083318767752,73714574573640,150360366842691,151780017143937,12687509555336,176748645909314,144186382778528,12412629559400,153521460609313,185165305414466,185165305414466,73714559901800,39170646999937,144725367587105,12412629559400,12412629559400,12412629559400,12687509555336,12382430570600]
private def wheelRows6Page1 : Array Nat := #[12412629559400,12687509555336,73714559901800,141978736033952,73714559901800,36971623744385,12687509555336,12412627454024,36971086872961,73714557796424,12687509555336,141875672023176,144725367587105,73714559901800,150360366842691,12687509553537,141978752811168,144083318767752,48001233977986,73714574573640,214452062928968,73714576679016,73714574573640,47871881642369,36837959671968,141875672023176,73714574573640,73852013527112,73714576679016,73714574573640,144323807051968,73714576679016]
private def wheelRows6Page2 : Array Nat := #[141978752811168,141875672023176,73714576679016,73714576679016,73714574573640,73714574573640,141978752811168,36837959671968,141978752811168,150360366842691,12687509553537,142526344858153,144083318767752,143625856485929,48001233977986,36322555855627,214452062928968,143625860170081,73714574573640,141875672023176,144323807051968,211692496225035,144323840606400,12687509553537,73714576678984,73714574573640,74264330387528,107616319570305,12687509553537,143625860170081,12687509553537,144323840606400]
private def wheelRows6Page3 : Array Nat := #[211692496224521,141884262088840,144323840606400,143625856485930,211692496225035,74084984031786,46901722350210,73714576679016,38071135371906,211692496225035,211692496225035,143625860170081,143625860170017,143625860170017,144725371797857,144725371797857,107616319570305,144725371797857,143625860170081,12687509569728,144323840606400,144323840606400,141875672023176,143625860170081,12687509569728,144323840606400,12687509553537,144323840606400,144323840606400,106941481887786,36837959671968,12687509553537]
private def wheelRows6Page4 : Array Nat := #[12687509553537,10479862808961,12687509553537,12687509553537,12687509553537,12687509553537,73714574573640,12687509569728,151913163161760,46631135281730,46901722350210,143625860170081,143625860170081,211692496109640,115629780779330,142526348542305,141875672023176,141875672023176,143625860170081,142526348542305,143224312266944,142526348542305,115629780779330,115629780779330,143224312201408,211416544576267,107616319570562,212244416184392,143224312266945,143224312266944,143224312266944,143224312266944]
private def wheelRows6Page5 : Array Nat := #[211692496109640,73714576678984,72889924075592,211416544576267,73714576678984,143220017234112,73714574573640,74497306673344,151780017143937,73714576678984,73714576678984,151780017143937,141884261957768,114530269217091,114530269217091,211666725912642,149572370399361,73714576678984,46626840314691,46626840314691,144725368113706,73714574573640,73714574573640,73714574573640,73714574573640,46626840314691,144725368113706,12275190612321,107616319570305,149842957500994,12412627518018,46626840248898]
private def wheelRows6Page6 : Array Nat := #[46626840249154,46626840248898,73714574573640,73714574573640,73714574573640,142526344331810,144323842680936,114529732346179,153012674789536,73714576679016,73714576679016,144323842680936,211692498215016,73714576679016,73714576678984,73714574573640,73714574573640,142526344858154,10346593525832,106941481887786,12275190612321,144323840606400,107616319570305,114530269217091,144725368113706,144725368113706,114530269217091,144323840575560,144323840575560,153012674756897,114530269217091,246738892390536]
private def wheelRows6Page7 : Array Nat := #[153012678967649,153012678967649,246708827160705,142526344858154,114530269217091,114530269217091,114530269217091,114530269217091,74264330387528,74264330387528,74264330387528,153012678967649,153012678967649,246708827160705,12275186434208,114530269217091,114530269217091,114530269217091,114530269217091,73714576679016,115629780779330,12275190612321,10204980740288,10204980740288,73714576678984,115629780779330,12275190612321,73714574573640,141978753335456,73989452480584,142526344331810,142526344858154]
private def wheelRows6Page8 : Array Nat := #[73714543124584,107100378891019,36971623743873,36971623743873,73714576679016,73714576679016,73714574573640,74264330387528,73714574573640,73714574573640,114530269217091,73714576678984,107100915761931,73714574573640,144323840606400,142526344331810,211692496225035,12966682427584,12275190612321,12275186434208,12275190612321,12275190612321,12275190612321,73714576678984,12412627484864,12275190612321,142526344331810,12382445242440,142663785382466,73714576678984,72889924075592,73714541019208]
private def wheelRows6Page9 : Array Nat := #[107616319570817,107616319570817,141978752811168,144182087811232,144319528861888,211692496225035,144182087811232,46626840314691,46901722350210,46226905063521,114530269217091,12275190612321,107616319570305,73714559901800,114530134933570,73714574573640,151913163161760,143220017234112,46226900852769,141875672023176,73714576679016,12382447347816,73714576679016,10449680599176,12382447347816,141875672023176,73714576679016,12687509553537,142423263675147,73714576678984,73714576678984,151780017143937]
private def wheelRows6Page10 : Array Nat := #[150089779841547,151780017143937,151780017143937,150089779841547,150089779841547,73714574573640,73714574573640,150394726581059,151780017143937,143763297076035,10346593525832,220349010550856,106941481887786,141875672023176,141875672023176,106941481887786,46901722350466,143224312266944,144083301990536,144083285213320,141875672023176,141875655245960,141875672023176,141875672023176,114530269217090,141875672023176,141875672023176,12687509553537,142423263675147,141875672023176,12382447347784,141875672023176]
private def wheelRows6Page11 : Array Nat := #[141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,151780017143937,152041980723392,73714574573640,73714574573640,114530269217091,73714574573640,73714574573640,141978752811168,73714574573640,12275190612321,149842957533376,107616319570305,73714574573640,73714574573640,46626840314691,73714574573640,73714574573640,143082576183456,73714574573640,46226905063521,46226905063521,144323807051968]
private def wheelRows6Page12 : Array Nat := #[46226905063521,143220017234112,73714574573640,73714574573640,73714574573640,73714574573640,73714576678984,141978752811168,73714576678984,73714574573640,46226905063521,114530269217091,36837959671968,151780017143937,151780017111169,73714576679016,73714574573640,141875672023176,73714576679016,114530269217091,114530269217091,114530269217091,73714576679016,73714576678984,151780017143937,46226905063521,143220017234112,46226905063521,114530269217091,73160507015240,46226905063521,73714574573640]
private def wheelRows6Page13 : Array Nat := #[73714574573640,141978752811168,141978752811168,36837959671968,141978752811168,107616319570305,141875672023176,114529732346179,73714576678984,149572370399361,73714576678984,114530269217091,46226905063521,141875672023176,114530269217091,149572370399361,73714576678984,151780017143937,73714576678984,73714576678984,176063594463361,73714574573640,73714576678984,73714576678984,73714574573640,143224312266944,46226900852769,114530269217091,114530269217091,149572370399361,149572370399361,149572236181633]
private def wheelRows6Page14 : Array Nat := #[149572236181633,114530269217091,114530269217091,141978752811168,149572370399361,143220017234112,149572370399361,141875674120328,149572370399361,73714576678984,73714576678984,176063594463361,114529732346179,176063594463361,114529732346179,114529732346179,176063594463361,141875672023176,73714574573640,176067889496194,176063594463361,176067889496194,176063594463361,73714576678984,176067889496194,176067889496194,176063594463361,176063594463361,176063594463361,114529732346179,176063594463361,176063594463361]
private def wheelRows6Page15 : Array Nat := #[176063594463361,176063594463361,176063594463361,114530269217091,114530269217091,150774845833376,46226905063521,73714574573640,141978752811168,141978752811168,74229978497409,114530269151298,74264330387528,114530269151298,212494597718146,73714574573640,12275190612321,73714574573640,144323840606400,12275190612321,106940407619618,73714574573640,212493523976322,12275190612257,106940407619618,106940407619618,73714574573640,212493523976322,212493523976322,106940407619618,141978752811168,12275186401569]
private def wheelRows6Page16 : Array Nat := #[73714574573640,144323840671936,72713836167971,46226905063521,150089779841547,46226905063521,46226900852769,73126155141312,143224312201408,46226905063521,46226905063521,144590124515458,46226905063457,46226905063457,46226905063457,214452062928968,212493523910786,212493523910786,184899013345410,214452062928968,114530269151298,12275190612321,46226905063521,36846541348898,106940407619618,107490163433506,106940407619618,46226905063521,36846541348898,114530269216834,141875672023176,114530269216834]
private def wheelRows6Page17 : Array Nat := #[36331145273378,106940407619618,151913163129121,36846541348898,141875672023176,73714574573640,73714574573640,73714574573640,73714574573640,114767431928331,212622374895776,212622374895776,141978752811168,141978752811168,12275190612321,106940407619618,46226905063521,46226905063521,36571663441954,46226900869153,176064131334273,185165305381056,73714574573640,73714574573640,141978752811168,214452062928968,73714574573640,73714574573640,73714574573640,214452062928968,141978752811168,46226905063457]
private def wheelRows6Page18 : Array Nat := #[46226905063457,114767431928331,144083318767752,73126155141312,115071443288256,73714574573640,73714574573640,176064131334273,46226905063521,141978752811168,73714574573640,46226900852769,141978736033952,114530269217090,141978736033952,114530269217090,107482655498400,212623448637600,114530269217090,115071443288256,212623448637600,114530269217090,212623448637600,114530269217090,212623448637600,185165305381056,106941481361442,106941481361442,106941481361442,106941481361442,176478062993505,114530269217090]
private def wheelRows6Page19 : Array Nat := #[107482655498400,106941481361442,106941481361442,114530269217090,212623448637600,106941481361442,114530269151298,114530269151298,114530269217091,114530269217091,114530269217091,176521008521250,176486649307170,114530269151298,12382447347816,114530269151298,114530269217091,114530269217091,114530269151298,211666725978435,211666725978435,114530269151298,114530269151298,114530269151298,114530269151298,114530269151298,114530269151298,36731235665992,114530269151298,114530269151298,106941481361442,114530269151298]
private def wheelRows6Page20 : Array Nat := #[114530269151298,73714576679016,144323840671936,115629780779074,46626840314691,141875672023176,114530269217091,141875672023176,143082576183456,176486648782882,114530269151298,114530269151298,115080024965186,73714576679016,73714576679016,143220017299648,115629780779074,36846541348898,141875672023176,141978752811168,141978752811168,115629780779074,106941481361442,141875672023176,141875672023176,73714576679016,141875672023176,73714576679016,141875672023176,46626840314691,36322555863082,141875672023176]
private def wheelRows6Page21 : Array Nat := #[10449680599176,141875672023176,141875672023176,141875672023176,150089779709961,141875672023176,141875672023176,141875672023176,176063594463361,141875672023176,141875672023176,73714576679016,141875672023176,141875672023176,46626840314691,46626840314691,144177776066720,73714574573640,74264330387528,107616319570305,114530269151298,12275190612321,114530269151298,12275190612321,211666725978434,73714574573640,114530269151298,106941481361442,46901722350210,214452062928968,46226905063521,73714576678984]
private def wheelRows6Page22 : Array Nat := #[46226905063521,143220017234112,114530269151298,12275190612321,12687509553537,141875672023176,144323840606400,144083301990536,144323807051968,73714574573640,73714574573640,141978752811168,141978752811168,12275190612321,45802210722177,144323840606400,149842823250112,106941481887778,149842823250112,149842823250112,106941481887778,149842823250112,46226905063521,46226770845793,46226900869153,143220017234112,46226770845793,144323840606400,143220017234112,73714576679016,73714574573640,114530269151298]
private def wheelRows6Page23 : Array Nat := #[73714574573640,73714574573640,141978752811168,46226905063521,144323840606400,73714574573640,141978752811168,151913163129121,12275186401569,73714574573640,73714574573640,107100915630345,211666725978435,107616319570305,150092069734530,141875672023176,46226905063521,81411273015618,141875672154248,141875672154248,144323842703552,73714576678984,114529732346179,114529732346179,106941481361442,73714576678984,73714576678984,114529732346179,74264332492872,176063594463361,114529732346179,176063594463361]
private def wheelRows6Page24 : Array Nat := #[114529732346179,176063594463361,246708290289793,176063594463361,246708290289793,73714576678984,74229978513600,74229978497216,187514111598627,141884261957768,114530269217091,144323840606400,106941481887778,114530269217091,153119933597768,10449680599176,74229978513600,141875672023176,141875672023176,10449680599176,36331145273378,10449680599176,10449680599176,141875672023176,141875672023176,141875672023176,141875672023176,36837959671968,141978752811168,141978752811168,141978752811168,106940407619618]
private def wheelRows6Page25 : Array Nat := #[46226905063521,36571663441954,46226905063521,46226905063521,149572370399361,151780017143937,142253634912416,151780017143937,12687509553537,12275186401569,114530269151298,73714576679016,106941481361442,144323840671936,143224329044160,153012674756897,114530269151298,114530269151298,114530269151298,151913163129121,151779882926209,12382445242440,73714574573640,141978753335456,141978753335456,212494597652610,212494597652610,73989452480584,151780017143937,141875672023176,151780017143937,149572236181633]
private def wheelRows6Page26 : Array Nat := #[149572370399361,141884262088842,73714574573640,73714574573640,73714576678984,141978752811168,73714576678984,73714574573640,143220017234112,149572370399361,141978752811168,141978752811168,141978752811168,143220017234112,74229978513600,144323840606400,143082576183456,143220017234112,144083318767752,143220017234112,212493523910786,211389700538498,211389700538498,144083318767752,143082576183456,73714576679016,144083318767752,73714576679016,149842957467840,211415470735496,144083318767752,151913163161760]
private def wheelRows6 : Array (Array Nat) := #[wheelRows6Page0,wheelRows6Page1,wheelRows6Page2,wheelRows6Page3,wheelRows6Page4,wheelRows6Page5,wheelRows6Page6,wheelRows6Page7,wheelRows6Page8,wheelRows6Page9,wheelRows6Page10,wheelRows6Page11,wheelRows6Page12,wheelRows6Page13,wheelRows6Page14,wheelRows6Page15,wheelRows6Page16,wheelRows6Page17,wheelRows6Page18,wheelRows6Page19,wheelRows6Page20,wheelRows6Page21,wheelRows6Page22,wheelRows6Page23,wheelRows6Page24,wheelRows6Page25,wheelRows6Page26]
private def wheelRows7Page0 : Array Nat := #[114530269151298,46226900852769,73714574573640,73714574573640,114530269151298,73714574573640,212494597652610,141875672023176,212494597652610,73714574573640,73714574573640,73714574573640,73714574573640,212494597652610,141875672023176,141978752811168,151780017143937,73714574573640,74264330387528,114530269217091,73714574573640,73714574573640,73714574573640,73714574573640,73714574573640,73714574573640,114530269217091,46226905063521,151780017143937,151780017143937,211692498215016,151780017143937]
private def wheelRows7Page1 : Array Nat := #[150089779841547,141875672023176,46226900852769,151780017143937,149842957467840,141978752811168,151780017143937,211666725978435,141978752811168,141978752811168,141875672023176,143625856485930,143625856485930,144083318767752,114530269217091,46226900852769,114530269217091,246738892390536,46226905063521,46226905063521,211416544477320,211666725978435,211666725978435,114530269217091,141875672023176,114530269217091,141875672023176,150774845833376,212494597652610,211666725978435,141978752811168,73714574573640]
private def wheelRows7Page2 : Array Nat := #[73714574573640,114530269217091,73714574573640,73714574573640,73714574573640,46226905063521,46226905063521,73714574573640,141978752811168,141978752811168,114530269217091,143220017234112,143220017234112,114530269217091,114530269217091,114530269217091,114530269217091,151780017143937,73714574573640,73714574573640,73714574573640,73714574573640,73714574573640,73714576678984,73714574573640,151780017143937,151780017143937,151780017143937,151780017143937,73714574573640,73714574573640,73714574573640]
private def wheelRows7Page3 : Array Nat := #[73714574573640,73714574573640,114530269151298,114530269151298,73714574573640,73714574573640,176486648782882,176486648782882,150089779841547,143220017234112,184899013345410,214452062928968,46226905063521,211390774280322,73714574573640,114530269151298,114530269151298,46226905063521,73714574573640,114530269216834,144083318767752,114530269151298,114530269151298,73714574573640,73714574573640,114767431928331,73714574573640,73714574573640,73714574573640,46226905063521,114767431928331,73714574573640]
private def wheelRows7Page4 : Array Nat := #[176486648782882,143220017234112,185165305381056,150089779841547,46226905063521,73714574573640,73714574573640,73714574573640,114530269151298,73714574573640,150089779841547,176478058782753,73714574573640,114530269217090,212623448637600,114530269151298,114530269151298,106941481361442,106941481361442,176478058782753,114530269151298,114530269151298,114530269151298,114530269151298,114530269217091,114530269217091,114530269151298,211666725978435,211666725978435,114530269151298,114530269151298,114530269151298]
private def wheelRows7Page5 : Array Nat := #[114530269151298,114530269151298,114530269151298,106941481361442,106941481361442,114530269151298,141875672023176,141875672023176,141978752811168,212494597652610,46626840314691,46626840314691,73714576679016,176068426367106,150089779709961,150089779709961,150089779709961,114530269217091,150089779709961,114530269217091,144177776066720,141875672023176,150089779709961,141978752811168,114530269151298,115080024965186,73714576679016,114530269151298,114530269151298,114530269217091,114530269217091,114530269217091]
private def wheelRows7Page6 : Array Nat := #[141875672023176,114530269217091,143082576183456,114530269151298,212623448637600,114530269151298,73714576679016,106941481361442,114530269151298,141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,141875672023176,211696791076936,211666725978435,114530269151298,114530269151298,114530269151298,114530269151298,106941481361442,106941481361442,184899013345410,46226905063521,211390774280322,211692496109640,73714574573640,114530269151298,114530269151298,107491237175330]
private def wheelRows7Page7 : Array Nat := #[46226905063521,106941481361442,73714574573640,73714574573640,106941481361442,114530269151298,212623448637600,114530269151298,114530269151298,46226905063521,106941481361442,114530269151298,106941481361442,143220017234112,106941481887778,185165305381056,106941481361442,46226905063521,114530269151298,211666725978435,114530269151298,114530269151298,106941481361442,73714574573640,176482354341930,73714574573640,73714574573640,149572370399361,176482354341930,246708827160705,114530269151298,141875672023176]
private def wheelRows7Page8 : Array Nat := #[114530269151298,144323840606400,106941481361442,73714574573640,211666725978435,74264330387528,212494597652610,151780017143937,212494597652610,151780017143937,114530269217091,73714574573640,73714574573640,73714574573640,73714574573640,73714576678984,73714576678984,73714574573640,211666725978435,151780017143937,211666725978435,74264330387528,141875672023176,149572370399361,114530269217091,246708827160705,114530269151298,151780017143937,114530269151298,114530269151298,73714574573640,73714574573640]
private def wheelRows7Page9 : Array Nat := #[73714574573640,106941481361442,114530269151298,114530269151298,151780017143937,151780017143937,73714574573640,73714574573640,151780017143937,151780017143937,114530269151298,114530269151298,114530269151298,114530269151298,114530269151298,114530269151298,114530269151298,114530269151298,74264330387528,73714574573640,114530269151298,114530269151298,114530269151298,73714576679016,106941481361442,73714574573640,114530269151298,106941481361442,149572370399361,149572370399361,149572370399361,149572370399361]
private def wheelRows7Page10 : Array Nat := #[73714574573640,46226900852769,46226900852769,73714574573640,46226900852769,46226900852769,114530269151298,46226900852769,46226900852769,114530269151298,46226900852769]
private def wheelRows7 : Array (Array Nat) := #[wheelRows7Page0,wheelRows7Page1,wheelRows7Page2,wheelRows7Page3,wheelRows7Page4,wheelRows7Page5,wheelRows7Page6,wheelRows7Page7,wheelRows7Page8,wheelRows7Page9,wheelRows7Page10]
def cubTag (k i : Nat) : Nat :=
  match k with
  | 5 => let j := i - 3; (wheelRows5[j / 32]?.getD #[])[j % 32]?.getD 0
  | 6 => let j := i - 116; (wheelRows6[j / 32]?.getD #[])[j % 32]?.getD 0
  | 7 => let j := i - 476; (wheelRows7[j / 32]?.getD #[])[j % 32]?.getD 0
  | _ => 0
def cubRows (word : Nat) : SixRows := ⟨Fin.ofNat 512 ((word >>> 0) % 256),Fin.ofNat 512 ((word >>> 8) % 256),Fin.ofNat 512 ((word >>> 16) % 256),Fin.ofNat 512 ((word >>> 24) % 256),Fin.ofNat 512 ((word >>> 32) % 256),Fin.ofNat 512 ((word >>> 40) % 256)⟩
def crossOK (g : Forest) (k i : Nat) : Bool :=
  let S := (stateSet g k i).toFinset
  let r := cubRows (cubTag k i)
  decide (S.card = k+1) && decide ((∑ s ∈ S, sixCost (readSix r s)) < sixCost (readSix r (targetOf g)))

def spanOK (g : Forest) (k start n : Nat) : Prop :=
  ∀ i, start ≤ i → i < start+n →
    nodeVerified g k i = true ∨ Impossible g.mode (targetOf g) k (stateSet g k i).toFinset

theorem spanOld {g k a n} (h : block g k a n = true) : spanOK g k a n :=
  fun i lo hi => Or.inl (block_at h i lo hi)

theorem spanSix {g k a n} (h : ((List.range n).all (fun j => crossOK g k (a+j))) = true) : spanOK g k a n := by
  intro i lo hi
  have v := List.all_eq_true.mp h (i-a) (List.mem_range.mpr (by omega))
  rw [Nat.add_sub_of_le lo] at v
  simp only [crossOK,Bool.and_eq_true,decide_eq_true_eq] at v
  exact Or.inr (six_cut (cubRows (cubTag k i)) v.1 v.2)

theorem spanMerge {g k a n m} (h : spanOK g k a n) (h' : spanOK g k (a+n) m) :
    spanOK g k a (n+m) := by
  intro i hi hj
  by_cases lt : i<a+n
  · exact h i hi lt
  · exact h' i (by omega) (by omega)

theorem forest_span (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : graphValid g prior = true) (rows : ∀ k ≤ top, spanOK g k 0 (g.levels k).1) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, Impossible g.mode (targetOf g) k (stateSet g k i).toFinset := by
  simp only [graphValid,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    rcases rows 0 hk i (by omega) (by omega) with ok|done
    case inr => exact done
    apply nodeVerified_sound g 0 i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact ok
  | succ k ih =>
    intro hk i hi
    rcases rows (k+1) hk i (by omega) (by omega) with ok|done
    case inr => exact done
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => col_sound _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact ok

theorem root_span {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : ∀ k ≤ top, spanOK g k 0 (g.levels k).1) (le : k ≤ top)
    (idx : indexedRoot g k i ws = true) : Impossible g.mode (targetOf g) k ws.toFinset := by
  simp only [indexedRoot,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←sameWords_sound idx.2]
  exact forest_span g top prior low geom blocks _ le i idx.1


theorem lower_span {g prior i hints} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : graphValid g prior = true) (blocks : ∀ k ≤ g.cap, spanOK g k 0 (g.levels k).1)
    (idx : indexedRoot g g.cap i (vars g.mask) = true) (hp : properB (targetOf g) = true)
    (ess : checkEssential (targetOf g) (vars g.mask) (graphPairs g.mask hints) = true)
    (all : (graphPairs g.mask hints).map Prod.fst = vars g.mask) :
    Lower g.mode (vars g.mask) (targetOf g) (g.cap+1) := by
  apply lower_impossible (proper_of _ hp) (essential_plain ess).1 (essential_plain ess).2 _ (root_span low geom blocks (Nat.le_refl _) idx)
  intro a ha
  apply essential_ok ess a
  rw [all]
  exact List.mem_toFinset.mpr ha


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof5_0 : spanOK g235 5 0 3 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof5_3 : spanOK g235 5 3 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof5_35 : spanOK g235 5 35 29 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel5 : spanOK g235 5 0 64 := (spanMerge wheelProof5_0 (spanMerge wheelProof5_3 wheelProof5_35))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_0 : spanOK g235 6 0 2 := by
  apply spanOld
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_2 : spanOK g235 6 2 52 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_54 : spanOK g235 6 54 62 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_116 : spanOK g235 6 116 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_148 : spanOK g235 6 148 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_180 : spanOK g235 6 180 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_212 : spanOK g235 6 212 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_244 : spanOK g235 6 244 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_276 : spanOK g235 6 276 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_308 : spanOK g235 6 308 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_340 : spanOK g235 6 340 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_372 : spanOK g235 6 372 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_404 : spanOK g235 6 404 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_436 : spanOK g235 6 436 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_468 : spanOK g235 6 468 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_500 : spanOK g235 6 500 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_532 : spanOK g235 6 532 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_564 : spanOK g235 6 564 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_596 : spanOK g235 6 596 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_628 : spanOK g235 6 628 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_660 : spanOK g235 6 660 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_692 : spanOK g235 6 692 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_724 : spanOK g235 6 724 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_756 : spanOK g235 6 756 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_788 : spanOK g235 6 788 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_820 : spanOK g235 6 820 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_852 : spanOK g235 6 852 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_884 : spanOK g235 6 884 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_916 : spanOK g235 6 916 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof6_948 : spanOK g235 6 948 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel6 : spanOK g235 6 0 980 := (spanMerge (spanMerge (spanMerge (spanMerge wheelProof6_0 (spanMerge wheelProof6_2 wheelProof6_54)) (spanMerge (spanMerge wheelProof6_116 wheelProof6_148) (spanMerge wheelProof6_180 wheelProof6_212))) (spanMerge (spanMerge (spanMerge wheelProof6_244 wheelProof6_276) (spanMerge wheelProof6_308 wheelProof6_340)) (spanMerge (spanMerge wheelProof6_372 wheelProof6_404) (spanMerge wheelProof6_436 wheelProof6_468)))) (spanMerge (spanMerge (spanMerge wheelProof6_500 (spanMerge wheelProof6_532 wheelProof6_564)) (spanMerge (spanMerge wheelProof6_596 wheelProof6_628) (spanMerge wheelProof6_660 wheelProof6_692))) (spanMerge (spanMerge (spanMerge wheelProof6_724 wheelProof6_756) (spanMerge wheelProof6_788 wheelProof6_820)) (spanMerge (spanMerge wheelProof6_852 wheelProof6_884) (spanMerge wheelProof6_916 wheelProof6_948)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_0 : spanOK g235 7 0 7 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_7 : spanOK g235 7 7 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_103 : spanOK g235 7 103 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_199 : spanOK g235 7 199 96 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_295 : spanOK g235 7 295 45 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_340 : spanOK g235 7 340 96 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_436 : spanOK g235 7 436 40 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_476 : spanOK g235 7 476 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_508 : spanOK g235 7 508 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_540 : spanOK g235 7 540 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_572 : spanOK g235 7 572 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_604 : spanOK g235 7 604 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_636 : spanOK g235 7 636 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_668 : spanOK g235 7 668 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_700 : spanOK g235 7 700 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_732 : spanOK g235 7 732 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_764 : spanOK g235 7 764 32 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof7_796 : spanOK g235 7 796 11 := by
  apply spanSix
  decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel7 : spanOK g235 7 0 807 := (spanMerge (spanMerge (spanMerge (spanMerge wheelProof7_0 wheelProof7_7) (spanMerge wheelProof7_103 wheelProof7_199)) (spanMerge (spanMerge wheelProof7_295 wheelProof7_340) (spanMerge wheelProof7_436 (spanMerge wheelProof7_476 wheelProof7_508)))) (spanMerge (spanMerge (spanMerge wheelProof7_540 wheelProof7_572) (spanMerge wheelProof7_604 wheelProof7_636)) (spanMerge (spanMerge wheelProof7_668 wheelProof7_700) (spanMerge wheelProof7_732 (spanMerge wheelProof7_764 wheelProof7_796)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_0 : spanOK g235 8 0 13 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_13 : spanOK g235 8 13 51 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof8_64 : spanOK g235 8 64 72 := by
  apply spanOld
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel8 : spanOK g235 8 0 136 := (spanMerge wheelProof8_0 (spanMerge wheelProof8_13 wheelProof8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof9_0 : spanOK g235 9 0 10 := by
  apply spanOld
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel9 : spanOK g235 9 0 10 := wheelProof9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelProof10_0 : spanOK g235 10 0 1 := by
  apply spanOld
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelLevel10 : spanOK g235 10 0 1 := wheelProof10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem wheelT : ∀ k ≤ 10, spanOK g235 k 0 (g235.levels k).1 := by
  intro k hk
  interval_cases k
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · intro i lo hi; change i<0 at hi; omega
  · exact wheelLevel5
  · exact wheelLevel6
  · exact wheelLevel7
  · exact wheelLevel8
  · exact wheelLevel9
  · exact wheelLevel10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 11 := lower_span (g:=g235) (i:=0) (hints:=16777299) (before_sound K219 V219) g235G wheelT (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K219 11 [(235,[]),(243,[67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V219 low235 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x433095a1cd00000000,0xff00000000ff00ffff])),(BitVec.ofNat 152 (word80 [0x410014a04d21212121,0x21212121212121212121]))),((BitVec.ofNat 152 (word80 [0x40db1a310400000000,0xff000000ffff00000000])),(BitVec.ofNat 152 (word80 [0x409b18310007070707,0x7070707070707070707]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x8c3a21c210000000ff,0xff000000ff00ff])),(BitVec.ofNat 152 (word80 [0x4322142100a0a0a0a,0xa0a0a0a0a0a0a0a0a0a]))),((BitVec.ofNat 152 (word80 [0x598fc00baa0000ff00,0xff00000000ffff00])),(BitVec.ofNat 152 (word80 [0x889c009a214141414,0x14141414141414141414]))),((BitVec.ofNat 152 (word80 [0xa2e48a4e1300ff0000,0xffff000000])),(BitVec.ofNat 152 (word80 [0xa264824e1258585858,0x58585858585858585858]))),((BitVec.ofNat 152 (word80 [0x920562644eff000000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0x920402044c60606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x2400141c70ffffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x80808080,0x80808080808080808080]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,11),(16,0,235,0,11),(1,0,250,0,10),(2,0,249,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(3,0,248,0,8),(33,0,218,0,8),(65,0,186,0,8),(66,0,185,0,8),(96,0,155,0,8),(0,2,25,224,7),(0,32,88,131,7),(35,0,216,0,7),(98,0,153,0,7),(129,0,122,0,7),(130,0,121,0,7),(160,0,91,0,7),(192,0,59,0,7),(1,32,88,130,6),(2,32,88,129,6),(32,2,25,192,6),(64,2,25,160,6),(128,2,25,96,6),(128,32,88,3,6),(0,64,33,154,5),(67,0,184,0,5),(97,0,154,0,5),(129,32,88,2,5),(160,2,25,64,5),(161,0,90,0,5),(192,2,25,32,5),(194,0,57,0,5),(131,0,88,0,4),(131,32,88,0,4),(224,2,25,0,4)]
def g251A : List (List Nat) := [[],[67],[96,81],[96,81,67]]
def g251D8 := limbs80 #[#[0xaa2c28879c5956154110,0x21c757559561443c6aca,0x617655110b9bc8acaaa2,0x644237f28c3aca8846fe,0xbc8aecaa2811bd95e117,0x2a8a054fe557655140ad,0x5b79161d5458276f22c3,0x81dd560a9ecad0eaa2c1,0x8727b0aaa6e0b0c6fe51,0x32cab82a91bf94603755,0xcaa56de45765c154d1fc,0x795e057655366f0bc0ae,0x59540f5cc2ac8b0281b3,0xf7728c0ac0a85ede4584,0x8b8ac15bf9460576542,0x4ef657845c560cdebaf,0x5955458737b28c2ee8b,0xd9ec0b00b2aa9e3d9,0x23605b8960e013c1c021,0x30d598a2d2534961101f,0x5728d4ce9191520e3d07,0xc08386d89a3320608b65,0x7c003c20101304509f07,0x3d871bc1f010c4384f0,0x6f0783f007b188cf07c0,0x46d17c1f00603745e0ac,0x746e0f82f07c01b83e0b,0x108ce0ac6f07c0c2c603,0x5f07c0c20542fc1f020e,0x8ce0b86f07c092c6b1b4,0x2c31b82e1bc1f004f14,0xf07c023c6d1782f0786f],#[0x3e1bc1b0bc01893e1b42,0x8731b42f07c083c5d178,0x485c2147d0a0bf07c0b1,0xf010b130542fc1f00144,0x304109f07c08386d1bc1,0x1270e0bf07c0a20191c1,0x805207f07c0843091a,0x2094c4f1071309b0fc1f,0x85193440cb62743f07c0,0xc04387e09c5f07c00785,0x10e08050901f073c1037,0x1bc1f008e068683fc1f0,0x4cd]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0xeb964581409bf845d910,0xeb564585419f7815d940,0xe3d6555161f355155161,0xb3f8159554d3d7555161,0xb3f855d954bb7815d954,0xf796554110ff16154110,0xbf98654110df97654110,0xdf97558110fb95458110,0xfb55458510bfb8558110,0xdf57558510ef56558510,0xdbd7655110f3d6555110,0xd7d7559510bf78159510,0x9ff865d5109fd8759510,0x9ff855d910dbf845d910,0xf3d6555140fb95458140,0xbbd8655140dbd7655140,0x9ff855d940bbf8559140,0xef96458150bfb8158150,0x9ff815d950b7f8558550,0xdbd54dc560bbf845c560,0xfb980551609fd85dc560,0xdbd8755160f3d5155160,0x9fd85dd160dbe8755160,0x9fd84dd5609fd81dd560,0xdbd54dc161bbf845c161,0xf3d75551619fd85dc161,0xf3d655c1549fd80dd561,0xbbf865c154dbd765c154,0xf3d8159554f3d8059554,0xfb7815d954bbf805d954,0xff98558110f3f855d954,0xfbd8459540ff98558140],#[0xff98158150dfd8759540,0xdfd815d950ff98458150,0xdfd755c560dff815d950,0xdfd755d160efd7559160,0xffd815d560bff815d560,0x824c09c000fff815d560,0x62160f606782b2114070,0xd0dd46722fd1608a144b,0xe4d424c11b88523f61d,0x2e9884bdc5b22bf950ca,0xf6677739d9bfcd986903,0x484a3591468704159fe0,0x1488a114eaa6892de933,0x15daade568cb1356baa0,0x19a82cea652b1a5848bf,0xe5754b9d9c74e076e136,0x17e046fe77d13dbde66e,0x70780445aa2390e984dc,0x3c0070e1606f168d83c1,0x161383c020248d087178,0x820fe003850a8338b46c,0x48a330dc2e0f001e381b,0x790174884f85c1e003c7,0x1e2084268cc370b83c00,0xe151b83c0858fc1e004c,0x48386e0f00240f102e15,0x13c1e0438648b1b83c08,0x6342783c00705c629b18,0x23c70802783c0870806,0x800e0c0d1062c1e8dc1e,0x62f078010870a06e0a2b,0x9118651b83c08383c7],#[0x8346e0031123707810e1,0x10f1b83c007e1c40283b,0x2f07808e198c1743f078,0xc45e0f00308e168c0ca,0x3c0870b46a283383c047,0x241c2fc1e00586065178,0x22c1c351b83c00bc3850,0xbc1e00661c28428dc1e0,0xe198c0de0f02160e188,0x707810e1a8ac6e0f001b,0xb4662f07810e1c1ac5a3,0xe1f83c0848401c2c401,0x1461c28502410e0f0212,0xa0cc2f07808e150bc1e0,0xc08813c4e2d0f83c00e8,0xf1418c5c3707810e1b83,0x1b83c0278a08e0f00324,0xc5c16181bc1e013c6c16,0x5e0f021c30370dc1e013,0xb0dc1e05141848370cc,0xda2f07808e181ac3026,0x1478b07e0f002f11170c,0x1423c1e04386a1707811,0x8509f07800f46244649b,0x1e003c323e1b83c00ba3,0x780c60683c68411a85c,0xda14218dc1e043c7217,0x64a02004c3f83c00992,0xc2109f0b83c00788070d,0xb0a8e0da330b83c0878,0x481e14168c430a70781,0xa0908707810e100dc1e0],#[0xc00ca38604f07810e0e8,0x51783c00ca3880902f83,0x20ee0f00402318401f0e,0x8e100fc1e003a121f161,0xf011c201842230df0780,0x344e0f0040231a2109e0,0x1f218a13e0f021c1d191,0x238549c49130ee0f003a,0xc41086c94451783c00c,0x44212c31008220e8622]]
def g251H9 := limbs80 #[#[0x8058554780002f14245,0x944704192b0c0000011,0x2660639b001e000010e5,0x80a,0x1c2502b014c000b0e00,0x0,0x93582589c8302ce50000,0x61a003c568b]]
def g251D10 := limbs80 #[#[0x9504439eb2aa9cf54554,0xa221fd58510ff2c0887f,0x40bfaec885fd75443dea,0x7bd64503deaa281fe581,0xebb2a1fe58150bfaeca0,0x5160f7aa8b05ff71582f,0xb05ff745837eb22c1ef9,0x6febb283fd58541bfeea,0xf95161f7aa8b0dff7058,0xeab0dff745877eb22c3e,0x443debb2a9ef5c154bfe,0x1ff58550ffacaa07fd65,0xfaeab07fd74583feb8ac,0x75587feba2c3ff5c161f,0x7f0600450320170007fd,0x12910e0f70dc0b909a0,0x1fa1db1c41a118a16b15,0xab29427525e243228211,0x834d3323172f82e12ca2,0xc264073ec3cd3aa38b36,0x360e0078d8d8583801e2,0xe0070d8380121c209e12,0x38a8d83801c38862a360,0x1c3c322e0e043878c182,0xe0e0071014318c138380,0x8d83801c308880ba362,0x801c34360e005870b8a2,0xfe2e0e007121a248d83,0x8c1d8380123090806a3,0x1c28988234760e0048e2,0xc122e0e011900b838020,0x70f0c8b83801c2a24327],#[0x80201c28a090862e0e00,0x1c34722e0e0080a0b83,0x887e0e0070c228c1f838,0xe0078e0b8380221c2890,0xd828b801c28bc8e14360,0x1c289088307e0e0070f0,0x8160e008878a1f838022,0x78c32118c8583801e3,0x8b83811c4030a612360e,0xd12409a322e0e0470c26,0xe0118ea22e228d83801,0x3b83801c3e4088862876,0x8e84c760e0080e24218a,0x6078e222183801c2e309,0x83801e423890760e0088,0x262219]]
def g251H10 := limbs80 #[#[0x931417d4395041003205,0x7c646040006a15b016b6,0x7000585703fc1ec05f91,0x400000510c8c4c04664,0x2ac04d070c070182a198,0x2885cd0b403bc49027a,0x41681f810124b82661a5,0x808988760eb230c5bc11,0xf2335061053c0dc1b910,0xe7436082236924b04a06,0x76b17318480205054461,0x12c0b6c84c2700880024,0xc7b1238080002c73c3e8,0x43a0000004083,0x6c9002f62200e3434000,0x9d160002495c0f000603,0x5f21ec31e15a460001e2,0x3500058eaa80024c0128,0xc]]
def g251D11 := limbs80 #[#[0x50ff503fd10ef953bd54,0x6e00ff587fd41ff583fd,0x1803c7a4c81d2b94819c,0xc608160c01c3048d082c,0x1a2c1803858d160c01c2,0x6830070f1230e830048d,0x70e187c180385200a28,0x220c786830]]
def g251H11 := limbs80 #[#[0x22b926c3831004282440,0x1c06f1bb0c8a031cd0f7,0xe04000318f2471,0x3815c0741eb25f0a58c,0x1508e1df12b200007163,0xd1092100009151f000e0,0x8a500a0b00041751a000,0xf2328b982000d1920d5,0x41310219e60940552600,0xd0e49fb94d14e86]]
def g251D12 (j : Nat) := if j=0 then 0xc2881840803ff else 0
def g251H12 := limbs80 #[#[0xc0123000000101004160,0x2180000bbe4,0x28800fac1c000040,0xb200002c400]]
def g251L : Nat → Packing
  | 8 => (28,4,6,0,0,11,0,g251D8)
  | 9 => (75,3,6,0,0,13,0,g251D9)
  | 10 => (39,2,6,0,0,12,0,g251D10)
  | 11 => (8,1,6,0,0,9,0,g251D11)
  | 12 => (1,0,6,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 9 => lookupWord 7 53 3 11 5 2 g251H9
  | 10 => lookupWord 22 101 6 13 7 2 g251H10
  | 11 => lookupWord 12 59 6 12 6 2 g251H11
  | 12 => lookupWord 3 31 2 9 3 2 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 19=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_19 : block g251 8 19 9=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 28=true := (@block_merge g251 8 0 19 9 g251P8_0 g251P8_19)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_10 : block g251 9 10 51=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_61 : block g251 9 61 12=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_73 : block g251 9 73 2=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 75=true := (@block_merge g251 9 0 61 14 (@block_merge g251 9 0 10 51 g251P9_0 g251P9_10) (@block_merge g251 9 61 12 2 g251P9_61 g251P9_73))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_2 : block g251 10 2 28=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_30 : block g251 10 30 9=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 39=true := (@block_merge g251 10 0 2 37 g251P10_0 (@block_merge g251 10 2 28 9 g251P10_2 g251P10_30))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_2 : block g251 11 2 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 8=true := (@block_merge g251 11 0 2 6 g251P11_0 g251P11_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P12_0 : block g251 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B12 : block g251 12 0 1=true := g251P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251T : checkedTables g251 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact (rfl : block g251 6 0 0 = true)
  · exact (rfl : block g251 7 0 0 = true)
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
  · exact g251B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := lower_forest (g:=g251) (i:=0) (hints:=16777299) (before_sound K235 V235) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K235 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V235 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_49539

open PEqualNP.Outside.L_meta_49539 in
theorem PEqualNP.Outside.L_meta_49539 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 0, 4, 3, 4, 0, 5, 1, 5, 2, 5, 1, 6, 2, 6, 3, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
