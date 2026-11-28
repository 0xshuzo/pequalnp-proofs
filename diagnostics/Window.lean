import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_36116.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_36116
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xfffffffffffffffeffff,0xffeefffffffefffffefe,0xfffefffefefcaa00ffff,0xfffffffffffffffffffe,0xffffffeefffffffeffff,0xfefefffefffefefcaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 2 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 3 &&& x 7) ||| (x 4 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[1,2]⟩,⟨.or,[0,1]⟩,⟨.or,[3,9]⟩,⟨.or,[3,6]⟩,⟨.or,[4,5]⟩,⟨.or,[6,12]⟩,⟨.or,[0,7]⟩,⟨.or,[5,7]⟩,⟨.or,[6,7]⟩,⟨.and,[14,11]⟩,⟨.and,[15,10]⟩,⟨.and,[13,8]⟩,⟨.and,[16,4]⟩,⟨.or,[17,18]⟩,⟨.or,[21,19]⟩,⟨.or,[22,20]⟩], 23⟩

theorem witnessMonotone : ∀ g ∈ smallCircuit.gates,
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  simp only [smallCircuit,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact ⟨Or.inl rfl,by decide⟩ | exact ⟨Or.inr rfl,by decide⟩

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
theorem witnessCorrect : ∀ x : Fin 8 → Bool, smallCircuit.eval (List.ofFn x) = target x := by
  decide +kernel

theorem witnessSize : smallCircuit.gates.length = 16 := rfl

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 4, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 13 sevenInputs.toFinset) (gates : List Gate) (o : Nat) (window : gates.length ≠ 15)
    (fit : ∀ g ∈ gates, (g.op=GateOp.and ∨ g.op=GateOp.or ∨ g.op=GateOp.not) ∧ g.inputs.length≤2)
    (correct : ∀ x : Fin 8 → Bool, (Circuit.mk gates o).eval (List.ofFn x)=target x) :
    ∃ (gs : List Gate) (out : Nat), (∀ g ∈ gs, (g.op=GateOp.and ∨ g.op=GateOp.or) ∧ g.inputs.length≤2) ∧
       gs.length≤gates.length ∧ ∀ x : Fin 8 → Bool, (Circuit.mk gs out).eval (List.ofFn x)=target x := by
  classical
  by_cases big : 16 ≤ gates.length
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
theorem g41P3_0 : block g41 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g41B3 : block g41 3 0 1=true := g41P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41T : checkedTables g41 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g41 0 0 0 = true)
  · exact (rfl : block g41 1 0 0 = true)
  · exact (rfl : block g41 2 0 0 = true)
  · exact g41B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g41G : graphValid g41 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low41 : Lower true (varsX 41) (graphGoal 41) 4 := lower_forest (g:=g41) (i:=0) (hints:=3) (before_sound [] baseKnown) g41G g41T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K41 := extendKnown [] 4 [(41,[]),(82,[16,67,101]),(84,[32,16,67,101]),(137,[117,101]),(193,[99,67,117]),(208,[64,16,33,99,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
def g43Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfdf00fff81fc7e3ffb,0xe01fff03f8fc7ff7c03f])),(BitVec.ofNat 152 (word80 [0x45c09245142904808b,0x81248a28520901170249]))),((BitVec.ofNat 152 (word80 [0xe6a8703ffe007fc7cd,0x50e07ffc00ff8f9aa1c0])),(BitVec.ofNat 152 (word80 [0x96a9b6d618b228112d,0x536dac316450225aa6db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb781ffffff8007f7,0x6f03ffffff000feede07])),(BitVec.ofNat 152 (word80 [0x235249820c0312204,0x6a49304180624408d492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100400400,0x4924082008008000924]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g43C : List ColumnInfo := [(2,0,41,0,4)]
def g43A : List (List Nat) := [[],[48]]
def g43D4 (j : Nat) := if j=0 then 0x1f else 0
def g43L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g43D4)
  | _ => emptyPacking
def g43I (_ _ : Nat) : Option (Nat × Nat) := none
def g43 : Forest := ⟨43,4,fun i => g43Y[i]?.getD (0,0),g43C,g43A,g43L,g43I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43P4_0 : block g43 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g43B4 : block g43 4 0 1=true := g43P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43T : checkedTables g43 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g43 0 0 0 = true)
  · exact (rfl : block g43 1 0 0 = true)
  · exact (rfl : block g43 2 0 0 = true)
  · exact (rfl : block g43 3 0 0 = true)
  · exact g43B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g43G : graphValid g43 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 5 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K41 V41) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K41 5 [(43,[]),(45,[33]),(85,[32,16,67,101]),(105,[48,97,33,80,66]),(116,[64,81,32,99,33]),(139,[117,101]),(153,[65,33,117,101]),(197,[33,115,67,101,84]),(202,[16,48,32,98,66,117]),(216,[64,49,32,97,33,117]),(225,[96,81,33,115,66,64,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V41 low43 (by decide +kernel)
def g51Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g51C : List ColumnInfo := []
def g51A : List (List Nat) := [[],[64,81]]
def g51D3 (j : Nat) := if j=0 then 0xf else 0
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
theorem g51G : graphValid g51 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low51 : Lower true (varsX 51) (graphGoal 51) 4 := lower_forest (g:=g51) (i:=0) (hints:=65605) (before_sound K43 V43) g51G g51T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K51 := extendKnown K43 4 [(51,[]),(53,[33]),(58,[48,32]),(60,[48,33,16]),(77,[32,16,67,101]),(89,[48,97,33,32,80]),(108,[48,33,16,100]),(113,[64,16,33,50,83,99]),(149,[65,33,117,101]),(156,[32,113,49,67,84,101]),(165,[32,16,116,100]),(172,[32,49,116,100]),(177,[64,16,33,50,83,115,99]),(180,[80,65,32,49,115,99]),(184,[64,49,32,82,114,98]),(204,[32,113,49,67,101,84]),(228,[80,97,32,49,116]),(232,[80,113,32,49,100,50,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V51 : Known true K51 := extend_ok (m:=51) V43 low51 (by decide +kernel)
def g86Y : Array (Bits × Bits) := #[(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g86C : List ColumnInfo := [(2,0,84,0,4)]
def g86A : List (List Nat) := [[],[100],[33],[33,100]]
def g86D4 (j : Nat) := if j=0 then 0x1f else 0
def g86L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g86D4)
  | _ => emptyPacking
def g86I (_ _ : Nat) : Option (Nat × Nat) := none
def g86 : Forest := ⟨86,4,fun i => g86Y[i]?.getD (0,0),g86C,g86A,g86L,g86I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86P4_0 : block g86 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g86B4 : block g86 4 0 1=true := g86P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86T : checkedTables g86 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g86 0 0 0 = true)
  · exact (rfl : block g86 1 0 0 = true)
  · exact (rfl : block g86 2 0 0 = true)
  · exact (rfl : block g86 3 0 0 = true)
  · exact g86B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g86G : graphValid g86 (boundsBefore K51) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low86 : Lower true (varsX 86) (graphGoal 86) 5 := lower_forest (g:=g86) (i:=0) (hints:=16843840) (before_sound K51 V51) g86G g86T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K86 := extendKnown K51 5 [(169,[16,80,114,50,64,99]),(195,[32,16,100,84,117]),(201,[16,48,98,32,64,84,117]),(209,[16,66,50,99,83,117]),(212,[33,113,49,83])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V86 : Known true K86 := extend_ok (m:=86) V51 low86 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,16,41,2,5),(16,0,43,0,5),(1,0,58,0,4),(2,16,41,0,4),(8,0,51,0,4)]
def g59A : List (List Nat) := [[],[48]]
def g59D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g59D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g59H5 (j : Nat) := if j=0 then 0xd0 else 0
def g59D6 (j : Nat) := if j=0 then 0x18989f else 0
def g59H6 (j : Nat) := if j=0 then 0x3480e000022dc00025 else 0
def g59L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g59D4)
  | 5 => (3,1,3,0,0,5,0,g59D5)
  | 6 => (1,0,3,0,0,0,0,g59D6)
  | _ => emptyPacking
def g59I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g59H5
  | 6 => lookupWord 1 11 0 7 2 1 g59H6
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
theorem g59G : graphValid g59 (boundsBefore K86) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 7 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K86 V86) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K86 7 [(59,[]),(61,[33]),(91,[16,67,101]),(93,[32,16,67,101]),(121,[48,97,33,80]),(122,[64,81,32,99,50]),(124,[64,81,32,99,50,33]),(157,[65,33,117,101]),(248,[64,49,32,97,82,114])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V86 low59 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff00ffffc3fff007fe,0x1ff0fffff85e060f00ff])),(BitVec.ofNat 152 (word80 [0xa0a05008800a05014,0x40220020980602111111]))),((BitVec.ofNat 152 (word80 [0xffff007ffc3ffff800,0x1fff0ff01cb4b9f00f00])),(BitVec.ofNat 152 (word80 [0x2c0c16050082c06058,0x81402042189431333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff80003fffffff,0xe0000fff23b56600f00f])),(BitVec.ofNat 152 (word80 [0x301018261113048260,0x984448021b064666666]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff,0xfffff000134bf800fff0])),(BitVec.ofNat 152 (word80 [0x40a0a0482224090480,0x12000904024988888888]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0xcea8c5ff0000])),(BitVec.ofNat 152 (word80 [0x80c0c07000380e0701,0x1c088e084628c4cccccc]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(2,0,105,0,5)]
def g107A : List (List Nat) := [[],[80,97]]
def g107D5 (j : Nat) := if j=0 then 0x3f else 0
def g107L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g107D5)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,5,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P5_0 : block g107 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B5 : block g107 5 0 1=true := g107P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact g107B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K59) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 6 := lower_forest (g:=g107) (i:=0) (hints:=83) (before_sound K59 V59) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K59 6 [(109,[33]),(115,[16,67,101]),(117,[32,16,67,101]),(229,[33,115,67,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V59 low107 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff00ffc3fffff007fe,0x1ff0fffff45e030f00ff])),(BitVec.ofNat 152 (word80 [0xa0a02880800a05014,0x40220020900603111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffff0003fc3ffff800,0x1fff0ff014b4f9000f00])),(BitVec.ofNat 152 (word80 [0x2c0c4b105092c46258,0x8940244214b4b1777777]))),((BitVec.ofNat 152 (word80 [0xfffffffc003fffffff,0xe0000fff2bb526f0f00f])),(BitVec.ofNat 152 (word80 [0x30100c006103008060,0x1844080299020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffffff,0xfffff000134bf800fff0])),(BitVec.ofNat 152 (word80 [0x40a090228224090480,0x12000904024948888888]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0xcea8c5ff0000])),(BitVec.ofNat 152 (word80 [0x80c0e00300380e0701,0x1c088e084628c4cccccc]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(0,4,137,32,5),(4,0,169,0,5),(128,0,45,0,5),(1,0,172,0,4),(8,0,165,0,4),(32,4,137,0,4)]
def g173A : List (List Nat) := [[],[48]]
def g173D4 (j : Nat) := if j=0 then 0x4fd5120 else 0
def g173D5 (j : Nat) := if j=0 then 0xc8404fd20 else 0
def g173H5 (j : Nat) := if j=0 then 0x2 else 0
def g173D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g173H6 (j : Nat) := if j=0 then 0x2 else 0
def g173L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g173D4)
  | 5 => (1,1,3,0,0,0,0,g173D5)
  | 6 => (1,0,3,0,0,0,0,g173D6)
  | _ => emptyPacking
def g173I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g173H5
  | 6 => lookupWord 1 2 0 4 0 0 g173H6
  | _ => fun _ => none
def g173 : Forest := ⟨173,6,fun i => g173Y[i]?.getD (0,0),g173C,g173A,g173L,g173I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P4_0 : block g173 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B4 : block g173 4 0 1=true := g173P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173P5_0 : block g173 5 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g173B5 : block g173 5 0 1=true := g173P5_0
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
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact g173B4
  · exact g173B5
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K107 V107) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K107 7 [(173,[]),(185,[66,117]),(205,[115,101]),(220,[64,16,50,98,117,82]),(241,[96,82,115,66,64,67]),(244,[64,16,82,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V107 low173 (by decide +kernel)
def g181Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ffffff003ff,0xff87ffc3545d520f83e0])),(BitVec.ofNat 152 (word80 [0xa0a80a209002a0a814,0x910008a445812318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffc000ff87ffffc01,0xfff87ffcd372a6007c1f])),(BitVec.ofNat 152 (word80 [0xc0310c402120c43118,0x8201210052302694a529]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x2c05002c20b00c020,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb02608b044c090241,0x30004c100907c94a5294]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc03800c00700e0381,0xc04470211aa6018c6318]))),(0x0,0x0)]
def g181C : List ColumnInfo := [(1,0,180,0,4),(4,0,177,0,4),(16,0,165,0,4),(32,0,149,0,4),(128,0,53,0,4)]
def g181A : List (List Nat) := [[],[66,117],[32,116],[32,112,64,84],[64,32,82,114],[64,82],[80,66,114,32],[80,114],[112,84],[112,82,66,64]]
def g181D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g181D5 (j : Nat) := if j=0 then 0xc1a0fd30fd10 else 0
def g181H5 (j : Nat) := if j=0 then 0x3 else 0
def g181D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g181H6 := limbs80 #[#[0xd01300b6000017b2,0x710099aace2500]]
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
theorem g181G : graphValid g181 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low181 : Lower true (varsX 181) (graphGoal 181) 7 := lower_forest (g:=g181) (i:=0) (hints:=132101) (before_sound K173 V173) g181G g181T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K181 := extendKnown K173 7 [(181,[]),(188,[32,16,113,49,67,84]),(236,[32,16,49,116,100])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V181 : Known true K181 := extend_ok (m:=181) V173 low181 (by decide +kernel)
def g203Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fff8fffd8b95000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x5012008488941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x807ff1fc2b1e600f0f00])),(BitVec.ofNat 152 (word80 [0x5882c0c1620a010b06,0x160a0411291e43333333]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0505802c222c08,0x182c48a01416b6666666]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x203000c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40400100000008888888]))),(0x0,0x0)]
def g203C : List ColumnInfo := [(1,0,202,0,5),(2,0,201,0,5),(8,0,195,0,5),(64,0,139,0,5)]
def g203A : List (List Nat) := [[],[96,49]]
def g203D6 (j : Nat) := if j=0 then 0x4e09f else 0
def g203L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g203D6)
  | _ => emptyPacking
def g203I (_ _ : Nat) : Option (Nat × Nat) := none
def g203 : Forest := ⟨203,6,fun i => g203Y[i]?.getD (0,0),g203C,g203A,g203L,g203I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203P6_0 : block g203 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g203B6 : block g203 6 0 1=true := g203P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203T : checkedTables g203 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g203 0 0 0 = true)
  · exact (rfl : block g203 1 0 0 = true)
  · exact (rfl : block g203 2 0 0 = true)
  · exact (rfl : block g203 3 0 0 = true)
  · exact (rfl : block g203 4 0 0 = true)
  · exact (rfl : block g203 5 0 0 = true)
  · exact g203B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g203G : graphValid g203 (boundsBefore K181) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low203 : Lower true (varsX 203) (graphGoal 203) 7 := lower_forest (g:=g203) (i:=0) (hints:=99) (before_sound K181 V181) g203G g203T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K203 := extendKnown K181 7 [(213,[64,16,33,50,118]),(217,[96,49,33,66]),(233,[112,81,33,99,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V203 : Known true K203 := extend_ok (m:=203) V181 low203 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff72ac9,0x182ea80003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044032080,0x180ca80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe03d528,0x15d8c201fc000fe03f80])),(BitVec.ofNat 152 (word80 [0x300b00500008235028,0x150840060c183060c183]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ce,0x83211e000007f000007f])),(BitVec.ofNat 152 (word80 [0x410c1160889000d84e,0x81201654a952a54a952a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8050058002e04804c4,0x2812b33870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774000007ffffc000])),(BitVec.ofNat 152 (word80 [0x26026011300880711,0x228300a142850a142850]))),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x38038021c01048913,0x424004c183060c183060]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(1,0,122,0,7),(2,0,121,0,7),(32,0,91,0,7),(64,0,59,0,7),(0,8,82,33,6),(8,0,115,0,6)]
def g123A : List (List Nat) := [[],[16,67,101],[80,97],[96,81,67]]
def g123D8 (j : Nat) := if j=0 then 0x2c6881bf else 0
def g123L : Nat → Packing
  | 8 => (1,0,3,0,0,0,0,g123D8)
  | _ => emptyPacking
def g123I (_ _ : Nat) : Option (Nat × Nat) := none
def g123 : Forest := ⟨123,8,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 1=true := g123P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123T : checkedTables g123 8 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g123 0 0 0 = true)
  · exact (rfl : block g123 1 0 0 = true)
  · exact (rfl : block g123 2 0 0 = true)
  · exact (rfl : block g123 3 0 0 = true)
  · exact (rfl : block g123 4 0 0 = true)
  · exact (rfl : block g123 5 0 0 = true)
  · exact (rfl : block g123 6 0 0 = true)
  · exact (rfl : block g123 7 0 0 = true)
  · exact g123B8
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K203) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 9 := lower_forest (g:=g123) (i:=0) (hints:=65603) (before_sound K203 V203) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K203 9 [(125,[33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V203 low123 (by decide +kernel)
def g189Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff722c9,0xc6ea80003f8001fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044032080,0xc0ca80a142850a14285]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfc003ffffffe03d52c,0x5d8c60000000fe03f80])),(BitVec.ofNat 152 (word80 [0x310b1050080823d12c,0x54840468d1a3468d1a3]))),((BitVec.ofNat 152 (word80 [0xffffc0001ffffad8ca,0x93211a01fc07f000007f])),(BitVec.ofNat 152 (word80 [0x400c0160809000504a,0x912012142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000804f6,0x691ab3fe000000003f80])),(BitVec.ofNat 152 (word80 [0x8050058002e04804c2,0x2812b33870e1c3870e1c]))),((BitVec.ofNat 152 (word80 [0x91711,0xa28774000007ffffc000])),(BitVec.ofNat 152 (word80 [0x26026011300880611,0x228304a142850a142850]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4e917,0x7e4005fffff800000000])),(BitVec.ofNat 152 (word80 [0x38038021c01048915,0x424004c183060c183060]))),(0x0,0x0)]
def g189C : List ColumnInfo := [(1,0,188,0,7),(4,0,185,0,7),(8,0,181,0,7),(16,0,173,0,7),(32,0,157,0,7),(128,0,61,0,7),(0,4,137,48,6),(0,16,41,132,6),(4,16,41,128,5),(20,0,169,0,5),(32,4,137,16,5),(36,0,153,0,5),(128,16,41,4,5),(144,0,45,0,5),(5,0,184,0,4),(9,0,180,0,4),(12,0,177,0,4),(17,0,172,0,4),(33,0,156,0,4),(40,0,149,0,4),(48,0,137,0,4),(129,0,60,0,4),(132,0,41,0,4),(132,16,41,0,4),(136,0,53,0,4)]
def g189A : List (List Nat) := [[],[66,117],[48],[48,66,117]]
def g189D5 := limbs80 #[#[0x509404836a5d54250120,0x483ca5515250120dab75,0x1cb70595408fb805d954,0x8185b54f033a]]
def g189D6 := limbs80 #[#[0x277b92caa07a94250120,0x9faebb12217edc15244,0x83f4a9280904fd72d951,0x20bf2eaa0241ee551404,0x482efb9aa2905fb75501,0x120b7ee8b0a419fd9551,0x44827ebb2a8906bd6455,0x91209feeab22413fdd95,0x425035eb2a84a04fd75d,0xd8940e7aa8a9281afd95,0x1545027ebaec4a06bd54,0x59540b7ee4aa281eedc,0xc165502f7b92caa05fb7,0x7259540dd8e4b2a81bed,0x5cb655027fb92caa06ef,0xd72d8154bdee4b02a93f,0x168a846200e85826004f,0x6832978b654269087634,0x2e9044a18fe783a9c8d6,0xa004b85aac95ea852a69,0x4012040000410318110,0x41c0068c042c00408102,0x59410000204003001001,0x5448200481c0040650,0x188100000081]]
def g189H6 := limbs80 #[#[0x73000000171000035000,0x28c00000000001,0x3420000388,0x4000005932000000]]
def g189D7 := limbs80 #[#[0xfd9510bfd8910b7d8d51,0xd9120bf59120fe50120b,0x5140bfd8940ef50940bf,0x154bfd9540bf59540ef5,0x20ff4c520ff54910bfd8,0xff58520ff54520ff505,0xff54940ff59120ff5512,0xf58d40ff54d40ff58940,0xd8154ff58154ff59540f,0x9c780ab0f614814800ff,0x49a7f482828df1872a04,0x37a6cccf58daeb592ab9,0x1e28a16124027c0ec1ce,0x8143850e1418a1c2e2c0,0xc092487c6009210c0c14,0x9308f1c793241c305480,0x21c992148a00a1c30506,0xc1149600e1c303039511,0x3864b101818008a258e3,0x4070c94182024872a48,0x6187051038606071454,0x8e0062c2401618380243,0x5090078840706490108c,0xe8843048226487c04828,0x11141d0a318687089921,0xca92448042a4912510a,0x14220]]
def g189H7 := limbs80 #[#[0xe876c002100080d02780,0x424c1844800094783e35,0x291a080000801c7e64b,0x44400000005c0000000,0xc35c5800105000000000,0x2046d866a1fc1df0a855,0x871947a01544c00fa47c,0xe5c00052b958000873c2,0x33c31c6043b40740bc2d,0x218c6b010c41d]]
def g189D8 := limbs80 #[#[0xd41fe98ff503fa41fd10,0x62a0d830007f553faa3f,0x26506222300a1e40fc6,0x8a100a24718f9648e108,0x8b1e280930a147484963,0x42038a02971658a08c81,0x1628212a330]]
def g189H8 := limbs80 #[#[0xc02d010112001000,0xc8b0000017679770a00,0x485e16e4e25800bb19,0x899d2ec30005f5fd0000,0x8d02fb281b9250c20007,0x50a97d8000b226cbda80,0x64820e00224a2f3,0x86000163000,0x71514622548394f1a00,0xa04e91c70000016100]]
def g189D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g189H9 := limbs80 #[#[0x28400000000000005,0x7ea24000000000000,0x1c8000000124003b4000,0x4040000880000,0x1a082c2801780000,0x31800010600,0x860000000]]
def g189L : Nat → Packing
  | 5 => (5,4,5,0,0,6,0,g189D5)
  | 6 => (33,3,5,0,0,9,0,g189D6)
  | 7 => (26,2,5,0,0,11,0,g189D7)
  | 8 => (7,1,5,0,0,9,0,g189D8)
  | 9 => (1,0,5,0,0,0,0,g189D9)
  | _ => emptyPacking
def g189I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 37 0 9 3 2 g189H6
  | 7 => lookupWord 11 59 6 12 6 2 g189H7
  | 8 => lookupWord 11 67 6 11 5 2 g189H8
  | 9 => lookupWord 3 59 1 9 3 2 g189H9
  | _ => fun _ => none
def g189 : Forest := ⟨189,9,fun i => g189Y[i]?.getD (0,0),g189C,g189A,g189L,g189I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P5_0 : block g189 5 0 5=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B5 : block g189 5 0 5=true := g189P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_0 : block g189 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P6_2 : block g189 6 2 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B6 : block g189 6 0 33=true := (@block_merge g189 6 0 2 31 g189P6_0 g189P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_0 : block g189 7 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_1 : block g189 7 1 11=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P7_12 : block g189 7 12 14=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B7 : block g189 7 0 26=true := (@block_merge g189 7 0 1 25 g189P7_0 (@block_merge g189 7 1 11 14 g189P7_1 g189P7_12))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P8_0 : block g189 8 0 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B8 : block g189 8 0 7=true := g189P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189P9_0 : block g189 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g189B9 : block g189 9 0 1=true := g189P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189T : checkedTables g189 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g189 0 0 0 = true)
  · exact (rfl : block g189 1 0 0 = true)
  · exact (rfl : block g189 2 0 0 = true)
  · exact (rfl : block g189 3 0 0 = true)
  · exact (rfl : block g189 4 0 0 = true)
  · exact g189B5
  · exact g189B6
  · exact g189B7
  · exact g189B8
  · exact g189B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g189G : graphValid g189 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low189 : Lower true (varsX 189) (graphGoal 189) 10 := lower_forest (g:=g189) (i:=0) (hints:=132099) (before_sound K123 V123) g189G g189T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K189 := extendKnown K123 10 [(189,[]),(252,[64,16,50,98,81,113,33])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V189 : Known true K189 := extend_ok (m:=189) V123 low189 (by decide +kernel)
def g221Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff7264,0xb70b2200000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403240,0x25032205145145145145]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d08,0x8e6670c0000000fc0fc0])),(BitVec.ofNat 152 (word80 [0x20642c828080823c08,0x8e4250638e38e38e38e3]))),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad87,0xb058468003f00000003f])),(BitVec.ofNat 152 (word80 [0x881302b0429008507,0x9058449a69a69a69a69a]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804c,0x6156adc0fc003f000fc0])),(BitVec.ofNat 152 (word80 [0x300400c000e040044,0x21142d8c30c30c30c30c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088131,0x10208010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800060820820820820]))),(0x0,0x0)]
def g221C : List ColumnInfo := [(1,0,220,0,7),(4,0,217,0,7),(8,0,213,0,7),(16,0,205,0,7),(64,0,157,0,7),(128,0,93,0,7),(0,4,137,80,6),(0,8,84,129,6),(1,8,84,128,5),(5,0,216,0,5),(9,0,212,0,5),(12,0,209,0,5),(16,4,137,64,5),(64,4,137,16,5),(68,0,153,0,5),(128,8,84,1,5),(13,0,208,0,4),(17,0,204,0,4),(65,0,156,0,4),(80,0,137,0,4),(80,4,137,0,4),(84,0,137,0,4),(129,0,84,0,4),(129,8,84,0,4),(137,0,84,0,4),(144,0,77,0,4)]
def g221A : List (List Nat) := [[],[64,50,118]]
def g221D5 := limbs80 #[#[0x551404c3c65515350130,0x4c3c65514354130e3965,0x5536354140e396455150,0xd8950f3380551515038e,0xb6785230602b9e0543,0x50400]]
def g221D6 := limbs80 #[#[0x3d4a1280987255450951,0xe6aa8a8a81ce5515050,0xc2fbb8a86904ed74d895,0x30f72a8a0261f654d404,0x4c37db2a80986f965501,0x130bf6eaa02617e5d540,0x4c3bcaa2a0987d94354,0x5130df6c8a8261be5915,0x544c27ebb2a8986bd645,0xd91309feeab22613fdd9,0xd425037db1aa0a04fd75,0x4d8d40e7aa8a9a81eb58,0xc1545027ebaec6a06bd5,0x7059540bf6e0b2a81eed,0x5cf655027fb9acaa06fb,0xd43d8950ddec4a0aa13f,0xedc1545439eaa286a86e,0x777055151eeae0aa2a3d,0x520d0160027eb9ec0aa7,0xfa370ce2e0aa2508e1e0,0x9263166541424d11e420,0x12811fe7c1ea711be6a1,0x8a9f2769a262932468a2,0xc48505c317140aaea82,0x7c508171f00504a60417,0x5c117040850117140800,0x442a261085c11703220c,0x804414050814105045c,0x10007020818042001c18,0x820404014040130d6361,0x4006010801812170c5c4,0x421705885c217040610],#[0x18]]
def g221H6 := limbs80 #[#[0xc30000d40000006b0000,0x0,0x6000,0x5200000000,0x50000,0xa60000000000,0x0,0x59c100000000000000]]
def g221D7 := limbs80 #[#[0x950951bbd8950eb50940,0x90a51dd55151f990951f,0x4530fe54130fe50130f9,0x130bf59130fd94530fd5,0x40fd54540fe54140bfd9,0xef55140bfd8d40fd945,0xdf55150bfd9540bf5954,0xfd8154fdd8151bfd8151,0x59130ff55130ff50d20b,0x9540ff58d40ff54d40ff,0x941ff50d50ff50550ff5,0xffd8154ff58154ff54,0x1ea314550880da164148,0x2834fc9d734e5a4a712c,0x3992af55b4ac540a5144,0x2542f7fef75d6b926eed,0xc784697165b49b90f196,0x19728164c7860078a312,0x548403c188794122a228,0xb0c32e39524451082834,0x20543c52129410c114c8,0x88c488c00e1411528425,0x81124d10b88543850450,0x150e14114243152e1172,0xc0982e3128e9c6c04a3,0x6485c30c0c097242920c,0x6451a28705146411a34,0x422838710303025c544a,0x21324446214831728443,0x64c9111a8518c64b9424,0x9096262421c1832488b8,0x85c22488b86383050]]
def g221H7 := limbs80 #[#[0x44760044261410102020,0x7ca01e0024d000119234,0xe2062900000040a45e47,0x1d42cd800b140000029,0x10c701c2ce8c000000,0x8c1119c26001c918b69c,0x17c5e4132003f1f52361,0x1c74311d92b1d213e549,0xf920008a2,0x1c41a0f8459a00280000]]
def g221D8 := limbs80 #[#[0xd30fe907f443eca3f551,0xa3fd41fe90ff543fa81f,0xd24b1e0a82a007f553fa,0xf8a01541b557aae4fa1c,0x88c24d14f88180554604,0x6488884c0099233d0108,0x74809638a13481094439,0x10b34c2046060a48e15c,0x83e280114c34795038c,0x238223e13451]]
def g221H8 := limbs80 #[#[0xb2420800b0243601143,0x1c0024b74400000008b,0x40dc178d000028c0000,0x43ce1c9fc141de3c1200,0xcd0002c3d4320499000a,0x18000c2ad742bc13,0xff3f48000000ba6003e5,0xa31210f0000011650ea8,0x31a44c43811e6f49bd64,0x200800a3088443497097,0x165]]
def g221D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g221H9 := limbs80 #[#[0x58dd4602,0x1f200000000000000000,0x2140000000000,0x6e000000022,0x62000000000000000000,0x41c0000000000000,0xd980000,0x352003a800000000000,0xc8000066000000000008,0x20a2df19,0x1f000000000000000000]]
def g221L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g221D5)
  | 6 => (38,3,5,0,0,10,0,g221D6)
  | 7 => (34,2,5,0,0,11,0,g221D7)
  | 8 => (11,1,5,0,0,9,0,g221D8)
  | 9 => (1,0,5,0,0,0,0,g221D9)
  | _ => emptyPacking
def g221I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 79 0 8 3 1 g221H6
  | 7 => lookupWord 12 67 5 11 6 1 g221H7
  | 8 => lookupWord 12 67 6 11 6 1 g221H8
  | 9 => lookupWord 4 97 1 9 4 1 g221H9
  | _ => fun _ => none
def g221 : Forest := ⟨221,9,fun i => g221Y[i]?.getD (0,0),g221C,g221A,g221L,g221I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P5_0 : block g221 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B5 : block g221 5 0 7=true := g221P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_0 : block g221 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_1 : block g221 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P6_5 : block g221 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B6 : block g221 6 0 38=true := (@block_merge g221 6 0 1 37 g221P6_0 (@block_merge g221 6 1 4 33 g221P6_1 g221P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_0 : block g221 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_6 : block g221 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P7_23 : block g221 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B7 : block g221 7 0 34=true := (@block_merge g221 7 0 6 28 g221P7_0 (@block_merge g221 7 6 17 11 g221P7_6 g221P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_0 : block g221 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P8_2 : block g221 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B8 : block g221 8 0 11=true := (@block_merge g221 8 0 2 9 g221P8_0 g221P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221P9_0 : block g221 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g221B9 : block g221 9 0 1=true := g221P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221T : checkedTables g221 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g221 0 0 0 = true)
  · exact (rfl : block g221 1 0 0 = true)
  · exact (rfl : block g221 2 0 0 = true)
  · exact (rfl : block g221 3 0 0 = true)
  · exact (rfl : block g221 4 0 0 = true)
  · exact g221B5
  · exact g221B6
  · exact g221B7
  · exact g221B8
  · exact g221B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g221G : graphValid g221 (boundsBefore K189) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low221 : Lower true (varsX 221) (graphGoal 221) 10 := lower_forest (g:=g221) (i:=0) (hints:=132099) (before_sound K189 V189) g221G g221T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K221 := extendKnown K189 10 [(221,[]),(249,[48,66,80,98,32,112])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V221 : Known true K221 := extend_ok (m:=221) V189 low221 (by decide +kernel)
def g237Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfff83ffc1ffffffa28,0xb40d0a0003f03f000fff])),(BitVec.ofNat 152 (word80 [0x508008400040f008,0x20010201041041041041]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fffe0ffe07590,0xe422f180000fc003f000])),(BitVec.ofNat 152 (word80 [0x416110500240827490,0xa40251934d34d34d34d3]))),((BitVec.ofNat 152 (word80 [0xffffc00000ffff25c6,0x93d84280fc0000fc003f])),(BitVec.ofNat 152 (word80 [0x980026084090001c4,0x92884086186186186186]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffff0000084d,0x6956a980000000ffffc0])),(BitVec.ofNat 152 (word80 [0x920024800092040801,0x4954a828a28a28a28a28]))),((BitVec.ofNat 152 (word80 [0x1171,0x18b1dc7f000fff000000])),(BitVec.ofNat 152 (word80 [0x1c020701081c080160,0x18b0884c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0xce93,0x4f80057ffff000000000])),(BitVec.ofNat 152 (word80 [0xe004380210e0100e13,0x45000530c30c30c30c30]))),(0x0,0x0)]
def g237C : List ColumnInfo := [(1,0,236,0,7),(4,0,233,0,7),(32,0,205,0,7),(64,0,173,0,7),(0,4,137,96,6),(8,0,229,0,6),(128,0,109,0,6),(12,0,225,0,5),(32,4,137,64,5),(40,0,197,0,5),(64,4,137,32,5),(68,0,169,0,5),(132,0,105,0,5),(192,0,45,0,5),(5,0,232,0,4),(9,0,228,0,4),(33,0,204,0,4),(44,0,193,0,4),(65,0,172,0,4),(72,0,165,0,4),(96,0,137,0,4),(96,4,137,0,4),(100,0,137,0,4),(129,0,108,0,4),(160,0,77,0,4),(196,0,41,0,4)]
def g237A : List (List Nat) := [[],[115,101]]
def g237D5 := limbs80 #[#[0x54930442f4615324c110,0x4427ce1d524c110f5153,0x60f524c110f5153d4930,0x4c110bd38254d30442f4,0xbd1839d530442f8e0975,0x5d6324427ce01754c910,0x442f8e0152509109f380,0xe017590910be38054a42,0x949109f183dc1524427c,0xbc9844c9304827ce0175,0x4c930483725d5324c120,0x482f2615324c120dcb75,0x54d524c120f894350930,0x54120d697554930483d2,0xb69854c950483d254d32,0x90950482da6163254120,0x4835adcd5254120b6985,0x6165254120b6b8354950,0x50d20b6980d4d52482da,0x8ef825d9534821fe1576,0xd8b524c21fe1574d8d20,0x4c3335cf62d4930e4d53,0xe0976d5130a6d85d8b52,0x50e328fb805d9544ca3b,0xf0d5350d5250aa761b54,0x615078031bd977254d42,0x496451f8e4662d138843,0xa4d087e3c1c8c65d2b94,0x693318cc05d2d14a9f4c,0x8813f1ecf075391bcd8,0xcbe1d,0x40800000004000000000],#[0x1000010,0x7610986000000000000,0x2]]
def g237D6 := limbs80 #[#[0x3e8a9a60887d1324c110,0xbe2e0292213d9da4244,0x427b3b0a4885d5731491,0x20ecea5292217cdc1524,0x483b4a92a0907c9324c1,0x543de2e2b00a51fdd564,0x2442fdb82a4884f570d8,0xc110fe2a4982213f5d76,0x30443f8b9260887f3524,0x4c910fe4ea98221fc5d5,0x632442fabaa64887d553,0x250910fcaa4a12217d5d,0x4a42442fbbaa84887e65,0x7054910beaeb21221f95,0x5d252442fbb9aa4887f3,0x57518910beaeb292217d,0xa50930482fabaec4885f,0xd9434c120fd2a498241f,0x7e5d530483eca9a60907,0x7e93254120bf6ea98241,0x1fa50950483f5192a090,0x7e95254120fd484a824,0x417edcd50483f5292a09,0x905f970d4520cfecaa8a,0xa41775cf51482f6b96a2,0x2904fd76d4520cfecba8,0x9241f354d32482efb9ac,0x64905ed754c920bdae89,0x192417b5d232483e6a1c,0xa84907ad4350920bdaeb,0xaa1241eb55142482f7b9,0xaa84906ef6550920ddac],#[0xcb212417bdd542482f6b,0xb82a4905ed7590920dda,0xaa6a9241fadc152482fd,0x7b9aa49076f5354920ed,0xdec8a9241bb59152482f,0x76b24a4905ef7454920d,0xbdaeb292417b5d252483,0x27ebb6a4905f970d4920,0xdbec6a1a417ddc54348,0x827ebb286906bd6450d2,0x209faeca9a41b758d534,0x482fab8ea6905f970d4d,0xd209faeda9a417b5cb53,0x34827fbaac6904ff7458,0x51209faebb1a413f5d36,0x54482fcb86a8906bd645,0x591209faedaa2417b5cb,0xd64482bfbaac89057c75,0x559120cf8eab22413fdc,0xcf644827fbaac89067f7,0x70595209faebb22413f5,0x5ca654827fb9aca906fb,0xd74d95209fae7b2a417b,0xb59542c83d6aa285904f,0xed6454b20bdaeaa1641b,0xaf59154c82f7ba2a5906,0x5ed72d53209faecaa641,0x13fdd165c827ebb6a990,0x86df654c930bbae89926,0x61bbd89424c2eebaa649,0x986bd6450930f3a86a12,0x2613fdd9524c3aea9aa4],#[0x49875d53d4930ddec5a9,0x12613f5db524c2eeb9ea,0xc4984fd74d8930dbaa7b,0xa1a61e7d51434c27ebae,0x2a6985dd7550d30dbeca,0x8a9a61b7d91534c2efb9,0xb6a8985dd73d5130bbee,0xe5b22613fdc9644c27eb,0xb92ca984fd75d91309fa,0xae732a617e5c2654c2f7,0xeb96ca984fd7699530bb,0xfee0b2e433f5d3654c27,0x6eb22a6995df7054d329,0xbbae7aa2653f5d9544cb,0xa7fb82c8994fd76d5132,0x29fee0b2a653fdd5644c,0xca7fba2ca996df735953,0x32f3ea8a1c65b750d608,0x8ca7ebb6a9196dd6550e,0x1429fee8b2c653fdc165,0x50b76a96c0a157f7558,0x81429fae7b0285af50f6,0x5250adfba2a4a14fd75d,0x54942f5a86a92857bdc1,0x25250bd7ba2a4a176d53,0x254d42f3aa6a1a857b5c,0xd76350a7eb86c6a15ef7,0x73d95429fae1b2a853f5,0xdc15290b76a92c1214fd,0xd73d81529fee0b2c857b,0x7d8d4354afbb8a86a94f,0xfd70d8d529fceca1aa5b],#[0x3fdc16594a7eba6c6a94,0x8813c0f00b406803c001,0xc2c028426822c1f01a41,0x3a436833c3203042f82d,0x6845c4504344183fc3e0,0xc4f04d44c84ac4904744,0x5a458857c56055452851,0x2860c5f05e45c85bc5b0,0xc6a069468866c6506346,0x73471870c6f06d46c86b,0xe87cc7b079478876c740,0xc86085483881c8108047,0x8e48c88ac8a089487886,0xc898c96093492891c900,0xca40a34a18a0c9f09e49,0xad4ab8a9ca80a74a58a4,0x38b2cb10b04af8aecae0,0xcbb0ba4b88b7cb60b54b,0xc24c08bfcbf0be4bd8bc,0xa8c8cc80c54c48c3cc30,0xcd50d44d38d2ccf0cc4c,0xde4dc8dbcd90d84d78d5,0xd8ebce90e74e48e2ce00,0xcf60f44f18f0cf00ee4e,0x14fd8facfa0f94f88f7,0xa909d08107506903d031,0xd1010f50e90dd0c10b50,0x18517915d15112511910,0x6925d2412051f91ed1c1,0xd2f12e52d92cd2a12852,0x48737935d3513253092f,0xa251e01488202a1080a9],#[0x80216e0e01489825a521,0x7825a5380200825a5383,0x21e0020c0b001e200048,0x482200800208202c31b1,0x888218b8814861e5211,0x80000460800200092822,0x60004000800008002000,0x28200102008410400,0x2020800a083020098200,0x20008000082000000820,0x80000a13084000020000,0x1e08006002000d182060,0x20c0800030200000282,0x10407421000000200080,0x282003020c08021a30,0xa083020030200000002,0x1820030200000000002,0x318200002007820,0x802a001000000028200,0xa82a0862b0a1018200,0x82002008400000080000,0x8a83058008a80040608a,0x40800a08a80042a0,0x10000000282000831204,0x21000a0820080060c82,0x1820000048200008,0x21802608008021000000,0xd422618004189840644c,0x20084c008102001828,0x4080080210182000000]]
def g237H6 := limbs80 #[#[0x46c1400000,0x21e000000000000000,0x0,0x34a000a1400000,0xa80000000075600,0x0,0xe2e00000000000000,0x3c5,0x6000000000000000000,0xe4f22d218007,0x80000000000000000000,0xca0e3,0x8a0000,0xc73a20,0x2ed800,0x32ad1112a0000000000,0xebb24000000000007440,0xe0800000001,0x1b20000000022884c00,0x24e68000000000000000,0xf36000004d8b,0x0,0x1d2800d0c00,0x28c8000000000,0x78400000000000000000,0xe76d3000001a0800000,0x0,0x2680000007b860000000,0x1081,0x5120000000000000000,0x3d080,0x32c000000000],#[0x0,0x14b00000,0x6230000000,0x20e00000000000000000,0x3820000000006d79f,0x2080000000000000,0xd03634000000000,0x73000000000000000,0x1ae800000c0000,0x7904be0000000]]
def g237D7 := limbs80 #[#[0xd58642af59321fc4c110,0x58c52bd58452be58052b,0x8910bdd8543dbd4a52b7,0x910fd8c910fd4c910bfd,0x10fd14910fd90910fd50,0xfd18910fd94910fd549,0xfd54b10fd50b10fdd891,0xb4c920fe54120fe4c120,0x90920fb50920fb8c920f,0x8d20fb94920fb54920fb,0x120bf59120bfd8d20bf5,0x20bfd9520bf59520bfd9,0xbf59320fb54b20fb50b,0xbfd8930f74c930bf5972,0xf59130f754d30f750d30,0x58321bfd9530bfd9130b,0x9132f754d32bf59721bf,0xe32bf58232bf59532bf5,0x42bf59632bf59232f750,0x2fb94942fb54942bfd81,0xbfd9542bfd8d42ef50d4,0xf59642fb54a42bf58242,0xd8d52bfd8152bf58052b,0x9652bf59252bf58252bf,0x520ff50520ff54910bf5,0x20ff58520ffd4520ff54,0xffd4920ff54920ff509,0xffd4d20ff54d20ff50d2,0xfd5120ff55120ff58d20,0x99520ff59520ff59120f,0x930ffd5320ff55320ff,0x930ffd4930ff54930ff5],#[0x30ffd5130ff55130ff58,0x2ff99530ff59530ff591,0xffd5232ffd5132ff5513,0xf54d42ff54942ff58142,0x58152ff59542ff58d42f,0x8552ff58552ffd8152ff,0xd52ff58d52ff50d52ffd,0x809607b052022000ffd8,0x18416214011e0ee0d30b,0xc62a427b2442061c81a6,0xb37d3623403252fc2e12,0x4cd48845841a3ff3dd3b,0xfa5d15a158655d5344fd,0x96f06ce69e66e64c61c5,0x8017d17af78676b74271,0xf68d48b289086083e815,0xe9d79ae98c97194191f8,0xad3abfaa4a82a59a29a0,0x90b75b61b46b2bb09ae7,0x6c32c10bf5be1bc6ba4b,0xccccb1c9dc82c67c53c4,0x90d7cd61d3fd1dd02ce7,0x7e63e33e11defdc6dabd,0xf04ef0edcec8eade92e7,0x641c0282881801052544,0x71048d0e1cdc10c40716,0x848d0e1891a1c3141840,0xc2840e124c3c0126c21,0x5444c960151132980544,0x5aa484d005291132580,0x2344992c020723450424,0x28e4c111c180a4782382],#[0x10d30a103844c2a0084a,0x7c400245806488700c9,0xf0c7c4802440a5c7864,0x2131f842c4848e011111,0x91e1850c3e009111891e,0xc6203c30406060092030,0x8086470090c101a2c23,0xe19182080478c4c79208,0x1c63c52e3c203040600,0x5e0090e261130098a101,0x3030048a18261130098c,0x1811240620220091020,0x826044018845805440c1,0xa90109100c14b1518863,0x42078a14203024050c14,0x982218c0028288143001,0x60180222130c00a91171,0xa8b1ca8418203030878c,0x4c6060210710386004c,0x9310985446440c101014,0xa93149c62254412343,0x90f0c78c0b019262110c,0x40071a2440e344861820,0x80c10140384121c68f1,0x181002478c0c0110c305,0x1c6891000d121c98a10,0xe2041810b08141083830,0x131e18e0888388890861,0x423ca07007841828f0e0,0x407890d1210c3c4303c2,0x9921e8c40c8c7863c684,0x3230a18d0a10f04b8f08],#[0x320243061880440a930c,0x818a900ca8d201901e24,0x480660497202122084a8,0x230a186462431a242108,0x182c326213243c6a0143,0x426284a1443434460988,0x6182a00cb8f401931a11,0x2424250208842181038,0xa8823]]
def g237H7 := limbs80 #[#[0x450f0a020100000009,0xa00001c07000a000f08,0x3c01080602010601010a,0x105860142602180c0104,0x1604260e000527072c06,0x121b030508dce20e4305,0xce742b07174da2370113,0xa384b95a60412d00efd0,0x85068cc1056843d38628,0xc68018000000659b8174,0xd0a000f328003584c3eb,0xd2782ff61fe01e38917e,0x48720006b0800148c18a,0x593cb2f7840492760884,0x2f7c000e2e2583564aa,0xc3dd9000097dc2100000,0xaa985167bfc2785f9786,0xc91098800000022c4407,0x403de3a29c0a3a22d856,0x562ef8ba185d4960ad8d,0xf0873af0b4800078ca8a,0x950770005701cac03183,0xd0000000123c44c689d4,0x1140009304d5fc8b6369,0x41852658a1607f3d3975,0x52e59c00002c24c4c49,0x10006ae44f14764b6d8e,0xfd2b0543e47800107fc8,0x702960003c4bf2b49324,0x2486ec655730000dd0,0xe2900000000004a00258,0xdc426e308ec0b0001034],#[0x121f74d3a312eb8c5eb1,0xade42766b803226d8800,0xe52196a90a9d57785405,0x4452dd943e379b9916f4,0x106a8daa7c9cd09db8ce,0xf1aa032a5a7012a35a1c,0x304ca9f426bec7b3fa18,0x4ba55cd112ac0914b02d,0x3c5b745835ea27b6a29,0x920c8bae241d62232ce1,0x8eb8a3853e51f26cea9d,0x8335163159d2e120e,0xd2c757422f3947aafcda,0x418170a111c091fc2b11,0x80ca504800dadc51318d,0x9822a12bfcc04aa41d94,0x4f1615c0474d23a8000e,0x13aa69bcea19000113e5,0x530ca9909a63009b2a0,0xc000f55849f8d1c2b208,0xfeadca8b4cec6c8a0c02,0xc00186f154804026487,0x3abc180000f4138,0xf4001e5e0007c108660,0x362a8c42a82,0x31f400087c4acf86c000,0x58f45b]]
def g237D8 := limbs80 #[#[0xf20fe907f443ee21f510,0x65fd31ff90ff487fa61f,0xbf8a5fe42fea17f8cbfa,0x780c001fd43ff297f54,0x2f4ae27c871d45a12033,0x202a1cd52645cff3a8cf,0x60e08051032c080ca228,0xd19200e28c21f18088c,0x50e40a3201470924004,0x1488818264029440e64,0x9034700438a347022219,0xb01218e31299b01510e1,0x3288818408049a38e09,0x2c09a4c0a8d01a48e209]]
def g237H8 := limbs80 #[#[0x5013d10000005,0x1a210a151101000d0512,0x52000448409372d0e,0x2408001109060b8f1720,0x10d9922dcdb5d71c604c,0xb55d2931951636d492dc,0xcbd5bd518bdf33167ad7,0xcc1768c000e8f93c3311,0x442bee14da12c01a3e54,0x80a8554b000dccb90c15,0x75765c22cb47e0a9083,0x76f32600086cba8bce00,0x8912de02f1351d136f5a,0xf000464e59165c1edb15,0x90f02f0000006635468a,0x10c3932ae2e000941948,0x470b000be556896ba1a3,0x15699ad0e83fd1191,0x6a9a992085ea25554f62,0x32520005347691003881,0x106566000adc63794e50,0x911c7635418428858e49,0x9cf6b018b907d609617,0x80d000e4fc0561bf4a34,0xe20005324c6000238743,0x81dde2700041f16e0a30,0x1b922133b000f9e000ec,0x23fb30002d20003b7000,0x945fcdaa3a50c92ba8ae,0x930c45aef2d643d70,0x944853350000bd1]]
def g237D9 (j : Nat) := if j=0 then 0x1882013f else 0
def g237H9 := limbs80 #[#[0x7180000000000224,0xbc0000000e9743000000,0x2613407001ea910cc9,0x3c00cb000f1400328000,0x4,0x22400000e39eb70b270,0xe00000,0x30108c00000080010b0,0x3a390c2400ba4000]]
def g237L : Nat → Packing
  | 5 => (41,4,5,0,0,9,0,g237D5)
  | 6 => (199,3,5,0,0,12,0,g237D6)
  | 7 => (112,2,5,0,0,12,0,g237D7)
  | 8 => (17,1,5,0,0,10,0,g237D8)
  | 9 => (1,0,5,0,0,0,0,g237D9)
  | _ => emptyPacking
def g237I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 14 307 3 11 6 1 g237H6
  | 7 => lookupWord 68 317 8 13 8 1 g237H7
  | 8 => lookupWord 39 179 8 12 7 1 g237H8
  | 9 => lookupWord 7 71 2 10 5 1 g237H9
  | _ => fun _ => none
def g237 : Forest := ⟨237,9,fun i => g237Y[i]?.getD (0,0),g237C,g237A,g237L,g237I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P5_0 : block g237 5 0 41=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B5 : block g237 5 0 41=true := g237P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_0 : block g237 6 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_13 : block g237 6 13 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P6_109 : block g237 6 109 90=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B6 : block g237 6 0 199=true := (@block_merge g237 6 0 13 186 g237P6_0 (@block_merge g237 6 13 96 90 g237P6_13 g237P6_109))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_0 : block g237 7 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_8 : block g237 7 8 61=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P7_69 : block g237 7 69 43=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B7 : block g237 7 0 112=true := (@block_merge g237 7 0 8 104 g237P7_0 (@block_merge g237 7 8 61 43 g237P7_8 g237P7_69))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_0 : block g237 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P8_2 : block g237 8 2 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B8 : block g237 8 0 17=true := (@block_merge g237 8 0 2 15 g237P8_0 g237P8_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237P9_0 : block g237 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g237B9 : block g237 9 0 1=true := g237P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237T : checkedTables g237 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g237 0 0 0 = true)
  · exact (rfl : block g237 1 0 0 = true)
  · exact (rfl : block g237 2 0 0 = true)
  · exact (rfl : block g237 3 0 0 = true)
  · exact (rfl : block g237 4 0 0 = true)
  · exact g237B5
  · exact g237B6
  · exact g237B7
  · exact g237B8
  · exact g237B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g237G : graphValid g237 (boundsBefore K221) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low237 : Lower true (varsX 237) (graphGoal 237) 10 := lower_forest (g:=g237) (i:=0) (hints:=1283) (before_sound K221 V221) g237G g237T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K237 := extendKnown K221 10 [(237,[]),(245,[96,82,115,67,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V237 : Known true K237 := extend_ok (m:=237) V221 low237 (by decide +kernel)
def g253Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe00007fc0000ff803,0xfe000881f04866324fbd])),(BitVec.ofNat 152 (word80 [0xa05028140a0502814,0xa000080900822124795]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff80001ff007fc,0x103319c081b84bb1f2])),(BitVec.ofNat 152 (word80 [0x68341a0d068341a0d,0x6101219c000a80a90f2]))),((BitVec.ofNat 152 (word80 [0x3fe0000003,0xfe20c41e0331c18c3e3d])),(BitVec.ofNat 152 (word80 [0x542a150a8542a150a8,0x5420040a0131c08c3828]))),((BitVec.ofNat 152 (word80 [0x1ff000000000007fc,0x307e00c3e01f03fc2])),(BitVec.ofNat 152 (word80 [0x381c0e070381c0e070,0x380104a0041a01f02d00]))),((BitVec.ofNat 152 (word80 [0x3ffffff800,0x1c3f8000fc001ffc000])),(BitVec.ofNat 152 (word80 [0xa150a8542a150a8542,0xa1c3a8000ec001610000]))),((BitVec.ofNat 152 (word80 [0x1ffffffc000000000,0x1fc00000ffffe000000])),(BitVec.ofNat 152 (word80 [0xc06030180c06030180,0xc0a400000be554000000]))),((BitVec.ofNat 152 (word80 [0xfe0000000000000000,0x1fffffff00000000003])),(BitVec.ofNat 152 (word80 [0x180c06030180c0603,0x11afb55200000000000]))),(0x0,0x0)]
def g253C : List ColumnInfo := [(1,0,252,0,10),(4,0,249,0,10),(8,0,245,0,10),(16,0,237,0,10),(32,0,221,0,10),(64,0,189,0,10),(128,0,125,0,9),(0,4,137,112,7),(0,8,84,161,7),(0,16,41,196,7),(0,32,208,13,7),(5,0,248,0,7),(9,0,244,0,7),(12,0,241,0,7),(17,0,236,0,7),(20,0,233,0,7),(33,0,220,0,7),(36,0,217,0,7),(40,0,213,0,7),(48,0,205,0,7),(65,0,188,0,7),(68,0,185,0,7),(72,0,181,0,7),(80,0,173,0,7),(96,0,157,0,7),(129,0,124,0,7),(132,0,121,0,7),(160,0,93,0,7),(192,0,61,0,7),(1,8,84,160,6),(1,32,208,12,6),(4,16,41,192,6),(4,32,208,9,6),(8,32,208,5,6),(16,4,137,96,6),(24,0,229,0,6),(32,4,137,80,6),(32,8,84,129,6),(64,4,137,48,6),(64,16,41,132,6),(128,8,84,33,6),(128,16,41,68,6),(136,0,117,0,6),(144,0,109,0,6),(5,32,208,8,5),(9,32,208,4,5),(12,32,208,1,5),(28,0,225,0,5),(33,8,84,128,5),(37,0,216,0,5),(41,0,212,0,5),(44,0,209,0,5),(48,4,137,64,5),(52,0,201,0,5),(56,0,197,0,5),(68,16,41,128,5),(80,4,137,32,5),(84,0,169,0,5),(96,4,137,16,5),(100,0,153,0,5),(129,8,84,32,5),(132,16,41,64,5),(137,0,116,0,5),(148,0,105,0,5),(160,8,84,1,5),(168,0,85,0,5),(192,16,41,4,5),(208,0,45,0,5),(13,0,208,0,4),(13,32,208,0,4),(21,0,232,0,4),(25,0,228,0,4),(45,0,208,0,4),(49,0,204,0,4),(60,0,193,0,4),(69,0,184,0,4),(73,0,180,0,4),(76,0,177,0,4),(81,0,172,0,4),(88,0,165,0,4),(97,0,156,0,4),(112,4,137,0,4),(116,0,137,0,4),(140,0,113,0,4),(145,0,108,0,4),(161,0,84,0,4),(161,8,84,0,4),(164,0,89,0,4),(169,0,84,0,4),(176,0,77,0,4),(193,0,60,0,4),(196,0,41,0,4),(196,16,41,0,4),(200,0,53,0,4),(212,0,41,0,4)]
def g253A : List (List Nat) := [[],[96,82,67]]
def g253D6 := limbs80 #[#[0x41fc054d425453150120,0x482bc5d9b2ca12a2a02,0xac0907e096558d535094,0x5158120acd76acc2c498,0x12a2b02415b2ecd96589,0x56554960482b65d9b30b,0xc9322b2ac0905e4bb368,0xd7a36456558120cd9746,0x3bb70aa92c298a41b165,0x1cfb361b925d951503c3,0xa39f64c3f26c0acaa05,0x2a151e6df96595415815,0x60543534b2f44c2302b0,0x1ac0a85c5bb368565dc9,0xd815d950d4d2cbd1308c,0xc92e898ac1473ec984e4,0x1494483018028b7dab0f,0xd6be725a422a11c57961,0xb40016c081000033b22,0x180c0d8001036040e8,0x1a0a080d0504000]]
def g253D7 := limbs80 #[#[0x504c3733965514154110,0x977258130d1ee5b76549,0x76156558f724c3479955,0x44366965e498458150e1,0x5150110dece594254540,0xa565485504437b396591,0x2f71a5d894154110ddca,0x54110fcc619545055044,0x6550550443f328655141,0x72a95954154110ddce59,0x110bdc69686505504437,0x58550443e71655896154,0xa66096154110f9c59582,0xf9c6896558550442ef3,0x950443c7976595625411,0x5958254110f1e5d96560,0x3ee59766095044367b96,0x44367b965958454110d,0x96554110ddc649915955,0x6978659541443c797664,0x4377153e416254510add,0x254510d7c5db90589514,0xb90589514435f376e416,0x3f386e416254510cfc61,0x85109fce8192d8d51443,0x589614436f163e41625,0x3a06496558510dbc5979,0x10b1fe999759552442ef,0x162442bf3a154f80589,0x65978058910afce8563e,0x97d69b9154f724438f97,0x72443c5d6558d53dc910],#[0x4d65dc910e1f6196554f,0xf69786595744421fda8e,0x442bf3a06098159510a5,0x8259510d3e5db9060965,0x1f90609654431f987e41,0x3fa1425453150120c7ea,0x50120fd454d514c54048,0x424c540483fa14258531,0xa9955093150120fe254d,0x120dea659424c5404837,0x54540483fa1425855150,0x965095150120deae4d42,0xdeae5942545404837a9,0x5404827dba3659515012,0x5096150120faa58d4258,0xaa59542585404837ab93,0x4837ab955096150120f,0xd4250120beae85535094,0x5955350940483f896354,0x83ba98654d4250120fca,0x250120eeae1953509404,0x953509404837a99654d4,0xfa9a654d4250120deae5,0x120beae995350940482,0x350940482faba158d425,0xba558d4250120faa5956,0x20beae856550940482fa,0x8940482faba359542501,0x654d6250120faa591535,0xf965956354d40483ae98,0x604836bb965915350120,0x853158120fb8589514c5],#[0xa595524c560483ee1625,0x48376b955493158120f9,0x3158120bba699524c560,0x59624c5604836e996589,0x3ec9535893158120dbae,0x58120f3a5d5624c56048,0x624c560483ceb7558931,0xeb955893158120dba655,0x120bbae95624c5604836,0x4c5604836e9985893158,0x6554d3158120dbae6162,0xf1e5d5654c560483e59,0x560482ee9a2d95315812,0x66131581209dee95984c,0xbe69b984c5604826fba6,0x483ee16258551581209,0x95158120fb8589815456,0xe5962545604836e99658,0x836eb935895158120dba,0x158120dba66162545604,0xd96545604836eb985895,0x7dba366151581209f6e8,0x81209bee999854560482,0x2605604826f9a6e61515,0xb935898158120eba60d6,0x20eba61562605604836e,0x5604836eb9558981581,0x454d4258120d9ee55656,0xdba6595350960483ea96,0x60483e69a15955258120,0x4d6258120f9a68d65549,0xa5955358960483ec9635],#[0x482ee9a654d6258120f9,0x6258120bbae995358960,0x956358960482eeba158d,0x2eeba550d6258120bbae,0x58120bbae85535896048,0x5358960483ec98354d62,0xeb9454d6258120ebae11,0x120bba6a153589604836,0x58960482eeba854d6258,0x8560d6258120bbae8583,0xbbae958358960483ae9,0x960482eeba1615625812,0x60d5358120bbae8d8558,0xba68b6454d60483e5965,0x482e79a5d915358120b,0x153581209bee999854d6,0xe556558d604826f9a6e6,0x8367b955958358120d9e,0x558120dba64991595604,0x59159560482edba36456,0x6e9936496558120f1e5d,0xc520f1e5d59359560483,0x258531483e6565549614,0x776549614c520ed9e155,0x20f35dd95358531483ce,0x8531483c7575595614c5,0x6615614c520b3de99755,0xe3dddb85585314838f77,0x31482cf5a5dd9614c520,0x15524c520e9b61965549,0xbddb855493148396d76e,0x482b6da6e15524c520e5],#[0x654c520adbe958654931,0x8d985953148387d865d5,0x30ff96e19754c5208f7e,0x4c520a5fe9586dd53148,0x76e15314830ff96dd985,0xd783d8d6154520a5fe95,0x520e3dddb8358551483a,0x58951482bcfa36194254,0x836436354520af3e8d86,0xcf3e0d92d8d514833db,0x1514831dd97e0f635452,0x61b7454520a77e8d865d,0x77e8d865d9514829dfa3,0x14823dfa36627654520a,0xd5258520a77e8d86dd95,0xddb9158d61483a6d65e0,0x8387d755978358520d3d,0x3d8520d37ddb93615614,0x79158d52483a5d8558d5,0xf4fa36456554920d9b59,0xd20b67e8d65dd143482,0x4dd9534831bd96e17745,0xd755978158d20c3fe199,0x20cf3e4d826056548387,0x56548355d75e4d81595,0x7e4d8159520c7761f936,0xa3fe9987605654831de8,0x504c3e596558d4254130,0x8d8254130f1e5d965509,0xe5d965609504c3e59655,0x4c367b965958254130f1,0x8254130d3ee5b7660950],#[0x958458d504c32fb96619,0x27eba26616454130f965,0x54130f1e5d965611504c,0x86611504c367b9659584,0xeba26518654130cbee59,0x130afae8984605604c2b,0x509604c3cbb755914258,0x75e516258130d3e65b75,0xd3edd792591604c34fb,0x1604c36e965e49845813,0xe498458130d7add79261,0xb659563e01424c33e985,0x1502bdba558f8050930e,0x9614c540b79e89765453,0xe8976e1531502de7a25d,0x297fa55db854c540a7b,0x64c540c7b61b925d9315,0x976585515031ef86e497,0x9cf83dc93254540b79e8,0x4540a77e8d86dc951503,0x25d9515031ed86e49765,0xfa25d96358540c7be1b9,0x40b3be897659561502ce,0x9561502c7da5dd965585,0x560f72d8940b3be89975,0xa7be8976e05635029efa,0x63502cefa25d96558d40,0x5d6558d40b1f69776595,0xbe8976e1563502cefa26,0x50339d84e4d8159540a7,0x8159540c7761f9360565,0x8987605655031de87e4d],#[0x29efa261d8359540a7be,0x59540d7a24b9061d6550,0x9261d655034fb96e4187,0xef96e498759540d3be58,0x940a6fe9191617765034,0x485605429fba065985dd,0xa95952158150d9ee5d65,0x9be69b974856054367a,0x560543c7965dc9315815,0x5954158150b9e6976250,0x9ee59655056054367996,0x543679975954158150d,0x54158150d9ee5d655056,0xe6165505605436799859,0x425f9a7e594158150d9e,0x1581509bee9997505605,0x598505605426f9a6e5d4,0x779a5e6141581509dee9,0x8150f9c5957158560542,0x75856054367997595615,0x97258971581509dee959,0x50b9e697625c560543ce,0xc560543c79655c971581,0x5d917158150d3ee59725,0xf1e595745c560542e79a,0x6054367965e517158150,0x957158150d9ee59655c5,0xee556260560542e7ba25,0x543a79656098158150d9,0x8158150d9ee556460560,0x958460560542beba2611,0x367965e518158150e9e5],#[0x58150dbae5d624c96054,0x974c96054367b9759532,0xb964dcd42581509be69b,0x150d3e65b7350960543c,0x58960543ce9735c96258,0xa560d6258150d3ee5373,0xd9e65574d8960542e7b,0x96054367965e45725815,0x5cd7258150f1e595735c,0x3ee99735c9605434fb96,0x543c79a15977258150b,0xd8258150f1e68d65dc96,0xe5d6450d60543a796560,0x426f9a6e5d4358150dae,0x3581509de6979850d605,0x9745cd60543cb9745917,0xcfba25937358150b3ee9,0x8150b7ae8984dcd60542,0x460d6054367b95591835,0x9656118358150afae898,0x50d9e5979460d60543a7,0xd9215428fda6e1d76485,0x561d724c550a7e682985,0xa3fe99875d94154297fa,0x415428fda6e1d7650550,0x617650550a7ee81985d9,0xfe99879d9415429f9a0a,0x542cf7a65c97158550a3,0x7258550c3f61f965c961,0x8d875c9615430ff87e59,0x25fba065d625c550a77e,0x4c950a7ee819261b7154],#[0x9161f625428fda6e1d76,0xfba065187d8950a5fe95,0x950c3fe5b865cd725429,0x605765430ff86e45765c,0x93e09815d950c77e4d82,0xd57e5493605765431df,0x5765434df9624d815d95,0xe4d815d950d57e579360,0x7761393605765434df96,0x65431df84e4d815d950c,0xb815d950d1fe5b956057,0xe9591e09765429fba060,0x8297fa5645879d95095f,0x24c560abe68298595215,0x5875c931582a7fa561d6,0xa7fa561d644c560a5fe9,0xc560c7b61f925d131582,0x75d1315831ef87e49744,0xf8564b754c560a5fe958,0x60abee81865954158317,0x9541582af9a0e1965505,0x5e1d6550560a9fe95875,0xa7be8974e0d71582a7da,0x715834ed65e49745c560,0x4585dc960c7be17925d1,0xfe9591617725829dfa36,0x582deba25d3805cd60a5,0x745cd60a7be8974e0573,0x17925d1735834ed65e49,0x29efa15d7825d160c7be,0xdd160a7be8d75e097458,0x5401b00028ffa664d85],#[0x4b0234114087033012c,0x41980c906002f415c099,0x109c048c2280f9078035,0x543181890b4054c29414,0xbf0d8069c34819b0cc06,0x7ec3d81e30ed075c39c1,0x231114087c43820d0ff0,0x9844b024f123090c474,0x28513e09e44e026d135,0xf0ad45642a31500a4451,0xb82d916b0b4c5a02c715,0x860bf45f42f11770bac5,0x6783331980c9c63c31b1,0x1c80e046cc35d1aa0d44,0x47503a51d10e7c738399,0x71ef0f547a43cf1e60ef,0x3488843520a10147e03e,0x9b249122490047723111,0x3ec9f04ef26a12fc9604,0x5792af150ca505192821,0x174cb885b52d9165cb10,0xc61b30317f4bd05d92eb,0x219d4cd865d32718fcc6,0xbc6c335d1a7cd2c68d34,0x8d1c5ce287113841bccd,0xe8873b39c1cd4e587233,0x3b41d94eb87533a81d34,0x4f3078f3c61e0cef4771,0x93db1eccf607ad3d51e8,0x44f907c53e11efcf787b,0xfb3fc1fbcfd87e93ed1f,0x6502c8134052004ffc7],#[0x85b429210d05c82b4142,0x225d11c88543e219d0bc,0x88bb45c22bd1588a344d,0x123651ac8d3465231d18,0xc8fd47d23dd1dc8eb47,0x98249d23c91b489243d2,0x2b49514a425152849394,0x4c225ed2f096f4b3258d,0x534499f4cb2635314987,0x14ec27553a49c94da269,0x4d494a3b50d282d3ec9e,0xa754329dd4dca6552e29,0xbed5e4ae95672b15560a,0xb6d5a62d0d668b195882,0x2f35764ba95cd2dfd6ec,0xc035fd2fdd7b8bd95eb,0xb32058d8c5d62a30b583,0xc8ce1666330d974cb164,0x9934759f8cf3675339d9,0xad0d5f6ab3535a88d3b6,0x6c9363db18d7d6ba35c5,0x5b84db96d8369db3cd9b,0x56f6378dbb4dcb6e4371,0x7dc2ce0d7053805bfcdf,0x4972338f5c68e3171438,0x9b5cd4e6172f3955ca4e,0xe9d74739fdcf8e797383,0x8389d64eaf7563aa5d40,0x10bb04078140c00a405a,0x39d04214e78188400cec,0xc4382ec220c8a04fe003,0xa0e42818004c08004840],#[0x20013020088a8384222,0x60223520f7044182055,0x510284154a0ef0481621,0x180a8383b0501802c185,0x58a3117064161a83828,0x300820055183a02dc11,0xc4b0085906080d06080,0xa080e820055020781541,0x1015c0484001e0550481,0x540ec18200008002e812,0xc183c040cc1820004021,0x2c18204c282000b020c,0x48b0a100a44b02170102,0x70609c28260e0810,0x10070608000060840400,0xa0102000908404024210,0xc1b0130007306081c040,0x450150008400090b0204,0x2c082018210100608,0x20412c2884581060000,0x210088403e0408000021,0xb30ae0414c2b0130006,0x821010060842c1d01500,0x106b062116041a848201,0x100f810340c0d0008408,0x8104b032046041884022,0x108409204b026041a84d,0x86800080a100806405d8,0x8818a1012062843c1,0x70780580024841c2e016,0x10100608460160009210,0x18058002601600040182],#[0x2e810401821010001821,0x8408106211a0410001c,0x21c1c8128107a040e00,0x61216810301c019a0421,0x8281821010c2f8105a04,0x2a10088402211e041492,0xe02418211706c0022840,0x5000641861080d706240,0x38241861080c1906084,0x430390608830200006,0x83a0008000828210a080,0xe08038200e080382001f,0x120c0e800241208000,0x20a0482000000000000,0x4a080008bc8484c,0xb0600210003030360008,0x402c1021c84ec106001,0x72137081d8182028483b,0x1820284820300f818208,0x21008001c081a060f8,0x20641839060800381820,0x18200108390a08000038,0xa080a8390a0e4082034,0x20741824120e42820019,0x80001b06080e040b800,0x603a04c100038002e00,0x2b8200003a0814013200,0xd8188430602940b40018,0x18ac10828a04c03c101,0x208028203d60a102b81e,0x10c100f02062080f0206,0x82100d00a805ac18ac00],#[0x8016081f084143060160,0x5822100c841432434c10,0x20c50290c50d302180,0x8224430400cb0360bc,0x915106443a82cc08a31,0xea0b705302268282314,0x840430803a08c55c2051,0x30840800003a081380ea,0x402018c402001f184c4,0xdb043300443dc08603b3,0x11430321321130690c50,0x101829bc1b000621090c,0x44a82982cc188086b04a,0x304d8603c080f0203c0c,0x8ba0a08c502000028494,0x57081c44a82982dc14c1,0x80103d04080002e0a31,0x2000002000080002000,0x2000082000d06010100d,0x150408050200e0a8e0,0x8200e08038200fb02100,0x200e08000e080f040803,0xe800206c10205008038,0xae0800ae081b04080d0a,0x401000e1000342820000,0x34282040ce070]]
def g253H7 := limbs80 #[#[0x3c3c2000000000014302,0x52400000b974da2d27d3,0x806d8800000ca002e881,0x2c000000000006b,0x266000000024f00,0x4000000083982001c400,0x291a43c70000050,0x90000000,0x8840000]]
def g253D8 := limbs80 #[#[0xa0a60887f04c9214c110,0x21f515354530443f2286,0x92150110f68b1ac2982,0x443e62a8a8a80887e85,0x4b9284a0221eb1645854,0xaa0887d85492154110ed,0xe716558550443e62a8a0,0x5354510e3cbb2caa8221,0x4237f28c3a64887555cd,0xa30ea92211bf9461d424,0x68846fe5187589108dfc,0xf9261d644422ff2ac3ac,0xdd5108efc9b0eb2a211e,0xb5285b8a809046fe5182,0x84a02417ab9550940483,0x6eae194250120dd4c32,0x650940482f532ca12809,0x120f54b22c4a02417ab9,0x2c8a12c0906ba6196250,0xb02416e99650960483d5,0xba6595258120f34b2aa4,0x89604839d2e6b12c0905,0xd75c22c4b0241ceb735,0xab12c0905bae51625812,0x241ceb75589604839d2e,0x64b6458120b75caac4b0,0x604838f2eab2ac0905ba,0x74c86c8b12416e992d95,0x3ac89043fe598754d20b,0x11bf94607764823df24c,0x56354130fa4a9264a826,0x4c38f2ecb2aa09879659],#[0xb2286b0261ec9624c960,0xc4a047be498759130f4c,0xef9261f6350395ac9b96,0x1581508f7c930fb2a811,0x2cf32bb12c0a869e5978,0xf06b02a1c7965dc96054,0xb059e6576458150d3cb2,0x434c9414863df24c26ea,0x8521f62b1a64b0a43f85,0xd3203b2c4997a9591425,0xc3b2656ad941d9624cad,0x7f458d214c11087fcc2e,0x48530443be6ec90a6088,0x10fe899282982217f396,0xc6a0a60885fce49414c1,0x82217f39650530443fa2,0xc5095150110bedc92c69,0x540443f62c8a8a80887e,0xfd8a12c2a02217f39654,0xb2280887ec5916150110,0x217bb95591404437770a,0xd92154110fb8b2a42a82,0x442fe72c90aa08877cd,0x9c9282a8221f71525055,0xaa0887dc5954154110bf,0xf715258550442fe72ca0,0x6154110bf9c92c2a8221,0x43ed2a4992a0887dc595,0x9aa4a8221f6962549504,0x8875edcd5254110ebcb,0xb7654950443af2eca92a,0x54110bbccb2a4a8221d7],#[0x7f730b12a0885dee5952,0xc6a822177995d8950442,0x879e5976354110f3cb2a,0x5d9150442ef32bb1aa08,0x110fb8c8acaa82217799,0x2ecb2aa0885dee496554,0xa8221d7b7659550443af,0xfce416250510bbccad0c,0x514144376f0ca1a82885,0x9fbcb30aa0a21bb7865,0xb12a2884fd657865051,0xa21f556354d51442fe72,0xe195354510ebbbb2a6a8,0x61443daac6992c2886dd,0xf9c82c4b0a21e7565549,0x92c28873d58f7258510b,0x15f595dc9614439eacbb,0xb814c9109facaf04b0a2,0x4427f720c3264884fd65,0xc82c4a92211fd96e1d32,0xa48855fe557354910bf5,0xfb90619524438faecb2a,0x589109fccaf00b12213,0x33f6edc02c48867e5db8,0x2c6b92211ff985d76244,0x8866f597845c910cdfc2,0x8659772442bef22a9ee4,0xc9108fecc2cbb92218fd,0xeb2dc0aa68847fe5985d,0x2b1a21e5d6558d534427,0x65fe177558d10cfbbb70,0x5d7634427f720c16c688],#[0x108fecaf04b9a211ff98,0x2bba2c88847fe5987551,0xa2211ff985d764442b7b,0xfe5985dd1108fecaf0cb,0x965442aff2abb2ca8847,0xa7fcb30eb2a2157d95dd,0xc16ca8847fe598759510,0x411fd95e09764427f720,0x95150120fd4a1262a02,0x483f5284b0a80907ea5,0x4b1a84a0241fa9535094,0xac0907ea5954250120fd,0xee96250560483dd2c498,0x6158120f74b12a2b0241,0x83dd2c4c0ac0907ba589,0x1ac4b0241ee965509604,0x907ba5956258120f74b,0x95358960483dd286b12c,0x58120f74c1ac4b0241ee,0xcf2caa9ac0907ba61562,0xcab02416f995d9160483,0x73ddd9614c520f74c92,0x6585514836df0aa92629,0x5209efc9b0ca8a41cf77,0xeeca92c29079b5955258,0xb0a41c7d75595614839d,0x3f6577658520a7fcb2ea,0x4b714835f2cac06c2905,0xcf6c32a5b8a41d6d655,0xb2ee29065f61565dc52,0xa41e6d6558d524823fb3,0x6577450d20cdfc2ee8a1],#[0x53482b7b2dba2869056f,0x3ebaacab1a418ff86dd9,0x3aca906be59580d8d20e,0x14fd96a1d654829ff2cc,0x921541308fecb702baa4,0x4c3af2a5b8aa0987da54,0xb12a4a82617db944c950,0xa09875e5d95254130fb4,0x7986549504c3af6eca92,0x354130dbdc32a4a8261b,0x2fb724b1aa0985f6e494,0x284b02617db9458d504c,0x985be6594258130f5cb2,0x65549604c3dd2c4a92c0,0x8130b7ccb2a4b0261e79,0xb286b12c0987b658d625,0x4b02616fb94589604c3d,0x5bee556258130e7dbaac,0xdc9604c2df329b12c098,0x30afccaee4b0261cf965,0x28b1ac0987b659163581,0x2616fb92591604c2fb7,0xee556458130e7dbaac8b,0x1604c2df325b22c0985b,0xb7cc96cab02617eb9261,0xb0a42985be6536558130,0x619df83dc9514c3daac6,0x9180d8530e6eb1ee4b0a,0x24c23fb31ba6c2986be5,0xcb2700a1261bd963e014,0x284984fe6578050930dd,0x3fb90619424c27f32dc0],#[0x6458930c7fc36eca9261,0xc35f2c8c06c4985be643,0xb303b92611fd98dd3624,0x49873759563dc9308ffc,0xd85597724c33bb0ab1ee,0xdc930c7ec32cbb926197,0x3ff2cc2ee49847f66165,0x8b1a613dd95e09634c2,0x865f61565dd1309eecaf,0x8597744c31fb0cb2ee89,0x130c7ec36cbba2611fd9,0xf2cc2ee89847f66365dd,0xbb2611ff9561b744c23f,0x7f657845d9308fecaf04,0xd931503d6ac8b0a62a04,0xf5ab22c2a8a815ef925,0xab22c2a057be49765454,0xa816bf955916150397ee,0xe17724c940af7c92ecb0,0x62502bdb2bb9264a067b,0xf6c2ee5b12819ed83dcb,0xb2c6a047fe5985dc940c,0x15ef925d965502bdf24b,0x98759540abecaeecb2a8,0x5029ff2cc3acaa057be4,0xb2a42b02a14fd96a1d65,0xc0a879e5953158150f3c,0x796558560543cf2caa0a,0x158150f3cb2ae2b02a1e,0x3cf2cac0ac0a85bee597,0x264b02a177b956056054,0xa879e5953258150f74b1],#[0x9650960543d72c8a12c0,0x8150f3cb2ac4b02a16f9,0xf6e6b12c0a87ba5c9625,0x4b02a16fb94589605439,0x79e5957258150b7cca6c,0x60960542df72cb92c0a8,0x50f5cb2286b02a1e7965,0xc9b9ac0a85bee5973581,0x2a1e796560d605439f2,0xee496458150bbdcab06b,0x160543d72e8b22c0a85b,0xb7dcb2e8b02a16f992d9,0xc22c0a85fae498458150,0xa11ff9761921543cf2ca,0x5187485509fdc830e90a,0x15427f321c1262a84efe,0xfcab0e98aa11fd97e093,0x282a84df657874c5509b,0x1fd97e19415423ff2ec3,0x82585509fcc8704b0aa1,0x42cfb2bb1ac2a847f65f,0x9b0eb0aa167d95d91615,0x2a84dfe5587585509efc,0xd8558f615426fb2bc3ac,0x5c5508fecc6e9b0aa1a7,0x1ff0d3b2e2a863fe1976,0xc7b8aa11fd98d8b71543,0x867be1d624c9508fecc6,0x7619325431ff0dbb264a,0x9509fdc830e992a11ff9,0xb2dc3a64a84bfe59874c,0xb12a137d95e05625423f],#[0xdf65783589508fecbf02,0x1d625423fb2fc1ac4a84,0x9fcc870eb12a13fb906,0xcc0ee4a863fe19765c95,0x2a15df93605765423ff2,0xe41825d950abfcab02bb,0x31582bdb2bb9242b057e,0xbfcab0e98ac197f85dd5,0x3a62b04bfe59874c5609,0x13fb90619415825fb2dc,0x9745c5609fcc870ca0ac,0x5834ff0ab2ae2b057be4,0xcaac4992c1aef8558932,0xc4b06be5978058960b77,0xbf8559143582df720b1a,0x650d60b5fcaac8a1ac1a,0x25ff2cc3a86b04fee418,0x2e8b9ac1af964e016358,0xb069fe15655cd60af7c9,0x75e09745835dacbc12e8,0xc121e7ab1ac3b82439ed,0xeeebc02c290c7fe5586d,0xdbaa43baf85591424873,0xf3d59161dc1318ffc830,0x61b70507d6ac8a12c298,0x618fecb70e992831ff95,0x2ab26e0b0c7fe5582dc1,0x92c31ff95613705869ff,0xbe5562dc132d6eb1f009,0xb714ca3ff2ac36e09957,0x8ffc8303baac51ff9061,0xa0a608847fe4183dd562],#[0x21fd96350930443fe2c4,0x895150110ff8b12a2a02,0x443f72c6a1280887fcd,0xcc9ec4a0221fb9655094,0xa80885fe6576250110bf,0xfb96559140443f72c8b1,0x2154110fdcca2caa0221,0x43fe2c4a0aa0887fc619,0x1282a8221ff362505504,0x887fc6194154110ff8c,0x16258550443fe50ca0aa,0x54110ff8c12c2a8221ff,0xff730992a0887fc61961,0xa4a8221f796550950442,0x87de60d5254110fbcb1a,0x258950443ef30ca92a08,0x110fbcb2ac4a8221fe98,0x6ecb12a08877e5d96254,0xa82217f99858950443bf,0xfe6636254110bfdcc2c4,0x950443bf2e6c12a0885,0xdfcc1b04a8221dfb736,0xcc12a0887de595825411,0x221dfb7660950443bf2e,0xe598254110dfcc3304a8,0x50442ff325b1aa0885fe,0xfdc9306a82217f998d8d,0xa2a0887de6195454110b,0x1f796559150443ef50ca,0x36454110bfdcc2c8a822,0x443ef2cac22a0885fe66,0x43308a8221bf98661150],#[0xa0885fee598454110dfd,0x799459550443ef324b2a,0x654110efcc32eca8221f,0x2ff724c32a08877e61b7,0x2ca90a217f992a195044,0x885fd64f6250510dfb4c,0x8658d41442feb2bb1282,0x510dfbc32caa0a21bf7,0xef0ca12a2886fda61655,0x4a8a21ff390589514437,0x77d5d96254510fbaa9ac,0x58951443beeecb12a288,0x10dfbc32c4a8a21bf586,0xcb22a2885fd64b63545,0xa21ef563589614437ef,0xd5d56258510f7ab2ac4b,0x561443beeeab12c28877,0xaffcb2e6a1221ef59259,0xb1aa48857fe597550910,0x21f759159552443cfaca,0x5d6554910ebecbacaa92,0x24437f2a7c02c48875fa,0xcb9f00b1221bf963e016,0x2c4886fe5978058910df,0xbf976e01624437f2ebc0,0x6358910bfbc8aa6b1221,0x439faecb1ac4885fde45,0xb2cab12215fd95dd1624,0x48857f65d6558910e7eb,0xd96dd562442bff2cbaac,0x58910affcaaecb12215f,0x3fae8c1ec48857f65776],#[0xe9b12219ff7460f62443,0x867f61774d8910cfec2a,0x859572442bfb2bba6c48,0x910eeeb1aa7b92219fe9,0xb0ca9ee48875f59553dc,0xb92215fd9654f724433f,0x7f61563dc910e7eb2ac7,0x9772442bff2ab1ee4886,0xcfecc2cbb92215ff935,0xcc2ee48867f64d85dc91,0xa215fd92dd9534433fb2,0xe597458d10edfba2c8b1,0x63442bfb29bb2c68857f,0xffbab05b1a219fd7560b,0xaac88876f5977459110c,0x19ff8659574442bff2cb,0x98159510cff4c2caba22,0x442ff720c12ca886fd60,0xc3b04b2a21cfd7660965,0xca8867fa1d8259510cfe,0xfd94a1d65442bfb29bb2,0x65d510afecb704baa215,0x2bfb25c32ea8857f6488,0x70cbaa219fd92e197544,0x9067f64985dd910cfeca,0x614c540483fe2a298a80,0x120ff4a9262a0241ff1,0xb2a698a80907fa589315,0x2a02417f9954c540483f,0x7fc5855150120bfccb26,0x54540483fd2c4a8a8090,0x20bfdc9aa2a0241f7953],#[0x2ca8a80905fe65951501,0x241ef96358540482ff7,0xe5956150120bfdc9ac2a,0x940482ff72ab0a80907b,0xbfdc8aa6a0241fe95358,0xa9a80907f658d5350120,0x41f796554d40483f72c8,0x195350120dfcc32a6a02,0x482ff32ca9a80906fee,0xdc8ac6a02417fb9654d4,0xa80907be5956350120bf,0x7fb9159540482ff72ab1,0x6550120bfdc9acaa0241,0x83fe2a298ac0907ee651,0x1262b0241ff1614c5604,0x907fa5493158120ff4a,0x9534c560483fd2c498ac,0x58120f7cb2a62b0241fd,0xbf2ea98ac0907bed9531,0x62b0241dfb754c560483,0x5fee553158120bfccaa,0x64c560482ff32c98ac09,0x120bfccc262b02417fb9,0x2caa0ac0905fee613158,0xb0241ff16154560483df,0xfa5095158120ff8c0aa2,0x4560483fd2c4a8ac0907,0xbfccb2a2b02417fb935,0xa8ac0905fee59515812,0x2417fb9854560482ff33,0x5956158120f7cb1ac2b0,0x604837f306c0ac0907be],#[0x7cb2b02b02417fb93605,0xac0906fe6158158120f,0x1fe95350960482ff72ac,0x54358120ff4a9ac4b024,0x482ff72aa1ac0907be59,0xb1aa6b02417fb9154d60,0xc0907f660d5358120fec,0xfb6454d60483df2c8a9a,0x358120dfdc22a6b0241e,0x2ff32ca9ac0907de5955,0x2a6b02417fb9654d6048,0x905fee615358120bfccc,0x6558d60482ff722b1ac0,0x8120bfdcaac6b0241ef9,0xf2cac1ac0905fee45835,0x6b0241bf98560d60483d,0x7be6456558120bfdcab0,0x59560483df326b2ac090,0x20bfdc8b0ab0241ef994,0x84a8a62905fee4d85581,0x8a41fe56254531483fca,0xddd1514c520efaba2a29,0x531483beaeca8a629077,0xdfac32a298a41df77654,0xa8a62906fde19514c520,0x417f79654531482feb2c,0x49614c520ff2a12c298a,0x1483fcac4b0a62907f95,0xaba2c298a41fd5535853,0xa629077ddd1614c520ef,0xef76558531483deacab0,0x614c520efabaac298a41],#[0x837eb0ab0a629077ddd5,0xaac298a41bf785585314,0x29077d5d9614c520bfbc,0xd5350931483beeecb0a6,0x4c520df6c2a8498a41fc,0xedacaa9262906fb61942,0xa498a41ded7654931483,0x6fb619524c520ef7bb2,0x6549314837df0ca92629,0x520bf7cb2a498a417ed9,0xaa6b1262907fae41624c,0x98a41ded7558931483f9,0xfb615624c520ef7baac4,0x89314837df0ab1262906,0xdf6c32c498a417ef955,0x8a9a62906fbe19624c52,0xa41ddd7654d31483bbee,0x619534c520eefbb2a698,0x314837bf0ca9a62906f7,0xfec32e898a419fd855d1,0xa2629067f617744c520c,0x19fd86dd131482bfb2bb,0x5654c520afecb6e898a4,0x4835fb0cb2a629075f5d,0xcc2ca98a415fd9759531,0x62905fe643654c5209fe,0xed92d9531482feb23b2a,0x54c520d7ec36ca98a417,0x27fb31b2a629057f65f6,0x2ea98a419fd865d53148,0x9057fe59754c520cffc3,0x86dd5314833fb0dbaa62],#[0xc520afecb6ea98a419ff,0xfeecc2a629067f5d9854,0xa98a413ff96615314833,0x67fddb854c520cfebb70,0x5d9314827fb2dc2a6290,0x20efdc82ec98a417fb90,0xcbb2629057fe55764c5,0x8a419ff865d9314833fb,0xd646764c520bfcc84ec9,0x931482fdb253b262905f,0x9fecc4ec98a415fd979d,0xbb2629057f657764c520,0x419ff86dd9314833fb0d,0x45864c520bfbc8b0c98a,0x14827ff2ac3262906fde,0xac8d0c98a417f990a193,0x262905fb64a864c520bf,0x5fd97a1931482fbb2743,0x864c5209fecc50c98a41,0x83fca84b0aa2904ff657,0x1ac2a8a41fe562585514,0x2907bdd8d6154520f7ab,0x793585514837ef06b0aa,0x54520efaba2c2a8a417f,0xbeaecb0aa29077ddd161,0x84a8a41df77658551483,0x6fb6194254520df7c1a,0x589514837df0ca12a29,0x520df7c1ac4a8a41feb9,0xf0cb12a2906fb6196254,0xa8a41afd8658d514837d,0xfe64363545209ffcc2c6],#[0x8d51482feb23b1aa2905,0xdefc1ec6a8a417ed92d,0xfb1aa2906bf61b635452,0xa413fd98d8d51482bfb2,0x5d38354520defc1ae6a8,0x514833fee9c1aa29067f,0xffbb706a8a419fd76e0d,0xa2a2904ff65b8354520c,0x19ff865d1514833fb0cb,0xb7454520cfec36e8a8a4,0x482bfb2dba2a29067fe1,0xc82eca8a417fb905d951,0xa29067f6197654520efd,0xf9909d9514833ff0cbb2,0x654520bfac8ceca8a417,0x2bfb2f3b2a2905fb64a7,0x6eca8a413fd989d95148,0x9067fe1b7654520cfec3,0x9361951482fbf26c32a2,0x4520defc9b0ca8a41bdc,0xf321432a2904ffe4d865,0xca8a417f591a1951482f,0x5df6568654520bf6c950,0xa1951482bfb2f432a290,0x209fec9f0ca8a413fd98,0x6a12c2907bb58d42585,0xa41eed65509614837df,0xb58d5258520df7c2a84b,0x9614837df06a92c2907b,0xf76b2ac4b0a41eed6358,0xa9ac2907b758d5358520,0x416fd9654d614839feec],#[0xd96358520bfbc8ac6b0a,0x14839feecb1ac29073f5,0xeba2c6b0a41ef79158d6,0xac29073fdd16358520e7,0xcff7558d614839faeab1,0x6358520d7fc2ac6b0a41,0x82dfb2bb1ac2905bfe55,0xa706b0a41cff7660d614,0x29067fdd38358520cfeb,0xd75e0d614835facbc1ac,0x58520cffbaf06b0a419f,0x9facaba2c2904ff65783,0xe8b0a419ff855d161483,0x67fe177458520e7eb2e,0x6595614839faecb2ac29,0x520f76c92cab0a41cff7,0xb2eb2ac2905bfe4d6558,0xb0a41cfe97595614839f,0xf7e4d8558520b7ec9eca,0x15614839feecc2ac2905,0xdfca9b01b0a413fd93e,0x6a9ec2906fb54d82d852,0xa41bdd8354f61483dbac,0x61553d8520ddec22a7b0,0x614839feeca9ec2906df,0xfec3aa7b0a416fd9654f,0x1ec2904ff66153d8520c,0x16ff9558f614835fb0ab,0x583d8520d7eb2b07b0a4,0x482fef22a9ae2904ffe5,0xcc2cbb8a41bbf8454d71,0x84905fbe456350920cfe],#[0xef9558d42483ddacab1a,0x550920bf7c8acaa12417,0x2fdf22b1aa4905fbe4d6,0xacaa9241f6d915955248,0x907fa54f8058920fb6c9,0x9154d62482fdf2aa1ac4,0x8920fe6b1aa6b12417ef,0xdb2ca9ac4906fbe11535,0x6b12417ef9654d62482f,0x7bb5956358920bf7c8ac,0xdd143482fdf2ab1ac490,0x20befc9acaa1a41dbd65,0x2dc2a869067f5db8550d,0x9a413fd95e19434827fb,0xf5db8154d20cffba702a,0x5534833feedc0aa69067,0xbfdc82eca9a413fd96e0,0xbb2a69077ee417654d20,0x419fd865d953482bff28,0x427654d20cffc32eca9a,0x3482fdb253b2a6905fe6,0xecaceca9a417dd939d95,0x2a69057f65e7654d20bb,0x5fd94dd9534827fb313b,0x8754d20cffc36eca9a41,0x82dff2cc3aa6905bf259,0xa702b1a419fd74e05634,0x6906bf5978158d20cffb,0xd75e05634835fecbc0ac,0x58d20cffbaf02b1a419f,0x3faedc0ac6904ff65781,0xe8b1a419ff76e0563483],#[0x67fe157458d20e7eb2a,0x5dd1634839facbba2c69,0xd20dbfc2acab1a419ff8,0xeecb2ac69073f5d96558,0xb1a416ff91595634839f,0x9fe156558d20f76c92ca,0x95634839fb2eb2ac6907,0xb7ec8ecab1a41cfe975,0xdc2ac6904ff6478558d2,0xa419ff76e15634833fae,0x657815cd20d7eb2b03b1,0x644827fb23c2ae6904ff,0xffc8acaba2413ff9560f,0x2ee89057fe4d655d120a,0x15ff9359774482bff22b,0xd8159520df6c1302b2a4,0x483afaeac0aca905f7e4,0x43b02b2a419fd8760565,0xca904ff64f8159520cff,0x7d7560d654837db06c12,0x359520cfec3b06b2a41d,0x27fb23c1aca9067fa1d8,0xf02baa413ff9160f6548,0x904ff647835d5209fec9,0x91e0d75482bfb27c0aea,0xd9209ffc8b073b2415fd,0xf73090aa0984ffe55839,0x2a8261f7952505504c2f,0x7de5498154130efcc16e,0x605504c37f304c0aa098,0x30fecc2264a82617fb92,0xc8a12a0987f658d42541],#[0x8261f7965509504c3f72,0xedd94254130efcbb284a,0x9504c37f30ca12a09877,0xbfccb284a8261bfb8650,0xa12a0985fee594254130,0x617fb98509504c2ff330,0x96254130fbcc32a4a82,0x4c3df2c8b12a0987fa6,0xccc2c4a82617fb945895,0x2a0985fee616254130bf,0xfd963609504c3fb286c1,0x8254130dfcc2304a8261,0xc3ef2cac12a0985fee51,0xb304a8261df976609504,0x986fe6198254130efdb,0x98458d504c2ff72cc12a,0x54130bfdc92c8a8261fd,0xff330b22a0987ee61164,0x8a82617fb98591504c2,0x87de5958454130bfdc93,0x6611504c3bf2ecc22a09,0x130dfcc3308a8261dfb7,0x724c32a0985fee598454,0xa82617fb94619504c2ff,0xfee498654130dfcc930c,0x19504c37f328c32a0986,0xf7cb1282b0261bfb946,0xa0ac0985fe661415813,0x261ef962605604c2ff73,0x5918158130dfcc1302b0,0x604c37f308c0ac0987be,0x7cb2a84b02617fb94605],#[0x12c09877edd54258130f,0x1ef965609604c3df30ab,0x58258130efdbab04b026,0x4c3df30ab22c0986fe61,0xbab08b0261ef96561160,0xc0986fe6158458130efd,0xfd95dc9414c2ff728c2a,0x258530defc1a84a8a615,0x37bf06a12c2987b758d4,0xf00a12619fd8650b714c,0x986fe5d78050930dfcb2,0x9058d424c37f2edc0284,0x930f6eb2ac6a1261fdb,0xbf2ab1a8498777dd5635,0xaa1261dbf75591424c2f,0x67f61b7550930e7ebb2c,0xdd5424c33ff0dbaa8498,0x30bfdc82eca12615fd96,0x2abb2849877ee4176509,0x12615fd95dd9424c2bff,0xf6577458930e7fbaac8b,0x7724c33feebc22c49857,0xcfeca30bb92619fd9161,0xc12c89867f65985dc930,0x619fd92617744c33feeb,0x4586dd130cfecb30bba2,0x15033fb2ac36e89867f6,0xbb92a298a81fb5425453,0xa62a07ed591514c540ef,0xdf77654531503beaeca8,0x614c540fdaa12c298a81,0x3f6ac8b0a62a077ddc9],#[0xb2c298a81df576585315,0x2a06ef619424c540efbb,0xd86dc931503bdee5b126,0x4c540edfbaac898a819f,0xf7f2ab2262a06efe1564,0xc898a81bbd8659131502,0x57f65b754c540ddfc32,0x6e15315033faedc2a62a,0x540affcaaec98a819ff7,0xf0cbb262a067f619764c,0x98a815fd95dd9315033f,0x7fe1b764c540cfec36ec,0x8551503beee4b0aa2a06,0xefabb2c2a8a81fb5645,0x4992a2a077ddd9615454,0xa81def72d8951503bdee,0x61b7254540cffc1ee4a8,0x515033ff0db92a2a067f,0xffc32eca8a819fd865d9,0x12c2a067fe1b7654540c,0x1bbf8350961503d7ac6a,0x54258540f5eb2a84b0a8,0x5039fac7b92c2a06efe1,0xb2ee4b0a819ff83dc961,0xc2a067fe177258540e7e,0xfd7658d61503d7ac8b1a,0x458540e7fbb2c6b0a81c,0x39faecb2ac2a07af5956,0x2cab0a81cff765956150,0xa073f65d6558540f5eca,0x95dd9615039fd2eb2ac2,0x940cfecc2cbb8a815fd],#[0x7acab1a84a05efe45635,0xaa12817bf9558d42503d,0x5efe4d6550940bdfc8ac,0x58f725027ff2ac1ec4a0,0x40e7eb2ac7b92815ff91,0x2ab1ee4a067f61563dc9,0x92815ff9159772502bff,0xf66165dc940affc9acbb,0x56350377ac9c0ac6a067,0xcffbb702b1a819fd76e0,0xb22c6a07af5956458d40,0x81b7f855956350377f0a,0xd96558d40e7ebb2cab1a,0x3503d7b28b2ac6a073fd,0xecbacab1a81e7f855956,0xac6a073fa5d6558d40e7,0x9ff76e15635033faedc2,0x8758d40afecaeecb1a81,0x2f7b29c3ac6a05fe643,0xaf0cb9a813fd96e15735,0xaa05f7e4d81595409fec,0xd876056550377b08c0ac,0x59540cff43b02b2a819f,0x3fb0ec1acaa06ef61183,0x8b2a819fe8760d65503,0x5fee418759540fddc83,0x261d65503bf720c3acaa,0x540ef7c930eb2a81dec9,0xb2dc1aeaa073fe598759,0x3b2813fd93e19755027f,0x7f64585dd9409ffcab07,0x17765033fb26c2eeca06],#[0xbfdcba42b02a19fd966,0x498ac0a87be589315815,0x2a1ef9644c560543bf6e,0xd894158150f7cb1282b0,0x60543ef2caa0ac0a87be,0xfdcb282b02a17f996505,0xac0a85fe65d4158150b,0x17f99850560542ff72ea,0x56158150bfdcc282b02a,0x543df2c4b0ac0a87fc5c,0xcbac2b02a1ef96458560,0xc0a87be5897158150bfc,0xf9725c560543df6c4b8a,0x158150f7cb22e2b02a1d,0x3bf2e8b8ac0a87bed917,0xae2b02a17fb945c56054,0xa85fee597158150fbcb2,0x8260560543df2c4c0ac0,0x8150f7cb2302b02a1bf9,0xf728c0ac0a86fe611815,0x4b02a1f7b9560560542f,0x77edcd4258150bfdcba6,0x58960543df2c6b12c0a8,0x50f7cb9ac4b02a1ef943,0xe8b12c0a87be60d62581,0x2a1ef974d8960543df2,0xe5cd7258150bfdc8ae4b,0x960543bf6e6c12c0a877,0xbfdcba86b02a1bf98360,0xb1ac0a85fee614358150,0xa1ef9645cd60543df2c8,0x517358150efcba2e6b02],#[0x543bf309b9ac0a85fee,0xcc2306b02a1ef96460d6,0xac0a85fee518358150df,0xfb974591605437f2e9c1,0x7458150bfccbac8b02a1,0x42ff72cba2c0a85fee45,0x3ae690aa1bf787585215,0x2a84ffe5d8348550cffc,0xe985d9215433ff0ebb24,0x485509ffcbb0c90aa19f,0xbeee4b0a62a84ff65b87,0xe498aa15ff9758931543,0x867fe1d724c550cfec3a,0x6dc9315433fb0db9262a,0x550afecb6e498aa19ff8,0xb2dba262a84ff65f824c,0x98aa15ff925d931542bf,0xfe6436250550afec96ec,0x8941542efb2bb1282a85,0xcfec3aeca0aa15fd97d,0xcbb282a867fe1d765055,0xaa19ff865d9415433fb0,0xa617650550cfecc2eca0,0x41542ff3213b282a867f,0xfecbceca0aa19fd879d9,0xb282a867f61b7650550a,0x13ff97619415433ff0db,0x987505509fecbf0ca0aa,0x5427fb2dc3a82a84ffe5,0xbb2e2b0aa1df5725c561,0xc2a873f5d96258550efa,0xfd875c961542dff2cb92],#[0x258550cffc3ae4b0aa19,0x33ff07b92c2a873f58f7,0x2c8b0aa13fd97e096154,0xa873fdd96458550e7ebb,0x96dd1615433ff0eba2c2,0x8550dfcba301b0aa15fd,0xfb0eba6c2a86df61574d,0x4b8aa19fd9461f615433,0x77b5c9625c550affcba6,0x58971542bfb2eb12e2a8,0x50bfcc86c4b8aa15ff97,0x2fb12e2a85df657625c5,0x8aa19ff835c971542bfb,0xfe59725c550cffc32e4b,0xd715433fae7c12e2a857,0xbbecaec6b8aa17f990d8,0xb9ae2a857f65f635c550,0xa19ff865d171542bff24,0xdb845c550cfebb708b8a,0x1542bff24bb2e2a867f9,0xec94ecb8aa19ff865d97,0xee2a867f61962dc550af,0x9fd9261b71542bfb25b1,0x624c950cfeca30db8aa1,0x433ff0ebb264a86fbe1d,0xc2ec992a13fe985d9325,0x4a84ffe5d864c950cff4,0xd97e05625427fb2dc3a6,0x58950ef6b9ae4b12a13f,0x3fb0eb9ac4a873f5d963,0xe6b12a19ff875cd62543,0x84ff65f8358950cffc26],#[0x1dd962542bff22bb2c4a,0x950cfec8b0fb12a15fd9,0xaedc0ae4a867f65187d8,0xb92a13fd96e05725433f,0x7fe19735c950affc8ae6,0xd972542bff22bb2e4a86,0xbefc9b02bb2a15ff935,0xc12eca85dfe55815d95,0x2a19fd8260576542ff72,0x24d815d950cffc1302bb,0x76543bbf26c0aeca8777,0xffc2302bb2a19fd84605,0xaeca857fe51815d950c,0x1cff9660576543aff2ac,0x3815d950cfec1702bb2a,0x542bff22c12eca857f65,0xc1b04bb2a19fd8360976,0xeca857f647825d950cff,0xfe98595215833fb22c3c,0x14c560f7ab12c298ac1a,0x2ff720b1262b07bd5916,0x2c498ac1afd865893158,0xb07bee41624c560d7fc3,0x95589315835ff0ab1262,0xc560d7ec3ac498ac16ff,0xfb0eb9262b06bfe1d624,0x498ac19ff875c9315833,0x57f657724c560cffc2ee,0x591315835fb0cb2262b0,0x60d7fc2ac898ac1aff86,0xeb2262b05bfe55644c5,0x8ac1aff87591315835fb],#[0xf61d744c560bf7c92e89,0x1315833ff0eba262b067,0xafecaee898ac19ff85dd,0xc2262b04ffe5d844c560,0xc16fd92d95315827fb2f,0x576250560afec96ea98a,0x1582bfb2bb9282b05bf6,0xec3ae6a0ac1afd8658d4,0xa82b067fe1d7350560cf,0xafd86595415827fb2fc1,0x6550560d7fc32caa0ac1,0x835ff0eb2a82b06bf61d,0x3aeaa0ac19fd875d5415,0x2b04ff65b8550560cffc,0xf95619415827fb2fc2a8,0x505609fecaf0ca0ac13f,0x7fb2bc3a82b04ffe5587,0xc4b8ac1cfd7358971582,0x73f5d5625c560d7fc1a,0x35c9715835ff0ab12e2b,0x560e7eb2ae4b8ac19ff8,0xf22a1ae2b067fe15725c,0xb8ac1cfd645cd71582fe,0xdfe55835c560cffc22e6,0xd71582dff2cc1ae2b05,0xcfeba706b8ac1afd64e,0xab22e2b073f5d5645c56,0xac1cfd655d1715835ff0,0xe41845c560cffc2ae8b8,0x715835facbc22e2b05fe,0xfecaf08b8ac19fd75e11,0xaae2b079fe15655c5609],#[0x17df9361571583aff0ab,0x56358960b7fcb30ab8ac,0x582dff2ab1ac4b05bfe4,0xc82e6b12c16ff9550d62,0xc4b05bfe457358960f7d,0xff955cd625839faeab9a,0x558960b7fc8aeab12c16,0x3bf720b9ae4b05bfe4d7,0xae6b92c15ff915cd7258,0xb057fe55735c960e7eb2,0x935d572582bff22baae4,0xc960cfec2a87b92c15ff,0xfb22c2ee4b057fe5543d,0xbb92c19fd93617725833,0x7af5d56450d60cfeca30,0xe1d435833ff0ebaa86b0,0x609fecaf0ea1ac13fd91,0xab22c6b06bf5938158d,0x9ac1ef964e01735835ff,0xf593815cd60efcba700b,0x1735833fae9c0ae6b06b,0xd7fc2ac8b9ac1cfd7559,0xba2e6b073f595745cd60,0xc1afd65e11735833ff0a,0x57845cd60cfebaf08b9a,0x4582bff28baae6b04ff6,0xfc9aeab22c16ff915d56,0xae8b057fe45755d160b7,0x9fd9161774582bff26ba,0x815d560cfec9b0bba2c1,0x82eff2ac0aeab05f7e4d,0xb306baac16ff96605755],#[0xab05fee41845d560b7fc,0xf955cd42d82dff2cc22e,0x58531affcaac7b82435f,0xfeb2ca12c298fed59142,0xc4b0a637f790589614c6,0x8dfde516258531f7ab22,0x65d9424c6bff20bb2849,0x931cffbaf00b12639fd8,0xaedc02c498cff6578058,0xb12639ff76e01624c73f,0xff6578458931e7ebb2c8,0x15624c73faedc22c498c,0x1cffbaf00b22633fd90e,0x5c2ac898cff643855913,0x2833ff9060a764c67fb2,0x61963dc141afecaec5b8,0x625079faecb1ac4a0e7f,0xfecaeecb12835ff955d9,0x1ac4b0ebf58f8058961a,0x55ff9158f7058b5ff08b,0x38158d62affcaac7b82c,0x22c00c80032000067fdd,0xd00520022c00ef005900,0x13c8086c03a601ac00b,0x39f01b100c9405d002ab,0x48047d02200103807a20,0xc0ac2052f027e8132c09,0x19c40c68060202e28164,0xc601d680e66070c035c8,0xe045082190102207c903,0x9d204d0025b8124c08d,0x6060abb053f02930141e],#[0x4c17ac0b9905ae02ca81,0x835241a020c980628030,0x742839a41c6e0e0506c8,0x7407a103c401dbc0eb70,0x81031080503f341f360f,0x226c110f0874042d8210,0x8ec23fc11d708d2845cc,0xa04bb4258c1294093684,0x9ee04ea826f01351098,0x5700a8e8532828d8143a,0x9a16850b24057d42b5a1,0xc2fae179a0bb405cd82d,0x6554321a18ba0c390607,0x3d86924344419f00cdf0,0x50dac86c9c35ea1aad0d,0x1c690e1086f90374e1b7,0xaf21d520e8a873b83962,0x843d321e460eff077043,0x80043f301f660f9a07b,0xaf083d4415a207b101f,0x6e11238885443c621a61,0x423ba11ae08c24454022,0x4a4424f0124e89128480,0x9fc4c4225d912c30957c,0x909ed44e5626f9135e09,0x14aa0a3545146282f13f,0xabc153f8a8dc542029b2,0xb62c1315e58ae0c55dc2,0x85ae02d3e16758b26058,0xbcc05da42e7417160b73,0x620c1c460682fec17c70,0xa18dc0c6186292310118],#[0x32b2193a8c8e0642231e,0x84a33d219d00ccdc65f4,0x5069ae349a1a398d1306,0xd79c6b6a35831aa88d4,0xb970db6c6d26364b1b07,0x541c110df946f50376b1,0x439481c858e338712238,0x75343a681d0a8e6dc72f,0xf8477483b721d950eb88,0xe8f3ac79883c711e1a0e,0x1ef80f7507b443d701e8,0xf211f720fa707ca83e17,0xba402b1fe10fde87e903,0x827640f320559021080,0xb94853a425520fb9069,0x3c910f087bc43a121a19,0xb22c7114ec8a1244d722,0x46d5233b919148c1045c,0xbc482c23ec91e448e66,0x209328492b2482122989,0x12e5896864ada2543928,0x63d1312098164bef25e4,0xed26c7934f09a2a4cd82,0xc4ec0273c138ec9c284d,0xa0664feb27e213df09e3,0x5e8a26450ea285694218,0xf94908a42051de28d614,0x29ca14d5ca5f252b1293,0x4db2a4f151b0a85e53f2,0x2e55f02ad415554aa465,0x8ae6e57102b7495a00ac,0x60f0b02a57c22bc815d7],#[0xb6964ecb1e658ab2c421,0x72d67969f0b410599f2c,0x5bea2dd696dc0b6925b1,0x9f45cc82e2f970e0b838,0x78bb585d852ea997484b,0x179e8bc905e2c2f08177,0xffc17ec0bea45f0a2f6c,0x1e307618290c0e460402,0xe623330ea9868cc2b661,0xc6c86327318018ab4c49,0x280c8dc643131f498e58,0xc99548ca406504326919,0x331b19810cbba65b632b,0x6f9336399aaccd08665d,0xa467ab33b719cf0ce2a6,0x8d11e685d341019fe4cf,0xa5a0d282692534799a2d,0x3c1a8ecd3fc69c134cd1,0xd35a01ac38d5ce6ab535,0x6c2435f91af2cd7486b7,0x9fa6cc0364c9b1c8d896,0x8cdbe26da936b61b4e8d,0x1bb80dd726e9d37301b8,0x7c69bdc4deaa6f2e377e,0x1937f91bf2cdf5e6f9e3,0x270b538419c19ce05470,0xe332716738a59c464e1a,0x99ce454720e38f91c758,0x59cc90e5fa72c0394c9c,0x39f39cf00e71c737239a,0x4f73a629d24ce8c27419,0x5e75723aab1d4bcea267],#[0xcec9676243b041d758eb,0xdc64eda276b53b471d99,0xee1df00ef3277673ba01,0xa3c471e170f06a78193b,0x795c3ca01e464f1b878a,0x3fc79e23cd29e650f2f0,0xcf5ce7a9f3d3c1e8ecf,0x1ee50f6f07b463d951ec,0xe311f0ecf8287bed3de3,0xd83e589f280f91e7c733,0x67d323e8b1f414f9d27c,0xfb7c7dad3ebd9f5a8fa8,0x8a4fc1a7dfc3ef01f710,0x49f9e0fcce7e403f1d1f,0x3f9d9fbf8fd827eb03f4,0xfc73fd59fe68fefc7f62,0x4e8016400820028ffdc7,0x500ec804f401f200b500,0x43501e280e040622027,0xdd2062102d88145409a2,0x84130a0891041081e140,0x832f417ea0b2d055e828,0x7ce83d641dd20dc906d8,0xa9091c845c421aa10390,0x214c10a1284e24258212,0x2f4216d90af2856842a6,0xd7434d219750c5685f94,0x2875d43a0a1cc10dfc86,0xfd287d843de21e550ef,0xa1104488114405a1fe9,0x52228d112488764427a2,0x44c3a258112728907446],#[0xa344501227f113c089b9,0x968a994544229dd14b68,0x116ce8b35458722bc915,0x2f1d176c8b9a45c4a2de,0xe22fd517de8bde45e6a,0x24640a31c118be8c4346,0x8d0d4678a32fd19308c9,0xb748d9e46c1235411a68,0x191c6a8e0e46fea37591,0xa3aad1d1e8e684726239,0x7ac23cf11e2a8eee4763,0xfa47e9a3edd1f208f744,0xc905f481c2409d202c8f,0x21d690da485f242b5210,0x66122e2914a48972441d,0x2247f523d891c548d4a4,0x495524a0d24b89235491,0x36d49a324c2525da92c6,0x8c941449eba4ec1273e9,0x12956949a4a3f251b528,0x55612a62950a4a6c252f,0xf7a57792b84959b4abfa,0xc4b3aa59392c4e96004a,0x97384b8325ba92d9c969,0xff697c94bd6a5e192ed4,0x1d30ec984f4c0ea60312,0x2640931a098b44c51a62,0xcdd2664d32ee995b4c9a,0x5c4d1aa689133fa99ec4,0x29af84d68a6ad535069a,0x371e9b684d9b26c95361,0x2a938f09c464e0a26f5d],#[0x7275453a6a9d034e6327,0x4f36279413c109dcb4ec,0xf244f7927b2d3d5e9e93,0x8c9f944fb6a7d453e6a9,0x940aea030500a27fb53f,0x85194228a0e2505da81f,0xff28789438ca19450bc2,0x65147a89a14482a22550,0xa331518aa8b8d45a4a2b,0x764a38051b228d4d4684,0xa1482ea3fb51f528f394,0x29369493aa4765227a90,0x2be295554a5ca51d5286,0x1e52f0a97414b52a5825,0xca6ba5349a99b14c8aa6,0x4ee4a74b5397a9bc94da,0x1015048a7f253e5a9e91,0xbaa319516aa88e5433aa,0x54aeaa5055234a8fe546,0x9f454f1aa6c5532aa979,0xd4aa4e55192a85953f4a,0x555caaac955512aa4554,0xadf156c0ab44558eaac0,0x2aab0b9580eabe055dca,0xc56682b2d15930ac7c56,0xad7256ab2b4915a10ace,0xc80ae0356f3ab6d55b1c,0xd5da2aeaa57472b99d5,0x2be515edaaf46578fabc,0x8102c0115fd0afcc57d8,0x1a586eac28160c6b03c5,0x6b1c158d2ac5f962aeb1],#[0x64f2b247591b2c86963e,0xd756656b2ee5963aca81,0x62d09567fcb3cc59cd2c,0x5a79ad305691eb4735a2,0x5e25ad2ad5cd6a98b50f,0xceb6b55b41ad9716c54b,0x16f1cb7675b952dc396d,0xe24d70d8b8455bfeadf0,0xc12e5417252b8ec5c62a,0x85d302e86173ccb9bf5c,0xbb4f5d9f2ec5d75e0baa,0x866bbf65de7aeea17702,0xd979b4bcb35e462f1697,0xaf6497aecbd4f5e8eaf3,0xf2aaf9117c3abdeb5ee7,0xd65f57afa797ceebe5b5,0x4bf465f9aafc397de4be,0x7fe6bfd75fddafdf97ec,0x2ad811ec0736026300c1,0x1304c5822ac0ee606930,0x60d930659830ac15e60a,0x26a612cb08c98400c1d9,0xd6c2da6159b0a5d84f6c,0x186f8c355619cb0c4985,0x10a5881ac3e661dfb0e6,0x76312bd8910c4616222b,0xe62b3b152d8a74c51362,0xc640630cb179d8b54c58,0xdaec6bb634fb19e18cce,0xed8ee6c72b6387b1bcd8,0xb229190cec8406401b1e,0x4b932559925ec9086465],#[0x964f1326ed9354c98e6,0x6ca8f6534329319460ca,0x968ecb15657732b49955,0xffd97dccbc765c532db9,0x13324198fecc58661332,0x669eb34859a0accde666,0xdc966d6b36459aeacd59,0x44ce7b672fb38e19c0cc,0xd9e24cef6676d33af99d,0x3e4d9eeecf5b679fb3c8,0x2b340bd9fe4cfcb67d7b,0x66852b4225a0c4d05c68,0xd1316885343b9a1a4d0b,0x42ad1ee68e3b46ada2c6,0x95a5d0d2c169423491da,0x34f31a760d37369a634c,0xa6e35251a8c4d43069ff,0x9f6ac73559daa6ad50e6,0x6d6676b1ab57e1abb8d5,0xaeacd73a6b7935b2dad0,0x16db026d7d66bd7b5df5,0xab64b9b1ccd8bf6c4c36,0x6d0936755b346d97c6ca,0xaca6d57369f1b4c0da2e,0xd8db456d94b6c35b5e2d,0x5b7e4dbc06dd236e21b6,0x727db8dadc516e1ab706,0x95b7411b9d0dcd76e5db,0x86ee3b7629badcdd526e,0xde486f1637841bbd2ddd,0xdeadec36f4e37a01bcc8,0x39bf38df806fa737c9db],#[0x381d5c0b2e0326ffab7f,0xb7b84f5c242e0ef7059,0x327105b8765c364e1967,0x8e2b87148b89a9c49ce2,0xc74ee375719c38bc1c5a,0x335c920e45e721638f91,0x8395a5ca9ae51b727fb9,0x730b397e9cb90e5ac72c,0x6d9735eb9a59ccdee632,0x38e78073a1b9c45cdeae,0xdd070e80673f539f0dcf,0xa471d1eae8c3744e3a17,0x5ba791d37ae99674a73,0x5756f3aab1d4deea3d75,0xebac75c83add1d658eb0,0x8deec3d7610bb041d7bc,0x4dda58ece476593b285d,0x3b791db7aedac76c2bb5,0x72d3b8a1dc44ee117700,0x12777b3bb3ddd66ee8c7,0x4ef8d77be3bd55de5cef,0xe0ccf03f7806bbff1df9,0x39de1c2f0c57854bc235,0x53c5e1e28cf11478873c,0x791dbc825e3c4f1c678d,0x2f3796bbcaede512f26d,0x40f38479aebccd9e61ef,0x9e8e6f43679fcbcf75e7,0xd589ea34f4f37a60bd26,0x28bd87debf0f5bb7ac4b,0x77b9d3dbf5edacf6997b,0xf81e7bf63df15ef3cf77],#[0x1d8f8ba7c4f3e1b1f074,0xbdf2e4f9357c923e421f,0xbe901f432f9dc7ce03e6,0xd8cbeb9df580fa997d33,0xfd7deb3eebdf6e4fb4b7,0x6fc997e33bf101f848fb,0xfb3cfd6c7e9d3f3c9f99,0xab9fd0efe3f7f0c3f76d,0x3bfd81fe5cff077f703f,0x802240049ffecffb97fc,0x1338080c033e01510076,0xed01cf80d44060602cb0,0xe056702978132c087603,0xcfe064703078175c0b3,0xfbc0f420769039881be4,0xe82394115a0875041381,0x5358281c13720981048,0x6e0c0482d54160e0acf,0x432020f41b834100583c,0xa148083406e19010680f,0x83405c1a8a4200d00e83,0x44a040690041d02e1005,0x280f01c030100203407,0x10a03a07032140700b43,0x2720a03a0704600f0427,0x890948801780e00f04,0x5d07a080570004c2805e,0x110a09805682e00088,0xc02b800221742e82015c,0x10a09b80029048268204,0x148241342026011c001,0xa178080ae000a05d0bc0],#[0x4870a16030680e85007,0x64a02409e17c18a00b02,0x409e17c18a00b02785f0,0x7c182505c2785f064a02,0x813c2802f07094170be1,0x7830581605f0be0c1605,0xc1f811380f0200de1400,0xc00781079614928e10b,0x3e084183c24a1083085e,0x4945f0be0c17125101e8,0x78e14928de17c183e058,0x3f02e141f0e0a7c1f810,0xf8170a16050520b7c278,0xc2f83210064228a10bc1,0x1814f83f022701e0401b,0x451014f83f02066c2925,0x2f0004a07c4f0be0e128,0x442f85f07c0014020174,0x6e0f04e04098057000,0x784f048501b842140a03,0x41f03f09e0a0a04206e3,0x320b42102c101803c08,0x170ba1013808e0007c5,0x238002017c2f8350dc0,0xda14047000402c86d06,0x902b803c103c0740e069,0x1cf09e0fc0842b04064,0xc1f814380f0200c0790a,0x101e7824281081b8c0a7,0x7e07c103c0856100c95e,0xd0a0820c880e80e214f0,0x1b840341b82d07a2008],#[0xf84a183a8020d016080d,0x94413608417c1d101e02,0xa0f01a037100e82703e0,0x703c070203c0580e0321,0xc8883d8160b41b8a4349,0x1b080881b8e0f0168380,0x91107a0e0407a0f01811,0x812030160c01e037100e,0xa83416c282e068182006,0x1e020074201d0218008,0xe0741c010680e817080d,0x23703a26c1d02c150f82,0x80b01c068501d03c0702,0xb0480c8692e0780e0407,0x280e050780e016860b42,0x40280e024060f0185844,0x681c030110a0380780e8,0x58001e03a2340e080284,0x4280c01c03c100e214f0,0x7f0610a0a03ce020c08,0x6016f09c060a0421c1bb,0x1678482882c210ee0c1,0x9c02d820740f0502c80,0xe0b013814b0482c1e0c,0x5b0410805f830610501e,0x4608c1084b783828158,0x9c044e12227c1e00d0bc,0x100f00bf064a454d8242,0x11380e040380501c037,0x301e03bc044e038140a7,0x7039291520778089c074,0xc181e0157060ea0a09c0],#[0x381c05842f070501809,0x2e0d053c16000780e84e,0x504e120b01341407882c,0x5481e017e0c1e129e020,0x5a0d041820c01684810,0x80f080b41c02c0c1e838,0x220000110702088b0a08,0x8807c0ae8303ba14228c,0xaa0b07a203de000d01b,0xe000d01b880d01b840b2,0x45a102738003a0702d82,0x2c1a0c82f41c1a07830,0x7102c1d0c0ad43582071,0x4e000a01c0a071435820,0x980f8a0681c0300c1610,0xc0c01e0370c006820480,0xe0a02802683d05c00130,0x341042188ff83d0a0c01,0x273800381c85784e03c0,0x7c04180c4b00b784e02,0x70bc041e0e2241e685f,0xf011820f04016227c183,0x4a1892582a88583c1085,0x178080a00800f8023dd0,0x38141200ae000a01c0b6,0x1f000482024015c00140,0x78082cb0bc00140d616c,0x28048040060a3411282,0x800c1404b1825f01e00,0x8d0ba0f8002414050090,0xc1309c0b8005c0a2208,0xaa101bd0b0701c1de01a],#[0x1701d06a189d07c04180,0x2c10fc0005008b0a0100,0x1c8d07c078000a0080a,0x80480800600b42e84e00,0x41a4210900dc07800211,0x8311ec2808005c014303,0x120e01c04808006009c2,0xe0401202001802b0bc00,0x4214285c1484005e000,0x221d43038096182ce0,0x8180c02804004005a178,0xa2c110227c1e85e0321,0x902f01e0002804804006,0x3b0a1205b0d6145004a0,0x585b064a02408282c358,0xc0834210e0e8160070a6,0xc2c0a0480800c114e19,0x24a1c28581494385702e,0xc004210358308a538370,0x2d0b02581054066c2d84,0x10840d6142296494240,0x88a6e0a80cd84b076070,0x702db0b60fc20281340f,0x6c25836041141f03c201,0x7c33850501603b0361,0x9c07c2b8300ce15c084,0x2c3850ac1144706e0420,0x416d02210e0f0038534,0xc300c05406584c06708e,0xac3385a04e05c183e0a,0x83432350270ae0dc083e,0x209c0502d09e04270145],#[0x41f6001381007052066c,0xa134189a6183842f07e0,0x19c008b04a119682001f,0x3e0574209ad0ac3080,0x704d03c0342f02219682,0x4089ce00100604402683,0x1bc2585d02430806f81f,0x4273800282096a1f210a,0xd020a0843fe121668103,0x282085109f09a0ec2f00,0x2a425c2f8425a433408,0x850580a740f021380a06,0xc00140e0701c0288180e,0xe05d0282402a0405b,0x40060981f0da0616006e,0x509139c00200a0280480,0x1004e05c0341820101c,0x6060949f0200c01f0004,0xf4189ce000a05010a5e8,0xc180ce83e04270140a0a,0x3e1484907f07c001409,0x1807b02482d21241c4e,0xf04d0bc0b8000a012010,0x8e0a0705c1d0a03006e0,0x600b02106853c240005,0x60a0370ac1c140601703,0x20782826029609070561,0x703b040f0502810b81d8,0x8203481c0b41e0805021,0x5a0b021080c30a03707,0xbc0858178182c0b01814,0xc381d85078301de0603],#[0x5bc0ec10420783509f02,0x2f02866c2f0306038380,0x82d07c0f42103c140758,0x20c05032e041802d0842,0x832e15070bc0fc081e83,0x8503dc0c1f0421015108,0x38200b60b8181e13610,0x9c0678184015c2a9c433,0x403c0f41e09b0842b850,0xc0e82d140802d058108,0x9065c2d8441c4781833c,0xe0626c210e4940df8186,0x1905a10840800740a434,0x7781b0807781c191bc08,0x80f585705c0c1481d1b0,0x71014585e060a44d82c1,0xe81e000a45d05c001a03,0x43784b044381b8e87b42,0xa1c27030581085458069,0x9c0c04002d03c00210e0,0x182c078210e0781283b0,0xf4278170bc0c1e0e24b8,0x11381f811820f0401c21,0x8352c0f02e07c14160c,0x5e040c82d0842830e061,0xb0801c00e82e00108684,0xc501401381e82e000986,0xdc140661b4119c81c0d,0x281827008e001704e00,0x146822503f03e0161741,0x4ee07c0005007008004,0x40dc1e0601c0084009c2],#[0x470008430880840b0311,0x903f00084304e0a20290,0x780042d0848540ac02,0xa470a813804007004,0x52404ed09c0d03d85e,0xdc0c04007004006c2f0,0x2a0c0200380200210827,0xa2c11002003802002108,0x84703e00028038040020,0x2100800e0080080ab0,0x812207e83e000b81d0bc,0x4202243685d07c03826,0x3409084342f000680b85,0x202101121b41e85e01c1,0xe8170887c8803a05c,0x5d06423827009343a37e,0xc22e09c03418281410e8,0xa185e0841f806830502,0xe09c014e08e0c04704e0,0x7006007800280424008,0x4486e09c034191614048,0x3827009384021d0ba048,0xc004e0c08742e83d0242,0x11c024e0e0c08490850b,0x70ac1404043c13c1f812,0x93021241f8009c188490,0xc184207b60813056202a,0xac482c084178306e052,0xa8000a584b0760ac085c,0x59e12c0842078268a40,0xb028170b032052c1d82,0x58056c2583b056041e0],#[0x1e03a86605d818283c0b,0x102c60a0f02e019242e0,0x605b058323c0bf09e0fc,0xc16c183c102e21403c07,0x82c0b010140b81583061,0xc0f04e0a052c221903a2,0xf030650a030201684207,0x83832850508403382f83,0x78703d06418060a8843,0xac47050520500cd82708,0x1080b40cf07e04430140,0xb0507c15830190502b06,0x70506e0b60c1621905a2,0x709050803c0750cc0eb0,0x5c209281bf022d2c1a19,0x1c10fc278220a0f00c8,0x4303c0750a58381c1706,0xb60ca14058341903a0b,0x80a782b8203a3842020,0xc8b6120a0560c0c814b,0x5828561b0a58403bc16,0x800c1303c1821583b056,0x602241303c100500900,0x81803c100f0380794504,0x214050040720f0400b60,0xbc208a111a048a04,0x40030040782b8c22844,0x20038060060081890024,0x20f40289a060283b0120,0x14010018bd03b608811,0x1e0500704d038142d89a,0x45040500705e89a07429],#[0x142208a03817c103a085,0x517a2284409a228300b1,0x10170e0a2c181c06e230,0x9a04650dc17800090076,0x30c12c30b446403f050b,0x4007c005ed82d0248bd,0x1700b07a04901461b828,0xc1e0602804186e0a0100,0xc06e1d140840f0306008,0x50406021c1383c101803,0x3c17800231c180370794,0x1140f81c060280380400,0xc30140240200304c0f86,0x100082707c308a07c0d,0xfe0c18114078300a00e,0x1e08224438000b020891,0x1f82f00b02491cb07a08,0x1604ad04028048040060,0x730cb83c29c17c2782e0,0xe4750a7830b9604724f8,0x429e13c1d82078305a00,0xe8c864274091904a2127,0xe13c1681085464500ea3,0x5e1045088d03c00210b,0xc12030ae0b4211422380,0xd0ba0f40c19b084889a0,0x1930a17040424770d60b,0xc021080c02103c0d0ec,0x60b41521c078202ad06,0x4982d0840b0407c10c1e,0x840b420360b42102c10,0x3c0a1b07810c40840b42],#[0x47707685d07a060cd842,0xa191815a1d8321704042,0xce84218e21bd09075c2,0xe06042c718a41d706e05,0x20f0605661b4003481a0,0x8340e0401402402003e0,0x681a87c1d02c1117702,0xe8401201001c2e04c0f,0x76081d02c1512c0f058,0x901000c0101e0ae340fe,0xa0d11a0f4102603c200,0x81680014024020030116,0x600805584834403a05,0x84b000bc1b8fa0004808,0x2830e060f03258069837,0x780dc400e0078183c060,0x700800f4283e1c050040,0x70203fa14148c0280480,0x1681f41d20c180a02802,0x4200b846020760583410,0x222a41d4202e108a907,0x10c4908a6020e846020d,0x107109804808a41f0090,0x226c1d07806808340c45,0x683c0c4da0be020e8460,0xa0b4305a30418060508,0x88907428211105a11115,0x7042a81e064448384864,0xc81415061077044684,0xa0c0e907e02190720380,0xe056020e01b874040e83,0x5c041e08074c130101c0],#[0x509c1406701028182630,0x6c10aa0782026b054045,0x407c41f80862a81e0481,0x6483f010c0ea1420fc04,0x1487c0c20e816c10a0,0xb01304292281960a80a,0x1301430dc0452442268,0x20981c0c30d6080b0803,0x4530cc04c1501120658,0x22a80e860300588520fc,0xb8203a181920fc043c0,0x2490302807980924138,0x83f010c4e701074181e6,0x200e8503241f8086078,0x8a30d405808a050c3501,0xc0451154058092410920,0x4c271058c02c4281020f,0xc417c041d082a84b7010,0x50503241d80e0080a289,0x7c040e8409b42b010320,0x80041500982e02e080e8,0x8404403e000c0f81100f,0x8804130201ec2840f441,0xd00d0007a190011010,0x100088168002816c150,0x11025001101283b054,0x6081e8d610450520f001,0x174001f0882e03c0b506,0x5806b042582054103c4,0x81f01c40ee09058a098,0x41b83808090080809008,0x8d04201c02ae0f4121d1],#[0x24504c823410610981a0,0x30058086c5dc1c012162,0x5301078190ee0203c311,0x3a0654110b108a015085,0x100306260020022030,0x70003d207209010da0b,0x507c202a01008412094,0x102920602341080f3001,0x160101808d041008d04,0x202101007140b0080b41,0x8807101200a012182b01,0x42090304802820110081,0x15809070182804c104b0,0x40c05c0485025030380c,0x4c18610c048822020e00,0x70102038056024305702,0xa0207002404060e01582,0x411813009602e0c50960,0x18402e024040612c140,0x8091004e83081200ad06,0x480840601c5d0640409,0x70a070204c02c04060a8,0xa098100f6142015a102,0x557010803d83a0042c44,0xb04283e20f60885a0514,0x116083084c0e80008,0x1026031a154210101435,0x3820803582096180a708,0xe08200e404043821004,0x43820c05007602e10401,0x7808305c60f01061100,0x2102e050802e094182e3],#[0x80817078081c040e0230,0xb0103808c0840b8130b,0x4916023021e0204c1e02,0x1021005042430a26020,0x618130b808220f808203,0x211808301010260f0104,0x8060f01078081c04080c,0x45108109808810b80810,0x80188a2102130110214,0x4c1a0608c1e02084c702,0xc088640c1a1630a102c0,0x102020604003011810a,0x46020c0610840c1e0207,0x11c08230a42381060308,0x66178106615030410012,0x8082b0221903060b0101,0x6020c061083068184213,0x1c082306423810603084,0xd0647e0620cc04604521,0x41181a04c0834180a04,0x810802cc2f020782109e,0x2cc2908e04283ca04605,0x870ae0c434061800180,0x8c04182d040f04008061,0x178106424c2a060c0610,0xc080f40c418494401c6,0x60ec1f0240c0a040092c,0x8201842301060308420,0x4140b0181211c082211c,0x422c1c06120620cc0461,0xe30bc081e09c081018,0xa423810a0f0c1d026042],#[0x3826906383140700c30,0x381040101401c4181828,0x8005c088485c08113883,0x2a01e418720d800520d,0x8506418320c19060802,0x182c906c0030041820,0x1d0604830860a03c836,0xea1241820141048309,0xd860703e03b05618200f,0x36182106906820381f01,0x202a0c219040603c03c8,0x8301ec3003c83100a0c8,0x1a000a81a00100f00e21,0x40e1c0c810a194789400,0x503d000e42a070a42905,0x1200080c010a3e800821,0x1060540d00088102400,0x1802083060500068002,0x2090a902100c0114003,0x3201001c300428320419,0x9405040c80440100e20,0x1c404a028204003c0386,0x850a431060a4202001e0,0x30040070c078070a828,0x800283c038830c8102,0xe100c01001c301e01c2,0x4300f00e180f052103f0,0x5203c06062141f8070d,0x180a0207201c201e01c2,0x8180f04c130601802030,0x9000406008081300f01,0x800e1a8501e01c3232],#[0x8088002030040070c06,0x800e180f00e110006860,0x30040070c07807080600,0x8478423c101802003860,0x601c160a030040626,0x1e01c000601c101e01c,0x80600800e180c01001c3,0x43040b242b000c060080,0xc0fc1580ec0d860a418,0x9a0cc0d040905603b0c,0x4040282090a1203d0a0a,0xb0c00f214402a01e42a8,0xa8002054038860c0a,0x441340022040d000541d,0x30045000c06008506418,0xc01001c383f40c41860,0x90a80710a1c8320410,0x2a01c31060d06064190,0xc8700c0c0600800e1c83,0x4044024404402404060b,0x10110090811009080508,0x850601c401340c06008,0xa0c1280a0c1900808190,0xc8404005403880940504,0xc010a0c038846412000,0xc0101100040600800e18,0x10601c402a01c22000d0,0xc3018021418071006008,0xb00e141500e100c01001,0x2181809104185b00e185,0xc102a01c000601c10180,0xc01001c302a01c430601],#[0x3004040300408300e200,0x142854001444a0680060,0x3444a050fd0012800309,0x3141d00502300c011400,0xa168028107c2a1f8184,0xb9091011117213804405,0xa1160110243049028064,0x720720484a01144d1080,0xac0f8442503a01b06220,0x81141590940f205008a0,0x82b212290a40e40c84e,0xc81c81402424640f2050,0x2c02430383f40c221881,0x441d8301e110c050142,0x410440244200a1100809,0x40608804840880484e1,0xe03c01264a14470a030,0x82214a1420060980d008,0x5050182890a0f8304a02,0x83e03921740b00144e58,0xa0f903e81111110cd021,0x1109101409c40fa04490,0x6054400f06822198051,0x121f0806008084e585b,0x28645c8484430044000e,0x61c1fa2f430322e0244,0x210c064b9090a0f9171,0x402030040405c04a0101,0x3040180202050090c041,0x260a060080906e844160,0x3c000983c001600041f0,0xc09008c001812011800],#[0xc410e0dc08a03004600,0x8112e83104383104aa,0x184306030046000c1683,0x30006030042060c08108,0x5060c1f0b018101802,0xc2006030044060cc2e0,0x270261e041084203014a,0x71406008080600808168,0x81f00e100a1096040f80,0xf40406008100381f92e1,0xf008232180c010400300,0x18020202e0254200a101,0x60082001d0c01802030,0x1808040402030041000c,0x8090c06008080b809010,0x5430040403004052180b,0x210050807c0385430040,0x80f80708060a081f00e,0xc0fa030806008080f807,0x138080d41832040fa030,0x4040940504a0c20040ac,0x60a020512141f062710,0x1381cd06c00543f80c29,0x413a0c341380c14060fa,0xf01a1f0c14209d06183e,0x204e80c2018020038641,0x11604210a0a0204e80c,0x201c401802020116142,0x1280a081900808190084,0x1160d8008094050090c,0x84206b062f02838110c,0x7b021d8300f604312a43],#[0x30045000c060080ac180,0x9b06109721842103084,0x30040070e4b809b0618,0xc201160420180200386,0xc200ee042012e0c20116,0xd213c0c301160c201160,0x505a09e81982060281,0x602c1b8a47d063037050,0x10f40d81982140e982a0,0xc10300f81b8203a191f,0x2c066080f092481e0414,0x50283c0813d0303a189,0xc490709e81a03124203c,0x20781e03182074384f40,0x383020c884f03170189,0x40f00a0a0750a109e062,0x44e0300b0141013b0330,0xb018300f0183005a6084,0xd213c0c307c427818607,0xe06109b04211305a101,0x303c1184a06c0cc1081,0x58301809c0a186e062f,0xb032c1129e06240cb04,0x84f031a1398660740cc1,0x4084b84100700c10b608,0x18028201dc060b430868,0x1856304427818889c080,0x503178181d080f109e06,0x85840301810b0809cc3,0x30940c5253042c250312,0x85b08427818d09cc3303,0x783e06e080e86040070],#[0x60f9c1227e062703708,0xc238244fc0c5e06e081e,0xa060c0444ee138186159,0x3c06260884f031416829,0x40dc103c100f109e0618,0x1821e81b0330447c6053,0x641c0a4c250305806464,0x78323e21e81b03704610,0x860493d0303a1f037080,0x6081f060a581d8207824,0x30307c192781940c3079,0xc1c0e03cc0c21584141e,0x24f04281d8212c25820a,0xb81b8403c1b03b041583,0x1a08800250880c088070,0x90004a1101a0e902128,0x1d63824a0190e1409008,0x748c89221c211402e10,0x11010180010560254906,0x10190504092089041e00,0x9008081380e081380e0,0x9008088c82027018920c,0x10411014821409008080,0x22825014102a010110a4,0x14094208c09c03a8270,0x421021010104e5040a03,0x3820082a04e08418080,0x18320d80040a4270540c,0x8208241b020e41b000a4,0x60ba41a080e41b000a41,0x7807906c08481e418430,0x2e06800203c038860c0],#[0x41e183a41e10210101,0x60c0800aa00183a041d5,0x3c130603c03840400510,0x8501e01c304c03c26040,0x408078070e8100f00e1a,0x3c038403c038403c0385,0x1020c218305d21504060,0x218304005403c856042a,0x2e064190340e181500e,0x8094182101018210101,0x2010014a0e8100714108,0x2002803860400550200e,0x4a143a000a81a000d030,0x1281050103aa00150007,0x2101012850501021010,0x23210215805800349063,0x402310940e40d8148140,0x3a138290940f20c81c81,0x2b0290a1583037043008,0x36270340f21482c81402,0x30ad21581207d02283a0,0xb4080702a1c8540fa04,0x4c1e000812600082a826,0x446000c09088c001e000,0x3e01c2c040400506048,0x10102805602433060a02,0x10808081080800e18210,0x14c001208143410280c,0x40fa03098101f4061810,0xa80c1c10220a140da831,0x11814850ac189c040800,0x1b039a0c341320c82a03],#[0x3082b302413a0c410c08,0x9d0184c0813a030d04e8,0x3800444180040240b840,0xe04028430402ac28444,0x101d11001560d800bc12,0x8300f6043b06c0803d81,0x309810091861c9718615,0x8883000a0dc1808048c,0xac11020ac1056042d056,0x6100a10c100ab06105a0,0x48097061807062100ab0,0x4c185a0aa0c1c1585142,0x4850c202c0c0000e8860,0x708432060816820b4180,0xc44303b0c0a206080f05,0x82e0a301e42821813080,0x181ee0a10570780c40f1,0x88501e09a0c0a00b90c,0x298309628194280b04d,0xf80e814817604508406b,0x8650c604581760425860,0x12c302826c1606420c14,0x59218c22863022c0bb02,0xa80bb02a184c0a07820,0x7040f04017c170028610,0x460788328283e100d505,0x15840348528298405806,0x89c15c201e0c16505704,0x4301d04e188720b02ec0,0x53050159820782c8604,0x90701db04850505a0c02,0xe060102b60b6081e080f],#[0x85003c841c218203a303,0x7219435821a0a0877021,0x283e0e0603e088490830,0xa181e42821813880f18,0xb0520790a184141481ee,0xc1781ce100f09b828302,0x80783213218c22863062,0x2b8419083820aa1e0570,0x5c10560c15a1403c0668,0x7081403e0ae100f0741,0x54280a0500870590c221,0x861302887081e6053041,0x60c404c8742021c17002,0x8860c1301d0813481013,0x40980e85a081e0407406,0x1c201e01e41860981e0,0x2040116082011608201e,0x40a4078080c1f8071040,0x3c03840e40e8403c038,0xf00e100f00ea080408,0x8302201c2200082d20a1,0x7080880710c181100e21,0x4541a821408807080880,0xc0306400100e08420780,0x202201c202201c212201,0x760c4204c078202201c,0xc1301e10c203b0622183,0x110c180790c268840815,0x4207920881201100388,0x820e432830116084219a,0x4c07207005408b218045,0x8a16c0e84088048080c8],#[0x82681148520790841340,0x9a4080ab08210a40f210,0x2c220e100c0801f40840,0xa0c05584088c58402018,0x82790601f40881540503,0x810803e81081f00830c1,0xa04058682f408150c03e,0x206044024200fa04242b,0x201c5054814414814000,0xf20540880694348210,0xc604e82e41e8102a2823,0xa04407009d0ac83d0202,0x1a024c1c831013c8300f,0x50806c0388401520450,0x102024014101b309204,0x38601e4084034c3282,0x40540202011608201a02,0x8050240826008600e08,0x270474710e886151381d,0xf28a0420c215140781a,0xf8130409c1e040741384,0x82404283e01121884880,0x60c301360c20840f081c,0x27081280a0121d17013,0x1c301a02341007101f,0xb610803b83702280d01,0x804482504200a5040c03,0x350201c40ba09ac08606,0xc824000a2c1809180698,0x7218c306034c34860d02,0xe581428261cc33850304,0x2281d4336090a080990],#[0x8b06608401001ec1982b,0xc2e0601ec085c0c0680,0x401ec1b82309604600e6,0x6044014e10202360c201,0xb816803d81102e05a00f,0xf609c088029c20403410,0x18202404183b04200800,0x6e04607801cc1381101,0x804dc0030b612c210077,0x108c8703e41b02600202,0x42a054001f864641052a,0x160840280024181a000a,0x5340044082101fa8511,0x321808b0412850116083,0x8003f0807807081300fa,0x1142128007412800290e,0x1fa85114212800a0b01,0xc2090641053400455841,0xec100ab081a85b0402a,0x40f0403c03840980780a,0x4280f00e1800fc0f040a,0x200124102502201c402,0x81e28201360c407a20e8,0x42a000c188290804d830,0x62250510b4010009400,0xac28807ac2840f042a82,0x7e001007b0a103c022a0,0xc2b8910281857062105,0x420ae0c5c287c000f014,0xf141c82304a04503ce1,0x285904609408b6081484,0x2181a81680044582141e],#[0x4080f14283e0c1148150,0x90d20b03218161052040,0x10c8f407308c01424831,0xe1ac1601f408804e40a8,0xa4305286803e81b062,0x20c04dc1481502258360,0xa058a47903984a00a164,0x609428560c4508440006,0xd84140c084b05204050b,0x8008ab08181e41601f40,0x9607ac20606240a810d,0x39850903885835a044,0x7d036144c3582c03e811,0xb0002b1301600090d00,0x81d040f0208580020858,0x214c283c307209410ba0,0xa42d04082b81c4004468,0x606487009907a085d040,0x203c30a0f8301b20cc18,0x1b214c28605a41882010,0x41013012202390a61430,0x702182d04e04c0408022,0x54012021413831403b83,0x64498420c0528204a18,0x14300ee0429060a6c286,0x822842407600202903ce,0x80190a81842a09400158,0xcc0e012e08c2283188,0x3704a0c411421203b001,0xa85a01210c22831408c8,0xa15830562290058481c2,0x30a21241d82014358250],#[0x641a831045385b081818,0x590a184e03d610303002,0xa4311421083e00100998,0xa04642e8230a2684c000,0x38200809985507a08048,0x29a1440a802542383100,0x30b48710a285130e619c,0xa50e583432221c0b4864,0x84432201e4296110c880,0x74068604804040790e5,0x807c061c0f40c2183070,0x60a4c10c03c03e030c07,0xf80c100808107b04c0,0x1e100f00e1012010100f,0x4101d404100f00e10260,0x21482101104904281d40,0x1e01c204a808201e01c2,0xe180f00e101e03603c30,0xf0110803d82084200f00,0x7b20881a021004d83080,0x2268202c020302c02020,0x904806818822603c0160,0x80b40e11c1a0d00e1207,0x868070]]
def g253H8 := limbs80 #[#[0x10074040824000032c6,0xd3c43400860010431003,0x111820404892050000c,0xc114c000049182001103,0x328d34321d70a0400122,0x8482010090810820c700,0x420000050846465c2187,0x528100145d0005400013,0x51004c10860861057c,0xc600124804a1919a4197,0x5198b4000aac56a20c11,0x43af5c9ab334cafaa452,0x786c000881cd0,0x150200039480000000,0x8c0e700038f800000000,0x74500000944688788375,0xa4f000354572246c4558,0x909dd6510a80000001,0x100000000002c4fc0900,0xc986e4500000000001c6,0x2d5a240683c00020ee,0xe993e0002d3423a5b160,0xa26a03c00093f800064,0x403b4ac00084c4000e2e,0xb3042194ee47fd478169,0x258d82580001520650fa,0x499e6cc000097,0x3af2111bd5076d8c403a,0xbdc6f000164d000007f3,0x3a0e435c0000001a0f40,0x8d18021072000,0x139b4c018c525d069448],#[0x52b905624b94c1c2075,0xa849c9e0cd08c8000000,0x5c06dd000212552c8eb8,0xb80000000406b094000a,0x2218655c92342544cac5,0xc8b284c12845a1c4a000,0xde4f78f06c69f19dd56,0xc43288d12480000c020,0xa08c00030fc000a4a800,0x36000031b24f40002479,0x988dd7080677d9a2c353,0xbcedb1fb951000186210,0x2e9300031339cb,0x4cccc4000846400081a8,0x2a72460000000e1540,0xa3c84a0749c00,0x28400005af241d15cc2c,0xc000d1c716948bb429f,0xd5ef9e6d6dc82c000ea,0x454000f4f0000d24,0x7b8a128912ba00000000,0x720084834514,0x3c371a9800,0x300000a4eec520001466,0xec000000000000000006,0xc000631084e98d1e4352,0xb31c000d54aa24423,0x41f18d8bdf3ffd5d4144,0x30000a9500000000003d,0x1160801ba61f0b30a1f6,0x5b347a00000002197041,0x6400004c3036b24cce18],#[0xe8d8472c827b24f0a33,0xe0ee8d30b08266453,0xfa950000031f186720c8,0x69cf4000856c816ec510,0x4474000f52b647000227,0x4dac303046045bb2f718,0x600003221040343a0337,0xc000bbff09f307800062,0xc0080000000000b1c,0x3e9217ce800022820000,0x798284600028,0x5320001cac000000,0xa9ac0000001a0d,0xb5105000000000000000,0x1021000144d0000000d4,0xc25,0x1f000000090ad95f5458,0xf48ff2bc00000b014002,0xb3dc00029bd0c,0x1a5758d30c000221b559,0xd80000000d1a00000003,0x6942512e2c81879e7b9c,0x560aa402fab181e7ca17,0xf55a590000000000dcb6,0x743c0000ae948c0003c,0x5354409f16cf2f21ac00,0x2453000000000032ca,0x9400024400000002cba0,0xd2990000b0fb35800072,0x8e6258956f00030648a9,0xa518000b83241c0002,0x5111125bf10dab200b80],#[0x586b0b5a1c2329c1b4d5,0xa0e5917,0x34000b22800060d14040,0x16190003d243d6d23af4,0x3b44000000,0xd9400007266c3d7338,0x6504acaa69c0b32fa380,0x10fb00003420003a1,0x4bf29700025587460000,0xb3c142b50c0a01bb8f34,0xa27d259d849f02e4b33a,0xb6421f4ebe30b5242093,0x159238000f4d5878c1dd,0xf8dca404967a53838a0,0xb9b3a2cb8e5a06625c00,0x7c8e35484000c01c000,0x4f4bf8c24000d4e34d28,0x400013f3474b372571f5,0xad0c21d55c8a700006b0,0x30000000062c7c175816,0x13b2b25aa9400000026,0xd2dd1392379ca8000000,0x21311ea28a447cc330a6,0x140500028544b3ca85b,0xfe8f0003e812c8fc3100,0xd0903d8000000190b93b,0x6b9c00043e5d290074,0x3ca4c3c40,0x4171cd4000149d000000,0x390000e32c000242be8c,0x4f9540001233bc40000b,0x40000003564f325cc560],#[0x20be0000000787,0xb40c200000000cc2cd04,0x622e4000000000000010,0xd44400039b4335b85115,0x68a598ce5646fcad,0x14ea00000000,0xc0000001442f3416de00,0x724f488cdb25aad4fd85,0x59000000010644a70000,0xd25a4e0237dd4baa1b0,0xcac00000000000000000,0x1c75fabaeaf00034fd,0x49d373a84c0c000200e0,0x26c379500004bd14dabb,0xc38d9e86b5b28c000ba9,0x1a00000001540000f535,0x200000000001c5e04994,0xc40c41b0003222f9b8b0,0x2da0bc00018223270644,0xa8000a9aac10826d255f,0x4000f318000c4b0000cc,0x85f000000049e32947b1,0x690002cab18e00000002,0xf41e8cc34fc0000001a]]
def g253D9 := limbs80 #[#[0xfa942501209bf845c910,0x9ef825d940ee96258120,0xff1214c110e796558150,0xff1514c110ff1414c110,0xfd9324c110ff1614c110,0xfd9534c110fd9434c110,0xbf9844c110fd9634c110,0xdf9754c110bfb844c110,0xbf9854c110dfb754c110,0xdf9764c110bfb854c110,0xff12150110dfb764c110,0xff16150110ff15150110,0xdf97250110fb94250110,0xbfb8350110dfb7250110,0xfb96450110fb95450110,0xbfb8550110bf98550110,0xff14154110ff12154110,0xf795254110ff16154110,0xdfb7354110df97354110,0xf795454110bfb8354110,0xf796554110bfb8454110,0xdfb7654110df97654110,0xfe54248510fe53248510,0xdf57448510fe55248510,0xbf58448510df77448510,0xbf58548510bf78448510,0xdf57648510bf78548510,0xbf58648510df77648510,0xdf57250510bf78648510,0xbf78250510df77250510,0xfb55450510fb54350510,0xbf78550510bf58550510],#[0xbf78650510bf58650510,0xf755354510bf78254510,0xdf77354510df57354510,0xdf57654510bf78454510,0xbf58654510df77654510,0xdf57258510bf78654510,0xbf78258510df77258510,0xef76358510ef56358510,0xdf77358510df57358510,0xef76458510ef56458510,0xef56558510bf78458510,0xdf57558510ef76558510,0xbf78558510df77558510,0x9fd874c910bf7814c910,0xded72509109ff874c910,0xded72549109fd8750910,0xbfb80589109fd8754910,0x9ff87589109fd8758910,0x9fd87d8910bf581d8910,0x9ff835c910bbf845c910,0xdbf845c910dbc845c910,0x9ff855c9109ff845c910,0x9fd83dc9109ff865c910,0x9fd85dc9109fd84dc910,0xbf78150d109fd86dc910,0x9fd8750d10ddd7350d10,0xddd7354d10bf78154d10,0xbf78158d109fd8754d10,0x9ff8758d109fd8758d10,0x9fd87d8d10bf581d8d10,0x9ff845cd109ff825cd10,0x9ff865cd109ff855cd10],#[0x9fd84dcd109fd82dcd10,0x9fd86dcd109fd85dcd10,0xdbf74591109fd8755110,0x9fd8759110cfd7659110,0xcfd76d9110bf581d9110,0x9ff825d1109fd87d9110,0x9ff855d1109ff835d110,0x9fd82dd1109ff865d110,0x9fd85dd1109fd83dd110,0xcfd76595109fd86dd110,0xbf581d95109fd8759510,0x9fd87d9510cfd76d9510,0x9ff835d5109ff825d510,0x9ff865d5109ff845d510,0x9fd83dd5109fd82dd510,0x9fd86dd5109fd84dd510,0x9ff835d9109ff825d910,0x9ff855d9109ff845d910,0xbf5819d910bf9809d910,0x9fd879d910bbd849d910,0x9fd83dd9109fd82dd910,0x9fd85dd9109fd84dd910,0xfe95250120dfb7150120,0xfb96450120fe96250120,0xbfb8650120bf98650120,0xfe95258120fe94258120,0xdf97358120fe96258120,0xef96458120dfb7358120,0xbfb8458120efb6458120,0xefb6558120ef96558120,0xdfb7558120df97558120,0xbf980d8520cff7658520],#[0xbbd84d8520bed82d8520,0x9fd87d8520cff76d8520,0xded42dc520bbf845c520,0x9fd83dc520ded52dc520,0x9fd85dc5209fd84dc520,0xfad64509209fd86dc520,0xbed8650920bef8550920,0xded7354920bef8650920,0xbef8454920def7354920,0xded7654920f6d6554920,0xbed8654920def7654920,0xfeb8058920bef8654920,0xdef7358920ded7358920,0xeef6458920eed6458920,0xded7558920bef8458920,0xbef8558920def7558920,0xdbf7450d20ddd7350d20,0x9fd8754d209fd8750d20,0x9fd8758d20ddd7358d20,0xbf980d8d209ff8758d20,0x9fd87d8d20bed82d8d20,0xdfb805cd20bfb805cd20,0x9ff845cd209ff815cd20,0x9ff865cd209ff855cd20,0x9fd84dcd209fd81dcd20,0x9fd86dcd209fd85dcd20,0xcfd7659120dbd7459120,0xbf980d91209fd8759120,0xbed82d9120bf581d9120,0x9fd87d9120cfd76d9120,0x9ff835d1209ff815d120,0x9ff865d1209ff855d120],#[0x9fd83dd1209fd81dd120,0x9fd86dd1209fd85dd120,0x9fd8759520d7d7559520,0xbed82d9520bf980d9520,0x9ff815d5209fd87d9520,0x9ff845d5209ff835d520,0x9fd81dd5209ff865d520,0x9fd84dd5209fd83dd520,0xbfb805d9209fd86dd520,0x9ff815d920dfb805d920,0x9ff845d9209ff835d920,0xbf9809d9209ff855d920,0x9fd879d920bed829d920,0x9fd83dd9209fd81dd920,0x9fd85dd9209fd84dd920,0xbfb8154130dfb7154130,0xf795254130fd93254130,0xfd96354130fd94354130,0xdf97654130f796554130,0xbf98654130dfb7654130,0xbfb8158130bfb8654130,0xef96258130fd93258130,0xdfb7258130efb6258130,0xfd96358130fd94358130,0xefb6458130ef96458130,0xefb6558130ef96558130,0xbfb8558130dfb7558130,0xbdf8348530fcd3248530,0xbdf8350530f9d4350530,0xedd6358530bdf8354530,0xbf980d8530bdf8358530,0xbdd83d8530edd63d8530],#[0x9fd87d8530bbd84d8530,0xddd43dc5309fd82dc530,0x9fd85dc5309fd84dc530,0xfdb804c9309fd86dc530,0xfcd624c930fcd524c930,0xddf744c930ddd744c930,0xbdf844c930bdd844c930,0xddd764c930bdf854c930,0xbdd864c930ddf764c930,0xbfb8050930bdf864c930,0xbf980d89309ff8758930,0x9fd87d8930bdd83d8930,0x9fd81dc930bfb805c930,0xddd63dc930ddd43dc930,0x9fd85dc9309fd84dc930,0xbdf8250d309fd86dc930,0xbdf8550d30f9d6450d30,0xbdf8650d30bdd8650d30,0xbdf8258d30fdb8058d30,0xedd6558d30bdf8458d30,0xddf7558d30edf6558d30,0xdbd7459130bdf8558d30,0xbf980d91309fd8759130,0xbdd83d9130bf581d9130,0x9ff815d1309fd87d9130,0x9ff855d1309ff825d130,0x9fd81dd1309ff865d130,0x9fd85dd1309fd82dd130,0xcfd76595309fd86dd130,0xbdd83d9530bf980d9530,0x9fd87d9530cfd76d9530,0x9fd82dd5309fd81dd530],#[0x9fd86dd5309fd84dd530,0xdfb805d930bfb805d930,0x9ff825d9309ff815d930,0x9ff855d9309ff845d930,0xbdd839d930bf9809d930,0x9fd81dd9309fd879d930,0x9fd84dd9309fd82dd930,0xfad42485409fd85dd930,0xebd6458540df77158540,0xbbd84d8540ebd64d8540,0x9fd82dc5409fd87d8540,0x9fd85dc5409fd83dc540,0xdef724c9409fd86dc540,0xbbf85509409ff874c940,0xdbf7650940dbd7650940,0xbbf8650940bbd8650940,0xcfd7658940ebd6458940,0xdef72d89409ff8758940,0xbbd84d8940ebd64d8940,0x9fd87d8940cfd76d8940,0x9fd83dc9409fd81dc940,0x9fd85dc940dbd64dc940,0x9ff8758d409fd86dc940,0x9fd87d8d40bbd84d8d40,0x9fd82dcd409fd81dcd40,0x9fd85dcd40dbd64dcd40,0xbbf82591409fd86dcd40,0xbbf8559140dbf7559140,0x9fd87d9540bbd84d9540,0x9fd82dd5409fd81dd540,0x9fd86dd5409fd83dd540,0x9ff815d940bef825d940],#[0xdef825d940dec825d940,0x9ff835d9409ff825d940,0xbf9809d9409ff855d940,0xbbd849d940bf5819d940,0x9fd81dd9409fd879d940,0x9fd83dd9409fd82dd940,0xbfb81581509fd85dd940,0xefb6258150ef96258150,0xdfb7358150dfb7258150,0xef96458150bfb8358150,0xf796558150efb6458150,0xbbd84d8550bf980d8550,0x9fd87d8550b7d85d8550,0x9fd83dc5509fd82dc550,0x9fd86dc5509fd84dc550,0x9ff87589509ff874c950,0xb7d85d8950bf980d8950,0x9fd81dc9509fd87d8950,0x9fd84dc9509fd83dc950,0x9ff815d9509fd86dc950,0xbf9809d9509ff825d950,0x9fd81dd9509fd879d950,0xdef72485609fd82dd950,0x9fd83dc5609fd82dc560,0x9fd84dc560cfd64dc560,0x9fd85dc560cfd65dc560,0x9ff874c960eed624c960,0xafd8650960ebd6450960,0xefb8058960bfb8058960,0xaff8458960cff7458960,0xafd84d8960aff8558960,0x9fd81dc960afd85d8960],#[0xcfd64dc9609fd83dc960,0x9fd85dc9609fd84dc960,0xbfb8058d60ebd6450d60,0x9fd82dcd609fd81dcd60,0xcfd65dcd609fd84dcd60,0xaff82591609fd85dcd60,0xafd82d9160aff8559160,0xbef825d160afd85d9160,0x9fd82dd1609fd81dd160,0x9fd85dd1609fd83dd160,0xafd84d9560afd82d9560,0x9fd82dd5609fd81dd560,0x9fd84dd5609fd83dd560,0x9fd8748760df57148760,0x9fd874c760df5714c760,0xcfd645c7609fd8750760,0xded724cb60eed624cb60,0x9fd874cb60ddd734cb60,0xebd6450b609ff874cb60,0xafd8650b60dbd7450b60,0xcfd7458b609fd8750b60,0xaff8558b60aff8458b60,0x9ff835cb609ff815cb60,0x9ff845cb60cfd645cb60,0xebd6450f609ff855cb60,0x9fd8750f60dbd7450f60,0x9ff825cf609ff815cf60,0x9ff855cf609ff845cf60,0xdf541dc121bbf845c121,0xded42dc121df561dc121,0x9fd84dc1219fd83dc121,0x9fd86dc1219fd85dc121],#[0xfe53250521bf78050521,0xbf58650521fb54350521,0xbf78058521bf78650521,0xfe54258521fe53258521,0xef76358521ef56358521,0xdf77358521df57358521,0xef76458521ef56458521,0xdf77558521bf78458521,0xfcd434c921fe7814c921,0xbed844c921fcd634c921,0xdef754c921bef844c921,0xded764c921bef854c921,0xbef8350921def764c921,0xbef8550921fad6450921,0x9fd8758d219fd8750d21,0xbf581d8d219ff8758d21,0xbf7815cd219fd87d8d21,0xdf7815cd219ff805cd21,0x9ff855cd219ff845cd21,0x9fd80dcd219ff865cd21,0x9fd85dcd219fd84dcd21,0xdbf74591219fd86dcd21,0x9fd8759121cfd7659121,0xcfd76d9121bf581d9121,0x9ff805d1219fd87d9121,0x9ff855d1219ff835d121,0x9fd80dd1219ff865d121,0x9fd85dd1219fd83dd121,0x9fd80dd5219fd86dd121,0x9fd84dd5219fd83dd521,0xbf7815d9219fd86dd521,0xdf7815d9219ff805d921],#[0x9ff845d9219ff835d921,0xbf5819d9219ff855d921,0xbbd849d921bed829d921,0x9fd80dd9219fd879d921,0x9fd84dd9219fd83dd921,0xdf561dc1319fd85dd921,0x9fd84dc1319fd82dc131,0x9fd86dc1319fd85dc131,0xef56458531df77258531,0xdf77558531ef76458531,0x9ff8758931bf78558531,0x9fd87d8931bf581d8931,0x9fd80dc931bf7815c931,0x9fd85dc9319fd84dc931,0xdbf74591319fd86dc931,0x9fd87d9131bf581d9131,0x9fd82dd1319fd80dd131,0x9fd86dd1319fd85dd131,0x9fd82dd5319fd80dd531,0x9fd86dd5319fd84dd531,0x9ff805d931bf7815d931,0x9ff825d931df7815d931,0x9ff855d9319ff845d931,0xbdd839d931bf5819d931,0x9fd879d931bbd849d931,0x9fd82dd9319fd80dd931,0x9fd85dd9319fd84dd931,0x9fd83dc1419fd82dc141,0x9fd86dc1419fd85dc141,0x9ff87589419ff874c941,0x9fd80dc9419fd87d8941,0x9fd85dc9419fd83dc941],#[0x9ff805d9419fd86dc941,0xbf5819d9419ff825d941,0x9fd80dd9419fd879d941,0x9fd82dc1619fd82dd941,0xcfd64dc1619fd83dc161,0x9fd85dc1619fd84dc161,0x9ff874c961edd634c961,0x9fd80dc961bf78158961,0xcfd64dc9619fd83dc961,0x9fd85dc9619fd84dc961,0xef78158d61bf78158d61,0xcff7558d61aff8458d61,0xafd84d8d61aff8558d61,0x9fd80dcd61afd85d8d61,0x9fd84dcd619fd82dcd61,0xafd83d91619fd85dcd61,0x9fd80dd161afd85d9161,0x9fd83dd1619fd82dd161,0xbdf835d5619fd85dd161,0x9fd82dd5619fd80dd561,0x9fd84dd5619fd83dd561,0xedd634cb61ded724cb61,0xdbd744cb61ddd734cb61,0x9ff874cb619fd874cb61,0x9ff835cb619ff805cb61,0x9ff855cb619ff845cb61,0xcfd7558f61aff8458f61,0x9ff805cf61aff8558f61,0x9ff845cf619ff825cf61,0xdbd805d3619ff855cf61,0xdbd835d361dbd825d361,0x9fd81dc132dbd855d361],#[0xddd63dc132ded62dc132,0x9fd85dc1329fd84dc132,0x9fd80dc5329fd86dc132,0x9fd85dc5329fd84dc532,0xbef81589329fd86dc532,0xfcf8358932fcd6358932,0xeec7658932bef8558932,0xbf9801d932eef7658932,0xcfd761d932bf5811d932,0xbef825d9329fe871d932,0x9ff805d932cff765d932,0xdef825d9329ff815d932,0xcff769d932bed829d932,0x9fd80dd9329fd879d932,0x9fd81dc1629fd81dd932,0x9fd84dc1629fd83dc162,0x9fd80dc5629fd85dc162,0x9fd84dc5629fd83dc562,0xbef8258d629fd85dc562,0x9fd80dcd62aff865cd62,0x9fd84dcd629fd81dcd62,0x9fd80dd1629fd85dcd62,0x9fd83dd1629fd81dd162,0x9fd80dd5629fd85dd162,0x9fd83dd5629fd81dd562,0x9ff805cf629fd84dd562,0x9ff845cf629ff815cf62,0xff9424c1109ff855cf62,0xff9624c110ff9524c110,0xff93250110ff9644c110,0xff96250110ff95250110,0xff96350110ffb6250110],#[0xff96550110ffb6350110,0xff93254110ffb6550110,0xff96254110ff94254110,0xff98254110ffb6254110,0xffb6354110ff96354110,0xff96454110ff98354110,0xff98454110ffb6454110,0xffa8654110ff98654110,0xff56548510ff56348510,0xff55250510ff53250510,0xff76250510ff56250510,0xff76350510ff56350510,0xff76550510ff56550510,0xff54254510ff53254510,0xff76254510ff56254510,0xff76354510ff56354510,0xff76454510ff56454510,0xff54258510ff53258510,0xff56258510ff55258510,0xff56458510ff56358510,0xff7814c910ff56558510,0xfed624c910fed524c910,0xdfd744c910fdd634c910,0xdfd754c910dff744c910,0xbfd854c910dff754c910,0xdfd764c910bff854c910,0xbfd864c910dff764c910,0xdfd7350910bff864c910,0xdfd7650910dfd7550910,0xdfd7354910fed6254910,0xbff8354910dff7354910,0xdff7454910dfd7454910],#[0xdfd7654910f7d6554910,0xbfd8654910dff7654910,0xffb8058910bff8654910,0xdff7358910dfd7358910,0xdfd7458910bff8358910,0xdfd7558910dff7458910,0xbff8558910dff7558910,0xdff7658910dfd7658910,0xdfd74d8910bfd83d8910,0xdfd75d8910dff74d8910,0xbfd85d8910dff75d8910,0xdfd655c910dfd635c910,0xdfd63dc910dfd53dc910,0xfdd6354d10dfd65dc910,0xdff7654d10f7d6554d10,0xff78158d10bfd8654d10,0xdfd7458d10bff8258d10,0xefd6558d10dff7458d10,0xdfd7558d10eff6558d10,0xbff8558d10dff7558d10,0xdff7658d10dfd7658d10,0xdfd74d8d10bfd82d8d10,0xefd65d8d10dff74d8d10,0xdff75d8d10dfd75d8d10,0xbff825cd10bfd85d8d10,0xdff825cd10bff865cd10,0xbff8359110dfd645cd10,0xbff8559110dfd7559110,0xbfd83d9110dfd7659110,0xbfd85d9110dfd75d9110,0xdff655d110dfd655d110,0xdff65dd110dfd65dd110],#[0xbff8259510ff58159510,0xdfd7659510bff8359510,0xdfd8759510dff7659510,0xbfd82d9510dfe8759510,0xbff825d510bfd83d9510,0xdff825d510bff865d510,0xdff865d510dfc865d510,0xdff825d910bff825d910,0xff93150120bfd829d910,0xff96150120ff95150120,0xff96350120ff95350120,0xff93158120ff96550120,0xff95158120ff94158120,0xff98158120ff96158120,0xff95358120ff94358120,0xff98358120ff96358120,0xff98558120ff96558120,0xff5614c520ff5514c520,0xfed524c520fed424c520,0xfdd534c520fed624c520,0xdff744c520dfd744c520,0xdff754c520dfd754c520,0xbff854c520bfd854c520,0xdff764c520dfd764c520,0xbff864c520bfd864c520,0xfed6250520fed5250520,0xdfd7550520dfd7350520,0xff56154520dfd7650520,0xfed6254520fed4254520,0xdfd7454520bff8354520,0xdfd7654520dff7454520,0xbfd8654520dff7654520],#[0xfed4258520bff8654520,0xfed6258520fed5258520,0xeff6358520efd6358520,0xdfd7458520bff8358520,0xefd6558520dff7458520,0xdfd7558520eff6558520,0xbff8558520dff7558520,0xdff7658520dfd7658520,0xbfd83d8520efd63d8520,0xbfd85d8520efd65d8520,0xdfd65dc520dfd63dc520,0xfed6550920fed6350920,0xfed6354920fed4354920,0xfed5358920fed4358920,0xfed6558920fed6358920,0xbff8550d20dfd7550d20,0xbff8650d20dfd7650d20,0xdfd7654d20bff8154d20,0xbff8158d20dff7654d20,0xdff7458d20dfd7458d20,0xeff6558d20efd6558d20,0xdff7558d20dfd7558d20,0xdfd7658d20bff8558d20,0xbfd81d8d20dff7658d20,0xbfd85d8d20efd65d8d20,0xbff855cd20bff815cd20,0xbfd85d9120bfd83d9120,0xdfd65dd120dfd655d120,0xfed8259520bff8159520,0xdfd7659520bff8359520,0xdfd8759520dff7659520,0xbfd81d9520dfe8759520],#[0xbff815d520bfd83d9520,0xdff815d520bff835d520,0xbfd819d920dff835d520,0xbfd859d920bfd839d920,0xff94154130ff92154130,0xff94254130ff98154130,0xff98254130ff96254130,0xff98454130ff96454130,0xff92158130ff98654130,0xff98158130ff94158130,0xff95258130ff94258130,0xff98258130ff96258130,0xff98458130ff96458130,0xff54148530ff98558130,0xfed4248530ff56148530,0xfdd6348530fed5248530,0xbff8448530bfd8448530,0xbfd8548530dff7548530,0xdfd7648530bff8548530,0xbfd8648530dff7648530,0xfdd3250530bff8648530,0xbff8250530dff7250530,0xdff7550530fdd6350530,0xdfd7650530bff8550530,0xbfd8650530dff7650530,0xdff7254530bff8650530,0xdff7258530dff7454530,0xdff7458530efd6458530,0xefd64d8530bfd82d8530,0xbfd84d8530dff74d8530,0xbff845c530bff825c530,0xdfd52dc530dfd42dc530],#[0xdfd64dc530dfd62dc530,0xfdd6350930bff8150930,0xdff7550930fbd6450930,0xdfd7650930bff8550930,0xbfd8650930dff7650930,0xbff8154930bff8650930,0xdfd7654930fed6254930,0xbff8158930dff7654930,0xfdd6358930fdd4358930,0xeff6458930efd6458930,0xdff7458930dfd7458930,0xdff7558930bff8458930,0xdfd7658930bff8558930,0xefd64d8930dff7658930,0xbfd84d8930dff74d8930,0xdfd65dc930bff845c930,0xfdd6458d30fdf8258d30,0xbff8159130fdf8458d30,0xdff7559130bff8259130,0xdfd7659130bff8559130,0xbfd82d9130dff7659130,0xdfd65dd130bff825d130,0xbfd82d9530dff65dd130,0xbff825d530bfd84d9530,0xbff825d930bff845d530,0xdff825d930bff845d930,0xbfd829d930dff845d930,0xff5514c540bfd849d930,0xfbd424c540ff5614c540,0xfbd644c540dff724c540,0xbff854c540dff754c540,0xdff764c540dfd764c540],#[0xbff864c540bfd864c540,0xdff7254540ff56154540,0xdff7654540dfd7654540,0xdff7258540fbd4258540,0xeff6358540efd6358540,0xfbd6458540bff8358540,0xeff6558540efd6558540,0xbff8558540dff7558540,0xdff7658540dfd7658540,0xbfd83d8540efd63d8540,0xbfd85d8540efd65d8540,0xdfd65dc540dfd63dc540,0xbff854c940bff814c940,0xfbd6550940fbd6350940,0xbfd83d8940bfd81d8940,0xdfd63dc940bfd85d8940,0xbff8158d40dfd65dc940,0xefd6558d40fbd6458d40,0xdff7558d40eff6558d40,0xdfd7658d40bff8558d40,0xbfd81d8d40dff7658d40,0xbfd85d8d40efd65d8d40,0xbff865cd40bff855cd40,0xbff8159540fbd6559140,0xfbd8459540bff8359540,0xdff7659540dfd7659540,0xdfe8759540dfd8759540,0xbfd83d9540bfd81d9540,0xbff865d540bff835d540,0xbfd859d940bfd839d940,0xff93158150ff92158150,0xff96158150ff94158150],#[0xff98158150ff97158150,0xff94258150ff93258150,0xff97258150ff96258150,0xff94358150ff98258150,0xff97358150ff96358150,0xff96458150ff98358150,0xff98458150ff97458150,0xff56148550ff54148550,0xfed4248550fed3248550,0xbfd8348550dff7348550,0xbfd8448550bff8348550,0xdfd7648550bff8448550,0xbfd8648550dff7648550,0xbfd8748550bff8648550,0xff5614c550bff8748550,0xbff824c550dff724c550,0xbff844c550dff744c550,0xdff764c550dfd764c550,0xbff864c550bfd864c550,0xbff874c550bfd874c550,0xbff8250550dff7250550,0xdff7650550dfd7650550,0xbff8650550bfd8650550,0xbff8750550bfd8750550,0xdff7258550ff57158550,0xefd6358550bff8258550,0xbff8358550eff6358550,0xeff6458550efd6458550,0xbff8458550dff7458550,0xdff7658550dfd7658550,0xbff8758550bfd8758550,0xefd63d8550bfd82d8550],#[0xdff74d8550bfd83d8550,0xbfd87d8550bfd84d8550,0xbff825c550dfd725c550,0xbff835c550dfd735c550,0xbff845c550dfd745c550,0xdfe765c550dfd765c550,0xdfd32dc550bff865c550,0xdff62dc550dfd62dc550,0xdff63dc550dfd63dc550,0xfed624c950bff814c950,0xdff764c950dfd764c950,0xbff864c950bfd864c950,0xbff874c950bfd874c950,0xfed7258950bff8158950,0xbff8358950dff7358950,0xdfd7658950bff8458950,0xbfd8758950dff7658950,0xbfd81d8950bff8758950,0xbfd84d8950bfd83d8950,0xbff815c950bfd87d8950,0xbff835c950dfd735c950,0xdfd765c950bff845c950,0xbff815d950bff865c950,0xdfd815d950bff825d950,0xdfd825d950dff815d950,0xbfd819d950dff825d950,0xbff8348560bfd829d950,0xbff8548560efd6548560,0xefd624c560ff5614c560,0xdff724c560eff624c560,0xefd644c560fdd434c560,0xdff744c560eff644c560],#[0xbff844c560bfd844c560,0xeff654c560efd654c560,0xbff854c560dff754c560,0xbff864c560bfd864c560,0xbff874c560bfd874c560,0xeff6250560efd6250560,0xfbd4350560dff7250560,0xbff8350560dff7350560,0xeff6550560efd6550560,0xbff8550560dff7550560,0xbff8650560bfd8650560,0xbff8750560bfd8750560,0xefd6358560efd6258560,0xefd6558560efd6458560,0xdfd725c560efd625c560,0xbff835c560dfd735c560,0xdfd745c560efd645c560,0xefd655c560bff845c560,0xbff855c560dfd755c560,0xefd654c960bff814c960,0xefd6358960bff854c960,0xefd4358960efd6558960,0xefd7558960efd7358960,0xdfd735c960efd43d8960,0xdfd755c960efd655c960,0xbff8150d60dfd43dc960,0xeff6550d60fbd6450d60,0xbff8550d60dff7550d60,0xbff8650d60bfd8650d60,0xbff8750d60bfd8750d60,0xefd6458d60bff8158d60,0xbff8558d60bff8458d60],#[0xbff815cd60ffb805cd60,0xdfd745cd60efd645cd60,0xefd655cd60bff845cd60,0xbff855cd60dfd755cd60,0xefd655d160efd7559160,0xbff815d560dfd755d160,0xbff845d560bff835d560,0xdfd7548760dfd7348760,0xefd624c760bff8548760,0xefd644c760dfd724c760,0xefd6250760dfd744c760,0xdfd7350760dfd7250760,0xbff8550760dfd7550760,0xdfd7350b60dfd425c760,0xefd4358b60dfd7550b60,0xdfd63dc121dfd435cb60,0xff56358521ff56350521,0xbff8058d21fed6350921,0xdff7458d21dfd7458d21,0xbff8558d21dff7558d21,0xdff7658d21dfd7658d21,0xbfd85d8d21dff75d8d21,0xbfd85d9121bfd83d9121,0xdfd62dc131bff825c131,0xff54258531dfd64dc131,0xff56458531ff56258531,0xbff8058931dfd7650931,0xeff6458931efd6458931,0xbff8458931dff7458931,0xbff8558931dff7558931,0xdff7658931dfd7658931,0xefd64d8931bfd80d8931],#[0xbff8059131bfd84d8931,0xdff7559131bff8259131,0xdfd7659131bff8559131,0xbfd80d9131dff7659131,0xbfd809d931bfd82d9131,0xdfd62dc141bfd829d931,0xdfd63dc141dff62dc141,0xfed624c941dff63dc141,0xbfd864c941dfd764c941,0xdff7358941bff8058941,0xbff8558941bff8358941,0xdff7658941dfd7658941,0xbfd83d8941bfd80d8941,0xbff825c161bfd85d8941,0xefd644c961bff804c961,0xbff8058961bff844c961,0xefd6458961efd6358961,0xbff8558961bff8458961,0xbff805d161bff805c961,0xfef8158932bff825d161,0xdfd63dc162fef8558932,0xbff835c562dff735c562,0xbff855c562dff755c562,0xbfd83dc562dfd73dc562,0xbfd85dc562dfd75dc562,0xbff8058d62dfd63dc562,0xbff815cd62bff8158d62,0xbff855cd62dff755cd62,0xdfd75dcd62bfd81dcd62,0xbff815d562bfd85dcd62,0xbfd81dd562bff835d562,0xdfd81dd562bfd83dd562],#[0xffd6350910dfd83dd562,0xffd6354910ffd6550910,0xffd6358910ffd5358910,0xffd6558910ffd7358910,0xffd7658910ffd7558910,0xffd6458d10ffd75d8910,0xffd8259510ffd6559110,0xffd654c520ffd8459510,0xffd754c520fff654c520,0xffd764c520ffd854c520,0xffd864c520ffe764c520,0xffd874c520ffe864c520,0xffd6350520ffd5350520,0xffd6354520ffd6550520,0xffd7354520fff6354520,0xffd7654520ffd8354520,0xffd8654520ffe7654520,0xffd8754520ffe8654520,0xffd6358520ffd5358520,0xffd6558520ffd8358520,0xffd53d8520ffd8558520,0xffd6550d20ffd535c520,0xffd7654d20ffd8154d20,0xffd8754d20ffe7654d20,0xfff8158d20ffd8158d20,0xfff8458d20ffd8458d20,0xffd8558d20ffd6558d20,0xffd8159520fff8558d20,0xffd8459520ffd8359520,0xffd6250530ffd5250530,0xffd4258530ffd4254530,0xffd6550930ffd425c530],#[0xffd7650930ffd7550930,0xfff624c540ffd624c540,0xfff654c540ffd654c540,0xffd6254540ffd3254540,0xffd6358540fff6254540,0xffd635c540ffd6558540,0xffd8158d40ffd655c540,0xffd6558d40fff8158d40,0xffd8558d40ffd7558d40,0xffd8758d40fff8558d40,0xffd655cd40fff8758d40,0xffd8359540ffd8159540,0xffd6348550ffd8759540,0xffd7648550ffd7348550,0xffd624c550ffd424c550,0xffd644c550ffd724c550,0xffd764c550ffd744c550,0xffd6250550ffd3250550,0xffd7250550fff6250550,0xffe7650550ffd7650550,0xffd7258550ffd6258550,0xffd7458550ffd6458550,0xffd74d8550ffd7658550,0xffd625c550ffd325c550,0xffd635c550fff625c550,0xffd764c950fff635c550,0xffd6358950fff874c950,0xffd7658950ffd7358950,0xffd825d950ffd815d950,0xffd624c560ffd424c560,0xffd644c560ffd724c560,0xffd754c560ffd744c560],#[0xffd7350560ffd6350560,0xffd7550560ffd6550560,0xffd835c560ffd435c560,0xffd845c560fff835c560,0xffd855c560fff845c560,0xffd7550d60fff855c560,0xffd835d560ffd815d560,0xffd424c760ffd845d560,0xfff8058931ffd8058931,0xffd8458931ffd6458931,0xffd8558931fff8458931,0xffd6358941fff8558931,0x14e007c0028800980000,0x1c0260011e007c003480,0x807400340018e00bb805,0x11a00888040c01f400f3,0xac0143009d004b002410,0x8030d017d80b90059002,0x714036e01ae00cd8064,0xd0082603e301e100e98,0xd8122c08fc046c022d01,0x29f814b40a2c04e6025,0x5bc02d0016100ad00551,0x7206180303017940bb00,0x40d3406830338819540c,0x1c200dce06da036181ac,0xcc81df40ec2073b038d0,0x6041b020180fac07ab03,0x8ef0464822b41122086,0x300096404a4024b01216,0x94140809d404dc0265c1,0x82a6814f20a58051e028],#[0x59f82c5015e60acd0558,0xdf05e182e88170c0b600,0x20c54061c0305c17f60b,0x19d40cb5064f031cc18c,0x63c1ad20d52069603454,0xa0384c1bda0dc706d303,0x75c03a841d000e55071,0xf3f079183c441df40ed4,0xb40fb907ce83ddc1eb60,0x820bc1047080e040001f,0x43802174109e0843841e,0xcc845e0229a112208808,0xf090c0480423b611b008,0x12b8095304a0024b4122,0x6a6132d098b04bfc25bc,0xb827ae13ac09c584dbc2,0x51f028d414350a0c84f,0xa86853d829b414be0a51,0x9e0ac3855c02a9e15290,0x616220af6857582b7415,0x2dca16c40b47859a42c8,0xe142ec817480b9105c18,0x605fac2f9e17b30bcb85,0xc39061583088182d0c0,0x9030c6e8632c31541889,0x82199b0cbd06550325c1,0x834441a0b0cf78676033,0x6b3035561a8f0d34868f,0xb386d2c36541b090d768,0x30dee06f00373e1b7e0d,0x1c6d0e26070d438321bf,0x9e81cce0e59072803908],#[0xd83abe1d430e96074403,0x77843b8a1da90ec9075,0xf3b879583c6a1e1e0f01,0x300f8787b903d721e9d0,0xe1fc80fd107e043eac1f,0x40a82042100b880143fb,0x43441ce20c61052881fc,0x40863042d6214a109488,0x11200884043e821ce10d,0x2e0115f88a3c44dc225c,0xa236411a408c7446022,0x480823d911e388e8447,0x925448d4244e12190908,0x930942849dc24cd12588,0x112cb095d44abc253d12,0x2659131c0985c4be225c,0xdfc26e7136809a944cfe,0xec4ed2274d139389c544,0x89f704f7627ae13c689d,0x4340a11c5060280f13f9,0xfe146e8a3045136287f1,0x8297d14b30a500524828,0x543a29f714ed8a6ac532,0xa7c55062a6215230a8bc,0x80ac5055f02adc155d8a,0x15d78ae4c56e42b56159,0xc54161e8b09857f62bd5,0xde2cc916590b26c58ea2,0x45b042d5c169d8b45459,0xb8605c022de016e20b66,0x5c0ba5c5d002e5f171f0,0xc17a08bc6c5df42ed417],#[0x2fe117dd8be905f1a2f6,0xee306018248c0a05ff0,0x6c619230b7184d8c2246,0xc504624a311318808c3,0x8df0c6886316317418ac,0x5419198c85c640031da1,0xa32bf19518ca1c64e032,0x668c332f198c0cc0465c,0xf846776339f19bc8cd9c,0xd0d1bc689c341e1a010c,0x1a8a0d3cc699034b61a4,0x5911aba8d5646a84352b,0x6236101afc8d7606b6e3,0xc6d6a368a1b398d9346c,0xde1c6ecc373b1b880dbb,0x340e0cc6ffc37c91bd40,0x31c968e3e0718638981c,0x39c81cd60e60472d4395,0x5523a831d270e87873dc,0x9c766e3b0c1d730eb3c7,0xf09c77f83bd11dcb8ed,0xe4d0f22078d83c5a1e24,0x171e800f3b879ae3cbb1,0xa3d911ebd0f5507a663d,0x7c583e101ef28f7107b5,0xb6c7d743e851f348f934,0x70fcc87e403f0e1f7b8f,0x1fe40feb07f163f6f1fa,0x772028900d4803c3ff3,0x60410a207210320814e4,0x88372419820be1055882,0x9008466421c21001076],#[0x6390ac08532427d212e1,0x3219b90c6c85fe42e821,0x43cd21db10e4086de435,0x8bc444222131105087dc,0xbc89a644ad224b111e88,0x115548a5e451d2280913,0x2e9117008b5c458822b1,0x452319918488c0045e42,0x846ab2347919f48cb846,0x8e5a4711237f91b8c8d9,0xe808f1c477223b011d24,0x3920548ffc47e223e091,0x2449121d890b44843241,0x9192483923ac919e48b3,0xfa497024af12530926a4,0xc93d049d124d81263c92,0x299494924a32250d927f,0x6712ac895404a8e25391,0x1259012c4c95f84ae525,0x4bb125c812dd096b04b4,0x87a4c21260012fa497a4,0x4c99644c9b263f931649,0x9350c9a584d102675133,0x6e01367c9b1a4d7126aa,0x38270e138149bdc4dd72,0xa4e9e2743939ac9c9e4e,0x9e0e4ef5276f13b1c9d6,0xdd49eb24f47279a93c64,0x93f809f7e4fa827c893,0x283394140a0725027280,0x102287094314a15c5088,0xfe515e28a6144d4a2325],#[0xa3c051c428d414630a2,0x4910a46452252907147f,0x6814ad0a530527c29329,0x29a514cb8a61052e229,0x53e529e214eb4a722537,0x8c4544b2a179504ca802,0x7ca99054b12a4d1520ca,0x95528aa6655122a7b153,0xae6156e8ab3255822ab0,0x492b141581cabea55e32,0x456c82b5615a18acde56,0xae80572e2b8915bd8adb,0xf08af60578f2bbc15d70,0xf960a0b02257f02bec95,0x2c4b161fcb0da585b2c1,0x90e2c7e16394b1a658bc,0x3e598d2cbb1652cb25e5,0x4b40a59e92ce6966ecb3,0x69ccb4ae5a452d199688,0x7f96b78b5845aa12d479,0x12db296d38b6645b162d,0x5bf12de816ebcb7305b8,0x8fa5c662e27970ccb81a,0xc0b9b25cc22e5597250b,0x17544ba745d1e2e83973,0xefd97754bb5e5d8e2eb4,0x822f331793cbc665e122,0x25ef22f7017ad4bd325e,0xbefc5f5d2f9b97c6cbe1,0xa0c0225feb2fe297e90,0x1183f0c1c060ab303398,0x30da98650c2d26143309],#[0x291313a98964c47061f4,0x6c6306317018ae8c5466,0xcc77463a331c398d5cc6,0x9244c8fe644f321c18fb,0x91193f0c9d464ce32591,0x832d099628cac8654d32,0x660532f719770cb9465b,0xd186670332c998f4cc42,0x74ce0c66ef336999adcc,0x99e84cef6675a339c99c,0x40f1a01ccfcc67d433de,0xd734561a240d0f268533,0x26960349d1a48cd21868,0xd4d26a3935049a7a0d35,0xe18d6846aef355f9aa64,0x99b0b4d8186be635e01a,0x36619b2b0d9206c79362,0xd5936a11b45cda006ce9,0xc06dc436d69b644dae06,0x4dd186e57371b1b840db,0xbd14de3e6efe37649bab,0xe89bed4df3c6f8237b09,0x3381b9c06ce0086fe837,0x70fa38719c2b8e106705,0x39871a638bb1c52ce236,0xb4e4fa725739189c804e,0x1ccc4e60c72ea39649ca,0x9e39ceace71e737339a9,0x9e3a371d0f8e80873e83,0x475273a859d36ce99274,0xebca75bf3acf1d590eaa,0xb18ed5476663b189d82c],#[0x29de54eee8773f3b851d,0x3c6a9e2bcf0ae78183be,0x9e83ce89e6acf2ba791e,0x247a493d191e858f3fe7,0x8f6907b2c3d769eaccf5,0xf298f8ce7c0f3de59ee0,0xb49f534fa127ced3e639,0x3f121f780fb887d9e3e,0x7f0f3f771fabcfce07e4,0xf367f7f3fb41fd44fe6a,0x9d00207fef3fe71fedcf,0xa0325015080644026a00,0xaaa04f9024481014072,0x8641352088503ba818f4,0xc83234179a0b71054482,0x7ea83d941d9a0e5d069,0x1dd08c08444421421031,0x821415098c84aa424721,0x42eba16b10b0c856a429,0x6684326218c10c3285fd,0xf286dd435e21a810d088,0xd0f2c8757439b21c690d,0x21f110b6882143f8a1ed,0x892241511b488b44449a,0xc44cb225ad12a8892e44,0x8a1d4503227bd13b089b,0x5168a6f452ea292d145e,0xd15ce8acb455ca2a9d1,0xa2db916908b36458fa2c,0x5faa2f79178e8b9745c2,0x77462da311118648c0c4,0x68cdd46632328119128c],#[0x1b048d6646a7a34a51a0,0x7fd1bc68dc246d823679,0x123a991d0a8e5f471ca3,0x478ca3c1d1df48ede476,0xf9647bd23d8d1e988f2b,0x128ff247eb23efd1f508,0x520b6904948192406d20,0x4325216490a04842241b,0xafa44f92244910648702,0xa48ef2471d2360919948,0x9292493624955245491f,0x69693344984a4b792570,0xe9279e93ae49c924db12,0x251bd28b094324a0b24f,0xaa32548129d694c04a43,0x134afba571d2b1a95714,0x2968d4b3b259552c5e96,0x2e3c97074b7aa5b512d5,0x112fbc97a94bbf25cfd,0x5a61d130c4984b4c1a26,0x4c8f26391319a98ac4c4,0xa224d00a6731331a9953,0x569b004d5ba6a4534b89,0x937f49bbb4dc826dbd36,0x72f539069c584e192705,0xe5a76593ac29d1d4e742,0xe4f36a79453c6a9dec4e,0x9f264f7da7b7d3d549e8,0xfd29fc84fdb27e193e98,0x3940eea05b501fa80513,0xa85614232a0ee505f282,0xf228749436ca19a50c1],#[0x66512a289094442a2005,0xaa2f9516c28b054536a2,0x476ea39b51b0a8d15462,0xf9484ea40651f028f39,0x2a92cd492ea476522aa9,0x52bb295694a7ca509526,0x63e5309a97a14b7aa597,0x94a69f5346a99c54cb4a,0x14ebaa737538129b854d,0xa0314fe0a7d953dea9e2,0x792a33150e8a84454142,0xa54b12a541525ea91854,0xaa985531aa91d5424a9b,0x670ab265587aabb955a4,0x115746ab8755b82ad515,0xab185586cac0b55fa2af,0x680ab359596aac8f5639,0xab56bdab57d5a86ad275,0xaae70572cab8cd5ba2ad,0x5ee8af3557802bb415d4,0xdd6018afeb57e52be7d,0x9ac365617ab08358312c,0x58d0ac5ed62d2b134588,0x22859062c7d563b2b1b3,0x86b2a75945ac9a96488b,0x5668eb330598cacbcd65,0xcfc5678cb3af59bfacdb,0x732d2ed690cb4605a10a,0x65acbad5c56a78b51b5a,0xb6b45b3aad9296c34b5d,0xeeeb7475b90adc016dbe,0xfd705ab8205bffadf296],#[0xae321714eb88b5c32ae0,0xcaf2e4f57242b9005c74,0xd5cf12e6dd7340b9895,0x6ba7d5d2e2e9017448ba,0x766cbb1a5d7f2eb11754,0xff977babba85dbeaed85,0x22f2d17908bc5e5e14ae,0x5ed22f5f97aa6bd235e7,0xe675f25af8a97bccbdbb,0xe6bec35f562fa557cfcb,0x17f34bf745fac2fcb57d,0x71800abff35febaff0,0x42b01cd80aec0456019b,0x260733033d8166c09c60,0xc17260a8b04d5823cc10,0x41ac1ec60e5b06bd8330,0x19855ec2986139308b98,0x30cd98634c2f96173b0b,0x1d4b0e4986f6c36461a4,0x2b620a30fe187aec3c06,0xec4a0623ab113d887ac4,0x8a58c51a6277b1339896,0x6918b1ac57662afb150d,0x4b18c98c22c5f062e531,0x636931aed8d3ec683632,0x77263ab31cc18e00c6e4,0xf2c7e263e331e958f12c,0x190c8c8486416320418f,0x246191d0c8cc645ab225,0xcfb262192d8c955649cb,0x264fdb2791939ac9b664,0xca876535b293d9466ca1],#[0x626caf2656b32ae99546,0xf59738cb8065afb2ce59,0xb30f19836cbfa65ef32e,0x66bb32ed992acc74662e,0x4a6699b34719a14ccf36,0xecdce66d9336319acccd,0x9cdcce57671db38699bd,0xbfd9db2ceb86750b3a01,0xeb3e359ececf416792b3,0x681bb4081a008cfe367d,0xd26853b4241a0d4d049,0x2d15b689fb4465a1e6d,0x9a400d1da68da34675a3,0x4a81a4fed25e69213489,0x98b4c55a5f2d2d8695e3,0xc69d834e51a6e6d35769,0xd43c6a12b5011a7d0d3c,0x9b8d4bb6a4fb520da8ce,0xa1aa98d52b6a85353b9a,0xb574dab6ed5a06ac4b55,0xb2ab58f9ac4ed60b6af7,0xe66b6535acdad2ed67b6,0x4d7566b9fb5c79ae04d6,0xafecd7d56bda35e4daee,0x21db0ead85e6c19b6071,0x63642db1cad8c96c5436,0x6cd336601b2d2d9486c9,0xa326d08b67d5b3bcd9c7,0xb8daac6d4ab69a9b49cd,0x5b6a2db3a6d8cb6bcdb5,0x7029b7c8dbc86dcc36db,0x5537211b8dadc426e133],#[0x2824a0b000e07dcc66e,0x1228120400c4a08c0428,0x85e0f81030562385e0f8,0x783e0704c0088003e01b,0xb8106414202102286e1,0x608380d078001ce1383e,0xe0f5840e078001f8380e,0x420c34170320f828020,0x2d820f43724830d03d0e,0xd037102e0b101800228,0x3d0dc94043d14434043d,0x840b38440600e082282c,0x17030b85108010dc340b,0x30b384e0838170500c34,0xf438105117020043d144,0xa0f840b00b170500c340,0x20841850d070d02e0e83,0x1010d0560e850c200e08,0xe84e0c3c08051120580,0x3410511002c0c040d02e,0xb0702c2e14430043d0dc,0x14430f783805861442e0,0x5c07820c01014450042e,0x1840e050f214608380e8,0x1b828503a0e068038285,0xe0f84050260f045240b6,0x2802140e8421982c0496,0xe102c8500b10870178,0x505111430043d1443e08,0x182c1417051242e14420,0x140e83823830b200e0b0,0x5c02c902c05c0782066],#[0xc0409a14e0e85e0b840b,0xc3a0d02c0c010f0380,0x50082209848103c0e03,0x10220f05a08210e8340c,0xc02820d01e0e85000266,0x38114200185088240f05,0x14302f0008824a082618,0x260882407460e03c1,0x4017840b80d0e03c140d,0x381002c0c2201300098,0xe02d0d048043c0e02d1,0x850882d102d0e02c0c01,0xb4260882c18381202001,0x50c06618381203044000,0x3dc00341c0b0df830f01,0xb00090371485e080125c,0xf840b042c0037140510,0x2c0024a142222850d02d,0x840b05c02c90f00b61b8,0x7000889e0c3c01e85e0b,0x5490741561883e0824a1,0x781d61b8282c37c00340,0x8040660b000882609080,0x3014290680b0e0401504,0xf000d0381c3d02c1a0e0,0x3406838148607e010f,0xa006c00240a4261828c,0x2c0d05e13000b0290e05,0x80b0e82c0d050c01b0e8,0xe838181a0e8340b0406,0xe81a0e0521b8227300,0x1a1b006142408890a30],#[0xb840b00b0e060a006e0a,0x905c003a068381286e0,0x98280906a0a8309b00,0x9a83a08241804a0f0,0xa0221404c00280e8401b,0xc0028098251e84c00260,0x4c00220a024182701504,0x85e0f013041d1148a140,0x300088260a0241a8207f,0x1b01c002209a82090701,0x20986a08260881a09050,0x2608a0b1486c002408a8,0x682c002909c221682090,0xa0241b00089840a0261,0xaa0b000d050130008826,0x380a0450c3811420e80,0x280460f00c0427a08292,0xba082c280ac005110040,0x802585c0301e1028e0c4,0x9e1783e1301c002c0a0,0xa42409c7002830984510,0xa421098409404807000,0xd07782a1683c00241f00,0x240a46017000a43a103,0x9283c00261c0800a85c0,0xc00240a4261c1da1b820,0x2c00240982b180801402,0x28c0024a0c1a09860200,0x2c0486c0024a0c2620,0x1005a0f000a301094602,0x2c003a1085a0f000843a,0x8e1382c030110870200],#[0xc4380c28c00250e04028,0x81784c002c0884214210,0x88211784c002c0a43,0xb01a1b00144211c06a17,0x1825010340b03a142901,0xa08870c402c002209821,0x190e850a302c0026a101,0xb0009a840888097010d0,0x380a021100800b0121,0x812020a684c002209c5c,0x280d05025860e048103,0x30109e840a4760821c0,0x1b82617000d0602002c,0x802802c00341583a1808,0x9c21b01e08050eb000e0,0x28600f82a1424c002220,0x1028c0024a141a088602,0x92850888c043a06438,0x28c04251c0800b0121b0,0x7000a434100900e85c00,0xd05c2285c00210d04a1,0x5098712c0a02382a1700,0x2909870240400c28c002,0x4310e0302002e13000b0,0x2186e0b84c002c0e0708,0x4100900428c003809460,0x3ac00210d040a70009c3,0x40b02286e083ac00381c,0x2c24140b09022064261,0x2182608a0b18220981a,0x121b0009022098826c2,0x9c8e17830a045100800b],#[0x140800b84c03010a42c0,0xc1700b2801a185108431,0x312c2602185e0f82e102,0xb81614400c070d03a0b4,0x9785e0f8116050eb8305,0xb85e17830b8400b450,0x85e0c401204e1402e0c4,0xf0401c28e1783e045817,0x6440184205b83e05850,0x60f04210040fb85e0f81,0xc4515850b43d1083e100,0x17830a019114503385e0,0xc614562b85e0c2e0f04e,0x61082d06783c0b812720,0x4401c29e0f8106585100,0x143e1c2901b83e043c61,0xa050c2829e0f81e102d6,0x801f2189ae17834b784,0x3e1b8500b83a043e1006,0x4280b45e1400e0e81094,0x1383a04284307e1783a0,0xe1783a04250f85e152de,0x2c0f85e0e81094288306,0x4150a0380303a14340e8,0xc00341429c0b00088271,0x4c0b000b438180a0eb02,0x9007840b4380f8601b8,0x21851603e17830b05810,0x81204e1400e0c2c16051,0x5c002509c281b85e0c2,0xc160b7840dc0c1086098,0xe049cc00401c161002c0],#[0x10a300a1425204221783,0x2da140c0a0709c26e0f8,0x685097000a07e0f81e10,0xf81c0016100610b83e0,0xe1783e04250a81d1c42e,0x420f8401b00094421002,0xce178309445142d0f4,0xe0c2c0f85e1783094451,0x3e0585c00250a08e1425,0x81e102d6143e1c2901b8,0x842e0f81614581429e0f,0x8060130009c1f094291,0x707c281785c0b00a0d3e,0x85c002507c281a84c002,0x42d0181fc00270a0601a,0x943f1028c001f094271,0x500b81a0c400f86c0043,0x85e1400e06830943e1b8,0xa0250bc4e1781a0c250f,0x302307c2509c1d1c0c0,0x401302c00240981f140e,0x37c03021086a0f00080,0x9850f70010042100a01,0x5108200c8309302c001f,0x2d1087012830dc2d108,0xc20160501c01e1302c0,0xe1404e0c25114501b85e,0x830a0451785e0c201604,0x145e17830a045138500b,0xe0c251144e1783020861,0x201785e0c08218451785,0x302c00291826c0b00088],#[0x240361448160509c1fa1,0x6088201b85e0c2812040,0x1f0a68409c660702c002,0xf83e0585c00401f02c00,0x2385e0f810943e140901,0xa40621783e049cc0040,0x901f83e0428a17000948,0x470a783e068506440180,0x9480a783e0685c008609,0x180901f83e070021a850,0xa4701822a1702c0024,0x2010040280407e85c0b0,0xf81e0e85c00401e85c00,0xa14292285088450c0901,0x16030280460f02c001f,0x83e07840b6850f88a142,0x383e041d0a0251c0901f,0x6785e0f810943e1b8503,0x71d8108b0009b0209060,0x3e140a0101f0a702c002,0xf81614581b85e0c25080,0x3383e0419094602407e0,0x385e0f810943e1b850,0x987e1783e04250f85,0xc1f0a0701181c0822093,0xa0200c850280460f0009,0xe13006142d0a09e17830,0x28003a170502407e0f81,0x837108600c3417038538,0x38141705627848021460,0x108371b84e0496c0d828,0x2850420dc6e0a0085184],#[0x84c0f820505c1600e138,0x70380384e0a140dc4223,0x170603b84e0a14170501,0x20505c141905384e0b03,0x1f83834064381f84c0f8,0x7056203d108560c3c00d,0x108506781c0d820fa0e1,0x50f05c1003c0c3d06582,0x4191085801840f456108,0xc0e1145c1588e083c0f,0x610420f03d14190d184c,0x3d1b84c0f820645c1410,0xa191705c0f82065850f0,0xf820f019170503b84e0,0x1c002718810c0370f04c,0x810f42d0dc407a820a68,0xa48076840a681c002718,0x241e07784e0a85a07000,0x21b8203b840889ac0037,0xe07784e0b0009c9a1c2c,0xc6c0f820643ca0442181,0xf0271c2ce0b002183c0d,0xa04421c1ee0b0021a810,0x10f027201bc03820f01e,0x250dc402b82c0086e128,0xdc40383d0b0371028c00,0x71f000e83d0c24c00210,0x1d140a02384e083dc003,0xc300dc3c0c230a42707c,0x9c2907c21183d0c0420,0x1f0a41d182e158200b00,0x6031082c15846100009c],#[0xa0827181ea0b000dc421,0xe0f43c10840841fc0029,0x4078000a41f09c1d180,0x143c4384a141e0f4420f,0x130009c1fa08291c03e,0x271b030f68206442140a,0xa8209c70781fa0b00218,0xa42708c502804c001f21,0xc030309a8209070381f0,0x4010240dc2d100401981,0x703c002010040a80e0dc,0x28076144e10300a085c2,0xc1c0700b001704017030,0x2c0e0e02785e04340b43,0xb45c004204c37102d108,0xc001310860002909c1f0,0x4e08270ac1f1440e0434,0x82c180c80c300dc3c178,0xdf0010850398480c2d10,0xe0b002183c0dc5e13820,0x420dc7e13820dc0e1085,0x42010850781de1382c00,0xb0007c27084601b0008,0x21c3c0f6840644214290,0x1f1f020f02226a84c004,0x27202807684c0027218,0xb840230300b0007c86a1,0xc0f000a02e1303c00260,0x421c0800842c02840dc6,0x82e100801c04c0f000b8,0x1f03c00280b84c030309,0x61c4e02185c00420b851],#[0x421c0301c54c002e1705,0x43d1805e1303e0837c00,0x143c07c7c0f820643ca1,0xf0190dc407b82c0086a,0x2c0086e12850f01f2382,0x602002c0024108502b8,0x8042100700425c00270a,0xe13821080e0dc7087000,0x40038207c270ac602808,0x44e1019e081f0ac271b8,0xa3000dc251824c00260f,0x61020c0042084501d820,0x602808e138210b000dc7,0x271f03e083c07c1909c,0xf027201ee0b002181f0f,0x98602886e0b00e101f0,0x9442100800824c0029,0x83d1c20c002110840f70,0xf048100a02384e098503,0xc0304089300989034510,0xac00510b860a08101b82,0x840405108056103d2181,0xc0a144560c000285115,0x20a70009c2014380a032,0xc38080560f000e02e0c2,0xc22e1781c1300a0c281,0x581585160480e8308056,0x7830f048138500b83080,0x1204e1400e0c201605e1,0x5e17830c02e1385e0c3c,0x8200c05e1783008300b8,0x408c1300a187e17830a],#[0x1785e0c300b84e1783e,0x830642e1b85e0c860803,0x783218200c05e170400b,0x9c211682098220c44e1,0x5e0f000a02e141fc0029,0x9c1028e0d85c002e1f8,0x84431385e0f000a02e14,0x61000a0c201584c00200,0x40c02607c600a830805,0x403d1c370a0320f82c03,0xc03714300a01b0b8420,0x2e07000c0421c02a0c42,0xe0c1b0742e1807c138,0x6c90a783e05851585e17,0x744210210e0d85c002e0,0x12029a17000841b08060,0x50240300886c0020a142,0x42812030c382a14220c4,0xc02c13000a68507c8a1,0x2407e0f81a145618086,0x982e1385e0c201544,0x80551785e0c20154408b,0xe0f000a02e178500b830,0x80081f0a704c00271f85,0x4602407e0f8161456180,0x86101385e0c100801908,0xe0c2006c100846218510,0x261f8500b83080561785,0x48138260700c10220c0,0x102907f0009c8e17830a,0xe0830614102c0860c02c,0x8180a1400901e86e0f81],#[0x51588e083c8503a0643,0x8192019e0d82e06140fb,0x6e1214c1783e044260,0x503d1829e0f810f0141,0xc850190dc60a384e0a19,0x1461305114562b84e083,0x984064a053810e819e0e,0x83a85305e0f81e083c10,0x5384e0f81e083c108192,0xe083c10a8106498001c0,0xea04420f0845384c1783,0x3ca041c289be0f822181,0x4a07914c0384e0b83108,0x40ae1383e083c10a8106,0xf05c0028a04251c5ac1,0x10d04c03050a43410090,0x82c17000d05c2305c002,0xb05c00360bc51680a023,0x2407e0f81c1700104701,0xc1784e0f8110a8206490,0x1e0c42c0282070909914,0x8110a82064a07914e138,0x8241c5a02807c1784e0f,0x8291c0660700c1422a0,0x8040100a01300c141fa,0x7e0f81c17001007c1700,0x8260424c170008880240,0x7830a305c00252408a1b,0x83c06414240901d82e0,0xf0142c26e1381e0f821,0x280721b84e0f82e0442,0x660782c0024c1422205a],#[0x83e0425c17000a080228,0xf85e0e8109519180901f,0x9c190d030e0250f8307,0x190d03094040d03a0b05,0x7820f11c0e8190e06084,0x1703c10020f03a064381,0x2c16040d83c0bc320830,0xb85e0c000b0581785e0c,0xf0706785e0f811043c1,0xe0c0401b85e0f810a830,0x85e0c3e0b0301785e0c2,0x8190b06e0f816145813,0x10a82070192385e0c1ba,0x6a0819090507b84e0783,0xa01027a081907c60882,0x64251785613830944514,0xe1185a08192b85e0c200,0xc0b460280901c5ae0f81,0x3f064431506e1519a0c2,0xf830901f0642613820f0,0x1085a0c2015830dc250,0x820f0190dc6e083c0df0,0xb85e0f000f045140a013,0x11450eb8300381614561,0xca101c0648e178307419,0x81a1219203ae0c42e083,0x819080486c2d07785e0f,0x1f85e0c080642e142608,0x9240860c0207e8406427,0x41680901c3ce0d850b81,0x5e0d82e0419a14301a8,0x141908876102da14190b],#[0xa141909470200260424a,0xca141907c702407e0f81,0x20a1419084702804e083,0x220981a090502403008,0x1906a0826093000886c0,0x9870a283c002406826,0x2208450200241a830930,0x81a0d03a0b0441826c00,0x8803c00251085108300,0x27142107f00a090609c6,0xb000a02f101f41b00094,0x80411b85e0c410b040d,0x5e0c410b04e1402e0f00,0x8301785e0f0008041178,0xe060b030178500b830b,0x21b8310985c00411785e,0x8209c7c020609824a082,0xc25114402804c001f81a,0x178381b00080251b85e0,0x1d85e0f8110b001047e,0x842010850b4420b03,0x9854181fc002109c500f,0xc002510c509206c001f0,0x371c20c002110c401c01,0xa0d140a02384e0b00818,0x142d1584a0e800902608,0x40f04a0f840b80d0e03c,0xa0118309f010a41d1c0,0x13016142e0f070f04a08,0xe0f840b80d0f0702403e,0x380c030b456128302785,0x98220b450e02d1283100],#[0xa0f06128401203044020,0x380f0340c38c08450d01,0x8340e060e9040d03c10,0xc14380f0340c8607c3fc,0x2e0a438180660c260903,0x5040e8341144e1302e00,0xd02d0c1a0343a0b8341,0x1f140de102e0f038143a,0x370c02e10230a01d094,0x610280dc51003c0dc30d,0x380dc6a0c400b030041d,0xc300e02f180d0bb840f0,0xc28074250e051003c0d,0xd0dc340f840b83c0bc40,0x848103d06c510a02c143,0x12830a02607458104a0e,0x407460a2830901d0985a,0x260903c1406c0426a0c2,0x486092830981d1683c08,0xc02f0c2809a83074241,0x3a100f098240741f143c,0xbc30f03a0bc3a0f02078,0xe0cc380c3811420e83c0,0x6e1302e002e08842181,0x78401384c0b800b8290e,0xd14040d02e0c04018510,0x860882e1028a10260881,0x881d17020d01a0c04098,0x708850f04a088609a840,0xc30f0380cc30a684c082,0x34c081e0e850e03c0c,0xd03012840a4270bc46],#[0x45080a0d03a0c046144,0x102ee1380a14290bc60e,0x40b83c0e050081e0cc38,0x60980d0881d0905c078,0x901d1809c08000f0380c,0xc02209c40680d098220,0x300e060d3020783a1029,0x8860742417010e80d0f0,0x1c260888607424140d08,0xd142026f85218220760d,0x830a0451086098220901,0x2ee13800a0270bc6e17,0x6140d0f07004280784a1,0x412a80178502403e102e,0x4520e800a0250bc40a20,0x140a0204aa005e168008,0xc1005e0c0a0204aa005e,0x841008606f031143a183,0xb800e83f100f1143f0e,0x40983e1382e003a0fc4e,0xc400e82098240fc5c0c2,0x92820a4261424a08260f,0x1005c0f010f030140f0,0xa008301784c0f010784,0x18210785e10400f05e0c,0x50983f0c03114260fc40,0xf010a02117030b43a0c4,0xfc3a0c240b45e0c1dc0,0x261408009800e842142d,0xa85084351025077030a0,0xa4261b82e003f0e8407,0x4e09801786e0b8003c24],#[0xfe00240983f1c0a0238,0x783a10250745e0c1ae08,0x61b82e003f0e84087030,0x860987e0b802182403c2,0x42683c4e080fe0024024,0x1b82e00240983f148611,0xd0bc402808c058012842,0x10a4210783514280941,0x281283e0b800a45210,0x2080800829c04270786a,0x8502586044520b450b45,0x81e098501a83a082607,0x21826a0822078501822a,0x29c04270b44084520f03,0xb460a0520b430b45208,0x80841d1009c1211a1838,0x85084110681e08850a03,0x18521205218260842207,0xa09470a01d128302407a,0x1a09c701582e0c3da001,0x41a114502808e1382a00,0xc3da001a0847613830f,0x2384e0a80170601584e,0x3d102e4682215837140a,0x884098220f8609282098,0xc05e0c3d06830142406,0x40f7830b830143009c3f,0x5c103de0c250681e140,0x6b80090260f46028020c,0xc1444e0b800d03713820,0x44e0b800dc51102e0042,0x6c2e0b0341382e003714],#[0xa0e06e0b01e001c14450,0x1a074381008009800d01,0x9c3418210681e0e04094,0x114370d04e0985e001a0,0x3e0c3d068450703a1801,0xc210681d0d040e8340b4,0xa182d0905c0c2d09c3f0,0x1a0e06e0b8008a850921,0x6850681d1c08009800e8,0xb800fc3a100900d8209,0x258400c21a141a0787e,0x3c0dc309683c041d1085,0xf0508402c04270f050b8,0xc0427074506c21c04420,0x2a0c05c043c0d8309506,0x804c04270f85e1783c04,0xc043e1a061441e094402,0x40b82c10c36140310841,0xb800dc511382e0037144,0x1002602060d03c0e06e0,0x60841e0e040960607438,0x4560f82e020609c34160,0x78341051078410c0a14,0x361421c041b078781821,0x3c0c26a00240bc40a58,0xf0340f020dc56103017,0x7005850c3030f0608036,0x372007c082317030140,0xdc402804c0f026003d0f,0x717020e83d0c24c081e0,0x340e03d0c0a01c011583,0xdc2814400183d1083c14],#[0xc0c3e0c05c142a0941d4,0x250742f0c250742f0c41,0x6b850f036142f0d83c0c,0xf0f020748607c2514222,0x941d07c2818360f02,0xf060002507c23074509c,0x7c261007c08000c0370,0x50001f0a02707450903c,0xc230744c0c1f21827074,0x10860941f09c1d142507,0x8090260bc46003d10840,0x4603400088260901d182,0x803c140a0102909c1f07,0xe05850c03c1f85e0c410,0x90e0450d03e140901f83,0x81e0d04c082909c34100,0x10c4a043a0f838103ac0,0x4000250742f10000941d,0x3020983d100700037160,0x160371020a0c1e104409,0x4e17830943e0b0502a83,0xc2909c301022c08260b0,0x2407e0f81614400c0707,0x21c0901f83e068516060,0x291c0dc0981092850f82,0x841100a60f0207e85160,0x11800ff0210c60828507,0x3102481b020981f140a0,0x80c082b0dc5083020784,0xe05c140b1202c1444e13,0x76831145c2301e10450,0x40f45111432a80e61022],#[0x42e144560c4a0d02e158,0xb8301f83040580b8561,0x115851180b61985e0c24,0x3cc058614478008a60b0,0x820c0456144660830080,0xc0200f301618511e0060,0x61182404450e05c1d820,0x85114c404480b0511014,0xaa610260538307701172,0x182c0685115863614608,0x83702d844a4a9e0c2685,0x198409b8360845c04142,0x40600178511705130376,0x60500b6083cc05861447,0x8451c1403901e0851170,0xe8452037051830f7010e,0x11460dc14619832a40b0,0xcc041430106181440451,0x682e000b01961182e0c5,0x83e0826c0586050d1682,0x60dc2c2a60b6103c4a7,0xf03814ab036000d03c0e,0x442d1584a140d8003a0,0x2d0c048102d0e0560c38,0x58560e000b5861207160,0xac1160a84c00560e070f,0x2a01160b00a11860e092,0x160a84c00560e060c128,0xa804582a130061838241,0x1520f000d05c14304a0,0xc005c114aa142c0d0481,0x638156128360c8801e85],#[0x5a0d8201f000f6851158,0x3417040de1502d8460c1,0xd82c0285618342415178,0x1a850d0450ca80540b20,0x80f450540b61a850d045,0x3c0e8340b050683c0d03,0x683e15870e03a0f0302c,0xe0340f4882e834003d0,0xa0d045100b0f38206b00,0x3c0683ac009c0e0706c3,0xc03810010c0a30dc4e08,0x7158320c3017030dc3c0,0x434158408c3815832083,0x1682c00230d05c144a08,0xe03c142ca103842c5c,0x5004381285c101f02c3,0xf10b17080f4230d03c0e,0xc0371423086844112c0,0x7007001704a140702c3c,0x3412044182c0e848100,0x182c048340f03a15060b,0x20e8609b830f28517030,0x4242c381c0805a82c004,0x80b0f4511500a092ce10,0x1583084160e0561300a0,0x1a0b830985c158602851,0x50b0f0a058380f03a130,0xc21a0d034b016e105ca1,0x100b01c3ce0e85170301,0xc04aa0c05e0c5c25856,0x8402301c00451088e0c0,0x2844b28242c4229040aa],#[0x1c371604085044002a02,0x115871603008448100b0,0x5c114e0a505211031602,0x8340f010a98502007c00,0x6821710b311412e84412,0x50440c2a02284a0d2c61,0x240b01f836145c160608,0x6505411030f4450f83c,0x5411030f43e42c3c2701,0x7c0086a0837252c0850,0x821a18481c1e2130402c,0x910ba18212408a168300,0x116864029a1505a0d030,0x8050440e3d4528201f00,0x642cd12c3745585a1283,0x4a0d038f52c09985a0a8,0x3da0b00270b0dc21a110,0x707884c070402c07e0c,0xe878102b027000e0280d,0x144611604073000e0280,0x382c401e0661809a0a0b,0x8582c401e050ac096158,0xb000f451102780d83071,0x1444c0b00a0c5c1445c0,0x2c000b0f4511d0242c3d,0x84004342ac37101dc088,0x130015838200b01c3017,0x1590b14444082b026826,0x371446c0b00170511382,0x85e0d05c1428c0b00218,0x144542c380dc5e102840,0xd03d0e09c08010fc37],#[0xb1707a09028043c00f0,0xc3e0c06412834083c0fd,0x1300a18382800c1701a0,0x14460c4300a28240b016,0x27051143002b82a190b,0x1c0185a18342b020f30,0x90b0e060a00900e8240a,0x3c270511c2ca1282a1,0xa0e0b0903c17022080bc,0x507482a0c2482c261826,0x43a114460824c0029098,0x101d208370b034141b0a,0x226c2c14456141b0d045,0xc3414040e83411440748,0x19850d045141d2082c0d,0xe0c3d0f3002703a2601a,0x2a13001583823022080b,0x84c01860e0a0c6020718,0xc5110310c02880982c06,0x2b8261a0b1446e085682,0xe08150eb002703824300,0x7e0f0127030203c06983,0x8302c1f144907c0b3080,0x49c0e070770220b00271,0xf10b170a02f820f03a06,0x242ca168441282408260,0xa00b40f82c003a27038,0xc0a026e138242c5c1c42,0xb01f832183da14301c2,0x70220b0002c8607c5124,0x1822a160b0903c142807,0x212c507482a142408a0b],#[0x91860888618020902,0x4240884b182840782a17,0x98220760b09060198240,0x21402088240983c15820,0x2e1284814860982482c2,0x98660c2e614481986614,0xc08b8098560c2e100580,0x42186606108318361684,0xa6158160f0210090d08a,0x216170210090d2000408,0xa1911480ea0004183604,0xb4480d086158460583c0,0x60d81c09858644524400,0x560c402683e153742184,0x3e6158460c45c083c218,0x6585c08b614561143604,0x302d4258460428831838,0x61c066158160c400f860,0x401c3e0398560583c085,0x8561c29e0f02e0419270,0xd852b0280183604140f,0x1706c109523c07c0b00a,0x23c07c004526b02a0cd1,0xa120503d0682305c1284,0x83c0185114da1a850b04,0xca0686c128445a07022,0x5060a808a0f00114aa3c,0xb00a05852902a1684a0,0x12860b306c109723c09c,0x804a2407a1a8508048,0x454007a1906a15052130,0x4c080fc000801d85a0c],#[0xc45914a044ca1906a11,0xc07a1a844b6836168143,0x1f000e70244204190403,0x230621b0421281a0d850,0x6144a1c972548f0780c0,0x7a0c45388603008c1b00,0x5a1104c0a81c003e0200,0x2da0e81430c4640fa150,0x204150403c0721a85a11,0x84a068301f000ff023c,0xc9a0788f03008c1485c1,0x10850300841b05c004a1,0x51202d16040302d10048,0x4401205044370b43d102,0x38580942d120407d030b,0xc0c9501f021149ac0285,0x51206055060de08c1284,0x85c00452d000b286a0e8,0x28de84a0e814182a022,0x8c1b04c0983c009531,0x14201205078092188403,0xa0d84a150c080ba1a83a,0x5114e07d0640c1501e86,0x4a0d03a043e0230001e8,0x85a050c341f46415a110,0x440c1501c86a12834b6,0xe8501c5bc0b00442007d,0x895c1084c0e810300820,0xf02c0095309c2683707,0x788420c370300841b04c,0x1c2c40285a0c2812060,0x3e143709a83a0585c004],#[0x30260e813685a0c40268,0xf050a02207f842690cc0,0x290c60c9a0f840142c0a,0x3008c138560f02c009a,0x700685a0c28120707884,0x4da1683c002010050800,0xb842709a43302c028161,0x683e10050dc2c0a30309,0x6a81c01851009431852,0x4616810f8c07d0301e83,0x7d0c40e834b41a01f8,0x8c130361702c009a302,0x8400f860788420c37030,0x10284309a1d0ca168326,0xa048f0f840152de1783e,0x3e1004215830f8401183,0x4832049c0f8401681270,0xe03e102b024340e03e1,0xa1856058316060703a,0x448018360428614581a0,0xe85c00401d13a144011,0x1618510045103809d816,0x18182a0220c60d85c00d,0x400f86032020b5096118,0x4402703e14066158160c,0x1a836141310045158360,0x1145023062198524c45,0x8524c401144a14041604,0x8c1b84c0981c00972c,0x22830fa853c1e01c8603,0x5d0c0268441281407000,0x21a83a150c342d089190],#[0x5d044042d02684a0697,0x407c0760702a0f003822,0x50780c02206c1485c108,0xd0c1005a1681a0c28160,0x7302c0283614ba1781a0,0xf840e02bc13010a0272,0x1a0f0061440249761440,0x836145820224042b0268,0xb00614e089010ae81026,0x304213012068309c2bc0,0x6831003e14380780c02,0xa1684a0683430281e85a,0x4010852049a0f840142d,0x81a0c3e1005272830f8,0x11c5214810a02511c527,0x32142811442042521428,0x428160520c9c0a045118,0xf81614400f8560d8161,0xc130302181c0302270c6,0x27040201e210830dc0c,0x2270b1083ee0f8105b0,0x840e00cc1008e070060f,0x707a0e81270400f85078,0x10080b684a0e810a10c2,0x81c270983ee0f81c009c,0x40142709828e0f812705,0x6850f84010832049a0f8,0x130520c810a025130520,0x10a02513052048309428,0x4500d8109428130560c0,0x182583062148326a0c09,0x2049c830251583214812],#[0x50510360a001445c1883,0x85c144640e0014838170,0xa85c0c51301402d03e0,0x758609d84e061424a0e6,0x42c1d0518460b0317060,0x80318661027e0582c0c1,0x84e0451c0c42260e1303,0x451c0c142c5607814609,0x85009e0e0418660984e0,0x158406784e0b030505c1,0x60b031585c182240c5c,0x84e083cc0c1917076120,0x886e0492c0c3c160802f,0xf442158517056083483,0xc60b81c0c3e158703b03,0xc5623030f44215848380,0x7070420e6158460b81c0,0x120505384e083cc0c191,0x90d03c0e040b48215838,0x300dc42103c14448102,0xf04a148d0dc560c380f,0x510c1e158510c0900c38,0x422038300f037150e170,0xdc560c2ec108d0e05c1,0x3c0c038140d170560c0d,0x7042b88d0f05c140e024,0x1004810302443d0dc2d1,0x560dc70b43c14834142d,0x10e1704a1091a083dc00,0x1583724381205c0c520e,0xc12844081101e820f700,0xe0b43d0e04a08564385],#[0x150e1707038520f44810,0xb8341703a1104608071,0x2c0f4511407c00401704,0xc042102e0f4510c40c08,0xc0f026102c108703a810,0x421c84c002e10840c028,0x8291c28c0f02a049b078,0x38291c1e21027a041d83,0xe848101de0827a041e8,0x5801820ea0e17058182c,0x43a1143801841160e170,0x6043c16060b03816030f,0x2c17030b058150e80103,0x86a1281616821450e2c8,0xd85160481d0640412022,0x15010f0581c9203809c0,0x4043c43858190ec0c244,0x500305c0c2c160509105,0x834170524b05c0c3c120,0xdc560c301702c028203,0x340e03d180e170560c16,0x2d1083d0c04c0282038,0xc0c3011450383d108561,0x300b84108300f43c1482,0xc05414580b856102a108,0xa090e1704c17030f82c0,0x3d10856100e1605c0e84,0xb43d0c020f4421584008,0x20b04213001082e0c420,0x3a082909e0e07c503a8,0x102b07c2715841020e17,0x7c270ac70783d10856],#[0x20b0380f451003c60b0,0x86c141dc0c9b1145103,0x26c422e84a0b811450e1,0x740ec0882c0f8114700,0x4215840283d108561040,0xa450383d0b44212840f4,0x1460e1089a101f09e0e0,0xe0f48a120260a0160456,0x3d10300a20260a846160,0x89ba14290b0703a850c0,0x7e850760e0a470a303c0,0xa6850781f8387078840,0x309d820760e07c807482,0x8409c1e07e0e201e2130,0x80207c27158407703209,0x9c70f0046081f09c541,0xe07c50788407c860760e,0x6c0b00148609c1e26e0,0x30226b00a0c3a2083093,0x1a850804a12058c08184,0xb87a1a850b9101285a,0x4814844120fa151ba0f0,0xb8bc1b000e84a11060e8,0x110203c0721a85a0f000,0x1c86a1683120844105c,0x6c0a83c003a28204140f,0x5212870748f208100290,0x2850d080901002906c00,0x402e163020610c089ac0,0xa0e85c002e2e86a0e854,0x8241f441034081501c86,0x7d030540721a83a144],#[0x2e1500a16830f048142,0xb00a04511e85a0f000a,0xc083c2685118560ad09c,0x561702c009a144408040,0xb00a04512385e0c20268,0xf09a1446080851581cc0,0x1101a158510c20103020,0x2268201586c0b002685,0x407e083c4409a3285a0d,0x4481001fa1505a0d03a0,0x284023c2b42702c003c1,0x288202702c00860f051,0xc0b000f09c144710010,0x1002b002183c14491002,0x2b02438158410082c08,0xe82e15830801c0e0561,0x8160c58180a6144a1584,0xd810f18516068003c615,0xc0b268240c02e120060,0xc042b090092148160c86,0x2c04810289c0c0ac1602,0x83840282c290930320e0,0x22816010ac0961581a09,0x41c60d81a09858402830,0x2830e8a09c260860380,0x181d2081002a06c0981c,0x5144bc0685a042ba0c56,0x9c1302c045627283c018,0x921b006143c144a0ae0,0x585144561c400af02c06,0x2985c005139010ae8102,0xf0220b01207040ac270],#[0x40685a0683158807410a,0x92183ca0d10342241502,0x890540901a1682a040,0x810302a0c3c2683a184,0x40c0b01c02830f05127,0x410c000aa0c3c1449c3,0x2142012451008220702c,0x72142021821124521821,0x80a60460f016049c158,0xc1d20b020400ac009c0d,0x80a60f04e07001449c2,0x63001589c201d20810c,0x14049c158ae0f82e0442,0x9c342709a85a0d0340a8,0x8340e8240a814043c440,0x7001589c284009c2602a,0x70ae085a09c26e0d02e0,0x9c2602930e0f82e05102,0x103020f2852683418280,0x2886c0009a14510f0e,0x5014400af0220b012041,0x8608450148620c21080,0x188560c2084021188308,0x5158a20c202721008452,0x20dc2660d820f6146070,0x562219852001085e144,0x70760d82605848530517,0x50b06582853848003c1,0x2d8460d8212c866045c,0x3e083c1730506498643c,0x68505c15838500be138,0xf856203a85086c143c16],#[0x158885383e048610b050,0x614420580c21b83e0414,0x841585c1614033050f85,0x7098503c10c5c1182851,0xf21903917e1382218141,0x10f84e09050f01917090,0x6e0f8110b0515888500e,0x810618415814303a8508,0x8846086140420e983609,0x428501060d826070515,0xe83c0e050b4820e0561,0x30e0810c03c0dc503482,0x682c003d14452103c144,0x182f052810c0270f0603,0x81203c13002ba820e042,0x85c158a0785115830f03,0xc5a45305a0c0d40e81a0,0x100da0d03a045c450561,0xe1708d0f060503c0e030,0x84114300e03c1704c0ca,0x81e2bb84e0c3c2351424,0x2c83c0b000e85e142709,0x3e86a100760a8311514,0x4c143023c3c150641281,0x82d17834183a0b852101,0x6514081044084217870e,0xe1020411021091417864,0x2c00421484c0b000e85,0x78607439e09140e8421b,0x10048141d09b82149141,0x56342d0f0520c1f40c2d,0x3a090204705c0007170],#[0xc5c15914285a45284a0d,0xb45a110340811a0e8201,0x41852120524414418380,0xb21831450380b4607814,0x570988607914148481c3,0x15e0a8602c3a4503820,0xc1aa0c07a051410080f,0xc0cbd0530526830201f4,0x420702c0037144509c83,0x272685117020f09a144,0x2683a2184144450f02c0,0xe14440dc81c0f022f43c,0x32f49a0b43a1b000682,0xd02c0114e103c170a613,0x83c4505c1c5aa082001,0x1703a45038202001f84e,0x3e089a450a12c1d20f82,0x3014270781d2f426e138,0x83c0dc51130310a810f8,0x1445c083c218271445c0,0x2a049b0b4521286c002e,0x820f281108194509c0c4,0xd8205281115107b84e0f,0x70de8661a846128360,0x6140f071304b45a1502,0x20451170709d82e0c30a,0x285042144420e8260b00,0x43a198621081144451b8,0x9820528117118502d14,0x184b0f02ca1184a0d83a,0xa041461911691982c072,0x60d820a284a0e822f407],#[0xc850a12c370b21582d84,0x60781d82f84e0f82a045,0x614282360b000d05c142,0x203611830aa810205c11,0xcbd60a8111586850b81,0x1783417050de04612036,0x88098261a140d060a202,0xc301703c02820e85c102,0x15851691408c5c158520,0x40f0370c0408c864505c,0xc3c1823c501417056141,0xc3c450908d14218300d,0xf84a08270981ee1381a,0x1030304503c20140e838,0x8a09140f4810816e0f8,0x4140dc580c214102aa10,0xf8561f05c0c3e0b0301,0x40f8561a824510340442,0x810f1140c0840d011091,0xf81450581c270983ee0f,0x8382683a14270981de0,0xc1704c02820dc431700a,0x4206514270310a8226c2,0x381c2607b84e0f81a08,0x52824c2821a820e98185,0xb68661a8461281605830,0x31178590e83009020380,0x60f840de82850421c4e1,0x82158ae0e140b056101e,0x4247086a0e8160d81052,0xc260580ce07838505620,0x1700e083a606140e0909],#[0xe0f8160a140c0a07686c,0x26045c302709a86c1700,0x760c5a0f214c1784e0f8,0x84e0f826045c16888640,0x3ee0f8160856203c01f,0xf816085a158610a1c85,0xe083c0ea14268381842e,0x6e0f811088660a140c08,0x1ec10842ba811083c202,0xc26a0e816145c1586088,0xc832b826171852343c2,0xc083f46442141ec1084c,0x5a111960a83c00452f04,0x820fc421906a042a2228,0x784a0c45464a0b82c465,0x8450d0503c07a1582a0,0x40019a1683610451c811,0x834642e1d19108450d06,0x6810b442150503c07a16,0x1785090190b45e103506,0x9614290fc50b119c0042,0x85411021091917870b11,0x719c1302c008f1086080,0x23c421704c09190fc421,0x4e0a81464422704c0919,0x824645e1c1e074850ff8,0x480b458101e07429e13,0xb4481c3d4182d12040c,0x10b45c0c1f4150320825,0x1101e824f28446437248,0x58808819108481025408,0x2684a0e82a0585c005c1],#[0xa1281a0e82101850f519,0x201d854f284171193030,0x5c12070950340811a0e8,0x5190b4a0988306703614,0x11c1485a130320e810f,0x1f052170320c3d464482,0x20831e1783a05190b4a0,0xee178346448183c0a684,0x3de10190f01a0f8a0a41,0x3c0645c1c2e0b685a0c,0x681906c2c302cc0881e1,0x1685c0e83c0a820f4400,0x10b840f43c0701a064dc,0x20f090b303a0f02a0b00,0x80fa8106a85a12831158,0x1aa0685a12831143c0f8,0x881a1282c003c60c5c32,0x61910880b20b01d8460,0xb056181e07583e1382a,0x5a0c2c158606900e1783,0x85e0e818642d1e1a60a8,0x82c0f05c614192429613,0xf0196145c420be1383e0,0xb2846128360e8260a810,0x17185864a1691482c070,0xc1a810781d82f84e0b83,0x5c158201f04210450f05,0x65830f8561c231585c0c,0x643e070561c2b615810,0x86158315845158360442,0x860f98560583a0856185,0x82d101c60d816168215],#[0x60d856043e15868643d1,0x56191ca09850f856150e,0xc2511484711460d810f8,0x145c10138158520a1960,0xd20190b42c108401c931,0x80c01ea0a84101854643,0x2504e824093ca1119170,0xb02d1085c0b0024c5c10,0xd30124c42158504d190,0x561c3c208930b0420b46,0x44318340a41ee178124c,0xc1b064b01f04c083d86,0xd01e1002ba1682e043ca,0xf108520e190b02d10c50,0x3d064421508c13028643,0x80717054143c03b84e08,0x1285e040ea0c562384e0,0x60685a0683158a1501e6,0x38642d18548380a61582,0x820f0191708613850b28,0x3ca0c5c284303885e13,0x70745085a128261182c0,0x15890af84e080e214541,0x1681ea101c60f8105185,0xc06e84a0e82a05851589,0x82a058360585158c1091,0x45a245a1091c4500aa0e,0x1e07407e1383e085c60,0x781de1183e0a858643d2,0xa584e0c2ca16190b470,0x47040200dc00371004,0x8d0a0d0368340e810f7],#[0xb042130320cae09985c0,0xb10cc003f10860dc2907,0x51104c00450fc42142e0,0x1bc002e1084090841084,0x942d1204104300b44810,0x1e8241b001003724410,0x7c00400f51c2e8440811,0x48228440d0204683a080,0x50dc26c0c838f585c18,0x2810470a5838683a0b,0x47028104760c2441501c,0xf4420b440910340700,0x4a0c130943d0b442143,0xf04808381584a11850f,0x560e040f0510c2b0e034,0xc2b025840f038140d178,0x434380dc5e110d158510,0x340e03c17000dc3f1444,0xe050fd0d0f05c100900c,0x100380f050ba844343c0,0x3c140d0f0370d040349c,0x2909a0f183a20c3d0b8,0x1008a0045178708084a0,0xa141b0fc5211448102a6,0x820fc42180f219800e84,0xb8026c3a0fc601984601,0x2086a01000e84a1829e0,0xc042a0740760303114d0,0xa114703f052170421282,0x4211440aa0821b054104,0x2860a8080b45e10920fc,0x1084a0c0781b052142c1],#[0x508084a08801085e1a80,0x421283a1280a083f108,0x1144210452643f1085a0,0x406e820b042102441042,0x44a26c451305c0c9b114,0x108521a800fc3a1284c1,0x26c3f0e850e8822009b,0x8450c9ba00421284a0a8,0x83c261c08108450c0f10,0x283c2620200248420899,0x4a160402486080842018,0x486615860b44a10300b4,0x61852202b02586a004a1,0x17030c01e809822f280,0xc3014230e03d0b4420c3,0x4300b448101101c3d0d,0xa0dc58102a0204212041,0x11c0c076145c160701c4,0x50540f01104400b4720c,0x190540c3d1044012060a,0x71284214830f42d26448,0x7c12820f49c2f000fc3,0x8241483c048004703c00,0x102f0f05c16800982286,0xd144312834100451045e,0x9c17038683c10450b03,0x8224043fa038460e8217,0x17032081a1044011470a,0xe1704c17038682c1005c,0x82090228682614821043,0xb850a082a1022868261a,0x941d170408a1a0a0260],#[0x3c1045818250745c1303,0xc5c0941d14c56158160c,0x74900c25a041d108503,0x1083da0d83255850942a,0x5c102920c252141d14c6,0xc41a04420f8523c25074,0xd83256810942a074900,0xe0c5c106810f861083da,0x56100f0f4340e03e1585,0x300c083d10c50303f10c,0x745c10810941d1704c1,0x5c10850941d170425c25,0x170941d1704204410f8,0x76850a06a0c410f85c1,0x3096850743d178317025,0x43e17831045ca143e140,0x14411703e1408106850f,0xb0d0500c411703e1383a,0x9282d0b0e850749282d0,0xc1d25a0b42c370e06074,0x1d83404970891782c3d1,0xb182b20a0b42c220f43c,0x3e0f050f81d43d0e01d0,0x5154500742c68009c42c,0x741a06407a090b183e07,0xd0d064544b4510b01c50,0x9bc043a181e4120b42c3,0x4960990b27062720b42c,0x430626d0b0b03a103ec0,0xc2190c1d1c2720f0988f,0x1443008142683d0623e0,0x970e49523c071516131],#[0x23d0c02030f919430081,0x723c45103f2688f01c4,0x44711c466102f1145610,0x7c707d174302207a112,0xc10050950c07a1124422,0x150881f2546078918310,0x8832560c2190c20860fe,0x390c60c0811c608a1541,0x810970e48f25407142f4,0xc62550c02030f9194300,0x5445109c60c5b2689501,0x130086104b1146610072,0xf45d0c0889a868971c4d,0xc20f02c010c0a09a1c1,0x68281c284308f01c9a16,0x1c9a1e0cc0b002710c2,0x625e0c24282710c60c95,0x441c1f45e84a050c8188,0x401a0d8320ba1281020,0x3c9702458120c0789343,0x80c3e4650c0204254392,0x4c11c081390c18974300,0x9a23d0c6042b024713c,0xac0920836042b07c40a,0x90ac60a01e26c9343184,0x2270281c280790c6100,0x1850ac091d0cc020ca0f,0xd850ac2714282709743,0x60f020a0954309c1c862,0x4013020a0974309c149a,0x8968382d0c072610c0b4,0x38298382d0c070e02745],#[0xa041f8544a0d0707c914,0x52061a1282c0d052550e,0x20e43860760b0260e128,0x49140250e181d2482747,0x7492464094385075172,0x240b860921023d100b85,0xc8f0803a15028411023c,0x1d1083c8f0803a151083,0xe161020d02255100d02e,0x100902e1824256104402,0x42044034268540895841,0x285440202703a2685a0,0x182e1002858443182e10,0x242688f6043f02468443,0x128327080ad8107c3410,0x4400a142b09d1084086c,0xc25d85024c3151814114,0x56188620c2b09d85149,0x28094403164490298215,0xb0e8684c4983a1002850,0x2760cc3189a255836045,0x1821680a158527097c10,0x103c2343f834380dc614,0xc4508d0f044391423438,0xc42148f44a0f0e82c151,0x988f4311415024520f23,0xa111b26e0f0e82c15160,0x194505e1084451101483,0x4380dc910be110c02d1d,0x4502d1491106110b4301,0x5459141202d110684491,0x48645054701e46491450],#[0x50260a89a0f0515c1e24,0xc1116a050c0989a45068,0x102682c0e850683a26c2,0x82607019c009a4506051,0xdc646110a19841402c1,0xd82e14184b09a0b20e14,0x86a042612c7855820f81,0x20b0e05e0dc48561482d,0x9e1582d8620e810e04b2,0x74501d0c5a109140f040,0x620c2a0ae821083c182,0xf83c1517a090e0f81d45,0x60d818505c1d14073050,0xd871828503e184b09a19,0x460909283d120b051301,0x3119120f40a8123c2946,0xc00290791b46470a48f4,0xb608294408f464683e81,0x43d0fc44651417842111,0x183f0789143919142284,0x146450981e8449147119,0x3d24c340b054701e4509,0x60b01d8560e810fc8204,0xc4982c0760c3d10540a,0x1543c07a1a01d8460a81,0x83a045c1e1a01d840b04,0x61a82d85185a82c07615,0x151446493108406407a0,0x286443221460c5a8645c,0x1926091503c0a61460d8,0x51543c07a1c8518460a,0xa98002074489283c240b],#[0xa81d60050a49943c8c0,0x80842026c29128521882,0x290809b2490f0a984020,0xa98502070a9840942e10,0x21850a850a49c2590f0,0x160c21844220f4743c29,0x951]]
def g253H9 := limbs80 #[#[0xe1780f0000000404,0x980e000040580911001,0x443f05c000144b01c12,0x180003c040140100407,0x380001c010841800025,0x4050c806058130142b,0x1041018020140000070,0x9012114000100b0e405,0x2900200c0203c1d0042d,0x100c02c9b00400094e7,0x34340003101c1d01873,0x8c01188000a00e00c28,0x34000940d06c0216809,0x382c00c000a47509c29,0x42603c4b008000141c,0x100201c010383001d66,0x21403014130000706808,0x4417004030080002017,0x700d0000204c1307c00,0x400403c010041f00000,0x987c02020028601ec9a,0x38ff0980204c1f00c42,0x50ecd50680c01419,0x6408080000001000004,0x380304c640a0030780e,0xe426000430547e0446c,0x1c0301280102c0406805,0x80000021004232fc18,0x15970014260006305442,0x108e000191840202012,0xc01138080141b03c1c,0xc0a02057048f000441],#[0x3424190000940e1cc8f,0xc040440010c0200000,0x23815054a611ce504803,0x300f08800094042b010,0x8006240015c0004410,0x1500002c040042600431,0x1b8571a8080041700009,0x18050ac02564053e11e,0xc204c250002b03465,0x1c041645f1000101401,0x60203a8014180e0108b,0x14100e8402cc6a00045,0x12c121c82e111cd1f00a,0xc1002c021ace606818,0x78b90943316c090a827,0x4003044411303f05d04,0x4000300c08c0608c02,0x5301d010220285b03c60,0x9a00c180480500403,0x410108320081800854,0x11405030b000c300341b,0x15c7e140035391624c23,0x7819014550003101012,0xc011241f0840206839,0x74b80de601c04007810,0x100324c120103f0041e,0x2743e498010d83b1a003,0x3e000910840d0ac24,0x2fc070141d0380100000,0xbaa81c4840000914817,0x450021494013c002950d,0x4fa4016c3ac609a08429],#[0x3d1803790343455a0aad,0x59099a6529e507e00008,0x256f0b800002029201cd,0x200b383ac39cbde2a809,0x50872dbacd9bbba4476b,0x89292de5104c9c3e3bbf,0xd0c619a82bbb31b41a85,0x494c170d54262fe520b1,0x8277cbd533c41caa9,0x1847b189270b3b9e0fd0,0x22e84bc688648f945b2f,0x505632be9bb03c03c193,0x3d56410000085c6b939c,0x538628244182b6741059,0x1ac050d2bbdc4457186b,0x59bd8cce42732115501e,0x15a5457e85fc03b7b32e,0x2f04b0d63328b5580a2d,0x35c9a45526e88d3005b6,0x171685ed2c873b50000a,0x239dce4f0a091b0b1061,0x2ff28ac9e33266e,0x9d40c6ebc292f7525d0,0x53bdadd22bafc51115fb,0xca97a4e2853a2f555a59,0xa31340db195ec3d83056,0x94bd108739d4d4099,0x56333e600000000b43a0,0x9bac23f0000b4c6504f3,0x43a498d4011fb3545,0x9d72099630b65c3d3e30,0x2cf00000000c8832c033],#[0xb6cea6c80f52a6e6544f,0x5223023f49c248c4bcab,0x434a0eb093da9f052d59,0x51f94485216a23a64fb9,0x5150000836d70a51c97c,0x24300006b27bb5eb29b9,0xd00113000004380d9a15,0xd2020c40000b873ea7ad,0x200006b047ab08541f,0x2cec097cae378028b5ad,0xb1981f20000c21f6bb4d,0x2860000d164835500004,0x3cf2b311ed53a15db53,0x398c3b8c428a2e37259b,0x3a7ac5e81968253aaf30,0x547a262918dd5999adf6,0x40feab6742614d4625c3,0x23bf15300001cbd7b871,0x3bd15bf70d6a2bc457e5,0x3c500000000000020f3b,0x187eabafbc90000446d7,0xa7d00008d138438e3480,0x84c253ada606aec8504e,0xb2000079e1b5320000f,0x43dcb159452798df9,0xa51e4cc41b101f1848f0,0x4a0f12c906a4c8c033e8,0xca3e1ef0285b4aed30e3,0x155a22dd06070770000b,0x30a0000505200002401c,0x58c0000000048bb78677,0xbeb00006003abd4c3d6a],#[0x486c74b100009203b,0x1aa0b3c200a0a2ec2e50,0x408990ffea5630c5f,0x4ef9588826b000080670,0x93839d10000f234e5857,0x20800005b810000606f8,0xa28a088f07920be3068e,0x84e506b000022f405c9c,0xfee1ead4038bb7287aa,0x561a074bc3e00000000b,0xdbf0000ea79000000007,0x138c611a2f00004ba6a,0xc7cc74b2a5000000000,0x8747929b393e9e50000f,0xd5dd37094a34020f0f7a,0xbbe000000005047227c6,0xd08e54161ae16,0x1a1e808cba2a32800000,0x572b20e72eed43d00002,0x1880000991643d33b2fb,0x466438f79cba1822197d,0x1afa237000078dd00006,0x1fe6a8144a64a5f6ae25,0xbaa000050f2000063c20,0xd5c95400000000000001,0xf9dd56221800b10a6b8,0x3f00000d43e7486228d4,0xb6294fea18084068,0x23663baca10226931010,0xb148a506135233dd419c,0xafadaa582a102f6e1440,0x3112c9982bf6a740b732],#[0x515af201fbd35da43f4,0x3375125f06e2365b2e83,0xf86ae800000000832e7,0x578e9c2f3a6c3fb12878,0x3e952e1ddcb280a41b8c,0xa62cc8dc00662c5415d1,0xcab129f0a672f3041f5,0x5bae154c8f4402250400,0x48d9598506d21e93d335,0x4466a362bd9fb3bda7ba,0x3bfa2ac2aeba371231c5,0x3de7340852500000000b,0x326e36fc54872382cac8,0x9162fc42992165a05dd,0x14eea67f137a5a62263b,0xaa90a53c2b6d09573ceb,0xb44812d8420c820f39a9,0xf6c05a7397ac4cf2adc,0xd124490bdb51c6c8c60,0x1265210ecc7b3ff742d7,0x58b7116c096e44e9012b,0x4d2fcfe63af4a868a3da,0xb57825160df63c7d01f2,0xc052aef1277533453f6,0x3e1dc53d2f932902390c,0xc702ab36056c500ad1f5,0xa270499b3f5d38174e79,0xafd63e5432c8a3225768,0xa7fad63739f842abdc45,0x3508be1727e74a80156d,0xc79755da33012d2e8d85,0x244044df32501f900001],#[0xb824a5e6151e0b604ace,0xbe20000e161417770d57,0xab4b4f2711b60e8a59c8,0x1dbb94d458f5b661e5b,0x34582d4683171dd75954,0x11973847bcb246a39bea,0x5a92aee63510000e57d5,0x84c58c3839c6aa6a7,0xaf1a34a58643388231d0,0x8291fd21b9a93c2926b,0x716b5,0x4f97c454b6a7103b33f0,0xae2495496802a7d298c,0x57553ca0000c33a00001,0x10243d014df2ae722426,0x37520b45aa68488d4a7d,0x1a70000658601be0d22a,0x56430b38593a3f3d3132,0x20f125760f00000cb484,0x9a0ebc135cda228d4327,0x710e8c6035620000e,0x93f1441a1fc72bef2c10,0x22f000094171b60e1e29,0xc500000532af39b4b54c,0xa9d11625115b33cb2c3b,0xb3bc592e5,0x352036825b4000064b50,0xb8ed17ea502385dc1ecc,0x26853955a12c157dd092,0xde60dbe8aeca523367c,0xb20551ca13144c20000f,0x13f5333923d5b9b00000],#[0x9c1d072329fe363a2761,0x756bc08c654063a2d17,0xe79503c591754d254ce,0x443f83b05c21442a8f8b,0x22fb35b3112224f4e,0xd98f0cdb18a30e1a39c0,0x574c1d508f7054b73000,0x1d46cff15cf035ac3537,0x128e25864e513a5f28b2,0xb3c1a3b2802175bb7,0x17b1247036214be00000,0xd769580413a1b242b9e,0xb7e323195552bb8357ba,0x891abfe7c62a4f0f1c43,0xaf8f24191a4abd712efd,0x301f057c56551f7b3641,0x6c856e940e11e122d99,0x5ad71bf69cf4bc52ae0d,0x2da4bd3e25b9b0f824d6,0x28f72b2aa9a18d5d1e7d,0x18e7972c249e5c1243bf,0xb4502bdf3cd884d75c51,0x3c66214d048f1cd22c29,0xbd80000126c43edeb474,0x336f0737a841306d0bc9,0x7a33eb70c8ba2101cef,0x42c45c042529b3d5292b,0x59a31a0c219fc013bdc0,0x27903493296d0b790bdb,0x8683524e45f3278a52dc,0x51468c14a6674eb113c0,0x1933aea4235ddca01382],#[0x20cce5b7f4ffcb438,0x8aba9234cf3d4ba4044c,0x550602504b07407441d0,0x9eb392474a2ca9943b45,0x9e2356a115b9b15393e5,0x4e73cc55ac2c9200002,0x19c469419b1095299,0x87643194437616f90fa0,0xaf58109fbbfe3bed13be,0xab9f1d2e1d9602db2a2a,0x4f660048272850e44cf1,0x40c8a96f2d300ecc3128,0xc18423015969018fa42f,0x537c9d95192e0330000e,0xc4db9b90a2250053f,0x21c131aa35b934bc1500,0x4227485000000003b03a,0x30c147e24c3d0ceb2e4c,0x446f0000ad6274c1c,0xd934ea00009c4993a90,0xca411a63b39d33112ea9,0x4c0e24b6163000009d69,0x1c0286b812e4293fb70b,0x34c65cb4aa83146510c7,0x1407ba514d50000b3764,0x3b220000d4d7380c6,0x4fc91a30000230fc1d60,0x25e00003178e4bf324c7,0x492d3dd43e255ab304dd,0x2f1035e02afe0e3324a0,0xb5cf1a5f1e4b3d90000b,0xc355871e1eb258d249af],#[0x5a103ee8b5838423b1cd,0x464247ca2263b1fc8b24,0x93a4318a5280000b4b4b,0xc75b1ded1cfc4240000f,0x3aab37cf29464d6856f2,0x47823df83d4b83cdca57,0x5ceea1f33736007a5c89,0x43911ae11472084e254d,0x14f1859ba64f37e25bce,0xcbc757a82b1319ff0eab,0x17ae38c307fb9a500004,0x51d0000e5391436eba13,0x3859559a121281f43b30,0x13e54b7a065520af0d81,0x136b4ede2ecd33bd008b,0xa7694cd0000b14bc16a0,0x92009f00abe8bee5356,0x976d00b746e1213d13a4,0x8fc80c90000ea33a4776,0x5600000a4d00000c5824,0xd81eb9a0a4d258ab21d8,0x4d1f4cb6133cb4ad1c5a,0x314000000002caf53f63,0x52380717b46000042215,0x4796c71917fc0c34dc52,0x2e681cb1069d00c6bce1,0xf312bebf8acee15810,0xc3be3782937b4a5ab133,0x481f3b082cb7b9c6b1be,0x4b3a878fc54236ec2335,0xd823934753d83fa60dc4,0x3f8c17c322bcc8aa57fc],#[0x52a1220baf43152f1b77,0x4337d60fbff93d2e56df,0xa89541b15a4e14344656,0x1724414a1e322880b1d3,0x1a2fd36542bf2fd228e6,0xaac00d2f281b5528ab53,0xb1afd2be23270af4ab21,0x9dee56cf9d8d1cae58f3,0x11484dad16840ee657c9,0x5a04497829c0483daf6b,0x2e23f4b4677176322a4,0x1f8634f209c83db44f75,0x43f036f50c2a400936d,0xb4c4546b55195a3401ee,0x44f083a322225b50273d,0x3e8224e4c5dbcb460d3e,0x28b15c0310e521d382e,0x9cbbc1f4211dd2607,0x431dc40000094e08ca60,0x48fd21c3043500002,0xc3f43cfa48a511361b30,0x245f56702b0e46c1ce8a,0x4e6a37d621bd0783183e,0x461706112e9d49899efe,0x17d4bd694ab1875b5c76,0x10b14d929bf9011336c5,0x49f320459c51304d19d1,0xed22d740b04b93224f0,0x9b3f2b4835f04c8ab129,0xaeff1d143032d02c1342,0xa9524f140546227386a8,0x16e8a8d0000916083d70],#[0x1859402a2848b84bba46,0x86d0000f48b73f98361a,0x453c06410d02b3560f15,0x8d0c4e340b5d36023773,0xb3f7493d41e842115710,0xc69245d5b36cdcd314d8,0x425438ae3077a98211ad,0x405745260a4f11ed0245,0xb0551d8a3f74a110482e,0x4fd70a9a1b4e22360598,0x2741039d4de292de0057,0x2d0d54543fee53040e59,0xba77471d580b3b1a4a9a,0xbf9dbcd20946513202b1,0x4b910bbea30d366d4f8b,0x4a1b48450fb28cbb20d7,0xb11e5877291614a3b8f0,0x320e4ced02a1c8b0c988,0x5a753029ac035890000a,0x10620000000032b54,0x751033d8a369022c0,0xc67a086e472a4ec00000,0x2df404c51da959e3280e,0x26713c3b0bff9a9f0661,0xe18128400000c,0x462bccd537aa32221730,0xb09012b7404a318b1,0x10872f2039d52dd01690,0x55e829d15570000e0c15,0x112450f0000027185190,0x2869020780a18aed2,0x4600000818ff27a99dc0],#[0xaa00148a400d16d1132f,0x1bd75aa8167731e95929,0x1d3c2e0a0e012e2b1919,0x55683cb782b92a40000c,0x454d20c0000db5b814cc,0x41cb39e24b8923ee584e,0x516ea2921dbb9b4229a9,0x28cd97aeb0ec1110145c,0xa9b8c9b808db5128323d,0xe25cc904802032612f7,0x51e05546408a0a8b10ff,0x469cb31c4e265ca81f00,0xf978b5b899c0f,0x54a00002045939900000,0x10b372554e327500004,0x2290000c387e3ea24f31,0x308119448a4634de4a40,0x2c790da086141e6fa221,0x166734403387b95f2c4b,0x1c8bb61cbb901f541ab7,0x9b6893e0f549fbd2e,0x9773174e07b503d08250,0x49ea1cc3423a53e0000c,0x2a8d38b7cba8a82a5698,0x201a300918b9ba8a5,0xdb51a5100f0ef72a00,0x594000031dfc4d80000b,0x85807611bb549080cb3,0x392f41a540b000060936,0x81c96468323c30dd6,0x15c47f34407b6574470,0x47472e78070c27f9396c],#[0x55b0000920150cf0c661,0x179c0e9025f5a1341f3e,0x57322a352cc44dc40269,0xd359b5d948e92050dc1d,0x2c69a9378bc75970b594,0x37f9430d0a32316ccb2c,0x321b4e4dd15d9d2745a0,0x30d027b93a392b841c70,0x52f247a11e8f107e52b6,0x858a2eb6198c5667297c,0x1238ae9dc6324110000c,0x8d262615317f042094e1,0x4d3c209f9a8b8951ba0a,0x26fa45cb568b459a51b9,0xc463346c1e07142a189b,0x50740fc94ddf11c3830c,0x44a632d7ac2e9d3d0a70,0xab1ac77c283cc0812484,0x2248391832f99ce83da3,0x5c015e1b9f02d83a474,0x3b644f5204bf4e8431f9,0xa8b0b69986f200e61dc4,0x55a0c2b03e34af2c33d,0x334b19b01187afe34506,0x13d7315921583271a0a4,0x5a8b2a62a63d38984755,0x92fb29500b9e08b4bbbc,0x80227d2abb105e70491,0x324f579f03124b6a3f23,0xa75b4ad24ee0202e511a,0xd5208a6112ac2ca010db,0x6b4f508175c428fa0],#[0xb91f4e941d0e1b653350,0x359c526b520c2a9cc72d,0x21a82aa305863e79bf78,0x3791b97a03a901bb014b,0x5b9242f0035e9d06017c,0x8da2a54c09bf583a3438,0x9e80000c907846382cdf,0x1b5245b0000a14114caf,0x3ec85be5a697b5680ba4,0x5cc5289c570605fec522,0x2ab0451a3a05509638e6,0xcb1785615a263b77b4b3,0x240c027b50a55b1334e6,0x42921d7518c84b273399,0x60389404c59db08c5,0x212f9823341820673e40,0x473cae5b45e0906985c6,0x536311099ab3050dafc9,0x83884124a65a3fd159f9,0x51811909199b5ae99a7c,0x5177444a2c05386c4898,0xab8446be47b5139f52ee,0x357955ad885753c619ef,0xc483d99209e41587b8ca,0x45af550b9ba9e3563,0x197bfb3c4bb1fa6af00,0x927f94ddcb3ea9e1124d,0x4154491e083737b85770,0x506404198b7d3c9f07c8,0xa35b47d334742ed00005,0xb6e25539b29ba4f31c21,0x3a8c8d104c76b8883ab1],#[0x4e1e0f442508829710a3,0xb1692177974b3a21b176,0x9db404600ac925a02ff8,0xa55a4c94342238d236bd,0x3c8d44bf3f145346d012,0x1207b647863d030fb8b9,0x4bb000090d489b9d2fa6,0xd80be470d264d,0x21ee1c1855c756ba2d60,0x49b95d018d9c58ec246b,0x265a1bc7456444c752c6,0x85a442e449de487726d9,0x7d717515bd530945b04,0x36a4a34d0e682dc0000c,0x3efe098632981f6895be,0x40a81bac1a9b496002cf,0x54f00adc53133adc4c4d,0x8a1b2f8c08ab16ccadea,0x43c82551394bab7f558d,0x149000003fc34aa81ad4,0x3f0000f001cb80926a2,0x8f6e55f21ffb11773ae1,0x8f52c90000937475435,0x5358f19c61eee0e4f]]
def g253D10 := limbs80 #[#[0x940443fc982216f5d361,0xa21fd48510ff2a0887f,0x10feac2887f551443faa,0x5fd73442ffb92217f5c9,0xfba2217f5d110bfee688,0xd910bfeea885fd75442f,0x907f940482ffbb2217f5,0x3f6a12417fdc520ff2c0,0xf5cd20fdac4907ed5248,0xe8905fd74482ffb9a417,0x482ffbaa417f5d520bfe,0x1fe54130bfeec905fd76,0xba64985ff714c3fcb026,0x634c3eea1a617fdc930f,0xa617fdd130bfae8987dd,0xbfeec985fd764c2ffba,0xff72503dea12817fdc54,0xbaa81ef59140bfee6a05,0x150bfeeca05fd76502ff,0x85ff72542ffb8aa1fe58,0xffb8ac17fdd950bfaeca,0xdc960dfec4b06fd62582,0x8b06fd64582ffb9ac17f,0x837eb2ac17fdd160dfec,0x7f5c760bfeeab06ff655,0xae7b05fd72d837eb16c1,0x5d82feba6c1bf59360bf,0x43fd50521bfee090dfd7,0xfda8490fed32487fab0a,0xd74486ffb9a437f5cd21,0xb2437fdd521bfee890df,0x31bfee098dff76486feb],#[0xdff744c6ffb9263fd585,0xfbb2637f5d931bfeea98,0xd941bfee4a0dff70506f,0xb0dff70586ffbb2837f5,0x77fb1ac3bf58d61bfee4,0xfd9161dfac8b0dff7358,0xe1b0dff75586ffba2c3b,0xd877eb1ec37f5cb61bfa,0x57f5d761bfae9b0dfd73,0xdac4995ff714caffb826,0x7058affbb2657f5d932f,0x2c57fdcd62bfee2b15ff,0x2bfae1b15ff7558affba,0xfd74d8afeb9ec57f5c76,0xa1221ff4c910bfaebb15,0x910ffac4887fd52443fe,0x87fd43443feb9221ffd8,0xffb1a21ff58d10ffaa68,0x59110ffaa8887fd73443,0xa887fd74443ffb2221ff,0x43febaa21ffd9510ffac,0xff4c520ffcec887fd764,0xac2907fd51483fea0a41,0x3483feb8a41ffd8520ff,0x41ff58d20ffaa6907fd4,0xffac8907fd73483ffb1a,0xd65483feba241ffd9120,0xb241ff5d520ffeca907f,0x30ffa42987fe76483feb,0x7fd614c3fea8a61ff505,0xea1261ff5c530ffec298,0x8930ffac4987fd524c3f],#[0x987fd644c3feb9261ffd,0x3feb2a61ff5d130ffec8,0xf5d930ffaea987ff654c,0x62a07fd21503ff3b261f,0x503feb0a81ff54540ffa,0x1ff4c940ffae2a07ff61,0xfae4a07ff62503feb128,0x73503ffb1a81ff58d40f,0xa81ffd9540ffacaa07fd,0xffceca07fd76503feba,0xfd41543fe98aa1ff4855,0xb8aa1ffd8550ffac2a87,0x950ffac4a87fd32543fe,0x87fd76543feb92a1ffd8,0xfe98ac1ff48560ffceca,0x5c560ffac2b07fd41583,0x4b07fd42583fe992c1ff,0x83fea1ac1ff5c960ffac,0xff59160ffae6b07fd635,0xaeab07fd65583feba2c1,0x1d83fe98ec1ff48760ff,0xc1ff50b60ffa65b07fd4,0xffa8690ffd70487fea1e,0xd73487ffb1a43ff58d21,0xa243ffd9121ffac890ff,0x21ffaec90ffd75487feb,0xffd424c7feb8263ff9d9,0xeb9263ffd8931ffac498,0xd131ffec898ffd644c7f,0x98ffd764c7febaa63ff5,0x7fe99283ff5c141ffcec,0xf5c941ffec4a0ffd6250],#[0xe0b0ffe76507febb283f,0x587feb12c3ff4c961ffa,0x3ff5cd61ffac6b0ffd72,0xfaeab0ffd74587feb22c,0x704cbfeb8265ff4cb61f,0x265ffdc532ffae2997ff,0x2ffcec997fd764cbfe3b,0xff7058bfeb82c5ffdd93,0xb1ac5ffdc562ffae2b17,0x162ffee6b17fd7358bfe,0x17fd7558bffba2c5ff5d,0x1b002280228000ffeeab,0x25e040e07080be811d0,0xc023583f007440cc0171,0xcd818542e8055e0a3212,0x7fb0f481d5838406b10,0x104fb098d1290235843b,0x7942df059b8ae9154829,0xda11a3a32f46330c211,0xd478f0ed01d2838ac6f3,0x22c42b4834101a1f743d,0x9281245447948d0115b2,0xc49f193a726d64c5095e,0xb6e55c8a9214d6292250,0x17612e145accb2995fc2,0x44c61988730725fd0bd3,0x5d069fcd1899ad32e264,0x9c9b38886ffcdbd9b363,0x94f2b9dee3b407548e74,0x8c8004fd51f413de67a,0x21b142ea84c107a20944,0xf1192a2ce451289110fb],#[0xa3a9319237a42a47a68d,0xa6d94cf298ad2ea25624,0xfd43428114faa9e4139c,0x508a8254dda9495208a2,0xac3757c0aeb55afaaf65,0xbd6f52d935ad2b449654,0xcbf057b9aef85cfab8,0xb2256354c475867b04b6,0x95a1033ae6630cb29939,0xc0cd62da9a34e66954d1,0x37836e34db79b4cb64b6,0xdca438fa7134e131bff,0x722ecc5d763a9e746ae7,0xbd2079a4f1ede1b3be87,0xc9f803e6a7bbaf6a9eb2,0x1bb023e025400e7f80fd,0x4299844f07660cec1348,0x8e218c3bf86f50cb216f,0xda9198a30145908a3d12,0x48ab90bb1ff63cec73d8,0xfa53cca2293a9258a478,0x8f5306a5cfcb5196072a,0x4e1b9b7735b668b4cda9,0x2a7de4f6e9e533ade739,0x30f450a87a508ba0c340,0x52e9a55b497e908d1c3a,0xd2a37d42aa7834df2997,0xccf588aae5d57daa5f52,0x581aaf635cfeb7d56aca,0x4ecb9d92eb1c162b6c34,0x6a16c0ad5a5a66b43167,0xdcb2b8db70eadfadba7b],#[0x42f015dc6bb27755ee72,0xfbf7e46f945ef5bd3d79,0x4047c21d82df0396024b,0x25c288e1bc2e0f058003,0x82120251201c0bc120e0,0x2885809447c188017820,0xc220a003822958305e08,0xa00841c0e0d058f10601,0xbc14010a341d061105e0,0x8700b0d400684a0c2a0,0x821c400803438750441e,0x740d0602c0c050181202,0x30a05985c260d040b20,0x80a042160a0300418e8c,0x4c120c840b201e0e0581,0x60021188e0d03014598,0x3844200b030150803014,0xd0b030140684c114416,0xa02c0c0401c07048580,0xc2cc260f0485058e15,0x40182e0385c106a00343,0x170983c102c71d064700,0x8110841080c201286166,0xe0f0302061587c2c0b07,0x63e408b70838061219c2,0x8481884144008030140,0x1983c0a160040230b83c,0xc2e0f023e80100982058,0x50702801006e68080c0c,0xc28843d070300c050200,0x40602a0c022dc20f46e0,0x20070b83800a04032308],#[0x7814203070903020064,0xc1e0600852016061f617,0x50a0c202c14060180902,0x11f100a030f85b84c1e0,0x3070c830090280617078,0x32e108616e170983c08,0xc0cb83e041d84c10510b,0x45c1d0388c0e13040e0c,0x14006e56240c05022070,0x240070e421e80d020e4,0x424008445240c0441617,0x81d001b943d1b84d020e,0x2171c421e80d0384c121,0xe03014040181a12004,0xa130a2e070e3d1b84c2,0x285c2608b80e1c0c020,0xc0c7b84c14006e5818,0x709822e0386210641c05,0x501e0902561c04080280,0xf020a08400243c240c0,0x28c2e0f0282080e82c2e,0xa0c0230c10f46e10280c,0x1830dc005c5620840602,0x1e0b025642840780e142,0x802c2e0e002e2b1606c,0xc1e0b02101c361908006,0xf05810a0660a3a186185,0x60200d03821a0507c260,0x240c044160f02400a0e0,0x1c0a0670983c16060b00,0x40c9286c260f05810a0c,0x5891d01408031e608703],#[0x30640c3ec2e0f0282801,0x2083236170983c0a0832,0x984c10dc3246170781c2,0x1a120056229405418047,0x2840c8e1b0ce040d85c,0xc2e0c5c19230b831e60b,0xf058142c008010047884,0xcc16050a191c3819c260,0x130782c0a14323e13063,0x3dc261704348006891e6,0x60f0300150183a50e806,0x300128190448330a82c2,0x14000c3724082ac2e0f0,0x3000d8e2b028050784c,0xc18ba001b230b832060b,0xf0581800707011030385,0xec2e130680069042c260,0x342302420e0ac3018782,0x3a1a4101a1a810e0ac40,0xc01a2f0120e023c2894,0xc0d09405083c288c5c20,0x3014080041c0a0242181,0x420690401e0e81e0d0,0x420f07058180a2ec220f,0x48090440c0501c04000d,0xd1c0c0501e0108562883,0xe06070185d84c1e010a0,0xa014080381404001a068,0xb84c18f01a3900783a1,0x2008bc4a4003c9000bb,0xb000f0d40c7441480c05,0x400208bc300796428260],#[0x785a0f20a4401e0180a0,0x4a4283c8030140400421,0x6007e3a2c0c04010ff00,0xe4108340f028120303c1,0x89052028100580251081,0x2241480c030161494800,0x1696060280c0082290f0,0x501808001180c103438,0x80c04004314890112436,0xb85c260f04800d0e4a02,0x2208003dc2e0c601a207,0xd82c007c7e8380944a0,0xc260b00832886860d610,0x28c04c2a0f0580288687,0x8450d0e1b0d40508512,0xc1a105a1a2003851ee0d,0xf0580428687010007b85,0x5c260f05010c8e3dc260,0x10585c1c040c3024798,0x83c00ac0c1f28922a020,0xe0b008303144907e0a02,0x101169443648240a0480,0x1602021c1c8185c1e0b0,0xa808195894490b0983c,0xc00ea045c240c0481007,0xa06302e0e06028110303,0x2818f06e3030803c0300,0x289211007a0502004010,0x4014080100408b9032b1,0x14048161707810ea0082,0x1a01408030020604382c,0x408010020e04372c143a],#[0x5c1e044a841f12421e81,0xe058142960716002058,0x85c260f03020c8c04006,0xc7b84c2e0069020d13,0xa0141e130102030dc91d,0x6070b83164083638ac0,0x1842c260f03808107070,0x42a0e03844140044452e,0xc780b1614490408c1686,0x4802144c3c229b050960,0x14c4b02d0c828085b078,0x32110585c1c06003e181,0x682804048a862c16074,0x110988a402c0f85c20f7,0xc1645288a0d0602d0882,0x31e85e038280144909a0,0xf050180170a2602d0c8,0x5143162c05a1a083f85a,0x580b82c10798241c0600,0x78390d8241898162424,0xd9448a4860165122883d,0xc451c17054360e02840,0x110988a421017851ee0d,0x6005c289a110802c6284,0x8b10d040e60e178280a1,0x9821ee0e008580a18d05,0x102c4840b2160b136107,0x4c0b120e150a21b04851,0x1109816241c35820c888,0x70b008120c8a72110486,0x3c180803c190c8fc220,0xe0c831002385c18b4904],#[0x32570881c1c0a0085229,0x8045342a37060200f064,0x680f048106b0b8340c00,0x85c1831023e20100c1ea,0xe150983408a08a4a100d,0xc426150645201a0c05,0x1c090b004bc31009c188,0x81683012088321b09814,0xb0b818620e0040302e3,0x831f100716830130415c,0xa0c500c128e06c2e0418,0xb830d8308045181d85c0,0x22040d85c18305045230,0x200cc2a1306321411494,0x4e60f030c42c00806848,0x47c401c3842168320902,0x5140304a401b07810621,0xf02251f0e160a60f028,0x83c0a18182518320cc2e,0x6110303800f0b8452f0b,0x30342400b868360a0e41,0x230e834141c810f6092,0x8072042b8481e0a005c2,0x281c810d40f058480170,0x481a101c3cc14010242,0x82f0982408a41c27200d,0xd85c0c012503420f0d07,0x170ac60481c094320a1,0x68761302960721606828,0x41c3e81a0a00562e161,0xe4110a003d221d05426,0x2083e290709c70340f08],#[0xc8481c00ac5c22940c42,0x710909001e921b82a081,0x3e290709c80320479820,0xe60a005c1c261041210,0x8798242c007a483b0903,0x24287c1c29201d848181,0x8521f0709c70b853098,0x84c12183e0e138e19c26,0x4101e10069445c561479,0xc8182617051047a0e002,0x2c00482040203007c190,0x8321a0881c1e092b104,0x6a002028958c0a8dc601,0x5620203d42a0d0304c10,0x8c48148190a8308204a2,0x65618221005959025110,0x1e04b0561c2185416050,0xb83c0a186040182185c,0xc1a0864202b122901043,0x6090041958b090401985,0x32b0c10050245782c2e0,0xc401010900608617028,0x480214ac604c1c56c2a,0xe1c21040149cc160f03,0x212052060860f02852b,0x15880c050ad83428802,0x20211c37854106421831,0x828f08a62070b8343080,0xd8a2182882c1e120081,0xc53098282a3e00812118,0x8182a443c68501e8641,0x2811832190914c1e0a0],#[0x3c2453048182c00b8513,0x8790540a18c0d0510c8,0x142a28840a4030982c19,0x21543211064b05e08a2,0x40c16011441a08b85631,0x6008282958b118510c84,0x431414432107d14c1e0,0x4148a4170983c0909050,0x60590c840660f02560a1,0x3384c1e0b025a0a14822,0x1e60b02860a110580070,0x70a82c1a04ac3e108583,0x9c26091f0040908c0c83,0x79025630323c07a15071,0xc8460c84c16170691800,0xa3dc18f305840c86880,0x5e1709831e609021927,0xd0a8101865045c2b0e1a,0xac40642585c1e0478581,0x2b10020361707810c8f8,0x8a68641882c2e0f023e,0x21504814204e00832b17,0x83cc120cb8192832931a,0x10f0b8192a002b42a070,0x25618a88342a041d84c,0xc2e0f0256243785c1867,0xb021c0c901b0c8410484,0x2c0a143251087984c1e0,0x804870285ac260c798,0x421c1a82036147b8340c,0x87a0c601b080fc14007e,0x420470b831ee0a004040],#[0x602030f60042200e91,0x80901b0b83c08a200412,0x2426400360a0042420f4,0xd0602d0826112005024,0x22e158a2584c1a512288,0x8174110700808347f0,0x241c1b02036147883809,0x9008a303c1a281320c3a,0xa06c18f05c403602510d,0x409908220e903d420370,0x502242874484048220d1,0x13034441d120c160a834,0x1a84130890c1d120e1a,0x741038160f1220052262,0x211612832181f85c0128,0x8828aa0784c043d0501,0x81b080fc02087e421c1e,0x14d078350429120985e3,0x2a0901030dc05090f211,0x1e841f91484426c1e408,0x4211452261a900641200,0x90b801489072484c220f,0xfc00904c3f1c2e1507e0,0xb00861203c4c3e08340,0x1005a004c22108c48426,0x1710c8008e14ac4a1c22,0x4141617071180884ac6,0x14460221431611434110,0x3c33202304c2e03063d4,0x110787090441a8213088,0x842220f0a1b0d0444c21,0xb4120048260d08880889],#[0x1100830d208ac5c1c320,0x84406147b83411583452,0xa01042413068443c0454,0x606c1600343fc2170806,0xd03f0483c00904c3f200,0x803dc2e0f05800d86880,0xda09001113114342220,0x341541e090b80121709,0x4018080c3c8090084407,0x141c0c13895001f140f0,0x50227140e02400f0602f,0x3408f46e36141e0d1287,0x11028001808604217980,0x271287c3a30f06c0642a,0xf184e254307c3a281850,0x44a3e200c03810d8782,0x80150c080c8330a80c1e,0x2044a1d240c02c2e0f02,0x2811f0a1a06c0b0b8314,0x501907022e158bc2e0c8,0x4a5c0e908582206002b1,0x209707c38a10a818120c,0x307810e9048032150283,0x4c1e0454301c3612c2a1,0xf022812a143a480b0a8,0x83c09050a3e183816816,0xd]]
def g253H10 := limbs80 #[#[0x104600800100c0108000,0x40108040080a130003,0x100600000200002114a2,0x104c0000005000002c24,0xe0034820ac0900020,0x40301022008a520401,0x20000040000000820,0xe8e1140100000000a2,0x83000000002410440,0x84010080a3800000421,0x140110020118601000b,0x18821000010088000500,0x220080000020,0x42200400882040001,0x10800000020042031020,0x100023c481040410004,0x820800300082094a0,0x30400000000800508003,0x840504800104a501800,0x1b440000e10080238003,0xcc0080000940000800,0x8041100200802308142,0x8000108420184138066,0x28ce301401100010946a,0x11804504004102320840,0x31020000200880000023,0x805380618848008003,0x300400802000001009a0,0x108a400c830806200006,0x7020630006009800,0x2014031040101000,0x21280a008121],#[0x204631e0030144730823,0x840119c2160c2011801,0x46009082101210ac05,0x18026000410b40000001,0x1801200230804200820,0xe0000000070a06308405,0xdd5a00000b86b3c,0xfc58c0001fd800000000,0x427f56bb7d2d6ac,0x0,0xa426842,0x239a00018b0f4cd,0xa0000000000000000000,0xa68c280d534cb40,0x20000000000000000000,0xc000000000001e6520b0,0x2994a5e400000000984,0x12d9087af81420000000,0x140c20000000,0xe000153380001d9ec000,0xd87fc00014d0f61caa70,0x1e84cc1e325d23ad,0x2000036966aa5e13e000,0x1039fac9,0x0,0x1a944000000000000000,0x1fcb3066c0000000,0x600a8000000000000000,0xb95a000000000000e5a,0xda65beaec0001c02c000,0x40000000129480001c61,0xd5a20000000140d],#[0x20000000000000000000,0xb39e34,0xa1a82000013220000d86,0xf8dc71b,0x2f9140000000191f0000,0x600000001e0de000083c,0xa694000000000001b75,0x2434e00000001cc5a000,0x179040000000136b,0x1ca5c0000000,0xe0000000190ae0000000,0xa93629c1136e426,0x1c2e800014cfc0000000,0x1881e000000000000000,0x129ae000000000000000,0x1461600000000000,0x1a15e2928000,0xc000000014618f874000,0x1e46,0x1dd4200000000000,0x189e6000000000000000,0xfec46000037000000000,0x1f8d800000001e465c02,0x12ae6466200000000000,0x1c8420000000,0x111a400000000000,0xc0000b7e451f225293aa,0x3ca2e0001236c791c032,0x1a6ba0000aa3ce62,0x8b26000000000000000,0x37f576d40000b92,0x77d779000000000000],#[0x4cba0a55a469a0000000,0x1cb616436e18a207,0x0,0x887d7a780000000,0x128e600000000000,0x1830902bb6230000,0x80000000089b60000000,0xab1e00016c0c00014bc,0x1980000000000402,0x4bad6000000000000000,0x40001e1560001c7e1655,0x80001985400000000220,0x1459800000000000161d,0x14671c98000000000000,0x0,0xc000000006c680000000,0x1609f22964963c65,0x24d,0x129f1a1d2000,0x2a36000175b20000000,0x16637e30e0000000,0x1cc36000000000000000,0x0,0x9ce400000000000,0x71bd77ae442360000000,0x762c06dbfbba97c4e57,0x56c6000091c4000,0xa0cb6327400010b6c000,0xfe5b8cd4a33ec8c0f2a0,0x128ea000006f200001d0,0x20580001f9320000000,0x3eb212cc184fa0000000],#[0x8b8a0000c891ab6,0xbebc33c680620c706000,0x80aae26480000416be63,0x7e4bc000000005a95e7e,0x9b6f5d74c4b,0x1691000000001374a000,0x1e5136d780000000,0xa00000000a2ca0000000,0x1462c000101ab72f,0x2666e72600000000000,0x0,0xc357d2ca41b9c88e000,0x13b52000000008396000,0xcd250f732f2000,0x15780a84000000000000,0x1c6741d40000,0x63f600000000000,0xa61c5420000000000000,0xa000000010a6ef2d60cc,0x120e6a0c40000657db77,0x86a660332d4e000,0xd13cac80000000,0x0,0x983e0001b12a000,0x136bc16922b432a32000,0xfa1600000000000,0x1f0e6000000000000000,0x18604000000000000000,0xc0001f01600000000000,0x1c86c0001c5940001ac8,0xc5f5ca546b8c0000000,0xc0000000000002260000],#[0x3493227f800000000c2e,0x2bb832100000632085f,0x0,0xbd1e00000000000,0xc240668c5e3f5a398000,0x1645c000000000a1cea8,0x88bcbade0000000,0x1489e000,0x189bc000,0x0,0x15a416ac40000000,0x3e2ce0000000169da000,0x2a5800015023c434228,0x128c00000000,0x0,0x80000000000000000000,0x1d7d,0x0,0x6d54f602000,0x642000101960000000,0x2000000018d640001874,0x1fc820000000092c,0x0,0x0,0x2810000123ec0000000,0xad82cd76065820000000,0x12352f94923f,0x1e7cc417e14ac000,0x997200000000000,0x0,0xa8a91030400000000000,0x143cda363a510c5c],#[0xa0820af20000000,0xac89200000000eb66000,0xc0000b4b3107e0001650,0x1bcd,0x41c200000000000,0x2bc0a00000000a366000,0x1d91a0000c02a0001250,0xa00000001d6a50864000,0x8000066560001854ec43,0x265826300000cbabc8b,0x9092c0000b815735c000,0x6000000012b73485b049,0xa0d1d0be62417bb2037,0x6000000013b000000000,0xff71600000000000060f,0xc47800000773c00009bf,0xcaa24da,0x119e80000000,0x95d600000000e078000,0x48a00000000000,0xa0000295545700000000,0x7aa0000088,0x1c4748be200003880000,0xb0c18000000000000000,0xe2bdc064c746896,0xa0000000000000000000,0x17aa4000000000001232,0x1cb740001cd5ab670000,0xebda00000000000,0xa88fe000000012b0c000,0xa0000000000000000c52,0x1eb9c0000f3d789c],#[0x1234,0x4a3e00000000000,0x80000264600000000000,0xb7ba000000000001f6b,0x6ee000000000000000,0x0,0xc268000,0x8e2a4fb61f342b7b2000,0x99052000000000001db6,0x68da000000011b7,0x60000000000012d6e000,0x200006a7200000000652,0x1c4e,0x1804a000,0x1298000137060000000,0xc0000000000000000000,0xc862229000000001f90,0x80000000000004c2c000,0xa11aa000032f6ab47c90,0x6ac3c93,0x80000c9d60001ab9a000,0xf67,0xa0001876200014686000,0xa6035d3699126d29c0b,0x1c7c20000000140e,0x3d15b2c23ecce0000670,0x400000000a2ad6b4e3d3,0x8000195ed9c5200019c6,0x1ed1402eb184bebec3cc,0x4611a000000000000000,0x424fe000000000000009,0x4a1a480308b3f09032a2],#[0xa046000000000000d5b,0x93e400000000000,0x7e1f000000001e63e000,0x1e25000000000e252226,0x6d264000000000000000,0x4490610e9e182d5228ab,0xc00200000000000034b,0xc7b8000000000000000,0xa62164468dd0bab1c000,0xa0001b85a9c99e326ec2,0x8000000000000c0db030,0xda1b0000032bffa0f7cd,0x900bd5bee000000001c1,0xe0000000000000001ecc,0x1c258e4a37cbcc5a,0x623db11c002080000000,0x80000000000000000434,0x646e8b4,0xa07a0001449400006be,0xc000056dbe87f671c000,0xb9cc0001c6e,0xcb6a261ea00000000000,0x400000000000016ed60f,0x2297de9eccd1dd2c1a0e,0x80001445200000000cce,0x42cd0c0a0000661b4aa,0x42d4000000000000000,0xc93400000000000,0x0,0x106b200000000000,0x40000000000000000000,0xd95e945e80000808b06d],#[0x145edca680000635,0x0,0x40600001ebae0000000,0xb24f62c0000,0xe00000000000089e2a43,0x1c3c0000000016d5,0xa5360001ca3a0000000,0x40bd1d85e00000001872,0x1e80471a7d754000046b,0xa000040680000205a000,0x9d8445a4d4a6a,0xa0000000000000000000,0xb1d00001036094b,0xac3e00018d20000,0x164968a2171f4000,0xa825a8add40340000000,0xf2c820001986228d4456,0x4000084be00000000071,0x71e800011462fa2,0xebc000008b8327ee000,0x128760001fd6e000,0x2632cd6a00000000000,0x824b800003ae9aae2000,0xc0001298400017b6a999,0x14816069880a3c31f682,0xa00011d1db115f244000,0xc0001f10e0000bae6a42,0xa154000000011c2,0x1c228000088f9e7ac000,0xe1fc000000000000000,0xc0000000178aba4e0000,0x6683e429a00000001663],#[0xe13caa9da28a46c50da,0x20000000000000000000,0x4a85e83893a50eb8f83a,0x423,0x1281567bc2120000,0x63a800018c580000000,0xda24200000000a9d2000,0x60001875600000001d61,0x70092dac3274e0000b90,0x3299a973800000001284,0x40001335fe844b95d0cb,0xa061200000000000184a,0x1f9fc00000000000043a,0x0,0x151ceccd8000,0x438240001e7a80000000,0x8b3,0x1833a000,0x1f9b400000000000,0x65060000000,0xc00000000000186de000,0x1473,0x188600000000143bc000,0x6ad800000000000017c,0xbb200000000000,0x6000029e800000000000,0xe000189d4224b324bad5,0xae5dc2012a4088a7f8a8,0x1207c000103294665329,0x2750000000000000000,0x10920000,0x4000000006d2a0000000],#[0xf08,0x121a6000000000000000,0x20000000000000000000,0xeb686000000000001e20,0x1a679ca16658,0x0,0x0,0x0,0x89b8000,0x106c20001f8ec000,0xb708000000000000000,0x400000001e15aa222000,0x787dae2e400000001ebe,0xd91ad4410000064cacd8,0x2d620000093db6e58d3,0x623cbe0b39ab90a5a000,0xf02f1897a0001e8cf200,0xc000124d9250400019cc,0x9dcb80000ab040000f94,0x60001495c0001cae445a,0x189fe000000000001259,0x16071ad9c00000000000,0x0,0x0,0x2c752000000000000000,0x63c842e0000011d,0x2aff635a00017b22000,0x1670c000000000000000,0xc8b60000000,0x8000085b6458a0000000,0xa0000000000000000872,0x10334000037c],#[0x1fa660000ea7c000,0xccd95c51800000000000,0x15a1,0xaa86e8e200013d22000,0x6ccc0a3800000000000,0xf0ec0001c458000,0x0,0xb2f800014b5a000,0x0,0x2000000013bec0000000,0x1e455e2fb6aa02a2cc47,0x20000000000000000000,0x165381ae,0x8822000,0xee20600000001fb70000,0x816,0x6c5cc000000008a44000,0x1e0aa00000001d4bc89a,0xca4d6000000002834000,0x1626c00000000b2d,0x25660000000,0x14c7161140000000,0x0,0x4b56e2124774000,0x2c610c84000,0x0,0x2000000000000d088000,0x8c01a00000000db1ba92,0x70aa0001879f22f,0x1508e000000000000000,0xef73e0001ece7ccc4000,0xdeced25b1482e000005f],#[0x824c6ccda000102e725a,0x8000000018466a0d9468,0x52638000000000000fb2,0x180cc000000000001ed2,0x1c0517b05b3d00000000,0x0,0x20000000099dc0000000,0x600005499410c00010da,0x400000000d2a400009a7,0x1935a000000000000696,0x400000000aa840000000,0x147c000000000000039d,0xa0000ecb40001e232000,0x151ea00000ce,0x80dc0000000,0x0,0x40d220000ebd40000000,0x10d3,0xf57cea44a00000000000,0x12c2e0001cb6,0x0,0x16977411d87d80000000,0x20232c900000000,0x64a760000ac1f96ee000,0x3410859e12ad1cd31288,0x6000197f66d8163b1671,0x18ba3040004e,0x16f20000000,0x19d643c9a0000000,0x1f2c4b1960000a0d2000,0xa0000000000000000000,0x98b9200000000000147b],#[0x1187326feecb1627d237,0x40001288da0f20000000,0x1e0d60001132,0x0,0x40000000000000000000,0x8c780000000007875a4,0x8c8a00018986c692000,0x17a057bc,0x60000dc8a00000000000,0x400000000000000011a2,0x40000d270000000010d7,0x5031c000000003a2aa31,0x420ea00000001a4335cd,0x80000000000000000405,0x2000142fdb8391c02c83,0xdc03ce98a0000000126d,0x7295823ada8,0x600000000c37c00007b5,0x93bd8257ec38ff73646b,0xeb530c4a0000c412f12,0xd40f8000000000000000,0x116c8000000000001a24,0x1a144000000000000000,0x80000000017460000000,0x8a220000000000010d4,0xd01c0000000000000000,0xe332000000006a66443,0x5f688000141660000000,0xe7e,0x0,0xe03f000016b940cfe000,0x1603e8439ac240001898],#[0xbf96e0000a7880000000,0x60000000000000000eb0,0x400000001a0c079966bc,0x1c03800000000000104b,0xa0000000000000000000,0x89f800012d7cf5a,0x2270489785fc000,0x0,0x13a96e05796f4e9a2000,0x145f010a5287a0000000,0x46c600000000000,0x1184847eaa1780000000,0x0,0xc0000000026840000000,0xe0001142800008d8944f,0x18ba964c282d,0x200005cd70d040000000,0x1830347de0001222da55,0x171b688838624000,0x1021d46a4a73b6a12000,0x5dec56000000000000,0xaa0771d4a00000000000,0xe0000817772400001684,0x1c6be000000000001436,0x169c2000,0x1c67c63000001e98c000,0x80000189dabf60000000,0x741c0000aaf,0x0,0x4000082aa0001fc2e000,0x826b86f0a9d9408e812,0x1445fc5220000000],#[0x1d60000729c0000000,0x27420000000,0xe2b84000000000000000,0x411600016c5,0x189b0000,0xa0001a2b800000000000,0xc1d,0x6a50d36ac00004818000,0x66798c29d9306c22bd1f,0x1e783e4ee6a0ce5f,0x0,0x0,0xa0000000000000000000,0x10a19e90,0xc0000dc4000000000000,0x1412,0xbc86000000005bc8000,0x189f6285,0x200018ae800000000000,0x3cf000000000f77,0x800000001ecf1a21e000,0x262a7637e29c7a1c80c0,0x1c10198328c74541,0x70bcb27f7e2458c34000,0xe00006826e1800000438,0xe08aaad8fa3514737ed2,0x1acf5e0902d70e3b,0x469ab22635952cc06000,0x16772db920001a589e1b,0xc16c000,0x1a5840000000,0x4d854a8200000000000],#[0xcbd68c40c22,0x0,0xe0000761aa5c60000000,0xc00000001eaea692b807,0x800000000c40a0001075,0x1ca340001ea9,0x4c56000,0x1fcdae1620000000,0xcf86d2a154a614a30000,0x89f,0x452109ce000,0x0,0xa0000000000000000000,0x1e29800000000aa8,0xaed680000708c6c8e000,0x5c9ca46,0x1a6e4000,0x1280e00000000199a000,0x5cb400000001e4dc000,0x83920000000,0xa00000001c69c4048000,0x4ad8b4adaa83a0001859,0xa68a000165e6d09,0x172e0000000000000000,0x0,0xac72000,0x0,0xe0000cb5488b00000000,0xeca80001e53,0xf99cf99eec14e0000000,0xe0000ba0600000000241,0x1230dcacd4277c7c],#[0x0,0x6c880000000,0x7039c000000000000000,0x1dd3400000000a18,0x1d7f000000000000,0x66f80001c8e40000000,0x0,0xfaec00016bb60000000,0x4a83600018a4c0000000,0x126e0cc1,0xa000157740001a77e000,0x49,0x0,0x1a33cd85000000000000,0x0,0x0,0x1d3480000000,0x0,0x1b7420000e442000,0x60000000000000000000,0x40000000000000000824,0x2462000147240001451,0x42cad0c9c2d3e0000000,0x1a8f0a92,0xf64f2000000000000000,0x10d9aaabef5b,0x19922000000000000000,0xa0000000000000000000,0xc51,0x18d7e66f425bd93d2000,0xc17a9e7d356c20000000,0x60000000000000000456],#[0x6d76e8c3cd1,0x40000000000000000000,0xf7b460001f8c6000017a,0x79c20001e20ae9ba03f,0x12486000000000000000,0x14089455cd80fdb2a000,0x1d44ada2e0000000,0x8cb796bc400000000000,0x778000145c98bcda6b,0xd2ce000000000000000,0x6000094e07be98b22000,0x154160001b2d800014a5,0xc0000000000000000000,0xfd9f83d,0xa21520001eaac0000000,0xc60bcad20000e14ce3e,0x103e2000,0x801e60000000151b4000,0x12c1c00000000ab98282,0xeb4c0000000021cc000,0xfe586000001bb65be000,0x12b1600004b40929,0xc0000000000000000000,0x4066ff58600000000848,0xdbd08ae000000000a4e,0x22d20001394e000,0xc8a1c5740000000,0x2ebee000000000000000,0x1a89925a53cd,0x0,0x140a043de6c44fb66000,0x80000000000000000000],#[0x1a6ca7d6c0000885,0x168f60001400,0x16690000,0x8000089cc00000000000,0x37e99b554b1,0x142b4000000000000000,0x87b7b9b5c0001e0e2000,0x200000001252d833e517,0x80000406a00003d5d4c1,0x1b869c56,0x0,0x20000000000000000000,0x20000000000000000b6e,0x6000000000000000139d,0xb84,0x0,0x1cbba000000000000000,0xe9e40000b7fa000,0xa940000000,0x0,0x60000000000000000000,0x161f4e78ce71,0x182d,0x6000000000001f0ac000,0x182c4000000012608f9d,0x0,0x1d6a685914a02bd3e000,0x4da400000000000,0xa11e00000000000,0x0,0xfb0694df2a71ac9e000,0x3d1d8160000000],#[0x3f78a0000ea4a0000000,0x1492fad084384a3d,0xd7abf64a82c280a04000,0xdad4421b2c2756918e06,0x70a52ab4543258239369,0xf3be6f7ffb2df649d002,0x11cf3679b772,0x1462600016a421690000,0x4000004f0f3ee0000000,0x1c4da00000001a01,0x1d626e5b20000000,0x182f6000027960000000,0x1724961a200000000000,0x25c840001e53a0000000,0x87fb189,0xa00000000dc3c0000000,0x162b168c8000148b,0x154be00000000000,0x1382e66bc0000000,0x142fe0001091a000,0xabd20000000,0xa0000000000000000000,0x82cbc0001a7950894c09,0x147a40000000199a,0x520a000,0x1a17a000000000000000,0x0,0x0,0x148a3e374000,0x60000000000000000000,0x6792822400000000260,0xbc1ea6514476000065e],#[0x80000000063d80000000,0x31ee000000000001a02,0x6748000,0xc6afe2b6000,0xe8d9fbc0466766478000,0xc0000000000015585a4c,0x80000000000000000881,0x1e21800000001ad1,0xa0000000049c40000000,0x1376c0000000050eeac3,0x10132000066cc0000000,0x20000000000000000000,0x59e,0x1e337dce1f58ba7ca000,0x1442c00000000000,0x60001c64000000000000,0xb01fe6bea0000000147a,0x600019748e9f55af90c7,0x423e00000001fbc,0x190ea00000000000,0x642da0001894e0000000,0x60000c2a200000001095,0xfd14000165ba0001496,0xc100000000,0x2c4c000000000e7c4679,0xc99c0000c49,0x20000000000000000000,0x8082ae96f000400001a5,0xd07d52d1031260000e18,0xd04d769b36c0851,0x4000000000001a74a000,0xe0000000000000000cc5],#[0x12184e54728a,0x4500000000,0x10660000000,0xe3d656fc0001a210000,0xa00010c1600000000000,0x401964140102caab0bf,0x0,0x1c34d48fc000,0x174da000000000000000,0xab28f8f2000,0x18bf0e80a00000000000,0xe0000000000000000000,0x38f,0x71802e99200000000000,0x7a4800000001c44,0xe22e000000000000000,0xe7c600003250000,0x165da000000000000000,0x1eb7c000110f4000,0xae9700001eb7e0000000,0x6000023b32b1200018da,0xa00000000414a24de6b7,0xa0000cda800000001037,0xe000000004afa00005bd,0x14ca,0xa0000000000000000b05,0x1142a000000000000a4b,0x0,0x10b6888d00ab8000,0x1213a0000000183120ab,0x1060c000,0xfa7f48a400016d40000],#[0x14be8d583a6ea0000000,0x1877f6eb1aa2000,0x3a5d00000e4f80000000,0x9cc3658018e2e5e,0x285de3100000000,0x164a00000000,0x82960000000000000000,0xd61ee254da11ec48213,0xc000000002cbe25d8f87,0x88bac000088d20001072,0x18c84e,0x7340000000000001a39,0x1d4a40000000,0x200002b889c67f1c8000,0x181700000e54a0001667,0x1671a000000000000000,0x7782000000000000000,0x2000064d200000000000,0x56f76d9,0xa32e00000000000,0x40000000000000000000,0xd70200000000ea6b80a,0x12344000065fa000,0x1462a0001a1be0000000,0xe286000005501c1a000,0x723300000a75e0000000,0x149faa7f1c25,0x84c6c00009b72aa5e000,0x13086000000000001c3f,0x97d5800012ce4a4ae000,0x1c08c00000001619e74d,0x40000000000000000000],#[0x1e6dc2c2681e,0xa49e983c53340000000,0x0,0x60000848f54192322000,0x80000000025300000030,0x1a82000012703636,0x20000000000016776000,0x3247e048800014146411,0x2cabd10c0000a7b,0x1c76fa9a59da40000019,0x60000857a00018482000,0xe0000b78e0000000054b,0x2000038df175d6aa6405,0xc0000000093a8c645304,0xe00009843cc1b2d58891,0xc29dc000000000001920,0xe00000d5123720001479,0x46d000000001ec6,0x1c41c00000000000,0x7fc27dcec00000000000,0x8a802640400002227cd9,0x241800000000a6a,0x163e4d24611ece784000,0xcaca21776421bd19c000,0xe0000000000012a4e4c4,0x56669e59e0000f6fb4c7,0x448566a000000000804,0x0,0xd6d,0x12544000,0xc0000000000000000000,0x3096c0001ecc60000ed8],#[0xe3b563a1916bfe654e27,0x6a7b593a22a93c704e5c,0x637ee00000000eda0748,0x101bc00000000594,0xc1dc0000000,0x143641a6e0000000,0x0,0x20000000103e60001a77,0x66146a78e508585,0x1ccee0000000,0x6000092c600000000000,0x20000412a0000000059b,0x60660a07273e93d9d9b,0x1dc89cd2c00000000000,0x0,0x40001095000000000000,0xc29,0x8a4800000001a500000,0x0,0x175556bb40000b836000,0xc8680000000,0x693000000000000,0xb7f2000048ca000,0x1dce7dc9e00000000000,0x1647c2548000,0x16cf800000001bd56000,0x145a0000,0x41944b0600000000000,0xa460000000,0x0,0x0,0x2017017c00000000000],#[0x8380000,0x62a800000000000,0x0,0x272a60001ec3097ea000,0xf209cc3800018c3c457,0x1eb2400004af0000052d,0xa53c520c000,0x42a1a0001eaf5e4ac000,0x11ada0000000000012a6,0xca62000,0x0,0x878000000000000000,0x109b200000000000,0x1001c000000000000000,0x0,0xce72e00000000c94c000,0xc84e00000000d8b,0x122ee08a76cfa0000000,0xf3d48000000000000000,0x20000000000000001fce,0x1d9440001ecd7f37,0xfa700af6000,0x60000000000000000000,0x18801836a00000001b93,0xe6ab5f1ca00000000000,0x187ed62f42b5,0xc3ba000000000000000,0xdbc08107963a5c278000,0x1c8d6587e42af998b80a,0xc15c19d2fb90900f4000,0xfdcb765c00000a90166a,0x15bf80848c525655],#[0x12122000,0x1d5920000468e0000000,0x40e8000000003080000,0x3d549740000000,0x0,0xa00000000712e0000000,0xa00000000398c0001587,0x40000000000000000619,0x76ce000103480000475,0x1aade000,0x0,0x235800008718000,0x78824a97e000083ee000,0xe33800000000000126f,0x31a0000000,0x6cf2da460000000081d,0x6429389a800000bde000,0x104a,0x0,0x10532b2a200016490000,0x161360001bb260000000,0x4c05e68,0x80000000000000000000,0xe0000000000000000abf,0x14764e1b648dec0a,0xa69e00000000000,0x0,0x1a93fdb1e000001a8000,0xe0c821300001753c000,0x1a972000000000000000,0x600002d3600000000000,0xe0bfd89668662be],#[0x1e29e0000000,0x20000000000000000000,0x600000001cbfe000146a,0x1e831c1d5e73303ade91,0x84ad725aba5340000000,0xa0000c3cfcd0d62c7880,0xbbce655800000000666,0x1e42e000000000000000,0x1899,0xc0000000000000000000,0x180400000a8d,0x5ae007d600000000000,0x73a7791800018b2a000,0x71cc4000000000000000,0x143c5a768d86bed6ce10,0x8bce000000000000c61,0x7f20000000,0x8ce8000,0x0,0x600000001483c0000000,0x8d1e0000792,0x39c60000000,0x0,0xc00000000000004cc000,0x100e,0x0,0x0,0x145780001c70b8b9,0x0,0xb8400000000,0x9c46040cb210f26d6000,0x40b8000176d],#[0xd3c8fcb1a00000000000,0x1ae0000419,0x87fe000000002096000,0x40000000000001c96000,0x1ea6c442,0x400012912183a0000000,0x23f2000099880000f8e,0xf9d6200000001489a000,0x806000000000000a1e,0x126fc203b83e80000000,0xd621d27278d20000000,0xbacdca38bb41a0000000,0xe9eac45a064e6265ba9,0x2b300000000000014d6,0x1e942c35e000,0x171a20000000,0xa18e860fc8ccf33e000,0x1405cc4b2000,0xec320000000,0x1474c000000000000000,0xa0000000000000000000,0xe7d00001c5c5412eaa7,0x60000000000000000000,0xa86fb12da92,0x4c860000000061de000,0x2000120f00001cc50000,0x1a64c000000009631e06,0x0,0x6b50000,0x0,0x4cc7c000000008cd4000,0x14c668a894215663],#[0x150c088320000000,0x2d4c000,0x16a080000d198000,0x10d46000000000000000,0xc1f74c5332c8000,0x13ea00000000016546b,0xa0000000000000000000,0xea64a00008a9e0001a8f,0xa000088f400000000774,0x424f1d700001719,0xb84564c80001681a000,0x1cd320000000,0x4b3a0001e0248b9e000,0x13ce80001699f8042000,0x5cba600000000a3ae000,0xfe8558a0fa5c3a5ebb69,0x1454304f6f05c0000a04,0x167590b814d0,0x47be0001a7b00000000,0x0,0xa0000000001f24b4a000,0x1a1f,0x1619200000000000,0xea9641cfb6de000,0xa0000da21376a0000000,0x1400e000000000000241,0x74ba4000154080000000,0x1c85200006660cc9,0x1eb2e000000000000000,0x0,0x0,0x1888909140000000],#[0x196b000000000000,0x1c9c800000000000,0xdcf80000000,0x154880000000190e4000,0x1c67a00000000000,0x1759865d4000,0xbc870a19800000000000,0x169f2b7,0x14c6507f400000000000,0x3c9de0000ab000000000,0x5b6b4256400000c42ac6,0xd68120000e4710b3dc73,0x60000000049880000015,0x40000000169680001198,0x10140695fa3b,0xa0000000169980000000,0x1cc6a00000000000152d,0x1c355153f4010000,0x1c3b80000000104edc88,0x1c8e00000000,0x1c9ee00000000594,0xc0000000081ec0000000,0xe00000001445600010c5,0xeabaeb32000000012ae,0x0,0x0,0x758c0000000,0xca0162a000000000000,0xe0001ca5023a00000000,0xbc7300000000062c9640,0xc8f20000f90e072,0x0],#[0x20001b03800000000000,0x2bf,0xa00000000478e0000000,0xc8a80001852e0001c47,0x10d02000000001c10000,0x2ac00000801e49a,0x1a10a215000000000000,0x1da68000,0x0,0x820e00000000000,0xd4c1a4c463fc000,0x0,0xbc0ee000000000000000,0x75b02a11dd460000234,0xa42800000000000,0x1502c000,0x51668bb00000000,0x8b6a00005924000,0xc95226280000000,0x5a300000000,0x7b046c14800000000000,0xbf9e490f37aa73d1a391,0xc0001ec0200000001f64,0x1823,0x40000000000000000000,0x40000431600000001e0b,0xc9f200000000e88,0x0,0x1278b0ce0000,0xc0000000166fbad26000,0x2000125a2000000002b5,0x1262e861e6d390d1ae8b],#[0x600000000f4dc0000000,0xa3c,0x0,0x1b62e0000ea4,0x11082000000000000000,0xf36b690c000,0xd0c80000036388540000,0xa04,0x40000000000000000000,0xc1778e2e3838cfbe3d80,0xec000001507,0x517d13b7e4b640000000,0xc000000014ac60000cad,0xf03,0x8000000000000867e000,0xe0001465ea8be000068e,0x1291,0xc00015ca000000000000,0x3a77a00000001605275a,0x7a1200000000dc4,0xc625c000000000000000,0xd94200000000abf,0x0,0xab08ad99159be48,0x1e940000000000000000,0x1e1040000000,0x0,0x1562b94a7ad660000000,0x12738000000014c76000,0x80000000100990c94000,0xdd19e24abc0080001385,0xf76e30e34722c86b854],#[0x3471400006cde0000000,0x19c4242,0x961e983b600000000000,0x4cc20000000000000ac9,0x267b6000000004160e90,0x162f,0x444d4d8318a0000,0x20000000000000000000,0x111cc0001495ba51ee2b,0x369868ef9174000,0x47dc0000e69607e3476,0x1c20c00000000000,0x60000000000000000000,0x98200000000000181c,0xc000144f400011b36000,0x1a22f6f04874fac13b7,0x59de16360000000,0x9428c000000012b70000,0x1d9a03cfe3093edaf4cb,0xc000000000001eca449e,0x107a20001cb974af,0x120734a815d1,0xf43a700fe00000000000,0xa0c,0x20000000000000000000,0xd7,0x20001c27b32d4948e000,0x72a26611000016169ad5,0x29786000107e7a767f33,0xa0000000000000000638,0xcb36000000008979f75,0xa43e000060fa000],#[0x4000000000000b110000,0x8933cf6b6b83400012b1,0x11812400bcb5,0x80000000000000000000,0x19ce2cbd,0xa28e00000001e6e6000,0x44e0000000,0x17d4000000000000000,0x4a2b4ca0000,0x0,0x1b9280000000,0x61180000a6e2000,0x2b2c1784000,0x2c34d0afa74000060b,0x0,0x60000000000000000000,0x120b,0x141f80001025e0000000,0x166c8a8d9a318944e000,0x6ad7babdc00000000000,0x80a6000000000001e51,0x0,0x7ed5c67a029be0000000,0xed06608,0x62480000a5574a28000,0xa00006bf5aab329ac000,0xa06e00000000a76,0xa8ec00013d240000000,0xc084000000000001e6c,0xaa7400000000000,0x132cc000,0x189d000000000000],#[0x80000000145d68600000,0x1589e00000000000086e,0x0,0xe0000000000000000000,0xd61e0000000000000ea1,0xe592439442be00002ab,0x0,0x2b1000000000000,0x0,0x10288a710000,0x199840001850e0000000,0x144b0074400000000f74,0x0,0x1cfa00000000000,0x116afa37,0x1fc0fb9c96158b5a9a08,0x5a13400002947e89c000,0x89b,0x180c600012a9a0000000,0x40000000000000000000,0x3bc400000000000172f,0x86683e1a1e6ce0000000,0x6417e12,0x148b40001840c000,0x103e000000000000,0xa28ac000000000000000,0xbb35ccf600000001ec9,0x4ea0000000,0x1c90e000000000000000,0x0,0xe0000e856e5f8a958000,0xa2d80000c17485e],#[0x200000000256f3d08000,0x162dc0000659c0562287,0x60000000000000000000,0x1044145b400000001899,0x400c6cbb2cc2000,0x60000000000000001628,0x9372726d800000001eca,0x62d6417214825b8b470,0x3770b4a9276d5a4c000,0x4938000000000000000,0x983,0x18036000,0x0,0xa00000001bcea0000000,0xa44800007d72eac,0x181ac8bbe000,0xc00000000075a0000000,0x142858bb,0x2000188c600000000000,0x402ed4,0x1cd3ab37000000000000,0x80001894a00008c4e000,0x1812600000000000157c,0x67c80000000]]
def g253D11 := limbs80 #[#[0x50ff503fd30ff483fd10,0xfd31ff487ff60ff583fd,0x8bfd32ffd87fd61ff507,0x460d223046003ff62ff5,0xd02faad26e8a1e26915e,0x2e16120a0c00048ef37e,0x68584838100020c2018,0x20183a16120a04000c8,0x508068583828100041,0x810019201a120e0a0414,0xe0a04001870685848382,0x584838002010d2216120,0x1a16120a000c043c8068,0x48068583828004011120,0x106201a160e0a0210680,0xc0870485848382800,0x84838180021c1a161206,0x216120e0600081870685]]
def g253H11 := limbs80 #[#[0x1922828560e008342e00,0x4c0d160a01a04000a43a,0x80f1503800180400c,0x58000c04028c80a03010,0x6000342a100801412100,0x63c0703c1e310d0200e0,0x4ba03011050c17000909,0xd3433100a8000a1e83,0x230003a0032000262000,0xd01060002a8202c1686,0x26170081c4a080232c18,0x6eb204e3979c01313eac,0x799fc30298f133891a92,0x4d8f020055a892c0a652,0xc7f8001775c82e05f,0x6bc44d15677a0d9966f8,0xda5c000061b39cb26ae0,0xe77746df789d454403a2,0xe74a1d67e90c66b5885,0x33930d46d8a3b599ddb4,0xba0a80f28c7a76250ff1,0x59a2c0a3de87e84e42e,0x3262ad0c43686cbdb70f,0xf083193ab6e8219a6e22,0x210e06000030a9619210,0x2590623478efa850001,0xe000120ce58b532b0266,0x80cc00000000262237a4,0x18954faa1c00070cf266,0x1a0a946be5d41d45033,0x611081f813308b642c0,0x43df80531a50f3e7e800],#[0xea2ad71580c0002d0c,0x879e6286f9bce3b39792,0x214b46d494e0003e1820,0x8ada82712c00011de47a,0xdac63409de088035d486,0x9c04c1ec56a095358a59,0xd4469248065149a45543,0x26a869014c18205a5067,0x98c616072d6c301fc1d2,0xb0fc2057902047413796,0xd01a23987834ab0d371f,0xe062d10be437219434b6,0xa66dc1cd18780e1e4cdd,0x60919d3c389848d4e90c,0x8ab88ce6068471105dd4,0x66cd183269a5c4840709,0x88e701d1a2f58c31aea6,0x923a70851ea018000685,0x60681eab6d442af0b3,0x1e42349c000299788380,0xa5f8001649d9e467dcd4,0x25282ce8e0000b7f7811,0x1a434856115fe73d0878,0x1c699207261800045,0x1c9024d9908379c84000,0x3122b8851c4a800083a5,0x54178951a5ba96c67882,0x7840143047a9b200014a,0x93d857064811629330d5,0xb7e09e2f315ab193418a,0xfa294463d6a22e487a38,0x9e0339a030000186f205],#[0x45d726040a7c9c5ba27e,0xe803d2498610001a46e1,0x862e21283e8000954392,0x13b9d6d763581a1cc029,0xe8001602b9f467ba9c6f,0x983ad462890a63a88205,0xfec586076779e234d8b,0x4661751a3e5acdaa6881,0x6b325c3114d3d9063062,0x544c21000058da566ba2,0x225155080b1a0351d4be,0x6800167c50a100ff5a28,0x18d816f213dc4fa5ff13,0xc2a8978a4f156896e7e,0x88954c1c434e09343241,0x663e2166c90e23f2153d,0x4a250699de7478b,0x59507e0006a3b63d7972,0x70eb253319e088d8622,0x84b909000003396a4400,0x87c45d98d7b59715d783,0x28c80005b140ec46e58b,0x4b12800060d89b0b8349,0x82cdc7d0440001d26390,0x3d05]]
def g253D12 (j : Nat) := if j=0 then 0x5080c1010037f else 0
def g253H12 := limbs80 #[#[0x980000000008800,0x1b000,0x39783e90c52e00ad800,0x3ce000000000ce000,0x20a50000,0x7c0000,0x7c00000003a00000000,0x300000000000000000,0x6801f04900000011600,0xdd1abc8a5,0x74c00000000000,0x584aa0000000]]
def g253L : Nat → Packing
  | 6 => (18,6,7,0,0,8,0,g253D6)
  | 7 => (371,5,7,0,0,13,0,g253D7)
  | 8 => (1489,4,7,0,0,17,0,g253D8)
  | 9 => (1752,3,7,0,0,17,0,g253D9)
  | 10 => (296,2,7,0,0,15,0,g253D10)
  | 11 => (15,1,7,0,0,10,0,g253D11)
  | 12 => (1,0,7,0,0,0,0,g253D12)
  | _ => emptyPacking
def g253I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 6 67 3 10 5 1 g253H7
  | 8 => lookupWord 136 811 6 14 9 1 g253H8
  | 9 => lookupWord 506 2203 10 16 11 1 g253H9
  | 10 => lookupWord 601 6011 5 16 11 1 g253H10
  | 11 => lookupWord 101 439 9 14 9 1 g253H11
  | 12 => lookupWord 6 101 3 9 4 1 g253H12
  | _ => fun _ => none
def g253 : Forest := ⟨253,12,fun i => g253Y[i]?.getD (0,0),g253C,g253A,g253L,g253I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P6_0 : block g253 6 0 18=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B6 : block g253 6 0 18=true := g253P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_0 : block g253 7 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_5 : block g253 7 5 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_101 : block g253 7 101 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_197 : block g253 7 197 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P7_293 : block g253 7 293 78=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B7 : block g253 7 0 371=true := (@block_merge g253 7 0 101 270 (@block_merge g253 7 0 5 96 g253P7_0 g253P7_5) (@block_merge g253 7 101 96 174 g253P7_101 (@block_merge g253 7 197 96 78 g253P7_197 g253P7_293)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_0 : block g253 8 0 68=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_68 : block g253 8 68 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_164 : block g253 8 164 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_260 : block g253 8 260 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_356 : block g253 8 356 45=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_401 : block g253 8 401 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_497 : block g253 8 497 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_593 : block g253 8 593 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_689 : block g253 8 689 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_785 : block g253 8 785 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_881 : block g253 8 881 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_977 : block g253 8 977 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_1073 : block g253 8 1073 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_1169 : block g253 8 1169 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_1265 : block g253 8 1265 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_1361 : block g253 8 1361 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P8_1457 : block g253 8 1457 32=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B8 : block g253 8 0 1489=true := (@block_merge g253 8 0 689 800 (@block_merge g253 8 0 356 333 (@block_merge g253 8 0 164 192 (@block_merge g253 8 0 68 96 g253P8_0 g253P8_68) (@block_merge g253 8 164 96 96 g253P8_164 g253P8_260)) (@block_merge g253 8 356 141 192 (@block_merge g253 8 356 45 96 g253P8_356 g253P8_401) (@block_merge g253 8 497 96 96 g253P8_497 g253P8_593))) (@block_merge g253 8 689 384 416 (@block_merge g253 8 689 192 192 (@block_merge g253 8 689 96 96 g253P8_689 g253P8_785) (@block_merge g253 8 881 96 96 g253P8_881 g253P8_977)) (@block_merge g253 8 1073 192 224 (@block_merge g253 8 1073 96 96 g253P8_1073 g253P8_1169) (@block_merge g253 8 1265 96 128 g253P8_1265 (@block_merge g253 8 1361 96 32 g253P8_1361 g253P8_1457)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_0 : block g253 9 0 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_5 : block g253 9 5 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_101 : block g253 9 101 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_197 : block g253 9 197 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_293 : block g253 9 293 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_389 : block g253 9 389 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_485 : block g253 9 485 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_581 : block g253 9 581 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_677 : block g253 9 677 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_773 : block g253 9 773 50=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_823 : block g253 9 823 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_919 : block g253 9 919 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1015 : block g253 9 1015 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1111 : block g253 9 1111 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1207 : block g253 9 1207 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1303 : block g253 9 1303 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1399 : block g253 9 1399 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1495 : block g253 9 1495 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1591 : block g253 9 1591 10=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1601 : block g253 9 1601 96=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P9_1697 : block g253 9 1697 55=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B9 : block g253 9 0 1752=true := (@block_merge g253 9 0 823 929 (@block_merge g253 9 0 389 434 (@block_merge g253 9 0 101 288 (@block_merge g253 9 0 5 96 g253P9_0 g253P9_5) (@block_merge g253 9 101 96 192 g253P9_101 (@block_merge g253 9 197 96 96 g253P9_197 g253P9_293))) (@block_merge g253 9 389 192 242 (@block_merge g253 9 389 96 96 g253P9_389 g253P9_485) (@block_merge g253 9 581 96 146 g253P9_581 (@block_merge g253 9 677 96 50 g253P9_677 g253P9_773)))) (@block_merge g253 9 823 480 449 (@block_merge g253 9 823 192 288 (@block_merge g253 9 823 96 96 g253P9_823 g253P9_919) (@block_merge g253 9 1015 96 192 g253P9_1015 (@block_merge g253 9 1111 96 96 g253P9_1111 g253P9_1207))) (@block_merge g253 9 1303 288 161 (@block_merge g253 9 1303 96 192 g253P9_1303 (@block_merge g253 9 1399 96 96 g253P9_1399 g253P9_1495)) (@block_merge g253 9 1591 10 151 g253P9_1591 (@block_merge g253 9 1601 96 55 g253P9_1601 g253P9_1697)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_0 : block g253 10 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_1 : block g253 10 1 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_97 : block g253 10 97 31=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_128 : block g253 10 128 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P10_224 : block g253 10 224 72=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B10 : block g253 10 0 296=true := (@block_merge g253 10 0 97 199 (@block_merge g253 10 0 1 96 g253P10_0 g253P10_1) (@block_merge g253 10 97 31 168 g253P10_97 (@block_merge g253 10 128 96 72 g253P10_128 g253P10_224)))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P11_0 : block g253 11 0 15=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B11 : block g253 11 0 15=true := g253P11_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253P12_0 : block g253 12 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g253B12 : block g253 12 0 1=true := g253P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253T : checkedTables g253 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g253 0 0 0 = true)
  · exact (rfl : block g253 1 0 0 = true)
  · exact (rfl : block g253 2 0 0 = true)
  · exact (rfl : block g253 3 0 0 = true)
  · exact (rfl : block g253 4 0 0 = true)
  · exact (rfl : block g253 5 0 0 = true)
  · exact g253B6
  · exact g253B7
  · exact g253B8
  · exact g253B9
  · exact g253B10
  · exact g253B11
  · exact g253B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g253G : graphValid g253 (boundsBefore K237) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low253 : Lower true (varsX 253) (graphGoal 253) 13 := lower_forest (g:=g253) (i:=0) (hints:=132099) (before_sound K237 V237) g253G g253T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K253 := extendKnown K237 13 [(253,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V253 : Known true K253 := extend_ok (m:=253) V237 low253 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K253 V253) (2, 0, 253, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_36116

open PEqualNP.Outside.L_meta_36116 in
theorem PEqualNP.Outside.L_meta_36116.window : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), gates.length ≠ 15 → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 2, 4, 0, 5, 1, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 4, 6, 0, 7, 1, 7, 3, 7, 4, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o window fit _ correct
  exact replaceShort g255R gates o window fit correct
