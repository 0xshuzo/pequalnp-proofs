import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_32153.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_32153
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xeeeefffffffeffffffaa,0xfefefefeeeccaa00ffff,0xffffffffffffffffffff,0xffffeeeefffffffeffff,0xffaafefefefeeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 2 && x 5) || (x 0 && x 6) || (x 3 && x 6) || (x 4 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 1 &&& x 5) ||| (x 2 &&& x 5) ||| (x 0 &&& x 6) ||| (x 3 &&& x 6) ||| (x 4 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,4]⟩,⟨.or,[0,6]⟩,⟨.or,[1,6]⟩,⟨.or,[0,1]⟩,⟨.or,[2,7]⟩,⟨.or,[11,12]⟩,⟨.or,[4,7]⟩,⟨.or,[6,7]⟩,⟨.and,[13,5]⟩,⟨.and,[14,10]⟩,⟨.and,[9,3]⟩,⟨.and,[15,8]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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

def lowRow (i : Fin 8) : Row := Fin.ofNat 512 (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0)
def highRow (i : Fin 8) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< ([3, 4, 5, 0, 1, 0, 0, 0] : List Nat).getD i.val 0))

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
    (lower : Impossible true graph 12 sevenInputs.toFinset) (gates : List Gate) (o : Nat) (width : gates.length ≠ 14)
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
def g73Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3ff63ff63ff63ff63f,0xf63ff63ff63ff63ff63f])),(BitVec.ofNat 152 (word80 [0x492049204920492049,0x20492049204920492049]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc7fbc7fbc7fbc7fbc7,0xfbc7fbc7fbc7fbc7fbc7])),(BitVec.ofNat 152 (word80 [0x924092409240924092,0x40924092409240924092]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8fdf8fdf8fdf8fdf8,0xfdf8fdf8fdf8fdf8fdf8])),(BitVec.ofNat 152 (word80 [0x248124812481248124,0x81248124812481248124]))),(0x0,0x0),(0x0,0x0)]
def g73C : List ColumnInfo := []
def g73A : List (List Nat) := [[],[99],[48],[48,96],[96,48],[96]]
def g73D3 (j : Nat) := if j=0 then 0x7 else 0
def g73L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g73D3)
  | _ => emptyPacking
def g73I (_ _ : Nat) : Option (Nat × Nat) := none
def g73 : Forest := ⟨73,3,fun i => g73Y[i]?.getD (0,0),g73C,g73A,g73L,g73I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73P3_0 : block g73 3 0 1=true := by
  apply cellsBlock (ar:=3) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g73B3 : block g73 3 0 1=true := g73P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73T : checkedTables g73 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g73 0 0 0 = true)
  · exact (rfl : block g73 1 0 0 = true)
  · exact (rfl : block g73 2 0 0 = true)
  · exact g73B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g73G : graphValid g73 (boundsBefore []) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low73 : Lower true (varsX 73) (graphGoal 73) 4 := lower_forest (g:=g73) (i:=0) (hints:=3) (before_sound [] baseKnown) g73G g73T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K73 := extendKnown [] 4 [(73,[]),(146,[16,67,118]),(161,[83,67,118]),(162,[16,83,67,118]),(193,[99,67,84,117]),(208,[64,16,33,99,83,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V73 : Known true K73 := extend_ok (m:=73) baseKnown low73 (by decide +kernel)
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
theorem g43G : graphValid g43 (boundsBefore K73) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low43 : Lower true (varsX 43) (graphGoal 43) 4 := lower_forest (g:=g43) (i:=0) (hints:=83) (before_sound K73 V73) g43G g43T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K43 := extendKnown K73 4 [(51,[16,67]),(83,[64,16,49,101]),(99,[99,67]),(113,[65,33,83,99]),(114,[64,81,32,99])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V43 : Known true K43 := extend_ok (m:=43) V73 low43 (by decide +kernel)
def g89Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf9f40fff81f8fe3ff3,0xe81fff03f1fc7fe7d03f])),(BitVec.ofNat 152 (word80 [0x41c492492412248083,0x89249248244901071249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfbb871fffe00ffc7f7,0x70e3fffc01ff8feee1c7])),(BitVec.ofNat 152 (word80 [0x8239249208a4481104,0x7249241148902208e492]))),((BitVec.ofNat 152 (word80 [0xe6a7803fffff0007cd,0x4f007ffffe000f9a9e00])),(BitVec.ofNat 152 (word80 [0x16a5b6dc30c071222d,0x4b6db86180e2445a96db]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x64ffe3ffffffff80c,0x9ffc7ffffffff0193ff8])),(BitVec.ofNat 152 (word80 [0x249204100800400,0x4924082010008000924]))),(0x0,0x0),(0x0,0x0)]
def g89C : List ColumnInfo := [(16,0,73,0,4)]
def g89A : List (List Nat) := [[],[48]]
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
theorem g89G : graphValid g89 (boundsBefore K43) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low89 : Lower true (varsX 89) (graphGoal 89) 5 := lower_forest (g:=g89) (i:=0) (hints:=393219) (before_sound K43 V43) g89G g89T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K89 := extendKnown K43 5 [(147,[16,32,48,64,118]),(177,[83,118]),(195,[33,49,97,65,84,117]),(226,[16,83,100,116]),(240,[64,16,33,99,82,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V89 : Known true K89 := extend_ok (m:=89) V43 low89 (by decide +kernel)
def g163Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0)]
def g163C : List ColumnInfo := [(1,0,162,0,4)]
def g163A : List (List Nat) := [[],[117],[16],[16,117]]
def g163D4 (j : Nat) := if j=0 then 0x1f else 0
def g163L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g163D4)
  | _ => emptyPacking
def g163I (_ _ : Nat) : Option (Nat × Nat) := none
def g163 : Forest := ⟨163,4,fun i => g163Y[i]?.getD (0,0),g163C,g163A,g163L,g163I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163P4_0 : block g163 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g163B4 : block g163 4 0 1=true := g163P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163T : checkedTables g163 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g163 0 0 0 = true)
  · exact (rfl : block g163 1 0 0 = true)
  · exact (rfl : block g163 2 0 0 = true)
  · exact (rfl : block g163 3 0 0 = true)
  · exact g163B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g163G : graphValid g163 (boundsBefore K89) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low163 : Lower true (varsX 163) (graphGoal 163) 5 := lower_forest (g:=g163) (i:=0) (hints:=85) (before_sound K89 V89) g163G g163T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K163 := extendKnown K89 5 [(163,[]),(178,[64,81,32,50]),(209,[65,33,50,101]),(210,[16,96,32,50,67,84]),(225,[80,97,33,50,67])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V163 : Known true K163 := extend_ok (m:=163) V89 low163 (by decide +kernel)
def g115Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff0ffffff003ff,0xff87ffc3545d520f83e0])),(BitVec.ofNat 152 (word80 [0xa0a80a209002a0a814,0x910008a445812318c63]))),((BitVec.ofNat 152 (word80 [0xfffc000ff87ffffc01,0xfff87ffcd372a6007c1f])),(BitVec.ofNat 152 (word80 [0xc0310c402120c43118,0x8201210052302694a529]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0007ffffffe,0x7ffcafd11df0001f])),(BitVec.ofNat 152 (word80 [0x2c05002c20b00c020,0x2c220a00a541186318c6]))),((BitVec.ofNat 152 (word80 [0x7fffffff,0xffff80004d2fe8007fe0])),(BitVec.ofNat 152 (word80 [0xb02608b044c090241,0x30004c100907c94a5294]))),((BitVec.ofNat 152 (word80 [0xffffffffff80000000,0x33aa61bff8000])),(BitVec.ofNat 152 (word80 [0xc03800c00700e0381,0xc04470211aa6018c6318]))),(0x0,0x0),(0x0,0x0)]
def g115C : List ColumnInfo := [(1,0,114,0,4),(2,0,113,0,4),(16,0,99,0,4),(32,0,83,0,4),(64,0,51,0,4)]
def g115A : List (List Nat) := [[],[65,101],[16,100],[16,96,64,84],[64,16,81,97],[64,81],[80,65,97,16],[80,97],[96,84],[96,81,65,64]]
def g115D4 (j : Nat) := if j=0 then 0x57d4d10 else 0
def g115D5 (j : Nat) := if j=0 then 0xc1a0fd30fd10 else 0
def g115H5 (j : Nat) := if j=0 then 0xe else 0
def g115D6 (j : Nat) := if j=0 then 0x23440bf else 0
def g115H6 := limbs80 #[#[0x7e2,0x82aa000046009900000,0x50000a70000c000000,0x10000f300000]]
def g115L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g115D4)
  | 5 => (2,1,3,0,0,4,0,g115D5)
  | 6 => (1,0,3,0,0,0,0,g115D6)
  | _ => emptyPacking
def g115I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g115H5
  | 6 => lookupWord 2 37 2 8 1 3 g115H6
  | _ => fun _ => none
def g115 : Forest := ⟨115,6,fun i => g115Y[i]?.getD (0,0),g115C,g115A,g115L,g115I⟩
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
theorem g115P5_0 : block g115 5 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B5 : block g115 5 0 2=true := g115P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115P6_0 : block g115 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g115B6 : block g115 6 0 1=true := g115P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115T : checkedTables g115 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g115 0 0 0 = true)
  · exact (rfl : block g115 1 0 0 = true)
  · exact (rfl : block g115 2 0 0 = true)
  · exact (rfl : block g115 3 0 0 = true)
  · exact g115B4
  · exact g115B5
  · exact g115B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g115G : graphValid g115 (boundsBefore K163) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low115 : Lower true (varsX 115) (graphGoal 115) 7 := lower_forest (g:=g115) (i:=0) (hints:=65605) (before_sound K163 V163) g115G g115T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K115 := extendKnown K163 7 [(115,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V115 : Known true K115 := extend_ok (m:=115) V163 low115 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff007f87f87ffc0,0x3fff8ffc48be5000f0f0])),(BitVec.ofNat 152 (word80 [0x5442a1505109100a8a,0x85092009489a53333333]))),((BitVec.ofNat 152 (word80 [0x1ffff8007ff87fff,0xc07ff1ffbb19600f0f0f])),(BitVec.ofNat 152 (word80 [0x1880c0606202010303,0x6020410290941111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xff8001ff941fb0f0000f])),(BitVec.ofNat 152 (word80 [0x610b0582802c222c0c,0x82c48a01416b6666666]))),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06030430443010,0x103000c20264a4444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008040040004020,0x20400100000008888888]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,5),(2,0,177,0,5),(16,0,163,0,5),(32,0,147,0,5)]
def g179A : List (List Nat) := [[],[64,81]]
def g179D6 (j : Nat) := if j=0 then 0x4689f else 0
def g179L : Nat → Packing
  | 6 => (1,0,2,0,0,0,0,g179D6)
  | _ => emptyPacking
def g179I (_ _ : Nat) : Option (Nat × Nat) := none
def g179 : Forest := ⟨179,6,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
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
  · exact (rfl : block g179 4 0 0 = true)
  · exact (rfl : block g179 5 0 0 = true)
  · exact g179B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K115) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 7 := lower_forest (g:=g179) (i:=0) (hints:=65605) (before_sound K115 V115) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K115 7 [(179,[]),(211,[65,101]),(227,[16,100]),(241,[64,16,33,50,83,99]),(242,[80,65,32,50,97,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V115 low179 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xe003ffffe1fff811e5,0x9c0bc000000fc0fc0fc0])),(BitVec.ofNat 152 (word80 [0x40a80a0244001110e5,0x9c0040c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xfffc00fffe1fffb10a,0x7c94700003f00003f03f])),(BitVec.ofNat 152 (word80 [0x84308c208044203102,0x6c046249249249249249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff00001fffda3d,0x31312000fc003f00003f])),(BitVec.ofNat 152 (word80 [0xc0100b0881400a3d,0x11110186186186186186]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x8b87903f00000003ffc0])),(BitVec.ofNat 152 (word80 [0x901204c0009824608,0x3839514514514514514]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ec8fc000003ffc0000])),(BitVec.ofNat 152 (word80 [0xe01c070110e044100,0x62ec8618618618618618]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x100200800010000000,0x820820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(1,0,242,0,7),(2,0,241,0,7),(16,0,227,0,7),(32,0,211,0,7),(64,0,179,0,7),(128,0,115,0,7),(3,0,240,0,5),(17,0,226,0,5),(18,0,225,0,5),(33,0,210,0,5),(34,0,209,0,5),(48,0,195,0,5),(65,0,178,0,5),(66,0,177,0,5),(80,0,163,0,5),(96,0,147,0,5),(35,0,208,0,4),(50,0,193,0,4),(81,0,162,0,4),(82,0,161,0,4),(97,0,146,0,4),(129,0,114,0,4),(130,0,113,0,4),(144,0,99,0,4),(160,0,83,0,4),(192,0,51,0,4)]
def g243A : List (List Nat) := [[],[65,101],[16,100],[16,96,64,84],[64,16,81,97],[64,81],[80,65,97,16],[80,97],[96,84],[96,81,65,64]]
def g243D4 := limbs80 #[#[0x10c86613935935354110,0x4110c866139355363541,0xc60a64e857460c745]]
set_option maxRecDepth 16000 in
def g243D5 := limbs80 #[#[0x90221c65765495148110,0x324c5204421bf26c3aca,0x60b2a6498a40886f0611,0x221dc1754c93148110f,0x24c520443b86ea992629,0x8b2aa698a40886f06153,0x221b618554a3148110f2,0x50520442ba726bac6290,0xaa2a4a0a40887e050d32,0x21b61855494148110f90,0x5204436c30aa9482902,0x9aa4a8a408847ce61759,0x1d63735495148110eb0b,0x520442ec726a92a29022,0x904a8a40885d86565254,0x7a1942095148110be0c9,0x20443aa2e6a9aa290221,0xe6a8a40885d864b53545,0x59655cd5348110ce9c1e,0x44359107c12ca90221c,0x4a8c408863621f835952,0x197e115188110cb9c3aa,0x4423e32fc0aa5102211f,0xa8e408870e5d56455220,0x9859573c8110ea2b9aa4,0x421bb2fc1acb902210df,0x9a60885d464f52545304,0x24c9518c110f29c8acaa,0x3ac2e4a92a318221f415,0x460886745d7835463044,0x607528c110be1c8aa499,0x7a726c0ea9182213d393],#[0x8088636e1f8359630442,0x4d51d0110e98aa2e2a86,0xa706b9aa3a0221d51735,0x884ae6538654f404433,0x554d0110cd9c3b02aa68,0xf0bba2c8a82215b39760,0x88798589525455044307,0x5154110eb1b92a4a8aa0,0xe6a9aa2a8221e516354d,0x8674e0f7354550443aa6,0x154110f18b22a928aa08,0x8aa0e2a8221b31845525,0x56c25172dc5504436630,0x54110da8a9f02992a088,0xc0e84a8221a598654d32,0x8e61954d0950443662a8,0x4110d2dc1ea6b12a0886,0xa6c4a822165993215625,0xc65281dc95044347308a,0x110ab8cad03b92a08856,0xa86a8221c39645537254,0x55181d0d504434b30ca9,0x10d1cc32a9a1aa0886cc,0xa6a8221a5984d8f53541,0x1164d4d50442cb726b26,0xb2cc9ea8b1aa08868e6,0x6a822165b93553635411,0x9645515044347308aa6c,0xb8cc9cc8aa2a08858ee4,0xa8221731911d15454110,0x7455150442e53243a2a8,0x4cc98e8b22a0885c664c],#[0x8221659932156454110b,0x41d150443332e8c18e8a,0xdcc2e83a2a08856ce457,0x22107f9561d644c9108d,0x5c04244217f28c3aca99,0xc9acab80848853ae4965,0x214bb945957010910a6d,0x94424421bf30b2ae6212,0xaf06b28848861b5d7825,0x10dd97e0d6510910c2eb,0x4424421bf26c3aca2122,0x2cab848488517e4d865d,0x68f935974290910a5dca,0x4244255b25c22cb21221,0xe2b82a488437e4d87596,0xb1941c57054910ae8c98,0x24423e53038ae0a92215,0xc38aa48862d5d9841c55,0xf9461f635491087bcc2e,0x44315ee8c16c8a92210b,0xba2a48852e64374d9152,0x85e01765491086fc9b0d,0x431a907c0aeca922187b,0xb2a48861de17815d9524,0x4e0d7654910c4fc2106b,0x29d724b22e1a922189f8,0xea488539e49645c75244,0xe0964d491086fc9b0eb1,0x4db2bc12c9a92218ad74,0xc488437e4d8759352442,0xd47558910c57ba704b22,0xbb2fc1acb3122107f985],#[0xa8843be61721c9654421,0xd7259510c6a39f02b92c,0xd3039ae4b2a2189f841c,0x88627213735c9654421b,0x7359510c4fc26e6b92ca,0x20416e6b2a210bf9460b,0x852725182dcd654429b3,0x154210a4fca305b9aca8,0x8b92c4a8421acb835897,0x59ae558158950842d572,0x48610f24c1aa6b12a108,0xa92a290c216659654951,0x3ae417558921842ccf2c,0x4610d32c2b02b12a3085,0x3ac4a8c214e990dd1625,0xbe51875895184299f26c,0xa1086fc9b0db92a30852,0x2a6b14214e990dcd6254,0xe458754d628425d321c1,0x30974c8702aa2c5084b9,0xeca88614af9261d64544,0x4174587510c21df24c26,0xa5dc82e8b26a21853ce,0x2a826187965e0174d443,0xf71545504c34b30ca9e4,0xd2ca9b05b0aa09875454,0xa8261a598654e5254130,0x735c9504c363708a9ae4,0x5fca30eb2e4298566650,0x2a610bf9461b71549308,0x9c9654c21df30b90e4b,0xfca30eb16a31863adc98],#[0x4610bf9461b7154a3085,0xd92515421df24c0eecaa,0xc3f06b08c2a8437e4d87,0xa1539905d15418550c6b,0x896154313f0839ac4b0a,0xc6e7312c2a8627e13735,0x14cd92193735855086ec,0xd6154299d24326e6b0aa,0x281b0cc2a8437a6064dc,0x939856017498550f18aa,0x6154295f24c32e930aa1,0xba6c2a8527e4d865d2,0xf39160b7054d50a74c91,0x35426b326c10e0a9aa11,0x5b82a6a86d264d821c15,0xf9460b6394d509b9c8b0,0xd4313ae9c12c631aa129,0xb9ac3a862bd0984dc961,0xa07403003000877c9309,0x9c258480800f41802d04,0x430831001f43d0720d41,0x8a013a2684b894122238,0x816a2c8578ac15229851,0xa433c660c41822f85d8b,0x3b0748e61c636c6c0d51,0x48d11221441c7f8fc1f2,0xe1392624b89592824047,0x5129c52ca41452844fc9,0x2cc58cb015d2b455caa1,0xc5ecbc1752e45bcb6169,0x4cc818d31461cc21812f,0xd41a534467cce19932c6],#[0x1c737e6dcda1b135c6ac,0x43c2778ed9d83aa748e5,0xf27d8f99f03da7a8f39e,0x83905a0840a808ff9fc3,0x911a2043a8690ba14422,0xda3846a8c917a2c45289,0x5049a92923a444828f91,0x4ca9892fa5c4b295929a,0xa9e93ba744e29b935a68,0x4947a8c512a1941a804f,0x53aa4542a794da9852aa,0xabc572ad959ab055aaa9,0x4000b3965ac858ab095f,0x1a4040b060669022400,0x81906140104100224002,0x10410881002b81c87,0x1041000,0x904100000000000000,0x2e034200001000400000,0x81810141000504000,0x5040000a001,0x0,0x0,0x40d04000000000000000,0x70c1000d0]]
def g243H5 := limbs80 #[#[0x82000004814091800,0xc10000000000]]
set_option maxRecDepth 16000 in
def g243D6 := limbs80 #[#[0x8520442f060c2148110,0x442f86142148110b6185,0x5495148110fc1324c520,0x4c1109f38754620443d8,0xe596554d30443d454d51,0x54440442f4e0d518c110,0x443745cd5110110de172,0xe1d5110110d717554440,0xd0110d71815d4404427c,0x8df835d950443acd9151,0xd4d504439658d5354110,0x4438e5915454110e5b63,0xe0d76d49108df835d952,0xd4d10cdb635c35344237,0xe596554d308429761763,0x589508439a54d6254210,0x8439a5516254210e6b53,0x58d5354210e6b5458950,0xd4610e39645515084396,0xce9625c3528433a58970,0xd5162842ba6035358a10,0xc335dcd6154430ae980,0x5977354430c9d64dcd51,0x54130e5953d85504c317,0xe5953d89504c35654f71,0x1cd504c2d66165354130,0x8c2d660f5454130b9984,0xe117654a30e396455150,0x54d508f787584615422f,0xb69821c153542dc60470,0x58c63542ce6107054d50,0x54237e1d6318d50c9d74],#[0xe0550481108bf845cb63,0x48110cf97654120442fc,0xbf181d4120442be61950,0x54520443d95495148110,0x442bbe096548110cf576,0x61d6548110adf8359520,0x481108ff855d9204423f,0xfe1524c520443f850931,0x4c520443f454d3148110,0x443bc5953148110bf184,0xdd53148110df1754c520,0x48110bf1854c5204437c,0xef1658c520443f854a31,0x8c5204437c5d63148110,0x442fc6163148110df375,0x5494148110fe13250520,0x48110ef16550520443f8,0xdf17550520443bcd9541,0x90520443f854a4148110,0x4437c5d64148110ef165,0x5495148110bf18590520,0x48110beb8254520443da,0xfe25254520443f854951,0x54520443dcd495148110,0x443f8e095148110fe082,0xd4d5148110f715354520,0x48110df17354520443dc,0xbf383545204437cdcd51,0x54520443bc5915148110,0x442fce115148110ef364,0xdd55148110df17554520,0x48110df175945204437c],#[0xbf185945204437cdd651,0xd4520442fa60b5148110,0x443765cd43481109f987,0x5955348110dd97354d20,0x48110afb8654d204439e,0xbf181d4d204427e61d53,0xd4d20442fa60b5348110,0x442be61b5348110e7965,0xe0573481109f987d4d20,0x48110df3815cd20442fc,0x9fb855cd204433e59573,0xdcd204433e5977348110,0x442fae0965481109f985,0xe056548110bdb8359520,0x48110afb8159520443bc,0xeeb8259520443ba20965,0x59520443b620d6548110,0x442bee116548110edb83,0x60a6548110cf88759520,0x88110af984d9520442fa,0xf735254620443dc54951,0x54620443bc5915188110,0x4437c5d55188110bf384,0x5d55288110bf38154a20,0x88110bf181d4a204435e,0xaf986d4a204435e5d752,0x55220443ae5915488110,0x442be6195488110d7975,0x60754881109fb8755220,0x88110d7975d5220442fc,0x9f987d5220442be61b54,0x592204433e5d56488110],#[0x443b6e0d6588110afb85,0xe1d6588110afb8459620,0xc8110df1815d6204433e,0xdd973543204437c5c550,0x547204435e5d550c8110,0x443755cd51c8110f6552,0x61d51c8110d757554720,0xc81109f787547204427d,0xcf5655c7204437954971,0x5cf20443735cd52c8110,0x442bbe0965c8110cdd65,0x5d565c8110adf8359720,0x4c1108ff87597204431f,0xfd153c8530443f854b21,0xc85304437c5d7214c110,0x443dc549514c110bf185,0x50d514c110f735254530,0x4c110fd15354530443f4,0xdf17554530442fce1151,0xd4930442fce05524c110,0x442f660f524c110bf181,0x61f524c110af986d4930,0x4c110ed96550d304427e,0xfd18154d30443765d543,0x54d30442f6e11534c110,0x4427ee1d544c110ed965,0x60f544c110bf181d5130,0x4c110af986d5130442f6,0xef381595304427e61f54,0x5d530443b6e0d654c110,0x4427ee09754c110df381,0x4c9518c110ddb835d530],#[0x8c110f715254630443f4,0xdf17254630443dcd4951,0x54630443f4e0d518c110,0x4437c5d5518c110bf384,0x595328c110fc9524ca30,0x8c110dd9754ca30443b6,0xde97254a30442fce0552,0xd4a304427e61d528c110,0x442be61b528c110bf181,0x595728c1109f987d4a30,0x8c110d7975552304433e,0xbf181d52304427ee1d54,0xd52304435e5d7548c110,0x4427e61f548c110af986,0xe1d658c110edb8359630,0x101109fb825d6304433e,0xdf1815d4404437c5d551,0x59540443ce5515050110,0x442afe116550110adf83,0xe0575501109fb805d540,0xd0110df171543404427d,0xf395454340442fce0550,0x54340442eee1150d0110,0x442fc60750d0110d7975,0x61350d0110f3954d4340,0xd0110d7975d4340442ee,0x9f787547404427d61d51,0x5c7404436d55171d0110,0x442b7e0d65d0110cf565,0xe1d65d0110abf8459740,0xd0110f7153547404423f,0xdf17354740443dcd4d51],#[0x54740442fce0d51d0110,0x4437c5d551d0110fb154,0xe1953d0110dd97354f40,0xd01109f98754f40442be,0xbb984d4f40442fc60753,0x5cf404427e61f53d0110,0x443ec60554d0110db954,0xe1d54d0110bbb8355340,0xd0110bdb83597404436e,0x9fb8759740442eee1165,0x99740442ee61265d0110,0x4437c60575d01109f987,0x61371541109fb835d740,0x54110a7f85589504427d,0xcbf74591504438f59154,0x595504429fe156454110,0x4423fe097654110adf83,0x5495154110cdf835d950,0x54110ef16254550443dc,0xdf37254550443bcd8951,0x54550443dc54d5154110,0x443bcd8d5154110ef163,0x58a5154110df37354550,0x54110df37294550443bc,0xef16494550443dc55251,0x1c550442fc6125154110,0x442fc6107154110f7154,0x5cb7154110bdb835c550,0x54110f7153dc5504437c,0xbf183dc5504437c5cf71,0xdc550443dc5537154110,0x442fc6137154110df274],#[0x54d3254110bf3814c950,0x54110edb634c950443d6,0xaf9864c95044376dcd32,0x8c9504427ea1d3254110,0x4427e61e3254110af986,0x60442541109fa878c950,0x54110bd98310950442fc,0xaf98610950442de61442,0x109504427e61c4254110,0x443ce55142541109fa87,0x61a4254110fab4290950,0x541109f98790950442be,0xbf181d09504427ea1e42,0xd0950443ce5534254110,0x442be61b4254110b7985,0xdc95254110bf38154950,0x54110deb72949504437a,0xb7b8558950442be61a52,0x589504439e54d6254110,0x442bee0d6254110e7b53,0xe156254110e788558950,0x54110bd983989504439e,0xe7954d8950442de61662,0xd89504439ed536254110,0x442fce057254110af984,0xe117254110bb8845c950,0x54110bf1819c950442ee,0xbf181dc950442f660e72,0xdc9504437c6077254110,0x4427e60f7254110df281,0xd537254110d7954dc950,0x54110cf964dc9504435e],#[0xf595350d504433ed9372,0x50d50443b6d8d4354110,0x442be6194354110b7985,0x5534354110bf181d0d50,0x54110b7985d0d50443ce,0xed96354d50442be61b43,0x54d5044376dcd5354110,0x443d6dcd5354110f7181,0xe115354110e796454d50,0x54110e7964d4d50442de,0xe795458d50442de61353,0xd8d504439ed516354110,0x443b6dcf6354110af982,0xd536354110e7954d8d50,0x54110af984d8d504439e,0x9f982dcd50442fce0573,0x55150443ae5915454110,0x443dca055454110f7181,0x5915454110b7b8355150,0x54110f3a6455150443ce,0xf3874551504439ed9154,0x95150443cedd15454110,0x443ae5925454110bf181,0x61a5454110b798595150,0x54110b7983d5150442be,0xe7b64d51504439e59354,0x59150442dee156454110,0x442bee0d6454110afb82,0xdd16454110eb87459150,0x54110e788559150443ae,0xbd983991504439ee1564,0xd9150442de6166454110],#[0x442fc6047454110af982,0xa087454110be9821d150,0x54110bd9831d150442fa,0xbf3815d1504436e5d074,0x9d150442fc6067454110,0x442fce055294110dbb74,0xe1d6294110de97254a50,0xd4110cfb87592504433e,0xcf5645c7504433d58971,0x58b504427de1171d4110,0x4432f5d164d4110a7f85,0x593714c910a7f8559350,0x4c9109f584dc5324433d,0xaef82591324427d61771,0x591324423f61d644c910,0x442b7e0d654c9108ff87,0xe1d654c9108fd8759532,0x4c910cf7815d9324423f,0x8ff855d9324423fe1176,0x5c2324437a549708c910,0x442f9e05528c910cf965,0xe0d658c910ced7654a32,0x8c9108fd8759632442b7,0x9f7815d6324423fe1d65,0x5c0424423fe15768c910,0x4433ed957010910cf965,0xd957310910cdd655cc42,0x10910aef825944244337,0xc7d7559442442b7e0d65,0x594424423f61d6510910,0x4431f5d765109108ff87,0x60175109108fd87d9442],#[0x10910c7d865d4424435e,0x8ff855d8424431fa1975,0xd8d42443cb5515250910,0x442b7e0d65509108fd87,0x61f65509108ff8759542,0x509109fb805d5424423f,0xde9525c2424423fe1975,0x5c2424433e5957090910,0x443ab5974290910cfb65,0x5d95290910eaf65d0a42,0x90910adf83596424433b,0x8fd8759642442afe1165,0xd96424423fe1d6590910,0x4427de0575909108fd87,0x1c570549108ff855da42,0x54910df3715c1524437c,0x9f581dc1524437cdc670,0x1c552442f560c7154910,0x4433d5d87154910bb584,0x9db7154910cf576dc552,0x549109f980dc5524433d,0xdf280dc5524437c60371,0xdc5524433dd8b7154910,0x4427d61371549109f583,0xd977154910cf565dc552,0x54910cf686dc5524433d,0xa7d85d8952442f360e62,0xd8d52442bb60b6354910,0x4423f61f6354910cdf73,0x61b73549109f980dcd52,0x54910b7581d51524423f,0xaed82d91524423fe1d64],#[0xd91524432fdd36454910,0x4427e60374549108fd87,0xe0965549108fd86dd152,0x54910adf8359552442bb,0xadf835d952442bb60b65,0x5d952442afe117654910,0x4426fe1176549109df83,0xe017654910cfb805d952,0x54910cf7815d9524423f,0xcdf835d9524433720d76,0x5d9524423fe0d7654910,0x4423f6077654910c7f85,0x61376549108fd83dd952,0x94910cf9655c2524423f,0xaef82596524433ed9570,0xd9652442b7e0d6594910,0x4433ed8970d4910aed82,0xd8d70d4910cf9635c352,0xd49109fb835c3524433e,0xcfb645c3524433e59170,0x5c7524433dd8971d4910,0x4433dd8d71d4910cf563,0x59171d49109f7835c752,0xd4910cf7645c7524433d,0xa7d85d8b524427de1171,0x58f52443375cd63d4910,0x4423f61f63d49108fd87,0x5d164d4910aef8259352,0xd49108fd87593524432f,0x8fd87d93524423fe1d64,0x5db524427ee0174d4910,0x4433720d76d49109df83],#[0xe0d76d4910cdf835db52,0x589108ff845db524423f,0xaef8259562442bbe0964,0x59562442b7e0d6558910,0x442bb60a6558910c7f75,0x6137358910c7f7599562,0x589108fd85dcd624423f,0xc7d751d562442b760c75,0x5d562442bee017558910,0x442be6027558910adf83,0x60f7558910c7f759d562,0x98910cdd655ce624423f,0xadf8359662442bbe0965,0x5d3624431f5d56598910,0x4423fe1175d89108ff85,0x6037254d10df1715c153,0x54d109f581dc9534427e,0xadf83595534423f61b72,0x595534439ee016554d10,0x4433ee017654d10e5f83,0xe0d7654d108ff825d953,0xd4d108fd82dd95344337,0x9f7815cb534427ee0970,0x5975344337d8d72d4d10,0x4423fe0976d4d10e5f83,0xe1172d8d10cdf835db53,0xd8d108ff855cb634423f,0xcdf835d7634423fe0975,0xdc1654437cdc77059510,0x44376e037359510ddb73,0xdc77059510cdf73dc165,0x59510af982dc165443bc],#[0xedb73dc165443b61cf70,0x1c965442be60f7059510,0x44337dcc7259510ced72,0xe057259510afb805c965,0x59510cdc735c965442bd,0xadf835c96544337dcd72,0x5c965442af2117259510,0x442be6027259510abf84,0xdca7259510af5819c965,0x59510cdf739c9654433b,0xcdc73dc965442b760e72,0xdc96544337dcf7259510,0x4423f61372595108fd83,0xe037359510afb805cd65,0x595108fd82dcd65443b6,0xcdf80dcd654433760373,0xdcd654433720b7359510,0x44337a0b7359510cdd82,0xe1172d9510cdf82dcd65,0x4c210bd983d49308423f,0x9f987d4930842be61b52,0x5d530843b6595534c210,0x8433ee19754c2109fb82,0x5855154210ee96248550,0x54210ee96254550843bc,0xbdb835c550843ba58971,0x58950843ba5895254210,0x8439e54d6254210ee972,0x6056254210e7b5358950,0x54210ee95358950843ba,0xee98358950843ba5cd62,0x58950843ba5516254210],#[0x843ba6156254210ee974,0xe197254210bbb845c950,0x542109f983dc950842be,0xe7b7654d50843b658d53,0xdcd50842bee197354210,0x843ae59154542109f982,0x5875454210e7b7655150,0x54210afb865d1508439e,0xaf983dd950842be60b76,0x54521842be6137654210,0x843b95895148610f6552,0x6195248610e756554521,0x48610aef8654921842bb,0x9fb805d5218433b5d562,0xdc1518437c5077054610,0x8439b58952546109f982,0xe195254610a7d8654951,0x54610e6d62d49518429f,0xcef72589518429f61b52,0x58951843b96056254610,0x8439b6156254610cef74,0x61d6254610e6e8558951,0x54610cee87589518433b,0x9f980dd1518423f61b72,0xdd1518431f5977454610,0x8429fe0965546108fd86,0x59170d4610cf9625c351,0xd4610e6d6254b518433e,0xced7258b518429f61952,0x58b518433b5d162d4610,0x8433b61d62d4610e6d85,0xe0174d4610cbd7459351],#[0x58610c7d655d3518427e,0xaf581d4961842be60352,0xdc5528423f61f5258610,0x8433b58b7154a109f980,0x6037354a10cef7358952,0x54a108fd86dcd528427e,0x8fd83dd9528423fe0d76,0x5c7528433e58d70d4a10,0x8433b5cd62d4a10ced62,0x61d63d4a10cdd7358f52,0x58a10aef8254d628423f,0xaed82d4d62842be60353,0x5c5628423f61f5358a10,0x842bbe157158a10ced75,0x61d5358a10ecd7354d62,0x58a10aef8754d62842bb,0xced755cd62842bb61f53,0x55162842bbe157358a10,0x842bb6075458a10aef81,0xe0d7558a10aef815d562,0x58a10aed819d562842bb,0x9f980dc953842bb60e75,0x5d9538423f61b7254e10,0x8423f60b7654e108ff82,0x5977055210eb964dc154,0x55210cf976dc1548439e,0xcf986dc1548433e59770,0xdc5548427e6037155210,0x8431f5977155210cbd64,0xe0d7159610c7d655c754,0x596108fd83dc965842b7,0xed773585510c23f60b73],#[0x589510c33ddd16154430,0xc3a75937354430cef74,0x5db7354430e5d65dcd51,0x54430cdd64dcd510c337,0xcdd86dcd510c33759773,0x591510c32fdd16454430,0xc32f61d6454430eb581,0x5977454430cbe8759151,0x544308fd86dd1510c31f,0x8fd84dd9510c23fe1176,0x58b510c33d5d161d4430,0xc32f5d164d4430ced74,0x61d64d44308fd8759351,0xd44309fb805d3510c32f,0xcf5755d1610c31f59574,0x5d5610c2bde157458430,0xc2bde117558430ed783,0x6137159430af5849d561,0x59430e5f835c5650c23f,0xa7d84dc5650c29fe1171,0x54d504c3d66015354130,0x4c3d654d2154130f5b80,0x61b2154130f5953c8550,0x54130df371545504c2be,0xaf982d85504c3d654d51,0x5c5504c3b654f6154130,0x4c376dcd7154130f5953,0x54f7154130bdb835c550,0x54130dd953dc5504c3d6,0xaf986909504c3ce55142,0x949504c3d654d5254130,0x4c2be61a5254130f5953],#[0xe156254130f595358950,0x54130f5953989504c2de,0xed953d89504c2de61662,0x1c9504c3b6dcf6254130,0x4c3d654d7254130f5953,0xe0d7254130dd8735c950,0x54130bbb845c9504c2f6,0xbd9839c9504c3d654e72,0x54d504c3d654f7254130,0x4c3d6e055354130f5981,0x5537354130f588754d50,0x54130bd984dcd504c3d6,0xf3b74551504c3d660d54,0x5d1504c2be60b6454130,0x4c23fe1d6548530bdb83,0xe0565c8530ced7654b21,0xc85308fd87597214c2bd,0x8ff855db214c23fe1d65,0xdc9514c2d760f5254530,0x4c23f61b72545309f980,0x61b74545309f980dd151,0x54530af781595514c23f,0x8fd84dd9514c23f60b76,0x5db514c277e1173d4530,0x4c23fe1176d45308ff82,0x5c952d8530af78154b61,0xd85308fd8754b614c33b,0xadd83d4b614c2be60352,0x5cb614c23f61f52d8530,0x4c23fe0975d85308ff85,0x61b71549309dd83dc152,0x54930a7d85d89524c23f],#[0xaed82d95524c2bbe0965,0x5d9524c2bde057654930,0x4c23f60776549309f781,0x60b6594930aef8259652,0xd49309fb815c3524c2bb,0xa7d85d8b524c33ed8970,0x595624c23fe0576d4930,0x4c31fdd66558930c7f75,0x5d56598930aef8259662,0x59530ddb73dc1654c31f,0xcfb72dc1654c2be60770,0x5c5654c3b6dcf7059530,0x4c2b7e0d7159530afb80,0x61371595308fd82dc565,0x59530ced721c9654c23f,0xaf7815c9654c2bee0172,0x9c9654c2be6027259530,0x8c23f6077259530cef72,0xe0d5154230ef16154550,0x54230e7954585508c2f6,0xbdb835c5508c39ed5161,0xdc5508c2bee197154230,0x8c3ba5895254230cf962,0xd4d6254230e795358950,0x54230bbb845c9508c39e,0xafb865c9508c33edd972,0x551508c3b658d5354230,0x8c39edd95454230eb964,0x6077654230afb865d150,0x54230af982dd9508c2be,0xddb735c1518c2be61376,0x585518c39d5496154630],#[0x8c3b5dcd6154630e7752,0x5895254630cf77458551,0x54630cef72589518c39b,0x8fd86dc9518c27e60372,0xdcd518c3375db7354630,0x8c27760b7354630dd980,0x5977354630cdd64dcd51,0x54630cdd86dcd518c337,0x8fd86dd1518c27e60374,0x5d9518c23fe097654630,0x8c23fe117654630cdf83,0x61376546308fd82dd951,0xd4630cf9625c3518c23f,0xe6d6254b518c33e59170,0x58b518c33b5c962d4630,0x8c32f5d164d46308fd87,0xe0552586308fd8759351,0x58630af980d49618c2bd,0x8fd87d49618c2bd60752,0xd51618c2be6035458630,0x8c23f61f5458630af581,0xdcd6254a308fd86dc552,0x54a309f980dcd528c33b,0x8ff815d9528c2afe1176,0xdd9528c32fe117654a30,0x8c33e58d70d4a308fd81,0x61d63d4a309df835c752,0x58a30afb8054d628c23f,0xaed82d4d628c2be60353,0xdc5548c23f61b7254e30,0x8c23fe0576552308fd86,0xe0d71d52308fd81dd954],#[0x59630adf835c5658c277,0x8fd84dc5658c23f60b71,0xdc9658c2afe117259630,0x5423f60774596308fd81,0x54f70545509f982dc151,0x545509f983dc1515435e,0x9f984dc1515435e55370,0xd8d5154397d8d5354550,0x5433ed897094550cdf73,0x60b6194550d79545c251,0x94550e7554d8651542bd,0x8fd87d8a51542bd61361,0xd92515432f5d36494550,0x543b5e0d61185508fd87,0xe1d6118550cf57458461,0x18550abf84588615433d,0x9f9805c8615423fe1d62,0x590615434f5d15418550,0x5427e60174185508ff87,0xdcf7058550dd873dc161,0x58550cdc735896154376,0xcef729896154337dcd62,0x9896154337dce6258550,0x543371cf6258550add83,0xd8d5358550cdf73d8961,0x58550d5f7354d6154397,0xddb80dcd6154357dcf53,0xdcd61543575537358550,0x543371937358550d5f54,0x9937358550cdd64dcd61,0x58550cdf64dcd6154337,0x97e87d51615434fdd154],#[0x19161542bb6086458550,0x542b760c6458550aee82,0xdd264585508fe8719161,0x98550ef140d86615432f,0xaf584d86615439d55361,0x552615432f5d36298550,0x5435e5c35498550d3d74,0x61f5498550d3d74d5261,0x98550af781592615425f,0xd3d855d2615436e60174,0x593615432f6197498550,0x5423fe0d72d8550afb80,0x60272d85508ff845cb61,0xd8550add839cb61542be,0x8ff825cf615429f61672,0x953615423fe1173d8550,0x542bee0174d85508fd87,0xe0174d8550cf8805d361,0xd85508ff825d3615433e,0x9f981dc1535423fe0d74,0xdc1535427e60b7054d50,0x542de6087054d509f984,0x6077054d50b7a861c153,0x54d50b7982dc153542de,0xb7984dc153543d6d8f70,0x5ca53542dee017154d50,0x542b760b6394d50cdf63,0x6017218d509f9805c863,0x18d50adf8258c635437a,0xcdf635ca6354337e1d63,0x5c7635426fe1172d8d50,0x5423fe1171d8d508ff82],#[0xe0572d8d50abf845cb63,0xd8d50cbc845cb635423f,0x8ff845cb635432fe1172,0x5d3635423fe0574d8d50,0xd42b7e0d70587508ff82,0x60f7258750af5819c961,0x587508fd84dc961d423f,0x8fd84dcd61d423f60b73,0x5d161d42bb2097458750,0xd42bd6067458750aef82,0x60b7458750add839d161,0x58f508fd83dd161d423f,0x8fd84dc563d423f60b71,0x9c963d42bde057258f50,0xd42b760e7258f50af980,0x6137258f508fd81dc963,0x58f50afb805d163d423f,0x8fd82dd163d423f60774,0x27007201200300060000,0xb011403f00ed03540b40,0x81920630174057014404,0x21008041f207b01c206a,0xa90a442700960237087c,0xc843120c0c2eb0b282,0xe7c3900dbc3570cfc33,0xe043210443f90f843c0,0x684cb12a848911a04471,0x452e147c50713e04e013,0x57f15e4561156c54c14f,0xf417945d616f85b81680,0x518fc630188461217e85,0x1aac6a51a58687195064],#[0xc386ff1bc06e11b486ba,0xc47591d2873b1cb071d1,0x87981e247831df47771d,0x8041fb07dd1ef07a41e7,0x67218484020a08192028,0xc23348b5229888e21d88,0x249c918244890323ac8d,0x5bc960254494224f092d,0xdc9b12688993263497e2,0xc9f927a89db27549c626,0xa4128c8a1a2850a0527f,0x922a0ca6b2970a56291c,0x12b2cac52ad8aa72a84a,0x2c4cb042bd4ae62b80ad,0xd6cb4c2d18b372ca0b22,0x68b942e14b7f2dc0b612,0x4bca2f10bbe2ebcba02e,0xc09300cbf42fb8bdf2f6,0x513108c3c30d8c273060,0x43294c9f321cc6f3180c,0x33b4cde333ccc9330ccb,0x4f8d2f3480d11342ccfc,0xf4d7735a0d62354cd4d3,0x4db6369cda13648d8335,0xdfe37bcde03768dcb371,0x343894e1f3840e0a3810,0xe3a20e703984e52390ce,0x3b40eca3aeceac3a74e8,0xc84f123c0cef43bb8edf,0x10f753d74f4e3d20f303,0xcfbd3edcfa83e64f933e,0xfea3f90fde3f3cfc93f0],#[0x3240b10144014fff3fe4,0xc41f506e417d05041050,0x43810c842e50aa429108,0x4c5119442910443f90ef,0x7518e45fd15e453d1404,0x91df47411c146c91a346,0x21e483d20947e91f447b,0x6f495d24849092334891,0xe4a7d2904a0527b49d52,0x4c512fc4bb52d54af52a,0xddd3684d6534a4ced323,0xfd3b04e8539b4e553864,0x53e64f813d14f2d3c54e,0x43750a1419504d4044fd,0x76519d461516d44c50f5,0xe52e14a9526948b52154,0x53954df53654d353354b,0x4d95305485512540d4eb,0x6558a55ed56c55515455,0x55b756c55ab569559f56,0x5f657c15e1576d5cc56f,0x59594d63b586960b57f1,0xc5ab569e5a3d68059c56,0x5bf96ef5ba56da5b2d6b,0xcf572e5c7d7195c4d70d,0x3977f5dc176a5d6d74c5,0xd7d05f297c45eb179d5e,0x80f60017fa5fad7e55f7,0x69616984b60f182d6079,0xa62ad89c623588761e18,0x63cd8ed63798d863258b,0x4c9923647591763fd8f9],#[0x3198665b996865659416,0x99e967219a7668599b66,0xa796961a4068c5a22682,0xaf6aa5aa36a75a8569fd,0xe6ba1ad06b29ac46ad5a,0x6c55b0f6c25b036bf5ae,0xd75b456cfdb306ca9b24,0xddba86e65b8a6dedb756,0xdbf96fcdbe46f55bcf6e,0xc3870c9c2c7051c056ff,0x8071c5c627171c4d70f9,0xd729dca17249c8c7219c,0x73bdce07369ccb72f1ca,0x471d16741dd0173edcf5,0xb5d5e753dd4974e9d2b7,0x5da6765dd9175e5d7375,0xdee77a1de2774ddc476d,0x247879e187825e0377f5,0x579bde607945e4278cde,0x7a95e9f7a41e8179ede7,0xb6ded57b19ec07ae9eab,0x8df147c15eff7bc1ee17,0x5f4a7d11f3e7ce1f297c,0xf897de9f747db9f5f7d6,0xc87ec1faa7e91f957e3d,0x4804e0047fd5fe67f5df,0x81b605e8162049810e03,0x2b20a6828209a822e085,0xd20e5835a0c782e20b28,0xe12d847a10f84260fa83,0x175859a157852214284c,0xcf87021b186ae1938612],#[0xe87fe1f987aa1db87561,0x891e24188ca223885220,0x9d226e89a2262897224d,0x862928a322868a0227a8,0xe2ec8b9a2ce8afe2b08a,0x34f8d023288c8a3138be,0x978e463828dce3648d7a,0x68f1e3c18eca3a38e763,0x903e409900e3fd8fba3d,0x13a43f90e642a906e415,0x5a487920647291b245d9,0xa4c692de4b192ae4a592,0x520946a50293f24ed937,0x56954254a951253e94e2,0xc961a58095c656b95965,0x96f25ad969e5a1964a58,0x8125fe97be5e9976a5cb,0xea63498ba628984260a9,0x6673999265e993e64998,0x6cd9afa6af9a8268899e,0x39bf66f79ba26e29b4e,0x99cce7249c7a7189c4a7,0x9dca76c9d767579d2273,0xe7e7999e4e78d9e1e778,0x327bd9ede7b19eae7a59,0xe7fc9fda7f09faa7db9f,0x85fa14284aa112823a02,0xb0a286892a23287da196,0x1a3ca8eca3528c5a2fe8,0xa4ea934a496916a41e90,0x6e29a9a66a98ba5aa949,0x4aa03a7ae9dca75a9bea],#[0x2a5da93aa48a8e6a2aa8,0xad2ab0eab4aa2aa7ba9b,0x3eacbeb0eabdaae7ab62,0x3ae4ab7aadaeb5cad36b,0xb066c0aafeebecaf2ebb,0x162c52b10ec3db0bac28,0x3ac88b1e6c73b1b6c67b,0x6cc7b306cbbb2b2c9db2,0xcf4b3bacdfb366cd3b33,0x21b44ad0cb41ad00b3ea,0x9b58ed5db53ad3fb4c2d,0xb666d93b636d7eb5bed6,0x762dc9b70edbdb6bada8,0x82e11b80adf3b7b6de7b,0xee50b92ae3bb8d6e26b8,0xe86ba02e7ab9aee65b97,0xbcbab6e9eba62e92ba32,0x4bbd6ee6bb82ec8bb0ae,0xbcd2f25bc7ef19bc4ef0,0xdf2f6dbd7af58bd4af43,0xeefb5bebefa0be6af8bb,0xefd9bf4efcdbf1efc1be,0x6c002ffabfaefe5bf7,0x45c0ff030c087012c033,0x4c1d706fc1a705ac1530,0xc2d30aec2a3099c22b08,0x3cf0edc39f0d8c3270ba,0xa7123c45310ec3ff0f9c,0xb150c52b144c4fb138c4,0x17dc5df168c58b15cc55,0xd7c7231c2c6cf19bc633,0xac88b213c8131f5c79b1],#[0xc9ab264c957246c90323,0xaef2acca7728eca23279,0x332fdcbbb2dfcb672d3c,0xf360cd23342ccab312cc,0x39fce67393ce37375cdb,0xf9cf873d2cf0f3b4cebb,0x6d05f411d02f405cfff3,0xd13743ed0e3432d0b342,0x233486d20347ad1d345c,0xe74b3d29349ed263492d,0xf4e9d38f4d4d33b4bfd2,0x531d48b513d4134f5d3b,0x8bd5f356dd59f558d503,0x1d6ef5b5d6bf5a0d66b5,0xd7a35d9d74f5cdd71f5c,0x87b618d827603d7f75ee,0x53645d8ff639d8ab624d,0x767bd9d766fd98365ad9,0x6a8da8b69cda5b687da0,0x402090402090402dadf,0x580e06100fa408840409,0x804180b04030b04020b8,0x20984020984028302160,0x40209840209840209840,0x5101325080a10080098,0x401928325040060340c,0x52850208054281850201,0x150a06a50a04120a8503,0x2408424a105428120c20,0x1045801044132826504,0x2018401080582818458,0x4150a04050a04030b85],#[0x818401002a120a06050a,0x150a06100a8503080542,0x88200120862c2090c20,0x2410444090c041014103,0x10018004018400001028,0x30548070802540022540,0x21824104440008052024,0xc0e069230c5110202901,0xe41081a080c3049a08a,0x2060482081c11202c304,0x22208406044409041208,0x35201c20001102000000,0x405200429102a491004,0x6122043120042208222,0x20448010820020886081,0x90021008121834320842,0x410402182002c1008208,0x160800b0404081818302,0x4820804104160804304,0x16040d22080008200016,0xc090c04100010086080,0x21820000104860801604,0x41028a08001030206040,0x812082000010200090,0x4000060804100005820,0x41048202001008208001,0x3c10082030400102080,0x4101820029001091021,0x401030201040608000,0xc40804104c4084010082,0x20800704160800000100,0xa0c1000608024068],#[0x2081810182000c10000,0x20004006018203034104,0x28a08001004808001008,0x2030206040c081810,0x1c0020461848004011,0x20c08000000401080200,0x1703420682000100400,0x22404020890183022404,0x2000200040170342008,0x40304000000804102c0,0x3000c100814102830103,0x80040a08125040a081a0,0x81410400148081414002,0x10541002a08541002a0,0x40a08041028200002040,0x2c082244085850084010,0x70a0890021014112604,0x1040208141c08212,0x80400082000001410002,0x20418102820014102821,0x8185070a08004001800,0x6040008385070a,0x408205040008be4a1000,0xc181080142028200040,0x10282000000000150420,0xc0a0890100052820294,0xc030404910010664812,0x1120215044a0c0018002,0x24040a0800104000814,0x8181030280050008000,0x2c28215070a081410302,0x2820800090100012054],#[0x8001000205040408181,0x10182000010602000402,0x1104002020204180814,0x30700080020c0410000,0x10186020800002030104,0xa1808392e0700180002c,0x2040602080803010604,0x46180831230420102,0x820000001309040,0x182000000c3040618082,0x303040d5104000010000,0x130c103020604000801,0x2000004c11202030c0,0x282000400006180020,0x20000504000000820404,0x10000080c1008,0x8003041e080010000080,0x4080c300840000004000,0x40000a09001010325040,0x26081410000282000050,0x2820000014101020004,0x30400002080000c1,0x2000010002000010002,0x40000a0800004000001,0x4120900200000020000b,0xc185810002020400080,0x4010400802004010b056,0x41000000002008183000,0x8006040608306040c099,0x8001001c08106060c0,0x3c1c1040105820f040,0x81400420080000010582],#[0x20000404200800100000,0x9040000000000000600,0x10012060a82081410402,0x42942001208300e1014,0xa504180a94100120a941,0x5084808015040a080000,0x5040800000001504480,0x24040000325040208008,0x50800080000010602080,0x148a30804082000410a,0x24040000000018002,0x10082000000400000002,0x802404060800,0x8000040000008002,0x99410400022082000010,0x100ca0800004820,0x1008200081000000008,0x410000002009,0x6080c101820000000,0x1a88001a960610001000,0x2020004000010000,0xc200020000100020004,0x18200040008003040322,0x6800c0a030006000400,0xc1008002820904120814,0x85088608582010141002,0x10b8205040080285040d,0x1c10581c4a0910060824,0xc1225090008141004a08,0x1c282070500085c28070,0x5814800d00850b0a090c,0x8541018020a1c160610],#[0xa0800c0400a82190418,0x20304001820000010100,0xa08000000000001008,0x80010202000400000000,0x204040800000004000,0x41010200000040010200,0x400802000412080002,0xa0800000100000800,0xc2000000205040000000,0x5410282050400601,0x2000400042082410a820,0x241000608001908,0x80000000000,0x4000020000102020004,0x204040000200000,0x80000000c10002040400,0x1020004100000,0x161410b0200581000000,0x402090010280085642,0x6010a80080410082c,0x40a00205040c28210040,0x80003e4215001a002050,0x82a23080a0021006420,0x80403001433142002d40,0x16083c1002c080000c50,0x800000000300840f04,0x502026002c5040000028,0x80000410000000000000,0x54104820000004100000,0x810c86020a8217042c08,0x241018a081410182005,0x304002020000000000],#[0x200002040000000200,0x80000000410000,0xc100]]
set_option maxRecDepth 16000 in
def g243H6 := limbs80 #[#[0x4040401011000091400,0x2000031700250801,0x4040012490b01180399,0xd930d3f250207210101,0x2e000e15060204010049,0x6771dbe0f0040170908,0x341f0e1010023d040a05,0xc01b0815260886030b02,0x40bb1b02022102d60201,0x4096c02b524fe02e,0x558c0000a016e0380520,0x507ca0a9f203a25c900a,0x4503d202c50f303a8041,0x60869067f26500004105,0xd0669073b0700000,0xb0ad7254c010e028e034,0xd09bf03b90580000,0x5a10300002577201f,0x22460000337700000000,0x911e0000e08b4238385c,0x901bb1070000609d0000,0x493ca072a8490432f145,0x1030c061b04ca918807a,0xd310007de07fc0ae,0x513c3104485a50ba1470,0x413a5047d155803f0153,0x703d730b906a500fb0be,0x5118429e91172208044a,0x1102232503747ba324c,0xd24d37a617b8640c,0x143d84e0000d04e807e,0xf9a61032e0890000811d],#[0x97bb005af053306e0075,0x693b7026605ca04b70a8,0x1051508aa09222168111,0xf1169085f08fe035,0x4308200150488652b0a4,0xf2070142e0980000d03e,0x4144d1ad1131679d3014,0xd631b05f9006a0186062,0x7333650111090000601e,0xc03680bd31409524b008,0x804d0000e020f01c3050,0xd00db36720550000,0xc06990244630f1a0b14a,0x243170a0c79f50400000,0x836ae0a37206f081,0xc2489057f1a280970000,0x20b74064600b4084c229,0xf0279369217270aad650,0x82128078431f623e962f,0x1082d646000093077838,0x10b60000000000000000,0xe0440000d0499088d204,0x1002279e1095b0540000,0x7000d02200006021502a,0x4156f30d0000c23d,0x4090a0b4448c21730000,0x600c0311409460b98077,0x5017025e7068305df215,0x504f5915a087b25bc093,0xc92080a680af30ac1080,0x99276013f277e36bd042,0xc527365100000000809a],#[0x3046310cb10192233029,0x500e68440220b06f70b2,0xc106713750a50000d233,0xd0ab90b8a420c0bf0000,0x80630000f62c906d708e,0xb30cc02dc0078076562d,0x50710241f0b1b0a28114,0x10b30000021400000000,0x4301004ab924a05eb479,0x6012c10b410e00000000,0x15620c111b10112019,0x17b9809f8211f07b4400,0x30a7b09c017171a1233f,0x74530213584ab0330000,0xd06b10831052a025e83d,0xd0bc583e306c401de02c,0xc09e200470590000,0x82350000424b00008043,0xc0a1000000390000c031,0x6445321ac24700006200,0x403c0091b056f647a079,0xb36890607045408d8023,0xe0099099459d6113e08c,0x448eb0035065458e2074,0x10b0101ae102005b720d,0xb222d81e456ac10f462b,0x502f811c60b5]]
set_option maxRecDepth 16000 in
def g243D7 := limbs80 #[#[0x2f4b9080887e02148110,0xaf2ea20221765cc4044,0x426fb9aca886bb64d011,0x10eb2a6a8261ba589508,0x433eb2aa4086ed62548,0x8109feeca90213f5d952,0x30427ebb6a40867d65d4,0x4c10cfacaa9821b758d5,0x530427fbb2a6084fd765,0x594109faeda98219f597,0x9204427fb9aca084ff72,0x148110fe262902213f5d,0x520443f8a0a40887f23,0x5148110fe2a290221fc9,0xdcd20442fcb9a40887f2,0xb6548110df2ca902217e,0xe5ca20443f8a8c40886f,0xf96588110df2c9102217,0x7d5c720442fcbac40886,0x7f3214c110bbae790221,0x1f650d30443f8a8a6088,0x86f9654c110fb2a69822,0x21fc54630442fcbaa608,0x885f9728c110fb265182,0x2217e5d6304437cb2c60,0x885f97510110fe2a220,0x221fc54740442fab8e8,0x80887b954d0110bf2e7a,0xa82217ddc550442fcbae,0xaa0887f151541109faec,0x2a8221fc1c550443f928,0x12a0886f96254110fe6e],#[0xa6a82217edc9504437db,0xb1aa08877b5354110ef2,0x6e6a8221bed8d504437c,0xdaa2a0887795454110bf,0xf6c8a8221be59150443b,0xfcb94a0886f96294110d,0xbf2eb28221be59250442,0x2fbb8a64885f571d4110,0xbf2e1192213f5d93244,0x42fcb8084884fd768c91,0x10afaea21221775cc424,0x4427ebb0848857e75109,0x910f5e85212217e5c242,0x2442fcb80a4884fd7690,0x4910bbae6292217d5c45,0x52442df3a0a4885bd741,0x54910beee2a92213f5d8,0x2524427fbb2a4884fd76,0x694910edea5292217e5c,0xc752442fcb86a4884fd7,0x73589109faeda92217d5,0x5ce624427fbaac4884ff,0xd75d89109fae9b122177,0xf595534436eb1aa6884f,0xff7654d109faeca9a219,0xb7d8f53442fcb86a6884,0x4fd76d4d10cfacba9a21,0x13f5d7634427eb96c688,0x86fb7059510bbee6b2a2,0x213fdc9654427fb82ca8,0x886df7359510db8e6b2a,0x4213f5cb654427fb9aca],#[0x1086f9654c210fb2a698,0x421ee55340842fcbaa6,0xa1086f96254210bf2eba,0xa8421de54d50842fdb92,0xaa1086f96354210ef6a6,0x8a8421de55150842fdb9,0xb2a1086f96454210ef6a,0xe0a8c21bb589218437db,0x312a3086ed6254610bf6,0x2e1a8c219f5955184377,0x7316a3086ed62d4610bf,0xdac4a94219f597518437,0x7fbb2a5084fd7654a10d,0xddac5a94217e5c352842,0x376b8ac5084fd76d4a10,0xddea6b1421bb54d6284,0x4376aa2c5086ed7358a1,0x10ddaeab1421bbd51628,0x84376a9cc5086ee7558a,0xa10ddaa931421bbd4e62,0x38436eb1aa7086ef5498,0x4e109faeca9c219f5955,0x53842fcb86a7084ff765,0x552109faeda9c219f597,0x5548435eb22a9085fb70,0x6552109faecaa4219f59,0x9754842fcb86a9084ff7,0x72596109faedaa4219f5,0xdd1658427fb9acb084ff,0xd6254430deac2a88613f,0x7dcd510c377312a2186e,0xbe6454430d7ac8a88617],#[0x3f5d9510c33eb2aa2186,0x6f561d44309feeca8861,0x1bb98b510c376b16a218,0x86be64d4430d7ac9a886,0x613f5db510c33eb2ea21,0x186f75258430deaa4b08,0x861bd5d5610c37aba2c2,0x2186f55298430deceab0,0x9061bb589520c37ba94c,0xa4184fd7654830cfacaa,0xa9061bb58b520c27fbb2,0xac4184fd76d4830cfacb,0x2b2861bb9d5620c376ba,0x8aca184ff72594309fee,0xe4b28619fdc5650c33eb,0xa9aa09867f7259430cfa,0xaeca826177dcd504c3ae,0xdb8aa0986fb61541309f,0xb2a6a8261bed89504c2f,0xbda9aa0987da5354130f,0xfb6e6a8261f61cd504c3,0x3bdaa2a0987795454130,0xbf2eb28261bed91504c,0xc27ebb642985dd73d413,0x30bf2e1a8a613fdd9514,0x4c27ebb6a2985dd73d45,0x9309faebb0a613f5cb61,0x24c2fab88a4985f97014,0x49309feeca92613f5d85,0x524c27ebb4a49876f529,0xd89309faeda92617e5c3,0x1654c37db82ca984fd75],#[0x2595309fee2b2a613fdc,0x85508c27eb96ca984ff7,0x6254230bf6e2a8461be5,0xd4d508c3bca9aa1186f9,0xb5454230ef2a8a8461de,0xedd9508c37cb22a11877,0xdf7354630deac2a8c61b,0x3fdd9518c27ebb2a3185,0x4fd76d4630bf2e1a8c61,0x13f5d9528c376b12a518,0x85f970d4a309feeca946,0x617edc1538c27ebb6a51,0x185f970d4e30cfacaa9c,0x461af591548c33eb2ea7,0x9184fd7655230cfacaaa,0xa4617e5c3548c27fbb2a,0xcb184fd76d5230cfacba,0xb2c613fdc9658c27fb8a,0x2c2286f572584509fee8,0xa8aa1b75c9631437aba,0xca2a85f97094550bf6e,0xe6b0aa1bd584615437bb,0xb0cc2a85df7358550bb8,0xce930aa16f5d2615437b,0xea9ec2a84fd72d8550b7,0xfae7b0aa19fd4f615433,0xfdb82a6a84fd74d85509,0xef6e0a9aa1de1c153542,0x36fb1ca6a85f97094d50,0xafae9a9aa15f5d65354,0x42fb388c6a85f57118d5,0x50bdce431aa17b5c8635],#[0x542deba0c6a86dd6318d,0xd50dbec731aa16f9d063,0x35427eb96c6a84fd71d8,0x87509fee4b0ea13f5d36,0x63d427fba2c3a84ff735,0x58f509fee4b1ea13fdc5,0x9520437eb2aa4084ff74,0x654c10dfacaa9821bf5d,0xcd650437eb92ca086fd7,0x5048110ff2a090221bf5,0x59520443faa8a40887fb,0xb5148110ff2a290221bf,0xe50d20443fcb8a40887f,0xfb5348110ff2a690221f,0xfe59520443fcb9a40887,0x7f95288110ff4ca90221,0x1fe55220443fda944088,0x87f950c8110ff6a91022,0x21fb54b20443faa8e408,0x885fd75c8110dfacb902,0x221fe54930443fca1260,0x887f9544c110ff6a498,0x8221fe54a30443fdaa26,0x60887f9548c110ff6a51,0xa0221fe54140443fdaa4,0xa80887bd5450110feaa2,0x1a02217f5d5404437eb2,0x8e80887fb50d0110ff2a,0xcba0221ef55340443faa,0xa9e80885fd75d0110dfa,0x2cba0221fed4f40443fc,0xaa8aa0887fa65d0110ff],#[0xfee4a8221bf58950443f,0xbfaa2a08877d5454110b,0xbfee8a8221bf59150443,0x3fcb8aa0886fd6554110,0xff264a8221fedc55044,0x43fc212a0887fa325411,0x10ff484a8221fe509504,0x443fca92a0887fb42541,0x110ff2c4a8221fe94950,0x443fc392a0887fa6254,0x4110ff4e4a8221fe5c95,0x50443fca1aa0887fb725,0x54110ff2a6a8221fed0d,0x150443fdb9aa0887f973,0x454110ff4a8a8221fe55,0xd150443fd322a0887f96,0x7454110ff2e8a8221fe1,0x54a50443fdba2a0887fa,0xd62d4110ff2a928221fe,0xf55350442feb96a0886f,0xfd74d4110dfac9a8221d,0xbf595324437eb2264885,0x6fd658c910fdaa519221,0x1bf59442442febac6488,0x85fd7510910dfeca2122,0x21fb54942442febb0848,0x886ff6350910dfac6a12,0x221bfd95424437eb2a84,0x4885fd7650910bfaeaa1,0x1221bf59642443f6a948,0x84885fd7590910dfecb2,0xa92217f5d852442febb4],#[0x2a4887fa7054910ff2e0,0x2a9221fd1c552442ffb8,0x12a4885ff7154910feee,0xc4a9221fb98952443f6b,0xb1aa4886fd6354910dfe,0xaa8a92217fdcd524437f,0xeb22a48877f5454910ef,0xfee8a9221bfd91524437,0x7fb2aa4886fd6554910b,0xbfaeca9221bf5d952443,0x2ffbb2a4886fe7654910,0xdfacb29221fb58a5244,0x42febaca4886ff659491,0x10bfae1a92217f5da524,0x4437fb16a4885fd71d49,0x910dfec7a9221bf58f52,0x24437eb26a4885fd73d4,0x4910bfae9a9221bfd935,0x624437eb22c4885fd76d,0x58910dfacab12217fdd1,0xd62442ffbaac4886fe65,0x558910dfee6b1221bf5c,0xd5624437ebaac4886fc7,0x6598910dfeeab1221bf9,0x5c153442febacc4886fd,0xd6554d10bfee4a9a21fe,0xf5cb534437ebb2a6886f,0xff7259510ff6e0b2a217,0xbfdc165443efb9aca885,0x6fd7259510df8e4b2a21,0x1bfdc9654437f392ca88,0x86ff7359510dfae6b2a2],#[0x21fe54930842feb94ca8,0x87f92154210ff6a4984,0x421fe5c550843fca8aa1,0x1087f97254210ff2a4a8,0x8421fe5cd50843fca9aa,0x43087f97454210ff2a8a,0x90c21fb54921843faa8a,0x2a3085fd7548610dfaca,0x4a8c21dfd4951843bea9,0x22a3085ff7254610dfac,0xcaa8c217fdd1518437eb,0xb16a30877d52d4610dfa,0xac9a8c217f5cb518437e,0xfa92c3085fd74d4610df,0xfee2a9421fe5c1528437,0xffb9aa5086fd6354a10b,0xdfaeca9421bf59552842,0x37eb1ea5085fd71d4a10,0xdfaa6b14217f5cf5284,0x43fcb82a7086ff5358a1,0x10dfacaa9c217fdc9538,0x842feb96a7086fd7654e,0x210bfee2aa421fedc154,0x48437ebb2a9086fd6555,0x9610dfae2b2c217f5c75,0x658437eb9acb086fd725,0x54430fbee6a8861bf5d1,0x5510c2ffba2a2186fd64,0x4d4430dfaeca8861bf59,0x95520c2feba6a2186fd6,0x7159430dfaeca9061bf5,0xdc9504c37eb92ca186fd],#[0xd6554130fbaa6a82617f,0xec85504c3fc90aa0986f,0xf97154130ff2a2a8261f,0xfe509504c3fdb8aa0987,0x7f95254130ff484a8261,0x1fe589504c3fd292a098,0x87f87254130ff4c4a826,0x61fe9c9504c3fcb92a09,0x987f97354130ff6e4a82,0x261fe551504c3fdb9aa0,0x987fb7454130ff2e8a8,0xa617f5cb504c3fca94a,0x42987ed52c8530dfaca9,0xa8a617f5d7214c37eb2e,0x2a29877d5254530ff2e0,0x8a8a617fdc9514c3bfa9,0xb2a2986fd6554530bfee,0xe5a8a61df54b514c37eb,0xa96c2985fd74d4530bfa,0xaec29261bfd4b614c37e,0xfb8aa4985ff7054930bf,0xdcc4a9261fb589524c2f,0x7eb2aa4986ff6254930f,0xdfaeca9261bfd95524c3,0x37f3b2a4985fd7654930,0xfdac5292617fdd9524c,0xc37fb2ca4986fd659493,0x30bfaed292617f5d6524,0x4c2feb8ea4985fd70d49,0x930bfaeda9261bfd8b52,0x24c37f32ac4986fd6558,0x8930dfacb312617fdd56],#[0x654c3fdb82ca985fd759,0x59530dfee0b2a617fdc9,0x9654c37fb8aca986fd71,0x259530dfae4b2a61bf1c,0xca654c37fb92ca986fe7,0x7154230ff2a2a84617f5,0x5c9508c3fca92a1187f9,0x97354230ff2a6a8461fe,0xe5d1508c3fcaa2a1187f,0x7d5254630ff2e0a8c61f,0xbf589518c3bfa92a3187,0x7df7354630bfee4a8c61,0x17fdd1518c37eb22a318,0x86fd7654630dfacaa8c6,0x61bf58b518c3bea96a31,0x186fd64d4630bfae5a8c,0xc61bf549618c2feba6a3,0x3186fd5458630dfea4b0,0x94617fdc5528c37faa2c,0xa5186fd6554a30bfee6a,0xa94617f5c7528c37ebb2,0xac5185fd73d4a30dfac7,0x4a9c61bfd4d628c37ea9,0x96a7186fd6554e30bfee,0xcaaa4617fdc5548c2feb,0xb8ea9186fd7655230dfa,0xae4b2c61bf5c5658c2fe,0xeba2cb186fd7359630df,0xfaa4a8aa17fdc1515437,0xffb92a2a86ff6254550e,0xdfec6a8aa1df54d51542,0x2feb94a2a86ff6294550],#[0xdfec928aa1df5525154,0x437eb10c2a85fd749455,0x50efaa830aa17f5c8615,0x542feba0c2a86fd64185,0x550dfac4b0aa1fedc161,0x15437fb12c2a86fe6258,0x8550efaa6b0aa17fdc96,0x615437eb1ac2a877f535,0x58550fb8e6b0aa1bfd8d,0x161542ffb9ac2a87df73,0x458550efea8b0aa1df55,0x91615437eb22c2a86fc6,0x7458550dfec8b0aa1bf9,0x5ca615437fb14c2a85ff,0xf5498550efaa930aa17f,0xfd92615437eb24c2a877,0xfd72d8550bfae930aa1b,0xbf58f61543bea9ec2a85,0x77d54d8550bfae7b0aa1,0x1bf993615437eb26c2a8,0x86fd72d8550bfae9b0aa,0xa1bf54f615437f396c2a,0xa86fd54d8550dfae7b0a,0xaa1bf5d3615437f2a6c2,0x6a85ff7054d50dfce9b0,0x9aa1df5c153542ffb8aa,0xa6a877d7154d50efee0a,0x29aa1df1d953543bfb8a,0x6a6a877d63d4d50bfae5,0xb1aa17f5c863543beb2,0x92c6a85ff7158d50ff6e,0xc8b1aa1bf59163542ffb],#[0xb94c6a85ff7458d50dfe,0xae5b1aa17f5c763542fe,0xeb8ec6a85fd74d8d50bf,0xfce5b1aa1bf5cb635437,0x7eb82c3a86fd74d8d50d,0xdfce4b0ea1bf5c961d43,0x37eba2c3a86fd7358750,0xdfae0b1ea1bf9d161d4,0x437eb92c7a86fd7158f5,0xdfae8b1ea1bf9c963d,0x370058008400b000b00,0x4047007f00e001540210,0xc8035406300b70150027,0x12b0238043407f00f301,0x40c1016f02c0053409d0,0xc007340e101af0340063,0x227043008240ff01eb03,0x413b026304b0091411b0,0xa80b04157029f05280a2,0x31706180bf417502df05,0x41b5035b06980ce41930,0xc00f441e103ab07200de,0x4370850106420303f307,0x4247047b08c011442210,0xd8136426504bf0960128,0x5470a68149428904ff09,0x42d305930b0015b42ad0,0x17c42f105d30b8816c,0x64f0c8818c4311060f0c,0x434f06870cf019a432f0,0x301c2437b06df0d981ac,0x75f0e981cf439907270e],#[0x43df07ab0f201df43b90,0x4820543fd07e70fb81f4,0x86710b8213441f082b10,0x445d08ab1130222443b0,0x38243447d08eb11b8233,0x96f12b8253449d092b12,0x44df09af133826344bf0,0x48284450109ef13b8272,0xa7f14e029745250a3714,0x456f0acb15702a945490,0x802cb458f0b0f16002bc,0xb9317082dc45b10b5316,0x45f50bd717882ec45d10,0xa831046170c1b18102fe,0xcab1930321463d0c6718,0x46850cf719c8334465f0,0xe035846a90d431a60347,0xdc71b6836846c70d7f1a,0x470b0e071bf037a46ed0,0xe039847290e431c68389,0xebf1d603a847490e7f1c,0x47850f031de83b747670,0xe03d947ab0f431e603c6,0xfbf1f583e747c70f7f1e,0x480f10031fe83f947e90,0xf041a482d104b207840b,0xcf2180429484b108720,0x4893111721f843b486d1,0x1045d48b31153228044d,0x1cb238846d48d3119723,0x4911120f23f847c48ef1,0x1849e49351257249048d],#[0x2db25904ae4955129b25,0x4999131f26184bf49771,0x284e149bb136726b04d1,0x3d727984ee49d713a327,0x4a13141b28084fd49f11,0x305224a39145f288850c,0x4f329c05334a5b14a729,0x4aa515372a505464a831,0x7856a4acb157b2ad0556,0x61b2c1057d4af115cf2b,0x4b2d164f2c8858d4b151,0x505a64b43167b2ce0599,0x6f32dc85b54b5f16b32d,0x4ba117332e405c54b831,0x285e14bbd176b2ec05d4,0x7db2f905ee4bd5179f2f,0x4c0b180b2ff85fc4bf31,0xd86174c29183f3060608,0x8af31406234c3f187730,0x4c7318db31a06314c5d1,0x7864b4c8f1913320863d,0x97f32e06594cad194f32,0x4ce919c733686684cc91,0x606894d0919ff33e8678,0xa7734d86974d271a3b34,0x4d631ab735486a54d411,0x506c64d851afb35d86b6,0xb6b36c06d44da31b3736,0x4dd51b9b37186e04dbb1,0x86fe4df71be337a06f0,0xc3b386070a4e0f1c1338,0x4e3b1c6b38c07154e211],#[0x9872f4e571ca33920720,0xd0b3a0073c4e751cdb39,0x4ea31d3b3a6874a4e8d1,0x387634ebf1d733ac8755,0xddb3b9876e4ed51da73b,0x4f0d1e0b3c0077d4ef51,0xe07984f291e433c7078a,0xeab3d407a44f431e7f3c,0x4f771edf3d987b14f5d1,0x707cb4f911f173e107bd,0xf6b3ec07d64fa51f433e,0x4fd31f9b3f207e14fbd1,0xd07f74feb1fcb3f787ed,0x2b40388034fff1ff33f,0x5033205b40a8811501d2,0x588275047208340f081b,0xeb41c8835506320bb41,0x509921234228841507d2,0xf885c50b121574298850,0x1c7437086a50cd218b42,0x510521ff43e887950eb2,0xc0893511f22334448885,0x29f45188a0513b226b44,0x517722df45a08b051572,0x788cc5191231746108bf,0x37746d88d851ab234b46,0x51d1239747208e251bf2,0xe88fb51f123cf47808ed,0x43b4860907520723ff47,0x5233245b48a891352212,0x509275249248b48f891c,0x4d3499092f525b24af49],#[0x528b250749f893c52712,0xd095652a5253f4a6094a,0x59b4b1895f52bd25774a,0x52eb25cb4b8096d52d52,0x40985530325fb4be0979,0x64f4c9098f5319262b4c,0x533f26774ce0998532d2,0x909af535926ab4d389a2,0x7074df09ba537126d74d,0x53a5273b4e609c753872,0x289e253bd27734ed09d5,0x7d74f989ef53d727a34f,0x540f280f50009fd53f32,0xe8a19542b28475078a0b,0x8b75158a275449288350,0x547f28f351c8a3554632,0xb0a51549f292b5238a43,0x99b5318a5f54b7296352,0x54ef29cf5390a6d54d52,0x48a8755072a0353f0a7b,0xa6354b0a94551d2a3354,0x554f2a935508a9e55372,0xc8ab655672ac75570aaa,0xb235628ac1557d2aef55,0x55b12b5b5698acf55992,0x48ae655c72b8356f0ada,0xbdf57a0af255df2bb357,0x56112c135810afe55f52,0xe8b19562b2c4b5878b0c,0xcab5940b2556472c7f58,0x56792ce759b0b31565b2,0x70b4c56932d175a18b40],#[0xd7b5ad8b5756a92d475a,0x210130848402b6556c52,0x586084c4021310084c40,0x2505141018505448404a,0x31512110c14484430300,0xc9448443111208544448,0x14110c14504432511120,0x50443141108545044315,0x50c48445432514110c94,0x11101020144840414111,0x6c31312101c4c40307a4,0xc40316a4070610484020,0x104048207241110101c4,0x42210101c40216430206,0x84031310120c4840216a,0x102048403a224100c540,0x46210104840286c51211,0x218100848445040416a,0x5a91884041824100c584,0x5100848402232b128610,0x21613100c541c904041,0x5804184c40d12100c4c4,0x30e00184c380862f1310,0x4021014885440380061,0x1404029188189461615,0x150d88544036200a4251,0x151010201c181446206,0x1825100c918a00184620,0x56944030510085494403,0x4149064184861524100c,0x34181430406151225109,0x120814484031524100c],#[0x4072415101014404831,0x40413c52b10105888944,0x440484c510120c441410,0x1c90444c507241110201,0x9490444170724111314,0x11104844205072411130,0x512110c1448443c50724,0x84432512110c94484432,0x9448443c025241110944,0x3170c100c222c3001310,0x84432512110c48442040,0x4c94424a201152514144,0x4161504020325185800,0x40804030706144414104,0x84030512100c5e184844,0x2100c94402051008100,0x52425101010084060404,0x840616152510111a9421,0x41105041010585494100,0x18582a5860994100840,0x5418100c086040210161,0x40210104010f0b100c58,0x21814100c1008403a50,0x5434504841514100c504,0x20c270454484140d120c,0x15140c60544050401151,0x4842415100c405450310,0x4485031415120c645450,0xe9420484040016150c5,0x130c1e9690404241610,0x442410150c5854403a51,0x54402a510130c1e90429],#[0x540c0448405a3811210,0x12100454483030117121,0x210100c0454484a381a5,0x6510101d945040408651,0x54114121194484030714,0x65634112110451944846,0x465148210118d0449944,0x4c36514130c51960840,0x1054504030514100d945,0x50c08605040415021410,0x14151010509440314101,0x4830514120c480450302,0x86450415011412105450,0x50944830114121510044,0x100c04485442514120c,0x11100450485440214151,0x3131296910044405a440,0xca540111046182a5404,0x415a4401112951100444,0x44044016111054110044,0x4c4a440a511129102944,0x44440c40a51111010e94,0x1054443a415110d11029,0xc110d94484436512110c,0x80651111959200444650,0x381651211960e0448464,0x84431512110c14484438,0xe9448443a512110c544,0x512110c5448443151211,0x84430415110d94484436,0x90544431564801110544,0x4100c54484431512110d],#[0x15021410145054403251,0x54405031004405450318,0x1440504140300102514,0x8005450315102514100,0x31525140c64945030915,0x945041510140c544050,0x8405840b05121010604,0x1860944031525100c10,0xc144450318152504021,0x225110c4894443021410,0x44430401170c48944431,0x180c549430512110c489,0x80850403181504020125,0x2100c08406050418140,0x4100c605424100408604,0x44841510081c54403021,0x5440318151410101a0c5,0xc4854503191512141050,0xa2100c30605431215140,0x58404150402101218105,0x1008544041510081008,0x10540c04484c305a1121,0x512100c5448303011712,0x15141010605040303011,0x4831415100c505440318,0x404504841514120c1450,0xc485450301121914105,0x1510045054484142512,0x1512100c044854404021,0x38512100c4a144030114,0x544031540160e144840,0xc51014105840215100b1],#[0x231440415100b144020b,0xc100c1c545c510120c34,0x4021010544021510085,0x18106454300c0804615,0x180c6014544050515c44,0x51415100c54405030540,0x19150514106054145040,0x408211514102c4054504,0x4503c510120c2c405450,0x14484030b10151410618,0x318541008404a115140f,0x54080450417150701040,0x1008584040403001610,0x10100840604030200161,0x50c08045060404010018,0x420340150c541c202401,0x7060854242150708542,0x590e000840706081c182,0x50706081c1821607060c,0x34307100c4c413cbc44,0x8840309410b07110c1c4,0x60c5e048818422060858,0xc81060c920418322810,0xc081822522100c94402,0x438112085c182251002,0x205042440906110c2605,0x3070609041c20614089,0x60c183020c060891040,0x6438004103090183a40c,0x4901822524060c640421,0x43818004101200183060,0x8904022410086600183],#[0x14305800890182062f,0x9101a0030580060c22,0x844415060c3416003068,0x81504215100858550c1,0x5248110101a058838106,0x406248162101a044832,0x18958831706089604189,0x56210944020807250610,0x8510085c1e1504406852,0x904032581062f1104542,0x1508604021825100c94,0x840625240c6418909441,0x544042425100c3094341,0x49104319850c41109490,0x240c1c5c1832400150e1,0x21707060e00142031906,0xb086418280050d0d1018,0xe0008317220a002c2810,0x94110c400851722060c0,0x708201c5c1842502100c,0x88c183100e084c482080,0xc482060438182430e083,0x20608110e0008422044,0x170c201c20807085c182,0x31701085c1d041841307,0xd040030140220d001888,0x622050c1810807060c5,0xc5c1830623170c405c2,0x184c3801708481131209,0x2090c180831713060c5c,0x21724230c19110c3060,0x4306021020181c300190],#[0x1c21722060c941808325,0x522060c0058201150820,0x1821106a50c44144030,0x60c144c1838105120c6,0x1c4c21204588c5431913,0x807250c148821025220c,0xc2014484041004444020,0x8050706101411210050,0x86040217250840942c3,0xc5c1831004944021806,0x402a523860c588821006,0x3100b0840082400b0854,0x20858544031004580900,0x10800202070908241172,0xc31715800c2458183054,0xc542428018150c54301,0x8201450808301192425,0xa04342810a080021508,0x60908005838116070c15,0xc11640250c4e140030c1,0x810c0c5c0028107a50c5,0x4830705060c4c0064305,0x70008245c21700085c54,0x80058307150809005431,0x70e08600030705090e0,0x31815090c25941c31809,0x8542420340150c610800,0x431300190c9100217000,0x104c00583150c0811005,0x2150908541c216091506,0xc580c1830403c0085430,0x430c0d02845440013160],#[0x31300190c18329431506,0x80c54183150709028854,0x43258008260214315070,0x1008260c209830860542,0x1404260c215045840216,0x82c1c942440925085c1,0x70785141026149430925,0x5430c542421506150c21,0x190c8543106494503001,0x810804245c2170454502,0x431610085c2420102080,0x1609085824281050a048,0x42420917090811004401,0x70844142430921170c6,0x241c41741090c5c0c20b,0x9020824881430904942c,0x8430944410c24940830,0x494083090b070c0005c9,0xb0708245c20925020c2,0x888142431609080c542,0x1c943052208948821815,0x88209045c9422502082c,0x8118100840115090814,0x885c202040811410020c,0x704550c1831615438010,0x85460243032508301c21,0x48431615100c30119250,0x42001058181c381050a0,0x20c83160c0f0021603,0x20454402830140151058,0x81430300170818141c34,0x5060c5c1c1830019081],#[0x40030c05060c6418207,0x4070c09005431700085d,0x20705090c0c58003154,0xc150c1c31843070c006,0x200170c6100943852200,0xc543020440150c640022,0xc070c550c1830316000,0x5003150c08605424315,0x61055002032142810c56,0x1523400a104010742211,0xd009200308070900542,0xd85800c1834303244015,0xe1410524804010885420,0x22210858541830124150,0x45884883084008402c2,0x8d005451004585440310,0x21610088e18210042914,0x409143c4031614085018,0x89030d15140c843c2211,0x2402408208821204581,0xd240c90542240108549,0x20515100c5c8854306,0xd0416005431815100c2a,0x508085421924150e0010,0x60054315100854402101,0xd0031504105428015083,0x400c5461003181008560,0x5431805100d002820518,0x4086054243070b090060,0x21815090c2c88543191,0xf15085011823220c604,0x105854403220b0860502],#[0x51008645450317240715,0xc5450223150808545031,0x840316045c5821516100,0x18090c40582191608605,0x6021018170c605840315,0x1918140d00]]
set_option maxRecDepth 16000 in
def g243H7 := limbs80 #[#[0x80040210001041,0x8000208400000088000a,0x4d824004800104000,0xc9601249000404088018,0x10082010002000000002,0x4800020800028000220,0x80000082c0010404001,0x80010000000080002080,0x64140006100000100020,0x2040008401201018008,0x402830494002000006,0x40120820800120200,0x8000000200110742000,0x10000080080000c10002,0x1006008108800160309,0x91821402301242082,0x8008080c01000a000200,0x4000000920404220108,0x1a032800c0000,0x804f00,0x0,0x0,0x0,0x0,0x0,0x0,0x180000000002223c0000,0xb,0x601270000000,0x0,0x24f0,0x7600001020f800000000],#[0xf06,0x6280000000005a12700,0x141be800003,0xa705c0000340fe00000,0xc27b000001a5c00000,0x68121208e40000000,0x0,0x0,0xc80000f00ea000000000,0x2e5b,0x0,0xf03cc000000,0x0,0x0,0x781d3706d6000,0xc1ed800000000000,0x8331000000,0x843f000000000000000,0x181f8000000000,0x0,0x1016a00,0x12d400002d0d3800000,0x236800000000000000,0x0,0x0,0x82d80000000000000000,0x5,0x20000000000000000000,0x977e98103b051,0xc027c00,0x0,0x0],#[0xeed0ba80000000000000,0x120a,0x0,0x8cd1c000000000000000,0x521f3203f3,0xe90000,0x40d000000000,0x0,0x0,0x1c43c00000,0x5075000001415a0000,0x3d18a800,0x162670000000,0x927b000000000000000,0x10536,0xd8000000000000000000,0x413a5000000000041,0x0,0x40000000000000000000,0x10a,0x0,0x6718200,0x0,0x0,0x0,0x0,0x160813c12c8000000,0x783fa0,0x200000e0a9c00001035f,0x1003,0x0,0x182e7a05d20c3600],#[0x0,0x0,0x4537000000000,0x101da000000000000,0x0,0x0,0x14e31,0x77b404900000507c4000,0x35876d036800000c4,0x0,0x0,0x2366,0x0,0x0,0x5d14000000,0x0,0x0,0x6d00000000000000000,0x20,0x348cc0,0x305d0000000000,0xc3800000000000000000,0x785f00000398,0x41278000000000000000,0x80000000000000000003,0x18082,0x250cae013700000000,0x212660000000,0x0,0x64062c00000000050802,0x35c0300000a041,0x0],#[0x4217800003889000,0x1016b000000,0x3844c381bd,0x0,0x10091000,0x0,0x9718a0000000000,0x180000e074e00002811f,0x37b803d28f07f819,0x0,0x0,0x80228,0x2000e000000000,0x15400000000000000000,0x18104800000000104,0x4088f000000,0x0,0x40fd000000000,0x2cc9f80000000,0x16ac9000000000000,0x0,0x0,0x5c00001a465d84060000,0x201,0x888500,0x0,0x580a700000000000000,0x198000000001e4180000,0x101,0x4805300000000000,0x40000000000000000000,0xc21800000000004011],#[0x0,0x101c00001106d0000000,0x76018e,0x1814fd816f00000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x943fc0000000000,0x38349501e4000000000,0x2537200000000,0x407fa0000000,0xeecf80,0xd49a800000000000000,0x0,0x7ac41828000000000000,0x1028a424f84a,0x200fa800009025a0,0x0,0x0,0x0,0x100b38418d0000000,0x0,0x40f34000000000,0x0,0x0,0x0,0x0],#[0x0,0x0,0x52938000000000000,0xb1112629100,0x610b500000720a200000,0x240d8782f000359e02a,0x0,0x0,0x0,0x0,0x0,0x20800000000000000000,0xb6,0x0,0x2893900000,0x9a021240000000000000,0x410,0xf01da00000000000,0x4115700000000034cd18,0x0,0x0,0x607440000000,0x0,0x0,0x20000000000000000000,0x12398ec4,0x1c106800000000000,0x805f80,0x80000000000000000000,0x120b98000000000c06d,0x50600000000000285000,0x101128000060],#[0x0,0xc0bd64425283fb,0x5079c0000000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x701d1000000000,0xfbc00000000000000000,0xe0,0x1c1f600000000000,0x180d885da30000000000,0x0,0x0,0x0,0x0,0xb00000000000000483ab,0xf3000000000000004226,0x603dc000015499b80,0x40ce8000000,0x34c568,0x0,0x0,0x0,0x4071c000000,0x0,0x0,0x0],#[0xf049a00,0x48397000000,0xe000000000302f9f06cc,0x6e00000000000000204f,0x48330721,0x0,0x0,0x0,0x0,0x0,0x2001520f30000000,0x0,0x40000000000000000000,0xbe800000000000000082,0x240,0x1056e000000,0x60e80,0x0,0x8a800000000000000000,0x40,0x0,0x1c0b20000000000,0x582780000,0x1ca1d40000382ab000,0x33900000000000000000,0xa,0x20d4c000000000,0x0,0x1206340000000,0x1290000000000000000,0x68bee0000000000c16ee,0x40253c20ce000000000],#[0x0,0xd22380000000,0x0,0x0,0x0,0x241e9582e500000000,0x100e7000000000000,0x304d300000000000,0x1994100000,0x0,0x65200003d01e00000000,0xa0,0x205e8000000000000000,0x0,0x0,0x0,0x0,0x0,0x98000000000000000000,0x1c2126895,0x5e8000000001e452400,0x89238000094556000004,0xcc118798a90000000000,0x1403a,0x3ab40860000000000000,0x120,0x0,0x2813af30f700000,0xeedc00000000000000,0x1445ec89283a9bb000,0x15c5a8000000,0x0],#[0x1486280000,0x0,0x160a4000,0x0,0x28100000000000000000,0xf8000000000000000000,0xb5703010000000003ddb,0x141,0x418800000000000c40c0,0x14870800006044400003,0xf2e0d780000000000000,0x1640,0x0,0x0,0x0,0x1700db85d9d000000000,0x622,0x1086c00,0x383130,0x1407a00000,0x900e0c0a7015560000,0x0,0x1403f0000000,0x0,0xc8000000000a40000000,0x711fa0000000002007,0xe13260000000,0x0,0x5026a0000000000,0x402d1000000449,0x0,0x5c187083f0000000],#[0x0,0xc0000000000000000000,0x7c00000000000000203e,0x3c0a48925ae08,0x1c1920000000,0x0,0x0,0x1a110000000000,0x0,0x980000000000000000,0x3,0x0,0x480000c208400000000,0x4028b000000000102,0x0,0x200800000,0x0,0x4cc283004a000,0x1b8c30000000,0x0,0x40ef000002119907196,0x0,0x77600000000000000000,0xe00d800004013d20,0x0,0x0,0x15c578000,0x0,0x2000c00000000000,0x0,0x0,0xe42cc000],#[0x0,0x209880,0xc00000000000000823a8,0x12a1d,0x0,0x0,0xe4218000000000000000,0x6885b00001,0x0,0x40c3dc86700000000,0x55e18000000,0x2232440099c210000000,0x0,0x0,0x140023808f000,0x702be00000000000,0x0,0xa0000000000000000000,0xcf0000000000021210c3,0x2c4,0x58c0d00000000000,0x48124938bcc088ac0708,0x381f01bb3400001c048,0x5067c000,0x0,0x0,0x0,0x0,0x0,0x100d5800000000000,0xa0664000000000000000,0x0],#[0x3c0e20000,0x101c1800,0x0,0x0,0x3c0c9,0x1086a00000000,0x0,0x7917600000000000,0x290360000000000,0xe00dc0000,0x0,0x0,0x401a6000000,0x2200c00000000000000,0x30a044c0000000000000,0x603e8502,0x6ce0000000000000000,0x4,0x0,0xd10cc0417388c68000,0xb2100000e0f600000000,0x14ed2800003b,0x1803c0,0x0,0x0,0x1c45c400,0x0,0x0,0xc0da80000000000000,0x0,0xed000000000000000000,0x4],#[0x0,0x0,0xa4250000000000000,0x0,0x34058800000,0x0,0x0,0x0,0x0,0x3062a08328,0x3209800003485b,0x0,0x2452800,0x0,0x80000000000000000000,0x244b100000320df8020,0x244b98000000000000,0x1591b00310000000,0x0,0x0,0x1a4347a5bf4810f0000,0x0,0x0,0x1e03f80000000000,0x74147,0x1a039400000000,0x20e7c0000000,0x0,0x0,0x0,0x0,0x257800],#[0x482c500000000000,0x5903e00000a47fc,0x0,0x0,0x0,0xe49f8000000000000000,0x1,0x0,0x0,0x142088000000,0x60bbc8043800000,0x0,0x900001240ec00000000,0x1c483000003bb,0x405000,0x0,0x0,0x38193304dd60d0c000,0x6004f000000000000,0xe0c0842b052c000000,0x3c133800000000000002,0x759e1280000608880000,0xb04e8f0f,0x3045800,0x3d09200000000000,0x2040500000,0x0,0xa800000000000000000,0x40,0x0,0x30000000000000030897,0x81c],#[0x3e08b000,0x0,0x0,0x1e04980000,0x108200000000,0x60132193000000000000,0x5d850000000000000028,0x1,0x39054000000000,0x0,0x0,0x58071000000,0x1e86990037c816c00000,0x12000000000000000000,0x4013ac01,0x0,0x0,0x0,0xff00001e219400000000,0xc0500dda12b0,0x38260000000000000000,0x5,0x0,0x0,0x0,0x0,0x0,0x394fd80000000000000,0x0,0x0,0x69261000000,0x0],#[0x1809780000000000000,0x20980000000000000,0x0,0x0,0x0,0x0,0xc400000000000000000,0x71,0x0,0x307f0e01300000,0x0,0x6442a0000000,0xb027dc42fc0,0x20190707ac00000,0x0,0xce082b4036400000000,0x101,0x2c19400000000000,0x1403a0000000000,0x0,0x0,0x1c10d800000000000,0x600090,0x0,0x80c0800000000,0x42c446a2000000000000,0x58,0x248388,0x124d400001410f,0x1d2d108b402d4000,0x680c6f11100000000,0x0],#[0x0,0x3c0067825b000000000,0xe40000582a600000000,0x628400000000000001c0,0x1a,0x20000300ca0000000000,0x4768,0x7a00000000021186000,0x54,0x0,0x100001e0784000000000,0xfa00000000000000583c,0x140cb7c42a080,0x605c800000000000,0x21177000000000000000,0x10422000000000,0x0,0x3012c0000000,0x0,0x7000d000000000000880,0xe040,0x80e50000000000000,0x1d0c880000a048000,0x0,0x1621a000000000000000,0x140e600000000000000,0x0,0x4180000000000022100,0x8,0x0,0x0,0x0],#[0x81500000080674000000,0x941f,0x0,0x2812e0000000000000,0x0,0x0,0x6076c00000,0x0,0x0,0x0,0x206180,0xa0000000000000000000,0x401f04063,0x5a00000000000000000,0x1e05c800000000090,0x303770,0x0,0x310aa0000000000000,0x0,0x3ccea80,0xc808f000000000000000,0x5243000001104c,0x1402b0000,0x783ed000000000000,0xdd2580000101ba000000,0x1,0x8508601c6000000000,0x80566000,0x0,0x922840,0x0,0x0],#[0xa2000000000703b4000,0x40,0x0,0xf300000000000000000,0x3c0428000,0x42db0540000000000000,0x20,0x510c80000000000,0x0,0x0,0x782fa000000000000,0x84a58000000000000000,0x804d9,0x0,0x0,0x67882109001f0000000,0x384a700000000018,0x0,0xe02cc0000000000000,0x0,0x4836d00,0x0,0x3047920aa0000000000,0x180ee0000,0xb03c0000000000000,0x0,0x0,0x7895c00000000000000,0x0,0x0,0x1006d80,0x7ca4e0000000000],#[0x2c20780000000000000,0x0,0x0,0x0,0x0,0x530ef5040,0x0,0x0,0x0,0x0,0x0,0xc24141a2e3080000000,0x49,0x0,0x661400000,0x2f800000000180f84000,0xb077a0000048,0x804700,0x401310000000000,0x7146e0000,0x201c730578000,0x0,0x80b6000000,0x77c,0x2000000011d702c00000,0xc08,0x4022700,0x706de000000000000000,0x0,0x0,0x0,0x0],#[0x38348000000000000000,0x25dc0,0x0,0x0,0x806800000000000,0x0,0x20077000000000,0x0,0x0,0x0,0x43400000000000000,0x0,0x0,0x4a9000000000000,0x13298000000000000000,0x0,0x0,0x2a00000000000000000,0x30,0x80552000018ca00,0x0,0x691fe000004ecb4000,0xa580000000000000000,0x20,0x0,0x0,0x3b29dec300f600000000,0x3c0578000000000e4,0x0,0x1405d8000000000d4098,0x20ad80000000000000,0x30c00000000000000000],#[0x3ccf3911d570,0x1810f40000000000,0x0,0x80088000,0x811e800,0x0,0x38863000018094800000,0x0,0x68402e30b600000000,0x3293ba03a00000000,0x1e46c40,0x0,0x80b000000000,0x910be000,0x0,0x0,0x0,0xa6609a514fe5187d0000,0x201a8b07,0x28afc00000000000,0x16629c0000000000,0x0,0x8200001c035601fa0000,0x290,0x580580,0xb9a0300001208b800000,0x2b0fc00000000020062,0x0,0x0,0x0,0xc0000000002029c00000,0x5f0850800005002a0269],#[0x3c0fa319dcd062f424,0x0,0x849dc000000000000000,0x1,0x0,0x19800000000000000000,0x7720000000000000080,0x7,0x3061a00b24000000000,0x0,0x0,0x361ea000010ce180,0xdc630,0xc80000955a8000000000,0xd40c0410acc41,0x10181000000000000,0x61ed8000000000000000,0x3,0x60951000000000,0x0,0xc42c0000000004053000,0x10,0x2c11a8000000000,0x0,0x1303f0000000000000,0x0,0x8380000000005904a0,0xf107be00000000000000,0xc07fc0000000006821,0x95f805d800,0x0,0x40895000000000000000],#[0x0,0x0,0x0,0x802d8000000000000000,0x0,0x144e1,0xd8c00000000000000000,0x7a8390000046,0x0,0x0,0x5200000000000000,0x15cba00000000,0xe0d3442090000000,0x0,0x1410980000,0x0,0x0,0x0,0x10963000000000000000,0x0,0xa0892d00000000000000,0x1070000000001a0714c1,0xad0a001e00003c,0x1041d000000000000000,0xfc000000000000000000,0x288a380000a0865a04,0x9fb010b00000e05fa00,0x200e6d0256000014,0xf200c,0x7258,0x30600000000000000000,0x2807de832536],#[0x0,0x0,0x2300000000000,0x0,0x972e000000000000,0x1005c0000000000,0x0,0x0,0x40b2000,0x40bd8000000001410280,0x2,0x1033e0000,0xa02a6000,0x0,0x3b5f000000,0x0,0x19202460ce8000000000,0x408,0x0,0x2189f0,0x4818c,0x207cc0000000000000,0x4ad000,0x2116600,0x1c1680,0x0,0x0,0x0,0x0,0x0,0x40f9800006147c0000,0x0],#[0x0,0x0,0x0,0xa03c40000000000000,0x0,0x40eb315a58000000,0x14022000000842e0,0x1ce328000030029,0x0,0x1da8000,0x0,0x0,0x18000000000840540000,0x291c50000000003016,0x17600000000000000000,0x10,0x0,0x0,0xd1c00000000000000000,0x481e300000e0,0x0,0x1649b800000000000000,0x0,0x0,0x0,0x3c217800000,0x0,0x0,0x0,0x0,0x1206cc00000,0x0],#[0x0,0x0,0x20b080,0x108c0a01330000000000,0x14114bbc27800060000,0x3c10e0000087784000,0x2dda4000000000000,0x0,0xe0482c14680000e087e,0x0,0x0,0x2184000,0x0,0x0,0x0,0x0,0x83bfc043200000000000,0x6,0x90000000000000000000,0x101c,0x7b40000000,0x80a28000000000649540,0x381b91024a00000c411b,0x100409126f20a9,0x0,0xb7d012a00000e042a00,0xc,0xb0352,0x0,0x0,0x38c228000000,0x0],#[0x922d600000000000000,0xd6000000000000000000,0x701038a7c7dd91299,0x766c00000000000,0x5002f000000000000000,0x282da00000000000000,0x1316c00001c01ac000,0x0,0x0,0x401e50000000000,0x0,0x0,0x20473000000000000,0x404e2813c80000000000,0x0,0x0,0x40cb00000000,0x0,0x19545982d40,0x802d00000080d380000,0x0,0xf00d2000000000000,0x0,0x0,0x429ef961cc000000000,0x0,0x0,0x0,0x0,0x0,0xb6d81a34810e00000000,0x298a20000060],#[0x0,0x0,0x1603a00000782470000,0xe00000000000000000,0xc05b400000000082,0x0,0x49a02,0x35000000000000000000,0x27df0526000000000301,0x3047042cfc44a908,0x0,0x0,0x518460000000000000,0x716920000000,0x0,0x206ea00000,0x4c00000000001099200d,0x2074c370000000001a03,0x24000006825f807a0a4,0x8829183eba24d76,0x400000000020434f7174,0x2483e00000f06a,0x0,0x0,0xa030e000000000000000,0x0,0x0,0x3610000000000017f000,0x60974000028,0x28428000000000000000,0x0,0x44340000],#[0x310b40000000,0x0,0x40000000000000000000,0x1e21f,0x205bc000,0x0,0x7b102000000,0xe00000000000000722dc,0xc400000000000000494a,0x210,0x12e0000000000000000,0x8,0x0,0x0,0x0,0x0,0x5043b000000000000000,0x90000000000000000000,0x320a600002c03,0x0,0xa055a000000,0x0,0x7bb68000000000,0x0,0xc132800000000000,0x1416200000000000,0xe8222800000000000000,0x90638000000000704e,0x16a00000000000000000,0x72,0x841100000000002099f0,0x0],#[0x0,0x8230b6e0bc0000000,0x0,0x8841e0000100d6c00000,0x115ae02ebc0eb,0x0,0xc10000000000c87ac00,0x28,0x0,0x10c44700000000000000,0xfa400000000000001846,0x20,0xec3b80121e818a310680,0x1089e,0x1dc5f800000000,0x18156000,0x2010700,0x2000e8b10c0,0x0,0xc0bc400000000,0x0,0x0,0x80000f17cd6200000000,0x100cd0000000001c0fe,0x0,0x0,0x0,0x0,0x2c000000000000000000,0x453d5603,0x383950000000,0x0],#[0xa087689290004400000,0xe4c0b5c0000000000000,0x3fa00000000000000920,0x82,0xc0598000000000000000,0x700d9,0x0,0x1843f40000000,0xa448400000000000,0x80000000000000000000,0xe0a5c0024,0x0,0x2bb7ef03100000000,0x0,0x20ce3800000000000000,0x0,0x401b1e5446000,0x0,0x254f700000000000,0x14091000001815500000,0x0,0x5c200000000000000000,0xa0,0x0,0x0,0x0,0x0,0x0,0x208c18,0xc03580000,0x0,0x0],#[0x0,0x4075420ac8,0x28000000000000000000,0x1804,0x0,0x201e000000000000,0xc8d5000000000000000,0x0,0x0,0x5dc0000000000000000,0xc929c1035f,0xb0000000000000000000,0x4038,0xd05b2000000000000,0x0,0x340780,0x1a65440000,0x0,0xe30ae0000000,0x904c1815700000000000,0xb34608104d,0x3d000000000,0x2419f80000305fe000,0x0,0x0,0x20354,0x0,0x2eea86ac000000000000,0xff00da400000000030,0x146db40000000008,0x0,0x0],#[0x0,0x1140000084258000000,0x38104000000000000007,0x0,0xcf5084d4040c00000000,0x1c1,0x41c2a82d200000000000,0x240b9800002070f64e5e,0x0,0x244388000000000000,0x28143800000000000,0xc06e0000000000000000,0xa062b,0x0,0x20e68000000000000,0x0,0x0,0x0,0xb07660000000000000,0x0,0x0,0xc03a130830c2d0000000,0x2c20e,0x0,0x0,0x0,0x1c82180000420b200000,0x0,0x1230000000000000,0x2c0f43814d4315800,0x0,0xc37e911000000],#[0x0,0x700c7000,0x0,0x79fc0f6800000,0x4046e00000086080000,0x1f0000022cf400000000,0xb0816000000000501,0x0,0x61854000000000000000,0x0,0x0,0x0,0x38255307fe000000,0x0,0x1c0dc,0x2c000004821a00000000,0x108f01b880000106b0a4,0x2d109683f5000008,0x0,0x7ba290000,0x41ea00000000,0x0,0xc049080a440000000000,0x12086c000000000,0x58000000000000000000,0xe215a00000402ee92,0x11b27015c00000000000,0x1200a20206a,0x0,0x0,0x0,0x0],#[0x1042e0000000000c421c,0x23c24000000000,0xed40000702f700000000,0xc21c03f0000000001e0,0xb05208,0x667a800000000000000,0x0,0x0,0x896500,0x194f6800000,0xb0000000001800b00000,0x4222,0xcf00000000000000000,0x30,0x800002036480d6400000,0x10000000000000009020,0xb080000000004009320a,0x2c4,0x1806ec0,0x1a0614,0x203ae000000000,0x240008000000000000,0x8d480000000009307200,0x444174,0x0,0x0,0x0,0x7138091590d7b001800,0x3a0ba800006,0x3ba87,0x0,0x12a7c80000000],#[0x0,0x0,0x1621400000,0x0,0x6f91870000000000000,0x3c,0x0,0x0,0x0,0x0,0x3014700000000000,0xc00001c2130000000000,0x3802bc232,0x0,0x2482d0000000,0x80083ac3f80000000000,0x0,0x8005440000000000000,0x14e0a80000084,0xa224c00000000000,0x282a1a51a68007000000,0x68000000000000001db7,0x3c13,0x0,0x613d500000000000,0x582660000000000,0xc097,0x0,0x0,0x2d87500000000000,0x0,0x0],#[0x230000000000000,0x0,0x14152800000,0x0,0x9000000000000000000,0xe80d40000331,0xe0804000000,0x0,0x0,0xba800000000000000000,0x4,0x6108900000000000,0x0,0x0,0x1507e3aaaee05d4000,0x38052800000000000,0x0,0x70002c00000000000000,0xb225,0x2d400000000000000000,0x18222e4cf1382d587,0x1a41840000000000,0x199a2,0x0,0xcc3e00000000,0x19eb00001c0688000000,0x4,0x4b3c0000,0x0,0x0,0x0,0xe020c],#[0x0,0x2c9319832ea24fa000,0x699e40000000,0x0,0x0,0x0,0x259c0b2c000000000000,0xe0,0xe474c6675c0000000000,0xa7021c0b1c000038a73,0xd10540000000000000,0x0,0x0,0x3420b8,0x3099d00000000000000,0x0,0xc4f00000102bd4093000,0xa02b2e45000,0x0,0x3d49b00000000000000,0x0,0x0,0xa00660,0x0,0x4a10f0000,0x180c700000000,0x5274a0821d4f48000000,0x9,0x0,0x1c09e9c1888000,0x4300000000000000000,0x78],#[0x0,0x0,0x4e80000000014c5ac000,0x2c4,0x1e01380,0x162110,0x3886e000000000,0x4f400000000000000000,0x12200a9000000000126,0x140710000000001e,0x0,0x0,0x0,0x0,0x0,0x7522b000000000000000,0x3400001c0ae000007820,0x82,0x0,0xb03d90000064e8800000,0x6905d000000000084c4,0x0,0x0,0xc158000003016e000000,0x4117d0000000001,0x0,0x924c4000,0x262d400,0x0,0x0,0x0,0x164005d59100000000],#[0x0,0xa0f218138800000,0xa07f200000000000000,0x5c0000060fdc00000000,0x8c3e6043e183,0x0,0xa04840000000000,0x0,0x1a07bc000,0x0,0x0,0x0,0x50805000000000,0xc7c00000000000000000,0xa0,0x0,0x92464000000000000000,0x415f029,0x2a272000,0x0,0x0,0xa007e00000000000000,0x6f000004679544288000,0xf21f0000000000002,0x0,0x0,0x8000000000020ac40000,0x41c,0x0,0x0,0x690990000000000,0x50046000000000],#[0x0,0x0,0x0,0x0,0x180594000000000610c,0x0,0x7030700,0xc024a000000000000000,0xa0000000000000000000,0x42070e05128147c02b,0x11040774000000000000,0x30,0x1801b000000000000000,0x18000000000000000000,0x2807,0x0,0x50306f0704000000,0x0,0x0,0x0,0xc4480000000000000000,0xe,0x10004,0xae000000000000000000,0x142cf0000000000b01,0x0,0xc935c000000000000000,0xbe052a08444000000000,0x101d4e80d,0x0,0x0,0x2420a0],#[0xb12b6000000000,0xa61ec00000000,0x22180000000000000000,0x201368,0x1a210c,0x0,0x280ab00000000,0x1441b800000000000,0x802fc0000400de000000,0x903d6,0x0,0x0,0x20de400000000000,0xf0722000000000202800,0xe22286e28b40000003f3,0x1529300000529a,0x221a000000000000,0x13d7801c000000000000,0x2012f000000000000000,0x0,0x6029e0000000000000,0xc20200000000,0x0,0x40000282511432c00000,0xa07e2641a,0x1c8be7043836226000,0xab440000000000000000,0x904a02,0x0,0x602f80000,0x1d200000000,0x0],#[0x1c15f681bc0,0x8007,0x0,0x10300000000000000000,0x304c628,0x60e7648200,0x0,0x0,0x0,0x60406000000,0x0,0x0,0x0,0x0,0x0,0x1844b0000000000,0x0,0x7831e000,0x3340039800000000000,0x3010a00000b,0x0,0x0,0x0,0x2400680,0x12050400000,0x621d2000000000,0x0,0x16050800,0x0,0x1848e000000000000000,0x34000000000000000000,0x80e],#[0xec80000000000000000,0x1a,0x2833c00000,0x0,0x0,0x1420000000000000000,0x20887e,0x30000000000000000000,0x4036,0x272df803bc0000000,0x0,0x103c9000000000000000,0x2053400001c435,0xb7000000000000000000,0x202ed000000000180,0x0,0x692380000000000,0x0,0x0,0xf235600,0x0,0x140c1000000000000000,0x8016,0x82c00000000000000000,0x8197c384130,0x0,0x0,0x0,0x0,0x0,0x0,0x20035622d8000000000],#[0xa577a00000000,0x0,0x41420000000000000000,0xc00001b8bd0000000000,0x30299000016820,0x0,0x0,0x0,0x90762,0x0,0x401380000000,0x242270000000,0x330e40000100a5000000,0x0,0x46000000000000000000,0x301,0x1e028b821200,0x0,0x0,0x20a04000,0x0,0x0,0x0,0x0,0x0,0xe031e00,0x803e40,0x109928000000000,0x6b16e0000,0x4c6e0418000000000000,0x50,0x211f30],#[0xc80100000,0x99000000000311458000,0x300,0x1830000000000000000,0x340fc0,0x6009ca0374000000000,0x0,0x0,0x0,0x0,0x0,0x0,0x80370000000,0x0,0x0,0x0,0x37e00000000000000000,0x3b0ec15,0x0,0xa74000000000,0x0,0x0,0x801e4000000,0x5234e0000000000,0x8000000000000000000,0x8083200000a51,0x6926821235806fc00,0x0,0x0,0x98000000000000000000,0x276c6067,0x0],#[0x0,0xa0000000000000000000,0x753e,0x0,0x35d978000000,0xd0558e6f1000007013b0,0x906bc00003019a03b29,0x0,0x0,0x140d74000000,0x80000000000000000000,0x3c0d5,0x901a000000000,0x522d40000000,0x201e400001e0b4c0,0x0,0x0,0xc90d6000,0x0,0x0,0x0,0x0,0xa0b04000000000000,0x0,0x0,0x0,0x8d4210680ca800000000,0x389,0x1814480,0x34ca30,0x0,0x880000906f5c07fc000],#[0x1c6,0x300aab062c000000,0x12262c,0x2d43700000000000000,0x3d10f2016600000000,0x0,0x0,0x0,0x16ab400000000000000,0x2c1609f0000000000000,0x13360000000000000031,0x1208cb4c9f0910ed,0x0,0xa6316000b000000000,0x0,0x0,0x1dbb0,0x2e514,0x731170000000000000,0x0,0x813b0000000000000000,0x108b780000107ce008be,0x394f400000300600000,0xa0420000,0x8945200,0xb11f80,0x1c9368000000000,0x1041400000000000000,0x7e0c41c000000000000,0x53,0xecc80000000000,0x1016800000000000000],#[0x9d0000000000404d8000,0x9018200000000070a,0x29510000000000000000,0xbe3,0x0,0xa0658e0808000,0xf10b34024c00,0x3078a000000,0x2a0e0f48100000000000,0x0,0x2c446000000012a000,0x0,0x0,0x0,0x2e3000000000000000,0x0,0xa0930000000,0x1a61b40000000000,0x0,0x802a20000000000000,0xea0000040f700000000,0x39,0x80000000000000000000,0x101ce685cec1d7,0x0,0x1bc00000000000000000,0x60924406ae00000c,0x308b4,0x404c20000,0x0,0x0,0x0],#[0x381be00000,0x62000000000000000000,0x47e00000000000000221,0x80ce3c08e8000080,0x261600000000000,0x2f274200000000000000,0x3100000000030c22000c,0x8000000000000000384,0x30f20000000000000018,0x5,0x0,0x0,0xb08920000000,0xa24ea000000,0xdd44b82cd0000180ff0,0x16889,0x0,0x14c00,0x0,0x70c0100000,0xae000000000000000000,0xa20,0x0,0x400ff0,0x0,0x931400000000000000,0x5515a000000000000,0x0,0x0,0x0,0x87800000000120dd0000,0x148],#[0x80796000000,0x0,0x9c000000000000000000,0x63c00000805f00000e01,0x24,0x0,0x0,0x408120000,0x0,0x3002c302dc00,0x9066e000000000000000,0x122f000000000000000,0x0,0x8400c0000000,0x0,0x0,0x0,0x3e800000000000000000,0x1c0,0x0,0x0,0x70017000000000,0xe6448400000000000000,0xd8798000000000e0,0x58167000000,0x80000000000000000000,0x5000000000000000e314,0x401,0x459d8000000,0x423000000,0x0,0x34c3c8000],#[0x29b00000000000000000,0x1c1130000060,0xedcc1800,0x2831900000000000000,0x0,0x0,0x0,0x0,0xd04e00000,0x0,0x0,0x0,0x8c01880000138b400000,0xf0f32c958800009026,0x0,0x0,0xa0042000000000000000,0xc181,0xe03a8c075400000000,0x661e8000000000000,0x102e200000000000,0x7037c000000000000000,0x0,0x501fb0000000000000,0x0,0x0,0x1073600000,0x0,0xd00c8000,0x481c94010c00,0x0,0xcd12c0028000000000],#[0x26000000000402230000,0xd00000000003005eb11,0xf2,0x0,0x3291aa00000000000000,0x9052400007184,0x267f0702000000000000,0x39,0xa455e0000000000,0x6a002300000428544844,0xe7a22a95014960990004,0x240,0x4034e00000000000,0x0,0x44000000000000000000,0x2a000000000000000406,0x2407c3105b0000146,0x385c680000000000,0x7834000000,0x1c900800000000,0x0,0x0,0x0,0x0,0x14a4dc00000000,0x0,0x0,0x11d428,0x9074c000000000,0x0,0x199cd821900000000,0x581a4804b0e07640],#[0x40000000004409600000,0x1c00000000000001c421,0x22c0000000002555f843,0x40ff1120481090000100,0x10885a,0x3033300000,0x518a30000,0x51920dfc000000000000,0x17ca000018891c10e3c0,0x111286,0x0,0x0,0x0,0x0,0x0,0x0,0x0,0x1e200000000000000000,0x8,0x82f60000000000,0x1407e80000000000000,0x0,0x0,0x4020a0,0x4808400000,0x0,0x0,0x40f88000000,0x0,0x0,0xa0c8800000000,0x2089e000],#[0x1055400000000000,0x0,0x1628d80000,0x0,0x0,0x0,0x6063000000,0x0,0x5bc00003910400000000,0xd2,0xe06b80000000001227a0,0xb44a05c06a781ccf0872,0x82a6d5e10000004035,0x0,0x38800,0x1690,0xac3f4000000000,0xb223e0000000000000,0x0,0x83d52025400000000000,0xc434a,0xc82480000,0x1b00000b00b800000000,0x2580000000014042c44,0x3c,0x2c414,0x0,0x0,0x0,0x3515700000000000,0x7805730874,0xc0000000000000000000],#[0x22be245ac4ca23969805,0x281ca00000c4,0x0,0x1e44680000002e2,0x12000002202400000000,0xc9b12c8c08ecc59ce1a,0x70,0x0,0x500000100d8000000000,0xd180000000014012850d,0xcfe80000000006044401,0xc0b18000080616000034,0x3,0x0,0x1048ea104700000000,0x0,0x260140,0x1e001000005084700000,0x0,0x0,0x22e0000098b48000000,0xa,0x4b100,0x0,0x100d3c0000000,0x281eb80,0x0,0xf264c000000000,0xa2800000000021094000,0x481d8000009286f8c,0x0,0x40000000000000000000],#[0x702f2a06a84481,0x2508b8000000000000,0x0,0x4c3980000f06a00,0x0,0x1c084b48d9881240000,0x0,0x260000000000000,0x0,0x0,0x0,0x0,0x158e141e00000000000,0x80000000000000000005,0x14ad370433,0x6089a00000000,0x0,0x4005900000000000,0x380e4000000000000000,0x0,0x2038000000000,0xa200000501780000000,0xc,0x0,0x3c8362815a0000,0x0,0x0,0x0,0x6a0ad,0x0,0x1112940fa80000000,0x3860000000000000000],#[0x80000000000000000000,0x50808000020107,0x0,0x9c80000000000000000,0x34,0x21885480b20000000000,0x0,0x0,0x14857e037e0000000,0x0,0x404a081c000000,0x46000000000000000000,0xb05,0x0,0x404e800000,0x0,0x405e0000,0x0,0xb1010000000001405c80,0x7,0x0,0x68ab0000,0x6473c0000000,0x290a400000000000,0xf830400000,0x0,0x0,0x101dd0000000,0x22350056c80,0x380980000000000,0x140dd80000000000000,0x1800a00000000],#[0x0,0x500a30,0x104d600000000000000,0x806406416000000000,0x0,0x380b800,0x0,0x0,0x0,0x0,0x0,0xd0171a00ec,0xdc000063a56b10c20000,0x1407,0xa6b241b2800000000000,0x1e,0x0,0x0,0x0,0x0,0x0,0x1e42c8000000000,0x0,0x28b2101c800,0x0,0x110278,0x2a93900000000000000,0x0,0x160f8c00,0x0,0x1e0198,0xf219a0000],#[0x1118bc01dc000,0x43180000000000000000,0x10,0x1019b00000,0x0,0x200dcc03dd000,0x0,0x0,0xa01a8000000000,0x0,0x0,0x0,0x80000000000000000000,0x38167,0x0,0x0,0x0,0x0,0xe06a20000,0x3089200000000,0xa6d6488cb81a30000000,0x183a5906578,0x0,0x0,0x0,0x0,0xb22918018c0000000000,0x0,0x141650000,0x0,0xd237800003c83e80,0x844f800000],#[0x1e03d40000,0x1e000000000000000000,0x1410000000000a0d2e42,0x202ae00000605758,0x0,0x1a280000000000000,0x3881cb10eb00000000,0x4f4c0000000000000000,0xe,0x9704a,0x1a000000000300380000,0x6d200003c0e5ac8cc610,0x21ec00000000000000d7,0x2483100000c,0xef080600000000000000,0x9084400000000048a1,0x0,0x1486180,0x0,0x3034a00000000f80000,0x27800000000000000000,0x3c4,0x0,0x7601a00000,0x988300000000000000,0x0,0x437c00006017f0000000,0xa,0x5c106800000000000000,0xd06b,0x415f80000000,0x0],#[0x20820000000007026c0,0x2450900000,0xad000000000000000000,0x703,0xa06d0108d00,0x0,0x50000000000000000000,0x84d,0x1293400,0x0,0x803be00000,0x8393c220e0000,0x0,0x7a80000000007015a00,0xa,0x200001c1908000000000,0xb6000000000000002023,0xac00000c4aea041b602,0x70,0x0,0x0,0x270050c0000000000000,0x203,0x0,0x7c934000012042000000,0xa8000000000000000000,0xc02,0x10c00000000000000000,0xc93f8000000000000004,0x285990000000000208a1,0x0,0x0],#[0x0,0x0,0x0,0x0,0x0,0x2006000,0xe24bc62fc70443000000,0x0,0x0,0xc00f6000038866000,0x6166200000000000,0x109ac0,0x0,0x0,0x0,0x6086e000000,0xb045b00f1c,0x0,0x1806180000585f6000,0xcdb004d610b47223000,0x60bec000000000000012,0x801c8,0x12000000000100120000,0x104a680000603,0x0,0xd04d0000038cef800000,0xc112c0000290fe,0xa02340000000000000,0x0,0x0,0x1007f800000,0xc057a000000000],#[0x1c0148000,0x4d980000000000000000,0x8,0x0,0x14c5a,0x0,0x0,0x5044aa046c0,0x258788000000000,0xc0c6c0000000000000,0x0,0x18263ac2000000000,0x29e11000000,0x0,0x120f9000000000,0x0,0x0,0x80000000000000000000,0x493,0xe5001610000000000000,0x82580000000000000381,0x883722d092010000010,0x2,0x0,0x8d800000000000000000,0x5107b00000c4,0x44d000000000000,0x3c1aa80000f01d8,0x22000000000208eb0000,0x80580000000000e11,0x7180000000000000000,0x1],#[0xa30ef8109c000000000,0xd4000000000000000000,0x548,0x27b00001e0300000000,0x1,0x7003a00000000000000,0x5f00000f635526294000,0xdbc800000000000001c0,0x80aa0000000001926b59,0x1ec5b4,0xcc000000000000000000,0x1809,0x5dbb800000000000,0xe4b38000000000506720,0x45585e20000000001,0x0,0x0,0x3c0000000000000000,0xc07e400000000000000c,0xe21f4000000000693d6,0xf019c0000000000000,0x0,0x0,0x240280,0x0,0x0,0xd68683124078c405d400,0x1e780000e0457645d04,0x1,0x0,0x2019800000000,0x0],#[0x0,0x0,0x0,0x6824b000,0x1c1132844100,0xa07b3cc9e000000,0x126704000000000,0x0,0x0,0x1206dc000000,0x28b3a9223a0000000000,0x0,0x0,0x0,0x812b0544c000000,0x581ded088c00000,0x84000000000000000000,0xc209f006,0x9c80000000000000000,0x1e,0x905d2,0x58000000000181280000,0x2200000000000000584,0x17da601f0000000000b2,0x2406880000f,0xc88888123,0x0,0x0,0x0,0x668c0000301a20,0x1104500001c0ad40000,0xe6760000],#[0x0,0xc0990000000000000000,0x3,0x303f6000000000,0x0,0x449c0000000000000000,0xc7658a,0x0,0x0,0x5d9400000000,0x0,0xa0278000038473800000,0x0,0xa6000000000000000000,0x318,0x5537a80108000000,0x800000000000001d1eb0,0xc8000000001646314409,0xf3288c0c26487,0x42980000000000000000,0x3c,0x0,0xc53740000,0x2c18e7b0e7c0462000,0x0,0xe6733843b000004008e0,0x16069615094984cb02f5,0x19e10a90bd0000,0x68400003803280000000,0x1c016800000000090,0x760,0x0],#[0x0,0x2b900000000000000000,0x40,0x394a80,0x1764dc46240000,0x0,0x1e004c00,0x0,0x0,0x241ef00000000000000,0x8e800000000057704000,0x102,0x0,0x20000000002029400000,0xf003,0x2408b00000000,0x250ca0000000,0x104b4a03700000000000,0x3395de000000000010ab,0x3635155489f,0x92c12385a01cc0000000,0x1c05e4000068,0x80000000000000000000,0x60e70810b,0x0,0x10859400,0x413a900000000000,0x70880c80000000000,0x0,0x0,0x1016b891a600,0x0],#[0x0,0x0,0x5ce40fb8000000000000,0x6e60000000007220cc0,0xd00f400001c1dc00000e,0x5000000000000006b807,0x52000000000000004033,0xae00000000000000508,0x49,0x4008000000,0x1a0b8c0000,0x3113f0000162160000,0x3899a000000000000,0x7814f5080c000000,0x4888d0000000000,0xb21800000,0x2442e800009040a000,0x0,0xa2838000000000000000,0x600002442b8000080854,0x805e,0x0,0x3000000048318000000,0xa,0x0,0x0,0x34c00000000000000000,0x4111ed1a9a0,0x80000000000000000000,0x100000000000000108ee,0x200f,0xbb233232ac036800],#[0x0,0x12820000000000,0x2c06900000b01ee0000,0xce400000000000000000,0x3c1578000000000ae,0xa0a4b003080000000000,0x148b69814700000,0x0,0xc011102eb000,0x0,0x0,0x0,0x0,0x423b00000000,0x0,0x1823a000000,0xc8000000000000000000,0x3c0c,0x0,0x0,0xc03ac00000,0xf8dcb900000122020000,0x46c00000000020078e05,0x140,0x29b2f000000,0x0,0x1c000000000000000000,0x506,0x0,0x0,0x829400000000000000,0x0],#[0x2c062000,0x2c94000,0x40f0c00000,0x0,0x0,0x8e80000000000000000,0x1c093a1,0x0,0x94000000000000000000,0x209328b1880000140f,0x0,0x50c0000000005032e0,0xa0000240d78000000001,0x5be43ec000000000b067,0x1898a044,0x0,0x0,0x0,0x12112080080000,0x32382000000000000,0x0,0x0,0x0,0x6220000000000,0x1930bb6a000000000000,0x50614e058a0,0xc00000000000001a0e28,0x100e3,0x0,0xe5800006808e0000000,0xf0205e,0x0],#[0x0,0x0,0x32a0000010cfa8000000,0xf,0xc0000000003852080000,0x1c84dd819,0x0,0x0,0x0,0x104a8,0xea000000070840654000,0x9,0x0,0xc0000000000000000000,0x3a1188030820c0,0x3c1e15822400000000,0x28089000000000000,0x0,0x18b3e00000,0x0,0x1e076c000000000000,0x14460a41b00000000,0x0,0x0,0xa12be0000000000000,0x80482000000000000,0x0,0x0,0x31a1d00000000000000,0x0,0x40f4400]]
set_option maxRecDepth 16000 in
def g243D8 := limbs80 #[#[0xd58430bb98a10bb58a10,0x98830bb58830bd98430b,0x84509f994309f59430bb,0xc50b758c50bd98450bd5,0x10bf58810ded4250b798,0xfe48110bf59410bf58c,0xfe8c110fe4c110fe8811,0xe54110fed0110fe10110,0xd8910bf58910fe94110f,0x9510bfd8d10bf58d10bf,0x210fe4c210bfd9510bf5,0x10bf58610fe54210fed0,0xbf59210bf58e10bf58a,0xbf58830bf58430bf5961,0xe94130fe54130bf59430,0x59530bfd8930bfd8530f,0x8630fe54230bfd9530bf,0x230bf58e30bf58a30bf5,0x50bf58450bf59630bf59,0xdf54d50bfd8550bf58c,0xbf58650bfd8d50dfd4d5,0xf58750bf59650bf58e50,0xd4810ff54810bf58f50b,0x8110ffd4c10ff54c10ff,0x110ff50110ffc8110ff4,0x10ffd4110ff54110ffd0,0xff10910ff8c910ff4c9,0xff14910ff90910ff5091,0xfd4910ff94910ff54910,0x54d10ff98910ff58910f,0x9510ff59510ffd4d10ff,0x610ff54610ff48610ff9],#[0x10ffd4a10ff54a10ffd4,0xff55210ffd4e10ff54e,0xffd4430ff54430ffd521,0xf54130ffd4830ff54830,0xc8530ff48530ffd4130f,0x4930ffd4530ff54530ff,0x930ff94930ff54930ff1,0x30ff98930ff58930ffd4,0xff54630ff99530ff595,0xffd4a30ff54a30ffd463,0xf55230ffd4e30ff54e30,0x94550ff54550ffd5230f,0x8550ff58550ff18550ff,0xd50ff54d50ffd8550ff9,0x50ff58d50ff18d50ff94,0x2c044000ffd8d50ff98d,0x1e07a834c16208f03681,0x8183d61c20cc85c02801,0x2e01628a704f42511108,0x8ecc7223681a30c745f6,0x47822e91088403f71ea,0xd9564a60507272932895,0x9c62c30517a0b7e5962b,0x909bfcdba6c234919c0c,0x47d93d49e1ced87433,0x475230512286f42a2091,0x53969a94c72579286913,0xa5642a614dea3850b27b,0xd7c2b9c5bd2d45634ae,0x1c67d330d8fcc5c61d30,0x90dc26ddc6d9b5d5a98d,0xf717a0bc0ddc2eaa740b],#[0xc1d60a70237fd3f0df42,0xf1c68c0c57e2190e3859,0xcb2a53525c919c8463d,0xb33f89e7ce466d132a98,0xd55596a6b4fea6ad25e8,0x24404b38d906c315e1a,0x818022213005011014a0,0x880c0122220006049084,0x4888a481802220206009,0x5244462848290101800a,0x888a500120a405280400,0x221940014910141800a4,0xa81240088c14a110c292,0x80491010093224880a50,0x3484880690094224054,0x9480a0401026201264,0x291244054894910102a4,0x814a112020500488084c,0x4061012520285284480,0x2434a061ca100c2024a4,0x685244042814a8020486,0x4242850e50808148120c,0x88850015244050a0209,0x240c0111429222185180,0x3a5284040a00a2520295,0x102a2284040a4481410,0x491018125284040494a1,0x8640908149100ca05005,0x2850c509081439420205,0x5202120a4032800a9220,0x80a002020a5480c5090,0x2a4062a50290101800a5],#[0x29420245244030008294,0xc1480a50a800a4880c1e,0x92223023050290142022,0x94a1119292221970a092,0x54a4880894a110cc0506,0x22a5484880b152922024,0x88900074a4078a949101,0x2932240688903a520295,0xe412111a2a5204842915,0xa951868b0c9921d2c50,0x4c92094911112c50c449,0xa4490808bc3468a0250c,0x10111c3441a0134a3864,0x8929024ba5244044a4c9,0x709125203980b101c248,0x224a4064889290122240,0x148111529010485325d2,0x4886a52029684052a21a,0xa52431786091a5824878,0x283848929420443460a0,0xb04a121e122289480a60,0xc0224412894908642844,0x201809488c582c402912,0xa488885c2824a4888d11,0x9414ac24401290283824,0x2454b112112034244412,0x9080a444948111529220,0x92222c44909125203168,0x241430e0254424b28412,0x2529225292222022f11,0x16509101522189051438,0x2a24a508085d29220225],#[0x4052224a4082e88a2520,0x921e224848929018b448,0xa1869490a5c14142961,0xa405300e1254414a1022,0xa120a14a50911091144,0x210014d8284a2524299,0x481004ac4490d1c2445a,0x880102a415488a242001,0x1d2222b1480a3440548,0x220040a8c552221a2229,0x1958488c002840292152,0x54a0e5514200148141c,0xc88a948a40516882802,0x140a40a8c5510b8a40a,0x88]]
set_option maxRecDepth 16000 in
def g243H8 := limbs80 #[#[0x1030420330400202100,0x20030000010110281000,0x15085000500000101310,0x12011100020110032004,0x220012101012014100,0x100001100032a0000001,0x110234102030001000,0x100000000301103100,0x12010002104040001000,0x100000000010004503,0x50046300120000116,0x10003000901210221000,0x230041150300122300,0x1010170001000042000,0x21000014350002412012,0x10002232022102203000,0x40030040120000000000,0x25000010025101260020,0x814b0000000001222314,0x3ec982d1ba249ed00000,0x516400000409,0x0,0x0,0xd01e00,0x1c00b0000,0x81d000,0x8e0000240e7373558845,0x185,0xc000000000000000000,0x341e7f35c00836072,0xf066109e882013509af0,0xb60000002eef043742a],#[0xe01180000000018,0x7000000000206a10000,0xc66140000c2,0x49000000000000000000,0x42aa0000000000000140,0x9408620429004260c29,0x3c267b0368000078b,0x0,0x0,0x0,0x0,0xb31a75a62405d8428d00,0xd90000000d0000000000,0xd6510000000000000261,0x80000000000000a2823,0x28daea60,0x0,0x0,0x0,0x320ae16720000,0x0,0x2660c841c000021f05,0x389b20000000,0x60c2f600000000000000,0x1424a00000000000c,0x9051000000000000000,0x9500003c232d20a4000,0x1041fa05fbde6d7003f8,0x239000028dc5d08d,0x300ac000000,0x1043c0000000000000,0x40f8000000000908c400],#[0x2,0x0,0x5007504e70000000000,0x16300000000000000000,0x57e020614,0x0,0x0,0xf3000000000e0b380000,0x21a0000000000000101,0x915a00000a49bf,0x46009eb9198c0000000,0x811600000057ba,0xb01a80000e04d8000,0x40000000000000000000,0x10c459d0000000002000,0x102b560140000042,0x2458d,0x49670000000000000000,0x3,0x74fc000000000013d000,0x2821bb14400000d,0x0,0x28def158ac0000707840,0x149300000,0x0,0x0,0x248090000000,0x21cfd00000000036b98,0x4065709900000000,0x0,0x14c1700000000,0x0],#[0x382f90000000000000,0x0,0x6340b15d6000000000,0x1c56380afc00,0x9a42a300000000000000,0x9d64828d0aec0000b15,0x14e6500001c1df5,0x2b2c000,0x39838000000,0xb9400000000000000000,0xb0,0x65000000000000000000,0x42cd101760417f05d701,0x0,0x8824101900000000,0x0,0xcc00000000060374000,0x24,0xb049e890000000000000,0x559a00000000000000c9,0xd16b00000,0x0,0x0,0x0,0x805b000000,0x0,0x0,0x9f040000349870000,0x0,0x103240000,0x937300000207e800,0xe5adc],#[0x501380000000,0x9030c00000,0x9ce51a80000f77f8000,0x180c8000010,0x70c00000000,0x0,0x2c184a10640000,0x0,0x910225000025af800000,0x707,0x0,0x16c000000000000,0x40000000000000000000,0x5010,0x1568900,0xe09040000,0xd0640000000,0x182c200000000000000,0xc089c0000000,0x18acc0,0x0,0x0,0x0,0x725e0000000000000000,0x7200000000000001084f,0x342d4000035d,0x140000707a9419900000,0x1bae813000000000049c,0x289c78,0x47478c09600000000,0x1c20b000000000000000,0x3c15a0000000000000],#[0x1082c00,0x1b000000000000000000,0x92a400000000010987c1,0xd0d5dc00000000000003,0x180f2f166a8959403,0x800001c0d30000000000,0x20c5,0x0,0x1002c0000,0x0,0x0,0x85b4000000000202b000,0x50071,0x41b261bc80000000,0x0,0xef530930000000000000,0x627d3d,0x86a81460000000000000,0x8047c00001206c00fa95,0x20d03000000000,0x0,0x0,0x73b40000000000000000,0x1c9eee,0x26d00000470000000000,0x30,0x0,0x82450000000,0xe348f8d04880000,0x319e092f262d000,0x71a74000000000,0x7080000000000000000],#[0xc31cd,0x806700000000,0x2c15d000000,0x28666706d000000000,0x0,0x0,0x610d000,0x3d04c00000816700000,0x0,0x85670000000000,0x0,0x0,0x0,0x0,0x0,0xcdc800003c8521477000,0x0,0x7b0000096c000000000,0x1cacd8071000fba,0x24700002c202a048c000,0x8014ba45100002c,0xa793c00000000,0xe3a74000090878000000,0x0,0x0,0x21149029900000,0x0,0x0,0x506a4000000000000,0x80000000000000000000,0x8c9c0a2f05bc0000c08a,0xb5],#[0x4c725f0000000000025f,0x4057c00000000281,0x815200000000000000,0x0,0x81c00000000000,0x0,0x109e00,0x0,0x0,0x0,0x0,0xf742df000000000a96d8,0x506,0xe731000000000000000,0x2012c00000000,0x5c9d800000000027a540,0x1423dc07e,0x0,0x9400001c215000020322,0xc059000000000805adc2,0x88000000003859f00003,0xa8000000002cd00c09,0x4d03b8025d000000000d,0xe5a000000000404e5003,0xb0c540000f7bf9d,0x205fc00009791,0x97408000000000000000,0xfc0000000000000,0x760e400,0xc4000010730425a00000,0x296055d00003c162125,0xc00000000000003c5aa9],#[0x2d8951a000000000301d,0x666048,0x0,0x0,0x0,0x42930000000000000000,0x105c7,0x9788102000000000000,0x6a0000000003966ae,0x4dbaa13c0000,0x340ed000000,0x3c2e60000,0x62208000000000000000,0x51780000000000000,0x702e800,0x0,0x6b6804ae25980060000,0x24217000000000f,0x0,0x3cdcd000000000d08500,0x0,0x0,0x0,0x0,0xbc42cf00002081f00000,0x3c1af604,0x9508a786d210217c9a80,0x639a79300000c7306811,0x2e,0x0,0x601c0000000,0x0],#[0x0,0x2484a00000000000000,0x3c2b6c36571cec000,0x0,0x292f0278000099750000,0xe001800000000000000c,0x1de01a022,0xc315ecc620000281ef00,0x19249,0xe113800,0x0,0x3c084707280000000,0x0,0x811,0x34024000000000000000,0x15ec00000,0x0,0x8a000000000000000000,0xd21c0000000000000342,0x406200000000000003,0x0,0x341900,0x667000000000f0500000,0x19,0x0,0x1ce13f4840000000,0x2c1a7b04f80000,0x305e000000000000,0x0,0x200400000000,0x0,0x21e421f6c2ad00000000],#[0xd0c1a1,0x3480a000001c430000,0xc27f0000000000000000,0x0,0x0,0x20768000000000,0x8134000,0x0,0xa2030000047918000,0x24013000000000000000,0x5e800000000,0x28e7800000000000,0x528100000,0x0,0x2029000000,0x73c40000000000000000,0xa,0xdb80c91126c00000000,0x82c7a13cf0051e0c858,0x59000003087018030000,0x3027df21fb420481,0xcc826f80000000000000,0x1a105cd4307d802,0xf701d190696242f00000,0x974,0x30000008460000000000,0x34a0,0xdc07e0000345f6000000,0x2c0b3b07384dc63185,0x4044c000000000000000,0x4a4517c0000000000000,0x143f9c2000000000190],#[0x204a800009060d,0x240d60000101b0000,0x1869e721f000000,0x5083c000000000000,0x15e150000382f3000000,0x96c41940000000000000,0x83184000037,0x0,0x42be000000000402bc00,0x380cfb162c013887c23,0x280d800002dc71000,0x666324a530,0x5dcf798b425b00000000,0x1098d000000,0x0,0x90a380000727ccc0b500,0x65b0161065f905340000,0x8c,0x4c000000000000000000,0x188961176452a7909,0x0,0x1cb000000000c365c000,0x80000203475e6c00001c,0x182eb3081,0x0,0x2c000000000404680000,0x80a8f00a40000e0a55c2,0x50000000000000000001,0x602,0x0,0xc5150000000000000,0x803bfc308000000],#[0x0,0x0,0x820000049df000000000,0x708b840,0x0,0x598000000002419c000,0x4a0bf000000000000003,0x5ad0000000000000216a,0xe04ae8,0x235b742500000,0x2068ec86400,0x35833000001e78,0xf721400,0x7e1ad700000000000000,0xd00,0x26123d82110000340870,0x1c96,0x0,0xf20e042c90000,0x0,0x806800000,0x0,0x0,0x30400006018c0000000,0x3c0e09,0x90911009121b5c000,0x907340,0x89800000000000000000,0x400f800001038c000054,0xc28b,0x0,0x18000000000000000000],#[0x278c0000000000000b0a,0x91068800005317000002,0x829d0000301c,0xd4016000000000000000,0xa46c,0x0,0x600cc000000003c2f1,0xd08b400000000000,0xd300cd00000000040778,0x1805c406980000c02,0x8067800000000000000,0x0,0x251ed00001ce57000000,0x65400000000000000000,0xc0,0x18285000000000,0xc17da05b400000000000,0x2065000003002d70169,0x103ac0000000,0x0,0xe0614000065794000,0x40ab80000000000,0xa8800000000000000000,0x61,0xc124,0xc44a0000000,0x98000000000000000000,0x67c0000000000000316,0xa01a400000000000006,0x602000014044708bc000,0x2e2331800000a0555a,0x0],#[0xb049c000000,0x0,0x800188025e25ac00,0xc4000000000000000000,0xd35,0x7212c00000000000000,0x10918000,0x0,0x180e4f29c000000000,0x0,0x609fc41bc237700000,0x806e183130000000,0x0,0x95c0000000000000000,0x300619,0x0,0x520b40,0x388f800000000,0x1c9a600,0x310780000,0x0,0x52089700000000000000,0x507,0x1814900000de0f0,0x0,0xc0000000000000000000,0x107a,0xf7331c2bcb5144000000,0x80b040000,0x8e2a000000000539fc00,0x142b3000000000d60d9,0x300d2000000000000],#[0x2261bd8370,0x1410800000000,0x40000000000000000000,0xd366,0xf245c000000000000000,0x0,0x0,0xa7920,0x80a440000000,0x0,0x1165200000000,0x3897e11b4c01fc000000,0x180f90000280a60000,0x107c8000000,0x611240000006d5c16e,0x0,0x640000000011aa190800,0x90b,0x323e40000200f400000,0x2600000097500000000,0x2882a572c40000b11b1c,0x40000000000000a09b,0x3741c00000000394fdf1,0x0,0x0,0xcc00002184c02e700000,0x1cfc2dd000000000026,0x30000140beb4ac400008,0x17,0x0,0x0,0x75778000000000000000],#[0xc07f,0x8008400000000000,0xb04c8000000000,0x274000,0x0,0x2842100000000,0x0,0x32a09b8e799601890000,0xd7,0x907f40000000008325,0x0,0x0,0x0,0x102f400000,0x10600000000000000000,0x5cc5db27720a6b000038,0x876065c000000000a21e,0xf0b6c1e9300002042570,0xd4000000000000000000,0x112,0xf0000000000c1ba00000,0x804,0x204ec00000,0x2025400000000,0x1806c000000000000000,0x87b7d41510000,0xa02c20e5800000000000,0xff0000259af000000000,0x9375f8c,0xf73d0000000000,0x154f5000000000000,0xd08a000000000000000],#[0x85870000,0x0,0x749bbc0e9d0b7,0x3007700000000000,0x39000000000000000000,0xc737c00000000200,0x425d7400000000000000,0x4989858,0x0,0x960f2825017900000000,0x941d7c2aa00000000038,0x6019a3a2408c00000319,0xc0010000006,0x5624,0x0,0x0,0xc0c380000000,0x10000000000000000000,0x302000015e9100001018,0x34209c0bfc0000973c88,0x5084800000000,0xb0ae0000000000000000,0x0,0x0,0xb0620,0x1c4c0000000000000000,0x300b100000c0e8b,0x0,0x957400,0x0,0x9da100000000000,0xd617a7fde59000000000],#[0xd04b601,0x0,0x1dc74000,0x0,0x1a1202aa5e5000000000,0x40000000000000a0c770,0x807a501ac9096,0x8090c8cfc00,0x35848000000000,0xe050800,0x0,0x0,0x0,0xe208c000,0x0,0x3c6f90000,0xe0c58070d00,0xa0aa40000000000000,0x0,0x3456b00000,0x459b0c1e5000,0x0,0x0,0x8dce2000000000000000,0x5b485995040ed6b6a488,0x92,0x0,0x0,0x18a0200000,0x908cc0000000,0xf685c0000000025e760,0x0],#[0x2001b606300,0x80000000000000000000,0x87,0x0,0x9e72000000000b79c048,0xc602f5f1ba79e6093797,0x5200000619640000900,0x54200001420cc,0xe500000000000000000,0xc,0x16400000000000000000,0x43590000000000000013,0x22b70ac000000a320260,0x520bac27c499c3c8,0x0,0x142ac000000000000,0x0,0x6e787301458c00000000,0x80000000000000000020,0x1023740a680000009e,0x0,0x7143c0000000000000,0x42a5617dc00003259000,0xd1bc4,0x1d986d730c0000000,0x1c6cc0000000000,0x0,0x0,0x95800000000000000000,0xf0,0x0,0x0],#[0xc0000000000000046498,0x39cd0000000000c63,0x1065c0000905a7c1070,0x186f0205ec000,0x0,0x38054a0be000000000,0xe8b1400008053c000000,0x30dcb000000000,0x96300000142160000000,0x44000000001c1b3f23db,0xf4b,0xc07a0,0x0,0x8264000004035c0,0x0,0x0,0x0,0x9026400,0xf0000000000000000000,0xcbc29fb02e00000608,0x3098f4056b,0x24200000000000000000,0x597c000000000000030,0x51c00000000000000000,0x3011100000000060,0xa8000000000000000000,0x107dc00000000202,0xe0938000000000,0x10e86000000000000,0x40000000005106c00000,0x20e00000000032688461,0x3945300000000000000c],#[0x1444d3057105690000,0x0,0x0,0x0,0x2e810500000000000000,0xd09,0xf0000000000000000000,0x702cac31,0x898c81227546b000000,0x0,0x149d2c2ea326d8000000,0x5700000000000002c0f5,0x466880000a007a5e,0x0,0x55c0000000000000000,0x7,0x21800000000000000000,0xe15f40,0xc25210a8400000000,0x50a78000070ae4000000,0x395b7,0x465e0000000000000000,0x3803a00001,0x0,0x0,0x0,0x24028000000,0x0,0x0,0xa9000000000000000000,0x25bec9,0x0],#[0x0,0x1c0760000000000,0x0,0xc2ec4268c0,0x4700000357b000000000,0x3425c70,0x204380000,0x0,0x0,0x7b40000000000000000,0xe000000000000000000d,0x18f00646081600002c2d,0x34,0x140a00000000000000,0x2495500,0x174800000000020833,0x1370000000000000000,0x3,0x241cfc20c5c075000,0xd401f5e5060000000000,0xe0047d886b031b21e,0x0,0x0,0x4032c000000000000000,0x50564431940bd2c00c,0xdbf0000126bf0000000,0x3,0x1b700003028f000,0x0,0x18e0029c000000000000,0x21,0xaf343170000000000000],#[0x55,0x7be0a240000000024560,0x202e50022c1c0702,0xd03120270a0048,0x0,0x60000000000000000000,0x99500000000042751826,0x81f5000038,0x201c60000,0x0,0x3e00003c0f6000000000,0x8059282,0x82124,0x30ddb000,0xa3597d8b97741400000,0xd03665cfcc01b4000,0xa07765ce6503000,0x0,0x340f711860000000,0x9a000000000000000000,0x55b5b59a400000000380,0x280bf00000000000000,0x3074000000001c844000,0x3c061c0000c00c000004,0x311e,0x3cdde000000,0x1066800000000,0x201d28087cde3500,0x9e0000000000000240de,0xc25a845,0x2c23000000,0x0],#[0x0,0x0,0x0,0x0,0x80e100000000000,0x221,0xb0c9c00,0x1f081108000000000,0x0,0xa09b800006208000000,0xc67d00000000,0x140fd000000000000000,0x0,0x208c200,0x9740662de79000018203,0xa01ac00000000280,0x8c000000000000000000,0x308,0xa000000000000005e0e0,0x2418,0x0,0x7cf075400000000,0x83d00,0x0,0x81d80000000000000000,0xc8004b70c98146317419,0x30a,0x14403d0c0400000,0x0,0x0,0x27400000000000000000,0x2800890],#[0x6900000000000000,0x0,0xe70b00000,0xe77a80000000,0x759e400000000000000,0x70880000000000000,0x202c0e0b5c0,0x0,0x0,0xa86600000,0x5ce521939c2730000000,0xf0000000000000000002,0x702,0x0,0xe25d0000000000000,0x80dc241000,0x3c26ff76ff829b0000,0x7065805b300,0xf31680000000000000,0x431e0000000000000000,0x20c1e,0x0,0x26051400000000000000,0x3817,0x3c160000000000400b80,0x0,0x60398000000,0x8205000000000,0x1e690000000000000000,0x2,0x0,0x9cc60000000000],#[0x0,0xc65f40000a02200,0x0,0xe037e1e68c0200000000,0xa18163c4235000038150,0x82c300000000000003d9,0x980000358b4000000002,0x36fac0ad602280000408,0xb06ad42b70000000004,0x14a94466400000000,0xc0000000000000b03c00,0xc0030000080909064,0xc0888000000000000000,0x8d000039d3900000c1f1,0x818b50230000000001c1,0xa205c000000001,0x309c0000000024311000,0x45ab907e000001,0x0,0x8433000000000000000,0x140370000,0x0,0x41f40000000000000,0x0,0xb750c,0x0,0x2c1210,0x3800e00000000,0xe6bbc0,0x255b80000000000000,0x90474000000000000000,0xc9000000000000000000],#[0x448740000000025c,0x8078c,0x30e7d000,0x0,0xf058489e5135b8000,0x39ccb615780000000000,0x604000000000000070c5,0x8621c815800c6a008eb2,0x181e0,0xa710000000001106800,0x40bfb,0x3540000000,0x0,0x24900000043bf73cc000,0x202dc0000000014,0x0,0x70b8c0000309ac029600,0x707ec0000000025ce1,0x91b00000000000000000,0x5a40f300000000000001,0x4a0000000002c9c6140,0x70000000005038800008,0x800298de,0x5e94000000000000000,0x15e560000000000000,0x0,0x125ea00001419d,0xc0b4800000000000,0x8ac09f00000000000000,0xc100000000020125a19,0x2,0xf0946c02],#[0x4050641c8000000,0xe6360000000000000,0x181d314b2c007900,0x4747c0000000000000,0xc0bec00,0x8c680000182f700000,0x280a3000,0x70b8400000,0xc0248000000000000,0x18300000000,0xb7400000000242bd0000,0xd006bc236a1,0x0,0x802ee8a110000000,0xe4914000000000,0x1980000000000000000,0xc,0x2c14e30954000,0x2e0408e009e4000000,0x0,0x0,0x0,0x607a000,0x4000000000000000000,0xe07,0x0,0xc1ec36f381b1779d4000,0x30210000030c6b000008,0xa6c00000000206ed0000,0x701bc057a37317800d12,0x75194000000001c13a,0x0],#[0x90424,0x0,0x0,0x5f00000000000000000,0x24071000004,0xf00000671e392af0000,0x1485090a1c000050,0x8d63,0x0,0xc04560bf4000000000,0x0,0x288350,0x13a20000000000000,0x0,0x54920000,0x20ba4000000,0x344f1000000000,0xc2a42123801b60000000,0x3,0x0,0x1da30000000000,0x208fc000080a10000,0x0,0x0,0x201e200,0xd08ec0000000014177,0xc998472280000f00bc00,0x0,0x31ccf000,0x705a3c0170,0x0,0x80000000000000000000],#[0x904e50ac40000d017,0xb309b9cf000000000000,0x60204c1db000000000,0x0,0x1c2ab00000,0x0,0x40000000000000000000,0x183,0x0,0x305ed0000000000000,0x85b100000000000,0xb0bbc0000,0xe60d400000000000,0x2260c000000000,0x281c0000547640000000,0x7,0x0,0x4036000000,0x4c44098c024c00000000,0x527a8000000000000040,0x3429c000000000,0x0,0x32068,0x60a080000000,0x0,0x200a400000000,0x10120000000000000000,0xb40000c07fbc208c03b,0x3257c0000a7,0x30b440000a054c0000,0x0,0xf06d500001010b00000],#[0x31092000000000101,0x0,0x0,0x385a7701540,0x0,0x0,0x6288c8182e09dc5462,0xb3470030c30b4c00,0x0,0xb031c0000000,0x0,0x0,0xe799c0,0x0,0x100ca00001c9d900,0x10248000000000,0x0,0xc31000000,0x8e80000000000000000,0x609d80000000039251e,0x0,0x115b6000000,0x0,0x0,0x1d26d007140000,0x485500002df090000000,0x0,0x149fe000000000000,0x3095d0,0x0,0x840a1000000000000000,0xc0489658],#[0x9277655ce00000000000,0x85000000000000000000,0x50b1000000000389,0x0,0x8312226440000000,0x41bbb076400000,0x20700000000000000000,0x1ccaca065f94,0x0,0x0,0x0,0x0,0x65ec000000000,0x0,0x0,0x18000000424d00000000,0x2c30da50748448000030,0x0,0x259b200,0x900240000,0x3830f0000000,0x0,0x0,0x2427e0,0x2408d00000000,0x0,0x31400000000246580000,0x0,0x7157c0000,0x7099400000000000,0x5c000000000000000000,0xb2c0000000000000001],#[0x90000000000000000000,0x4c304d482690000141b,0xc0000000000000000004,0x6a80000000000000a07f,0x60beba5fff0,0x790000389d5808040000,0xe75cc00000000209,0x3d884800000000000000,0x82680000202a6101,0x4000000000d0a8000000,0x20ad3559,0xc0000000000000000000,0xb54029800000000022b3,0x24279e0,0xb5ab40000000000000,0x0,0x0,0x10288000000000000,0x7488000000,0xd71725ecc9a700000000,0x6d5b9c1b63002300003d,0x3006,0x20bc8000000000000000,0x1400000017c00001484e,0x300f1b88ec48,0xa0798000000000,0x3dceaa1be80000000,0x3018e0,0x224c000,0x0,0x0,0x15f0700],#[0x0,0x830b903a9006802a8c00,0x202ca00002c31b00002,0x500000d0c8c0000000,0xf000000000071d4d42f6,0x19200002007200000d90,0x3417400000000000002c,0x0,0xd010000200c200,0x2b000000000000000000,0xc9e509c8c2c6027fd82,0x1,0x3c035000,0xd00003197f0000000000,0x3561,0x0,0x0,0x8056c81f410a5e86ea00,0x328a4000080a8a4112,0x44b3400000000000,0x3414a449cc000066608,0x2408f000,0x8022400000,0x0,0x375000,0x3c07400000844f0000,0x0,0x154,0x1061800000000000,0x0,0x77530309000000000000,0x79c240000c],#[0x0,0x40000000000000000000,0x34aaa4053b040,0xc95e00,0x0,0x0,0xe02a4,0x8224b37040000000,0x0,0x0,0x720ea4996501b80,0x1098e000000000c0b4,0x204247020c000000,0xc00001c1bf000000000,0xa04a595e80000281,0x0,0xc8240ce504540000000,0x40b5800000000000004,0xd0900000000000000,0x9108c0,0x2456a0000000000000,0x0,0xa0000000000000000000,0x305,0xd1080,0x0,0x0,0x0,0x506f80000188f7000000,0xc290c0000475d,0x0,0x10170271cc0000],#[0x90a058d960000000,0x803f0,0x49b05e3000000000000,0xfb26844002000000000a,0x2da000000000d04120d6,0x2ac0000b26210,0x1106,0x0,0xb50000115cf000000000,0x16ba00000000000003c9,0x3400000000182e800002,0x9a882c5473340000508,0xf486485659,0x0,0x4000000002003b000000,0xd283,0x0,0x527680000000000000,0x7b3800,0xfa00ff41b98000000000,0x1d0d00003041d174,0x100270,0x0,0xf258c0,0x7499cc07b0000,0xe25f4000000000000000,0x45804500000000000000,0x102,0xb0000000000000000000,0x33f80280000000000335,0xa0000000000000000005,0x500000000000000c2b],#[0x34,0x0,0xfe00,0x0,0x21bbc00000000000,0x0,0x380d4000000000000,0xc0c1400002796181be0,0x50ac0000000000000,0xc0000000000000000000,0xc066,0x22818000000000000000,0x0,0x811e0000000000000000,0x1118ac0963,0x2045fc12e000,0x2c1560000100470,0x0,0xb900000601000,0x0,0x3988e00,0x0,0x409b0000000000000000,0xf0578cdc300002,0x13959dc72000,0x148a000000000302f00,0xb0bb4000,0xd66980000000000,0x182c80000000000000,0x0,0x5d000000000000000000,0x206],#[0x4f4a0a00000000000000,0x856,0x0,0x1c271c3760000,0x31580,0x0,0xf0a9c000000,0x0,0x302b800005082800,0x0,0x531540000000,0x804cc00000000242130,0x0,0x1816a000000000000000,0x0,0x0,0xb1b700000000000000,0x288210000000,0xfcc1ee00003c1ae00000,0x21d40000000020000f04,0xe086400005,0x100000030283c519c000,0x24,0xc0c00000000000000000,0xf0054000030,0xc7000000000000000000,0xc6d00000000000000181]]
def g243D9 := limbs80 #[#[0xd30fe187f843fa21fc10,0xa1fe50fea87f143fc61f,0x19508a379506c1e003fe,0x505103092051009f96db,0x814900091440c2040407,0x51020520d10085051030,0x4900091440810c051020,0xc2052405009505103081,0x24002440c20450065040,0x10308100519410308115]]
set_option maxRecDepth 16000 in
def g243H9 := limbs80 #[#[0x40018000008008200200,0x88400102601042210a,0x24f00801800900820000,0x767b030546b00000000f,0xe,0x71200000000000000000,0x8700000000000000004,0x0,0x4bb95f0000000000000,0xf,0x0,0x0,0x0,0x0,0x0,0x34ed05d0000000000000,0x602900004,0x4f00000000000000000,0x8,0xd4620,0x350275600000000e1200,0x41800000000000000004,0x55200000000000000004,0x35c00003,0xb02b0000236500000,0x0,0x0,0xf215977800000,0x0,0xf06e606900000,0x98600,0xb07e00000],#[0x926a00000,0x0,0x1053d03a000000000,0x2400000000000000000,0x8,0x0,0x0,0x325b0000000000000,0x0,0x4079000000000,0x71a000000000000945b0,0xe03c4048c042b,0x18700000000000000000,0x5,0xb615401e0,0xd01b00000000a00e0,0xf0570,0x25223453766000000000,0x0,0x84750000000000000,0x702c000000000,0x2f00000000000000000,0xc,0x0,0x55900007742000000000,0x500d00000000d,0x0,0x0,0x0,0x0,0x0,0x0],#[0xe71e000000000,0x0,0x225310350000606c0,0x0,0x4600000000000000000,0x93900000000000000009,0x1021a0280000f,0x517dc57600000,0x13a000000000000672b0,0x98300000000000000002,0x625000007,0x205f0000000000000,0x0,0xb04d0,0x75f00000000000000000,0x1170000000000004340c,0x70100000000000008,0xd14900000,0x7180124b000000000,0xc7630,0x10a11290000000000000,0x4,0x7800000000000000000,0x2000000000000000009,0xa,0x0,0x20660000000000000,0x13b0000a0509082b47d0,0x72410,0x824a0000000000000,0xc0710000000000000,0x0],#[0xe009904a0000a5510,0x72e1810000154f00000,0x24900000000e76b0000d,0x355c7,0x0,0xc702c083000000000,0x0,0x0,0x0,0x0,0x0,0xf5412762000000000,0x0,0x0,0xb36f0,0x66600000000000000,0x80080000000000000,0x11400000000000000000,0x3,0xf0450000000030390,0xd24000000,0x27d00000000000000000,0xf03200000000d248e,0xe26200000,0x5e00000000000000000,0x7,0xf377476a000000000,0x0,0xe04e6064000000000,0x1370000f275000094680,0x87b00000000b0540000b,0xa],#[0x0,0x25100000000000000000,0x7,0x0,0x30630,0x1040000000000,0x0,0x407b0000000000000,0x0,0x0,0x150000307fb25400000,0x979806d3085900600003,0x9,0x410b00000,0x0,0x0,0x700a7646f21400000,0x0,0x0,0x506b00000,0x0,0x0,0x0,0x20589062000000000,0x200700000,0x20180,0x0,0x304400000,0x0,0xb0050,0x513c867a0,0xd1660],#[0x503d8038a07a00000,0x0,0x0,0x45900000000000000000,0x4216a18200000000d,0x0,0x6a001c2463870300000,0xf46a002d93520000b,0x0,0x35d2061b217000000000,0xb1160000000000005,0x0,0x95ec7690000000000000,0x5,0xe7790,0x0,0xe07300000,0xe861e0760,0x51360000000000000,0xe26be13e00000,0x0,0xe17c000000000,0xd64700000,0x246e01ad00cf109236e0,0x218b0750000936cc7551,0x3,0x0,0x17000000000000d5500,0xc36400004,0x90490000000000000,0x100000000000010840,0xe],#[0x0,0x0,0x80600,0x72600000000000000000,0xd,0x0,0xb0220000000000000,0x0,0x9111000000000,0x17f200000000000024e0,0x5,0x7400000000000011460,0xd25ac74300001,0x45a00000000000000000,0xa052000000003,0x0,0x107c00000,0x313900000,0x0,0xc05c0,0x0,0x807df04700000,0x47400000000000000000,0x2,0xb54b000000000,0x0,0x905b0000000015770,0x18400000000000000000,0xb1837,0x0,0x0,0x72900000000600300000],#[0x0,0x34100000000000000000,0x9,0x0,0x0,0x211c0000000000000,0x0,0x6800000000000000000,0xf,0x13800000000000000000,0x372a60809,0x0,0x101200000000202a0,0x5a70317067000000000,0xf,0x3516065804c000000000,0xf2440000000000000,0x9011734f0,0x675ed03f0000b0260,0x21850000000000000,0x0,0x55d0000b03e000071480,0x90810000c2138,0x0,0x10410000000000000,0xf00000000000000000,0x4,0x424500000,0x0,0x0,0x0,0x806f0],#[0x500b00000,0x0,0xb661000000000,0x501f0,0x0,0x0,0x7000000000000000000,0x0,0x0,0x0,0x70340000f05632630,0x101d000000000,0x0,0x5569000000000,0x0,0xf12d9540000000000,0x0,0x36db34c6037602e00000,0x7013000000005,0x0,0x0,0xe0270000000000000,0x70160000000000000,0x14012f0000000000000,0x3650040000000000005,0x61f00000000000000009,0x3,0x0,0x0,0x403b00000,0x21000000000937600000,0x6],#[0xd34d0000200200000,0x2211927400000,0x1350000487a000000000,0x5100000000f20d00003,0xe025e077724700000,0x10800000000000000000,0x3023000000000000a,0x0,0x0,0x0,0x0,0xb2120,0x0,0x0,0x0,0x3339783059e18600000,0x67b0000d12a2614517ed,0x860000b21900000000d,0x21673,0xd73900000,0x604300000,0xd13f0,0x10190,0x40550000000057830]]
def g243D10 (j : Nat) := if j=0 then 0x3f else 0
def g243H10 := limbs80 #[#[0x85c022a0a40080201480,0x180fc8c152080,0x5c60001e4600130e0000,0x85200000c000c4c512ea,0x866ea64b067e8e104ca2,0x200001cd250d0680000,0x806e10ee5e2368b6cfb1,0xd162870a6cc248000e62,0x4d2b8240c448944fae06,0x62092426400082b804e8,0x932ca000e910a046ac08,0xa000000001627e500002,0xcaa24540200000000060,0x10e2001a12]]
def g243L : Nat → Packing
  | 4 => (3,6,5,0,0,4,0,g243D4)
  | 5 => (192,5,5,0,0,11,0,g243D5)
  | 6 => (1104,4,5,0,0,14,0,g243D6)
  | 7 => (808,3,5,0,0,15,0,g243D7)
  | 8 => (136,2,5,0,0,13,0,g243D8)
  | 9 => (10,1,5,0,0,9,0,g243D9)
  | 10 => (1,0,5,0,0,0,0,g243D10)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 13 0 10 2 4 g243H5
  | 6 => lookupWord 88 409 8 16 8 4 g243H6
  | 7 => lookupWord 490 10037 3 19 11 4 g243H7
  | 8 => lookupWord 367 5443 4 18 10 4 g243H8
  | 9 => lookupWord 76 1553 3 16 8 4 g243H9
  | 10 => lookupWord 15 83 7 12 4 4 g243H10
  | _ => fun _ => none
def g243 : Forest := ⟨243,10,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P4_0 : block g243 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B4 : block g243 4 0 3=true := g243P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_0 : block g243 5 0 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P5_96 : block g243 5 96 96=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B5 : block g243 5 0 192=true := (@block_merge g243 5 0 96 96 g243P5_0 g243P5_96)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 2=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_2 : block g243 6 2 50=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_52 : block g243 6 52 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_148 : block g243 6 148 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_244 : block g243 6 244 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_340 : block g243 6 340 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_436 : block g243 6 436 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_532 : block g243 6 532 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_628 : block g243 6 628 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_724 : block g243 6 724 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_820 : block g243 6 820 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_916 : block g243 6 916 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_1012 : block g243 6 1012 92=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 1104=true := (@block_merge g243 6 0 436 668 (@block_merge g243 6 0 148 288 (@block_merge g243 6 0 2 146 g243P6_0 (@block_merge g243 6 2 50 96 g243P6_2 g243P6_52)) (@block_merge g243 6 148 96 192 g243P6_148 (@block_merge g243 6 244 96 96 g243P6_244 g243P6_340))) (@block_merge g243 6 436 288 380 (@block_merge g243 6 436 96 192 g243P6_436 (@block_merge g243 6 532 96 96 g243P6_532 g243P6_628)) (@block_merge g243 6 724 192 188 (@block_merge g243 6 724 96 96 g243P6_724 g243P6_820) (@block_merge g243 6 916 96 92 g243P6_916 g243P6_1012))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 8=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_8 : block g243 7 8 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_104 : block g243 7 104 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_200 : block g243 7 200 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_296 : block g243 7 296 45=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_341 : block g243 7 341 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_437 : block g243 7 437 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_533 : block g243 7 533 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_629 : block g243 7 629 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_725 : block g243 7 725 83=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 808=true := (@block_merge g243 7 0 341 467 (@block_merge g243 7 0 104 237 (@block_merge g243 7 0 8 96 g243P7_0 g243P7_8) (@block_merge g243 7 104 96 141 g243P7_104 (@block_merge g243 7 200 96 45 g243P7_200 g243P7_296))) (@block_merge g243 7 341 192 275 (@block_merge g243 7 341 96 96 g243P7_341 g243P7_437) (@block_merge g243 7 533 96 179 g243P7_533 (@block_merge g243 7 629 96 83 g243P7_629 g243P7_725))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_13 : block g243 8 13 51=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_64 : block g243 8 64 72=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 136=true := (@block_merge g243 8 0 13 123 g243P8_0 (@block_merge g243 8 13 51 72 g243P8_13 g243P8_64))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : block g243 9 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : block g243 9 0 10=true := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P10_0 : block g243 10 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B10 : block g243 10 0 1=true := g243P10_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact g243B4
  · exact g243B5
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
  · exact g243B10
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 11 := lower_forest (g:=g243) (i:=0) (hints:=65605) (before_sound K179 V179) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K179 11 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V179 low243 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xa0a298a637e918810,0xfe0007f01fc07f])),(BitVec.ofNat 152 (word80 [0x2022802622e100800,0xa142850a142850a14285]))),((BitVec.ofNat 152 (word80 [0x82a5781044047cb650,0x7f0000000fe03f80])),(BitVec.ofNat 152 (word80 [0x2057810440420b452,0x64c993264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1dd70285805cacb1a0,0x3f80000007f])),(BitVec.ofNat 152 (word80 [0x1d9102858050acb129,0x52a54a952a54a952a54a]))),((BitVec.ofNat 152 (word80 [0xc432269eb880be4c00,0x3f8001fc0000003f80])),(BitVec.ofNat 152 (word80 [0xc032028ea0809e4801,0x83060c183060c183060c]))),((BitVec.ofNat 152 (word80 [0x10a99b6d2c92c842a0,0x1fc0000000000fffc000])),(BitVec.ofNat 152 (word80 [0xa8036d0890c842a5,0xa142850a142850a1428]))),((BitVec.ofNat 152 (word80 [0x6154172348210167df,0xe0000001fffff0000000])),(BitVec.ofNat 152 (word80 [0x2044152008000106d6,0xc183060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x3f00c064938102186f,0xfffffffe000000000000])),(BitVec.ofNat 152 (word80 [0x1d0080001101000008,0x10204081020408102040]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(8,0,243,0,11)]
def g251A : List (List Nat) := [[],[96,84]]
def g251D11 (j : Nat) := if j=0 then 0xff else 0
def g251L : Nat → Packing
  | 11 => (1,0,1,0,0,0,0,g251D11)
  | _ => emptyPacking
def g251I (_ _ : Nat) : Option (Nat × Nat) := none
def g251 : Forest := ⟨251,11,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
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
  · exact (rfl : block g251 0 0 0 = true)
  · exact (rfl : block g251 1 0 0 = true)
  · exact (rfl : block g251 2 0 0 = true)
  · exact (rfl : block g251 3 0 0 = true)
  · exact (rfl : block g251 4 0 0 = true)
  · exact (rfl : block g251 5 0 0 = true)
  · exact (rfl : block g251 6 0 0 = true)
  · exact (rfl : block g251 7 0 0 = true)
  · exact (rfl : block g251 8 0 0 = true)
  · exact (rfl : block g251 9 0 0 = true)
  · exact (rfl : block g251 10 0 0 = true)
  · exact g251B11
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 12 := lower_forest (g:=g251) (i:=0) (hints:=65603) (before_sound K243 V243) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K243 12 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V243 low251 (by decide +kernel)
def g255Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x1027cf035042000000,0xff0000ff0000ff00ff])),(BitVec.ofNat 152 (word80 [0x10258a015040050505,0x5050505050505050505]))),((BitVec.ofNat 152 (word80 [0x22d40854496000000,0xff0000000000ff00ff00])),(BitVec.ofNat 152 (word80 [0xd40854012232323,0x23232323232323232323]))),((BitVec.ofNat 152 (word80 [0xf43812d0d0fd000000,0xff00000000])),(BitVec.ofNat 152 (word80 [0xf42812c0d0ddafafaf,0xafafafafafafafafafaf]))),((BitVec.ofNat 152 (word80 [0xe2c3a2baac17000000,0xff0000000000ff])),(BitVec.ofNat 152 (word80 [0xe24200baac179a9a9a,0x9a9a9a9a9a9a9a9a9a9a]))),((BitVec.ofNat 152 (word80 [0x4b7a8074da550000ff,0xff0000000000ff00])),(BitVec.ofNat 152 (word80 [0x4332807018451c1c1c,0x1c1c1c1c1c1c1c1c1c1c]))),((BitVec.ofNat 152 (word80 [0xa29211500b2900ff00,0xffffff0000])),(BitVec.ofNat 152 (word80 [0x29201100b20505050,0x50505050505050505050]))),((BitVec.ofNat 152 (word80 [0x5c88680d2a60ff0000,0xffffff0000000000])),(BitVec.ofNat 152 (word80 [0x88860040220606060,0x60606060606060606060]))),((BitVec.ofNat 152 (word80 [0x854404a2b588ffffff,0xffff0000000000000000])),(BitVec.ofNat 152 (word80 [0x84400402a488808080,0x80808080808080808080]))),(0x0,0x0)]
def g255C : List ColumnInfo := [(4,0,251,0,12)]
def g255A : List (List Nat) := [[]]
def g255D12 (j : Nat) := if j=0 then 0x1ff else 0
def g255L : Nat → Packing
  | 12 => (1,0,1,0,0,0,0,g255D12)
  | _ => emptyPacking
def g255I (_ _ : Nat) : Option (Nat × Nat) := none
def g255 : Forest := ⟨255,12,fun i => g255Y[i]?.getD (0,0),g255C,g255A,g255L,g255I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255P12_0 : block g255 12 0 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g255B12 : block g255 12 0 1=true := g255P12_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255T : checkedTables g255 12 := by
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
  · exact (rfl : block g255 11 0 0 = true)
  · exact g255B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255G : graphValid g255 (boundsBefore K251) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 12 sevenInputs.toFinset := by
  rw [show graph = targetOf g255 by decide +kernel]
  exact root_index (g:=g255) (top:=12) (i:=0) (before_sound K251 V251) g255G g255T (by decide) (by decide +kernel)

end PEqualNP.Outside.L_meta_32153

open PEqualNP.Outside.L_meta_32153 in
theorem PEqualNP.Outside.L_meta_32153 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), gates.length ≠ 14 → (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 1, 5, 2, 5, 0, 6, 3, 6, 4, 6, 0, 7, 1, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o width fit _ correct
  exact replaceShort g255R gates o width fit correct
