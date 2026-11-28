import PEqualNP.Defs

-- The two-mode live-state and cofactor checker follows L_meta_1674 and L_meta_670.
-- The graph, restrictions and all search certificates below are for L_meta_51786.

-- Shared forest and cofactor certificates from L_meta_1674 and PR 11111 for L_meta_1677.
-- The original credit line is retained below. The two root certificates here cover the unpinned graph.

-- The checker and the bound certificates are adapted from PEqualNP/Outside/L_meta_1667.lean (Apache-2.0).
-- Two modes: u=false are monotone runs (AND, OR); u=true are runs up to complement, where negation is free.
namespace PEqualNP.Outside.L_meta_51786
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
def graph : Sig := (BitVec.ofNat 512 (word80 [0xffffffff,0xffffffffffffffffffff,0xfefefffffffffffefffe,0xfffefffaeeccaa00ffff,0xffffffffffffffffffff,0xfffffefefffffffffffe,0xfffefffefffaeeccaa00]))
def sample (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)
def edge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 3) || (x 1 && x 4) || (x 0 && x 5) || (x 2 && x 5) || (x 3 && x 5) || (x 0 && x 6) || (x 1 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6) || (x 0 && x 7) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 5 && x 7) || (x 6 && x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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
  (x 0 &&& x 3) ||| (x 1 &&& x 4) ||| (x 0 &&& x 5) ||| (x 2 &&& x 5) ||| (x 3 &&& x 5) ||| (x 0 &&& x 6) ||| (x 1 &&& x 6) ||| (x 2 &&& x 6) ||| (x 3 &&& x 6) ||| (x 5 &&& x 6) ||| (x 0 &&& x 7) ||| (x 1 &&& x 7) ||| (x 2 &&& x 7) ||| (x 4 &&& x 7) ||| (x 5 &&& x 7) ||| (x 6 &&& x 7)
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



def target (x : Fin 8 → Bool) : Bool := decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)
def smallCircuit : Circuit := ⟨[⟨.or,[0,5]⟩,⟨.or,[6,7]⟩,⟨.or,[0,2]⟩,⟨.or,[1,8]⟩,⟨.or,[4,6]⟩,⟨.or,[6,8]⟩,⟨.or,[1,7]⟩,⟨.or,[5,9]⟩,⟨.and,[14,12]⟩,⟨.and,[13,3]⟩,⟨.and,[15,10]⟩,⟨.and,[9,11]⟩,⟨.or,[16,17]⟩,⟨.or,[20,18]⟩,⟨.or,[21,19]⟩], 22⟩

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
def K41 := extendKnown [] 4 [(41,[]),(73,[101]),(97,[83,67,100]),(100,[32,16,83,67,100]),(104,[48,16,33,82,66,100]),(146,[16,67,117,101]),(161,[83,67,116,100]),(193,[99,67,117]),(194,[16,99,67,117])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V41 : Known true K41 := extend_ok (m:=41) baseKnown low41 (by decide +kernel)
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
theorem g45P4_0 : block g45 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g45B4 : block g45 4 0 1=true := g45P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45T : checkedTables g45 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g45 0 0 0 = true)
  · exact (rfl : block g45 1 0 0 = true)
  · exact (rfl : block g45 2 0 0 = true)
  · exact (rfl : block g45 3 0 0 = true)
  · exact g45B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g45G : graphValid g45 (boundsBefore K41) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low45 : Lower true (varsX 45) (graphGoal 45) 5 := lower_forest (g:=g45) (i:=0) (hints:=1283) (before_sound K41 V41) g45G g45T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K45 := extendKnown K41 5 [(45,[]),(75,[33,101]),(99,[33,83,67,100]),(147,[16,32,67,117,101]),(163,[33,83,67,116,100]),(172,[32,16,49,113,65,100]),(177,[66,83,115,99]),(178,[16,82,67,50,115,99]),(202,[16,50,114,66,101,84]),(240,[80,16,66,99,33,114,50])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V45 : Known true K45 := extend_ok (m:=45) V41 low45 (by decide +kernel)
def g83Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x2fc38ff01fff1ff02,0xfc38ff01fff1ff02fc38])),(BitVec.ofNat 152 (word80 [0x42ccdb2a5451240242,0xccdb2a5451240242ccdb]))),((BitVec.ofNat 152 (word80 [0xfdcbc7fffe07fe3ffd,0xcbc7fffe07fe3ffdcbc7])),(BitVec.ofNat 152 (word80 [0x1448490c1860408414,0x48490c18604084144849]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xece607fffff8003fec,0xe607fffff8003fece607])),(BitVec.ofNat 152 (word80 [0x8a7b6b06085892808,0xa7b6b06085892808a7b6]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1b3df8ffffffffc01b,0x3df8ffffffffc01b3df8])),(BitVec.ofNat 152 (word80 [0x893124c08106003089,0x3124c081060030893124]))),(0x0,0x0),(0x0,0x0)]
def g83C : List ColumnInfo := []
def g83A : List (List Nat) := [[],[64,97]]
def g83D3 (j : Nat) := if j=0 then 0xf else 0
def g83L : Nat → Packing
  | 3 => (1,0,1,0,0,0,0,g83D3)
  | _ => emptyPacking
def g83I (_ _ : Nat) : Option (Nat × Nat) := none
def g83 : Forest := ⟨83,3,fun i => g83Y[i]?.getD (0,0),g83C,g83A,g83L,g83I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83P3_0 : block g83 3 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g83B3 : block g83 3 0 1=true := g83P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83T : checkedTables g83 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g83 0 0 0 = true)
  · exact (rfl : block g83 1 0 0 = true)
  · exact (rfl : block g83 2 0 0 = true)
  · exact g83B3
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g83G : graphValid g83 (boundsBefore K45) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low83 : Lower true (varsX 83) (graphGoal 83) 4 := lower_forest (g:=g83) (i:=0) (hints:=65606) (before_sound K45 V45) g83G g83T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K83 := extendKnown K45 4 [(83,[]),(90,[48,32]),(114,[64,97,32,50,83]),(139,[16,67,118]),(153,[48,113,33,32,96]),(170,[16,80,32,50,67,118]),(184,[48,113,32,33,82,101]),(216,[48,113,32,33,82])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V83 : Known true K83 := extend_ok (m:=83) V45 low83 (by decide +kernel)
def g101Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe7d01c7fc0fc7cfe7,0xd01c7fc0fc7cfe7d01c7])),(BitVec.ofNat 152 (word80 [0x51d124928a290a051,0xd124928a290a051d1249]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3f8b8e38fff007f3f8,0xb8e38fff007f3f8b8e38])),(BitVec.ofNat 152 (word80 [0x884b924930c3210884,0xb924930c3210884b9249]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x3fe7703ffffff803fe,0x7703ffffff803fe7703f])),(BitVec.ofNat 152 (word80 [0x100024924104020100,0x2492410402010002492]))),((BitVec.ofNat 152 (word80 [0xc018ffc0fffffffc01,0x8ffc0fffffffc018ffc0])),(BitVec.ofNat 152 (word80 [0x200049248208040200,0x4924820804020004924]))),(0x0,0x0),(0x0,0x0)]
def g101C : List ColumnInfo := [(1,0,100,0,4)]
def g101A : List (List Nat) := [[],[101],[32],[32,101]]
def g101D4 (j : Nat) := if j=0 then 0x1f else 0
def g101L : Nat → Packing
  | 4 => (1,0,1,0,0,0,0,g101D4)
  | _ => emptyPacking
def g101I (_ _ : Nat) : Option (Nat × Nat) := none
def g101 : Forest := ⟨101,4,fun i => g101Y[i]?.getD (0,0),g101C,g101A,g101L,g101I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101P4_0 : block g101 4 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g101B4 : block g101 4 0 1=true := g101P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101T : checkedTables g101 4 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g101 0 0 0 = true)
  · exact (rfl : block g101 1 0 0 = true)
  · exact (rfl : block g101 2 0 0 = true)
  · exact (rfl : block g101 3 0 0 = true)
  · exact g101B4
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g101G : graphValid g101 (boundsBefore K83) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low101 : Lower true (varsX 101) (graphGoal 101) 5 := lower_forest (g:=g101) (i:=0) (hints:=1285) (before_sound K83 V83) g101G g101T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K101 := extendKnown K83 5 [(165,[118]),(169,[48,114,32,80,101]),(195,[33,101,117]),(210,[64,16,98,50,49,81,117]),(232,[48,16,114,66])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V101 : Known true K101 := extend_ok (m:=101) V83 low101 (by decide +kernel)
def g105Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xdf7ec03c3ffe0fbefd,0x80787ffc1f7dfb00f0ff])),(BitVec.ofNat 152 (word80 [0x820404444444210408,0x8888888420810111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fbf43c3c3fff03f7e,0x878787ffe07efd0f0f0f])),(BitVec.ofNat 152 (word80 [0x40808888888420810,0x11111110841020222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xe03fbc03fc3fffc07f,0x7807f87fff80fef00ff0])),(BitVec.ofNat 152 (word80 [0x81011111110841020,0x22222221082040444444]))),((BitVec.ofNat 152 (word80 [0xffc03ffc003fffff80,0x7ff8007fffff00fff000])),(BitVec.ofNat 152 (word80 [0x102022222221082040,0x44444442104080888888]))),(0x0,0x0),(0x0,0x0)]
def g105C : List ColumnInfo := [(1,0,104,0,4),(8,0,97,0,4),(32,0,73,0,4),(64,0,41,0,4)]
def g105A : List (List Nat) := [[],[101],[83],[83,99],[99,83],[99],[48],[48,101],[48,80],[48,80,96],[48,96,80],[48,96],[80,48],[80,48,99],[80],[80,96],[80,99],[80,99,48],[96,48,83],[96,48],[96,80],[96],[96,83,48],[96,83]]
def g105D3 := limbs80 #[#[0x23ea6a1221e12148110,0x8028]]
def g105D4 := limbs80 #[#[0x2fd0910bd42443e48110,0x609085870]]
def g105H4 (j : Nat) := if j=0 then 0x1800000088000 else 0
def g105D5 (j : Nat) := if j=0 then 0xd1027d10 else 0
def g105H5 := limbs80 #[#[0x200000000001e2,0x2200001fc610,0x1e1430008a000]]
def g105D6 (j : Nat) := if j=0 then 0x3904f else 0
def g105H6 := limbs80 #[#[0x0,0x5680000094000049000,0x2c0000090002]]
def g105L : Nat → Packing
  | 3 => (2,3,2,0,0,5,0,g105D3)
  | 4 => (3,2,2,0,0,5,0,g105D4)
  | 5 => (1,1,2,0,0,0,0,g105D5)
  | 6 => (1,0,2,0,0,0,0,g105D6)
  | _ => emptyPacking
def g105I : Nat → Nat → Option (Nat × Nat)
  | 4 => lookupWord 1 11 0 5 1 0 g105H4
  | 5 => lookupWord 2 23 1 9 2 3 g105H5
  | 6 => lookupWord 1 23 0 9 0 5 g105H6
  | _ => fun _ => none
def g105 : Forest := ⟨105,6,fun i => g105Y[i]?.getD (0,0),g105C,g105A,g105L,g105I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P3_0 : block g105 3 0 2=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B3 : block g105 3 0 2=true := g105P3_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P4_0 : block g105 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B4 : block g105 4 0 3=true := g105P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P5_0 : block g105 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B5 : block g105 5 0 1=true := g105P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105P6_0 : block g105 6 0 1=true := by
  apply cellsBlock (ar:=4) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g105B6 : block g105 6 0 1=true := g105P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105T : checkedTables g105 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g105 0 0 0 = true)
  · exact (rfl : block g105 1 0 0 = true)
  · exact (rfl : block g105 2 0 0 = true)
  · exact g105B3
  · exact g105B4
  · exact g105B5
  · exact g105B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g105G : graphValid g105 (boundsBefore K101) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low105 : Lower true (varsX 105) (graphGoal 105) 7 := lower_forest (g:=g105) (i:=0) (hints:=3) (before_sound K101 V101) g105G g105T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K105 := extendKnown K101 7 [(105,[]),(225,[83,67,100,116]),(228,[32,16,83,67,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V105 : Known true K105 := extend_ok (m:=105) V101 low105 (by decide +kernel)
def g59Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc00fff0ffffffc00ff,0xfff0fffeea3a5303f03f])),(BitVec.ofNat 152 (word80 [0x84a08a210802284a02,0x80220882200a53145145]))),((BitVec.ofNat 152 (word80 [0xfff0000ffc3fffff00,0x3fffffc009adfd000fc0])),(BitVec.ofNat 152 (word80 [0xc42c405090b10c4b,0x11404108092d994d34d3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff0003fffffff,0xc000fffd77e88afc003f])),(BitVec.ofNat 152 (word80 [0x90130026104c0100c,0x584120152a08828a28a]))),((BitVec.ofNat 152 (word80 [0x3fffffff,0xffff00012697f4000fc0])),(BitVec.ofNat 152 (word80 [0x2e09c08b8227026090,0x26009c11269264b2cb2c]))),((BitVec.ofNat 152 (word80 [0xffffffffffc0000000,0x39d530dfff000])),(BitVec.ofNat 152 (word80 [0x300e000c00380380e0,0x3808e0208d5104c30c30]))),(0x0,0x0),(0x0,0x0),(0x0,0x0)]
def g59C : List ColumnInfo := [(0,2,41,16,5)]
def g59A : List (List Nat) := [[],[83],[65],[65,83],[48],[48,80],[48,65],[48,65,80],[80,48],[80],[80,65,48],[80,65]]
def g59D5 (j : Nat) := if j=0 then 0x3f else 0
def g59L : Nat → Packing
  | 5 => (1,0,1,0,0,0,0,g59D5)
  | _ => emptyPacking
def g59I (_ _ : Nat) : Option (Nat × Nat) := none
def g59 : Forest := ⟨59,5,fun i => g59Y[i]?.getD (0,0),g59C,g59A,g59L,g59I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59P5_0 : block g59 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g59B5 : block g59 5 0 1=true := g59P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59T : checkedTables g59 5 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g59 0 0 0 = true)
  · exact (rfl : block g59 1 0 0 = true)
  · exact (rfl : block g59 2 0 0 = true)
  · exact (rfl : block g59 3 0 0 = true)
  · exact (rfl : block g59 4 0 0 = true)
  · exact g59B5
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g59G : graphValid g59 (boundsBefore K105) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low59 : Lower true (varsX 59) (graphGoal 59) 6 := lower_forest (g:=g59) (i:=0) (hints:=65603) (before_sound K105 V105) g59G g59T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K59 := extendKnown K105 6 [(59,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V59 : Known true K59 := extend_ok (m:=59) V105 low59 (by decide +kernel)
def g91Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf003ff87fe1fffc01f,0xfff87fffe474a4007c1f])),(BitVec.ofNat 152 (word80 [0xa12845108440228940,0xa01108826014a45294a5]))),((BitVec.ofNat 152 (word80 [0xfffc0007ffe1ffffe0,0xfffffc0335be20f83e0])),(BitVec.ofNat 152 (word80 [0xc030162028040b0182,0xc0a00108225922318c63]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff80001ffffff,0xf0007ffccfd11df0001f])),(BitVec.ofNat 152 (word80 [0x240980130884c0203,0x2c2120087c108a5294a]))),((BitVec.ofNat 152 (word80 [0x1ffffff,0xffff80004d2fe80003e0])),(BitVec.ofNat 152 (word80 [0xb82e045c111702c14,0xb005c104d26c9ce739c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffe000000,0x33aa61bfffc00])),(BitVec.ofNat 152 (word80 [0xc0300060001803018,0xc046021182211084210]))),(0x0,0x0),(0x0,0x0)]
def g91C : List ColumnInfo := [(0,16,73,2,5),(16,0,75,0,5),(1,0,90,0,4),(2,16,73,0,4),(8,0,83,0,4)]
def g91A : List (List Nat) := [[],[48]]
def g91D4 (j : Nat) := if j=0 then 0x5bd4940 else 0
def g91D5 := limbs80 #[#[0x240d140ff40fd40fd20,0x2012]]
def g91H5 (j : Nat) := if j=0 then 0xd else 0
def g91D6 (j : Nat) := if j=0 then 0x18989f else 0
def g91H6 := limbs80 #[#[0xa008005200000000001a,0x118000f]]
def g91L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g91D4)
  | 5 => (3,1,3,0,0,5,0,g91D5)
  | 6 => (1,0,3,0,0,0,0,g91D6)
  | _ => emptyPacking
def g91I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g91H5
  | 6 => lookupWord 1 19 0 7 2 1 g91H6
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
theorem g91P5_0 : block g91 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g91B5 : block g91 5 0 3=true := g91P5_0
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
theorem low91 : Lower true (varsX 91) (graphGoal 91) 7 := lower_forest (g:=g91) (i:=0) (hints:=65603) (before_sound K59 V59) g91G g91T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K91 := extendKnown K59 7 [(91,[]),(115,[83]),(122,[48,32,82]),(155,[16,67,118]),(186,[16,80,32,67,118])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V91 : Known true K91 := extend_ok (m:=91) V59 low91 (by decide +kernel)
def g107Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff00ff87f87ffc0,0x7fc7ffffd3b94000f0ff])),(BitVec.ofNat 152 (word80 [0x1440a0a05101100285,0x2902008418941111111]))),((BitVec.ofNat 152 (word80 [0x1ffff0007ff87fff,0x8007f1fc231ee00f0000])),(BitVec.ofNat 152 (word80 [0x588ac4c5622a012b06,0x2b214491231ee7777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffff80007fff,0xfff801ff9c1f30f00f0f])),(BitVec.ofNat 152 (word80 [0x61030101800c220c08,0xc0188201c1602222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe000000000007fff,0xfffffe000be4bf000ff0])),(BitVec.ofNat 152 (word80 [0x800c06060430443010,0x300200c20260b4444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffff8000,0x6442cffff000])),(BitVec.ofNat 152 (word80 [0x1008080040004020,0x40040100000008888888]))),(0x0,0x0),(0x0,0x0)]
def g107C : List ColumnInfo := [(2,0,105,0,7)]
def g107A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g107D7 (j : Nat) := if j=0 then 0x3f else 0
def g107L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g107D7)
  | _ => emptyPacking
def g107I (_ _ : Nat) : Option (Nat × Nat) := none
def g107 : Forest := ⟨107,7,fun i => g107Y[i]?.getD (0,0),g107C,g107A,g107L,g107I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107P7_0 : block g107 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g107B7 : block g107 7 0 1=true := g107P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107T : checkedTables g107 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g107 0 0 0 = true)
  · exact (rfl : block g107 1 0 0 = true)
  · exact (rfl : block g107 2 0 0 = true)
  · exact (rfl : block g107 3 0 0 = true)
  · exact (rfl : block g107 4 0 0 = true)
  · exact (rfl : block g107 5 0 0 = true)
  · exact (rfl : block g107 6 0 0 = true)
  · exact g107B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g107G : graphValid g107 (boundsBefore K91) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low107 : Lower true (varsX 107) (graphGoal 107) 8 := lower_forest (g:=g107) (i:=0) (hints:=99) (before_sound K91 V91) g107G g107T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K107 := extendKnown K91 8 [(107,[]),(241,[65,33,83,99,115])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V107 : Known true K107 := extend_ok (m:=107) V91 low107 (by decide +kernel)
def g109Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff0ff01fe3f8ffe0,0x3fc7f1ffd675000f00ff])),(BitVec.ofNat 152 (word80 [0xa0a20a14148120142,0x82902402163411111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff000fffe003ff1fff,0xc007fe3f317a00f00f00])),(BitVec.ofNat 152 (word80 [0x2c2c42c18590a04583,0xb214084b17a33333333]))),((BitVec.ofNat 152 (word80 [0xffffffc001fff,0xfff8003fede10f00f00f])),(BitVec.ofNat 152 (word80 [0x303083020600c48604,0xc01890829c122222222]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffff0000000001fff,0xffffffc01388f000fff0])),(BitVec.ofNat 152 (word80 [0x404004040801000808,0x10020010000044444444]))),((BitVec.ofNat 152 (word80 [0xffffffffffffffe000,0x2816ffff0000])),(BitVec.ofNat 152 (word80 [0x808008081002001010,0x20040020000088888888]))),(0x0,0x0),(0x0,0x0)]
def g109C : List ColumnInfo := [(4,0,105,0,7)]
def g109A : List (List Nat) := [[],[101],[48],[48,101]]
def g109D7 (j : Nat) := if j=0 then 0x3f else 0
def g109L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g109D7)
  | _ => emptyPacking
def g109I (_ _ : Nat) : Option (Nat × Nat) := none
def g109 : Forest := ⟨109,7,fun i => g109Y[i]?.getD (0,0),g109C,g109A,g109L,g109I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109P7_0 : block g109 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g109B7 : block g109 7 0 1=true := g109P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109T : checkedTables g109 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g109 0 0 0 = true)
  · exact (rfl : block g109 1 0 0 = true)
  · exact (rfl : block g109 2 0 0 = true)
  · exact (rfl : block g109 3 0 0 = true)
  · exact (rfl : block g109 4 0 0 = true)
  · exact (rfl : block g109 5 0 0 = true)
  · exact (rfl : block g109 6 0 0 = true)
  · exact g109B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g109G : graphValid g109 (boundsBefore K107) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low109 : Lower true (varsX 109) (graphGoal 109) 8 := lower_forest (g:=g109) (i:=0) (hints:=1283) (before_sound K107 V107) g109G g109T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K109 := extendKnown K107 8 [(227,[33,83,67,100,116])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V109 : Known true K109 := extend_ok (m:=109) V107 low109 (by decide +kernel)
def g171Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc03ffff0fffc03f,0xf0ffffffe8561e00f0ff])),(BitVec.ofNat 152 (word80 [0x202828140220028280,0xa2020020880612111111]))),((BitVec.ofNat 152 (word80 [0xffffc01fff0ffffc0,0xff0ff00cb5790f0000])),(BitVec.ofNat 152 (word80 [0x42b1315854022b030a,0xc4142242089579777777]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffe0000ffffff,0xff000fff33b526000f0f])),(BitVec.ofNat 152 (word80 [0x88c0406118448c2423,0x98488032b104aaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf00000000000ffffff,0xfffff000134bf8f00ff0])),(BitVec.ofNat 152 (word80 [0x3018180608830080c,0x200304014868444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff000000,0xcea8c5fff000])),(BitVec.ofNat 152 (word80 [0xc0202018000c03030,0x8c08c08462084888888]))),(0x0,0x0)]
def g171C : List ColumnInfo := [(0,2,41,128,5),(2,0,169,0,5),(8,0,163,0,5),(1,0,170,0,4),(32,0,139,0,4),(128,2,41,0,4)]
def g171A : List (List Nat) := [[],[80]]
def g171D4 (j : Nat) := if j=0 then 0x5bd4930 else 0
def g171D5 (j : Nat) := if j=0 then 0xc8404fd30 else 0
def g171H5 (j : Nat) := if j=0 then 0x5 else 0
def g171D6 (j : Nat) := if j=0 then 0x232a8bf else 0
def g171H6 (j : Nat) := if j=0 then 0xb0 else 0
def g171L : Nat → Packing
  | 4 => (1,2,3,0,0,0,0,g171D4)
  | 5 => (1,1,3,0,0,0,0,g171D5)
  | 6 => (1,0,3,0,0,0,0,g171D6)
  | _ => emptyPacking
def g171I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 2 0 4 0 0 g171H5
  | 6 => lookupWord 1 2 0 4 0 0 g171H6
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
  · exact (rfl : block g171 0 0 0 = true)
  · exact (rfl : block g171 1 0 0 = true)
  · exact (rfl : block g171 2 0 0 = true)
  · exact (rfl : block g171 3 0 0 = true)
  · exact g171B4
  · exact g171B5
  · exact g171B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g171G : graphValid g171 (boundsBefore K109) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low171 : Lower true (varsX 171) (graphGoal 171) 7 := lower_forest (g:=g171) (i:=0) (hints:=115) (before_sound K109 V109) g171G g171T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K171 := extendKnown K109 7 [(171,[]),(185,[65,33]),(217,[65,33,101]),(218,[16,48,32,66,117,101]),(248,[80,65,32,98])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V171 : Known true K171 := extend_ok (m:=171) V109 low171 (by decide +kernel)
def g173Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfe1ff01fffe3ffc03f,0xe1fe1fffb19d500f00ff])),(BitVec.ofNat 152 (word80 [0x1440a1414048028281,0x44044008218911111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffe01ffc7fffc0,0x1ffe1fc6d3a20f00f00])),(BitVec.ofNat 152 (word80 [0x5882c18582810b0305,0x882804112d3823333333]))),((BitVec.ofNat 152 (word80 [0x1fffffe0007fffff,0xfe0001ff9e1bc000f00f])),(BitVec.ofNat 152 (word80 [0x6113020613124c2426,0x13089201e12caaaaaaa]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffe0000000007fffff,0xfffffe000be08f00fff0])),(BitVec.ofNat 152 (word80 [0x800404080400100808,0x400040000004444444]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffffffff800000,0x6446ffff0000])),(BitVec.ofNat 152 (word80 [0x1808101800603030,0x118111824046c8888888]))),(0x0,0x0)]
def g173C : List ColumnInfo := [(1,0,172,0,5),(4,0,169,0,5),(8,0,165,0,5),(128,0,45,0,5)]
def g173A : List (List Nat) := [[],[112,50]]
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
  · exact (rfl : block g173 0 0 0 = true)
  · exact (rfl : block g173 1 0 0 = true)
  · exact (rfl : block g173 2 0 0 = true)
  · exact (rfl : block g173 3 0 0 = true)
  · exact (rfl : block g173 4 0 0 = true)
  · exact (rfl : block g173 5 0 0 = true)
  · exact g173B6
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g173G : graphValid g173 (boundsBefore K171) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low173 : Lower true (varsX 173) (graphGoal 173) 7 := lower_forest (g:=g173) (i:=0) (hints:=1283) (before_sound K171 V171) g173G g173T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K173 := extendKnown K171 7 [(203,[33,101]),(211,[16,32,67,117,101]),(234,[80,16,33,66,100]),(242,[96,16,66,83,115,49])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V173 : Known true K173 := extend_ok (m:=173) V171 low173 (by decide +kernel)
def g179Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xffc00ff87fc3fff00,0xffffffe257e300007fe0])),(BitVec.ofNat 152 (word80 [0x20a82a051048802a2a,0xa12004a546306318c63]))),((BitVec.ofNat 152 (word80 [0xfffff0007ffc3ffff,0xff1ffd9276c00f801f])),(BitVec.ofNat 152 (word80 [0x42308c262110088c0c,0x4c0444811226ca5294a5]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffffff80003ffff,0xff001ffce8f541f0001f])),(BitVec.ofNat 152 (word80 [0x84c130480261113030,0x10588900e8d114a5294a]))),((BitVec.ofNat 152 (word80 [0xf0000000000003ffff,0xffffe0005f98fe0003e0])),(BitVec.ofNat 152 (word80 [0x701c070438221c040,0x60600e100b98d8c6318c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffffffffffc0000,0x3280bbffffc00])),(BitVec.ofNat 152 (word80 [0x80200800400020080,0x80801000000021084210]))),(0x0,0x0)]
def g179C : List ColumnInfo := [(1,0,178,0,5),(2,0,177,0,5),(16,0,163,0,5),(32,0,147,0,5),(18,0,161,0,4),(33,0,146,0,4)]
def g179A : List (List Nat) := [[],[65],[16,84],[16,80,64],[64,16,81],[64,81],[80],[80,65]]
def g179D4 := limbs80 #[#[0x9bd89544426d6215110,0x31826f625474]]
def g179D5 := limbs80 #[#[0x7c54443f2808857d4d40,0xfea8885f95110beaa221,0x7d4d40bfa8a81fb40502,0xcc8d018160c02faa3a07,0x882188201161080d176b,0x8118204c10001]]
def g179H5 (j : Nat) := if j=0 then 0x200d85100a9b0 else 0
def g179D6 := limbs80 #[#[0x540a0380ff40fd40fd10,0x2150c8543]]
def g179H6 := limbs80 #[#[0x80003610031100000140,0x19350800d0fc9704,0x85420d985dc700254000,0x61800712]]
def g179D7 (j : Nat) := if j=0 then 0x1605f else 0
def g179H7 := limbs80 #[#[0x600000191ba0018869,0x334002080000,0x30400e65c800b9003a8]]
def g179L : Nat → Packing
  | 4 => (3,3,3,0,0,4,0,g179D4)
  | 5 => (10,2,3,0,0,7,0,g179D5)
  | 6 => (3,1,3,0,0,6,0,g179D6)
  | 7 => (1,0,3,0,0,0,0,g179D7)
  | _ => emptyPacking
def g179I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 7 0 8 2 2 g179H5
  | 6 => lookupWord 4 29 3 10 4 2 g179H6
  | 7 => lookupWord 3 31 0 9 2 3 g179H7
  | _ => fun _ => none
def g179 : Forest := ⟨179,7,fun i => g179Y[i]?.getD (0,0),g179C,g179A,g179L,g179I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P4_0 : block g179 4 0 3=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B4 : block g179 4 0 3=true := g179P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_0 : block g179 5 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P5_1 : block g179 5 1 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B5 : block g179 5 0 10=true := (@block_merge g179 5 0 1 9 g179P5_0 g179P5_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P6_0 : block g179 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B6 : block g179 6 0 3=true := g179P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179P7_0 : block g179 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g179B7 : block g179 7 0 1=true := g179P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179T : checkedTables g179 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g179 0 0 0 = true)
  · exact (rfl : block g179 1 0 0 = true)
  · exact (rfl : block g179 2 0 0 = true)
  · exact (rfl : block g179 3 0 0 = true)
  · exact g179B4
  · exact g179B5
  · exact g179B6
  · exact g179B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g179G : graphValid g179 (boundsBefore K173) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low179 : Lower true (varsX 179) (graphGoal 179) 8 := lower_forest (g:=g179) (i:=0) (hints:=65605) (before_sound K173 V173) g179G g179T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K179 := extendKnown K173 8 [(179,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V179 : Known true K179 := extend_ok (m:=179) V173 low179 (by decide +kernel)
def g229Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x7f01fc7f01fc7e7fc,0x7f1f9fe7ea000f00f0f])),(BitVec.ofNat 152 (word80 [0x50a14290a142905028,0x50a414051ea111111111]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x7ffe007ffe007f9ff,0xf801fe7f8b700f00f0f0])),(BitVec.ofNat 152 (word80 [0x60c18320c183208430,0x60c821084b7111111111]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xf8000007fffff801ff,0xfffe007fe640f00f00ff])),(BitVec.ofNat 152 (word80 [0x810204010204010040,0x81004010000222222222]))),((BitVec.ofNat 152 (word80 [0xfffffff800000001ff,0xffffff8001af000fff00])),(BitVec.ofNat 152 (word80 [0x20408020408020081,0x2008020000444444444]))),((BitVec.ofNat 152 (word80 [0xfffffffffffffffe00,0x181ffff00000])),(BitVec.ofNat 152 (word80 [0x40810040810040102,0x4010040000888888888]))),(0x0,0x0)]
def g229C : List ColumnInfo := [(1,0,228,0,7)]
def g229A : List (List Nat) := [[],[118],[101],[101,117],[117,101],[117],[32],[32,118],[32,101],[32,101,117],[32,117,101],[32,117]]
def g229D7 (j : Nat) := if j=0 then 0x3f else 0
def g229L : Nat → Packing
  | 7 => (1,0,1,0,0,0,0,g229D7)
  | _ => emptyPacking
def g229I (_ _ : Nat) : Option (Nat × Nat) := none
def g229 : Forest := ⟨229,7,fun i => g229Y[i]?.getD (0,0),g229C,g229A,g229L,g229I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229P7_0 : block g229 7 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g229B7 : block g229 7 0 1=true := g229P7_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229T : checkedTables g229 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g229 0 0 0 = true)
  · exact (rfl : block g229 1 0 0 = true)
  · exact (rfl : block g229 2 0 0 = true)
  · exact (rfl : block g229 3 0 0 = true)
  · exact (rfl : block g229 4 0 0 = true)
  · exact (rfl : block g229 5 0 0 = true)
  · exact (rfl : block g229 6 0 0 = true)
  · exact g229B7
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g229G : graphValid g229 (boundsBefore K179) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low229 : Lower true (varsX 229) (graphGoal 229) 8 := lower_forest (g:=g229) (i:=0) (hints:=1285) (before_sound K179 V179) g229G g229T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K229 := extendKnown K179 8 [(233,[48,114,32,80,101])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V229 : Known true K229 := extend_ok (m:=229) V179 low229 (by decide +kernel)
def g123Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff60ac8,0x4caee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060880,0x400ce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe021c2c,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208221c28,0x3c941264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0x81210b01fc000fe0007f])),(BitVec.ofNat 152 (word80 [0x400c0160809009404a,0x12103142850a142850a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x691ab200000000003f80])),(BitVec.ofNat 152 (word80 [0x8290298014e04820d7,0x6812b2d9b366cd9b366c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803700,0xa2821060c183060c1830]))),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801008015,0x1c000481020408102040]))),(0x0,0x0),(0x0,0x0)]
def g123C : List ColumnInfo := [(0,16,105,2,8),(16,0,107,0,8),(1,0,122,0,7),(2,16,105,0,7),(8,0,115,0,7),(32,0,91,0,7),(64,0,59,0,6),(9,0,114,0,4),(33,0,90,0,4),(40,0,83,0,4)]
def g123A : List (List Nat) := [[],[83],[48],[48,80],[80,48],[80]]
def g123D4 (j : Nat) := if j=0 then 0x1a2b6460b5454120 else 0
def g123D5 := limbs80 #[#[0x50940483aa5954250120,0x483ca5515250120eab65,0x5915254120d697554940,0x54120e6b64549504839a,0xb6982d51504835add152,0x5d9544838ed935454120,0x4832ed9170d51208fb80,0x1d37059520a3d85d9354,0x8d01d345ca0d141c032e,0x8080002836294c]]
def g123H5 (j : Nat) := if j=0 then 0x3a8000 else 0
def g123D6 := limbs80 #[#[0x3b4a92a0907a94250120,0xfd2a4a02412fdd16548,0x837db2a80906f9655012,0x20fd6e4a8241fa549504,0x483bdaa2a09077954541,0x120df6c8a8241be59150,0x44833eb2aa8905fb7454,0x51209feecaa2413f5d95,0x544835fb26a8905f970d,0x591209faedaa2419f597,0x1654827ebaec8904ff75,0x59520b7ee8b2a417edc,0xd1654835e3a2ca906fb7,0x70995209fee8b2a41afd,0x5d3654827ebb4ca905f9,0xb7054950bf6e0a92a13f,0xfd93525433fb22a4a877,0xbf7458950afae9a92a19,0x3fdd162d427eba6c4a85,0x78a8431e4d85f258a401,0x5610fb7aba1b6d564309,0x75a2b74ea0cee5d288dc,0xee46ef5da1cde3b037bb,0x8178f049085f3f6ba9c,0x82141100f1e010649ce1,0x810000808205c7806102,0x80101c4080141c80801,0x400e0e2043820700400a,0x8604002005041020050,0x35040000a8]]
def g123H6 := limbs80 #[#[0xbe4e000861b305e8210,0xd09a5c00000f61e268a0,0x7a0400507000f2400506,0x80000000a00355000e2,0xd4d246c432c2210,0x123c516a5d8800000000,0x562200020c00]]
def g123D7 := limbs80 #[#[0xf59120fe54120fe50120,0xd9520bf59520bfd9120b,0x8950dfd4950df54950bf,0x120ff55120bf58b50bfd,0x20ff59520ff59120ffd5,0xff58950ff54950ff995,0x90ba2585a0c000ffd895,0xc9ce691865a144481023,0xb1c159079aa528ba107,0x648b3242c461f3906207,0x3186c55cc7149207c465,0x522105c731c4c4792217,0x54d62cc51e2cd41851b3,0x51c6185887105506cc4c,0x88710920789516245019,0xf1c065221624501c4195,0x60940c75540]]
def g123H7 := limbs80 #[#[0x3978905508c946840346,0x105631299000044524c0,0x83d323e295c2840768a,0x1e087896425acd124621,0x30000a14d08da4140ea6,0x8242fa8501bc4df5011,0x8990020d034400020272,0xa2084e000240a0000004,0x844c19d698885d12,0x404304c682702e08344b,0xc5a7c00101ba0b498a03,0x38404201522c01660e60,0x220074000623000781bc,0xc1880f0005803c3f2c34,0x1114448a15124933d]]
def g123D8 := limbs80 #[#[0xc79aa407fd43faa1fd20,0x98d13568298d131ea414,0x1ad046]]
def g123H8 := limbs80 #[#[0x9020000000204,0x10500,0xa2f000b10,0xa50d6260000000000000,0xe4000010f40,0xd06000000,0x100000000080436b0000,0x33,0x501000000000000000,0x0,0xd4100000,0x8700000000002860e611,0xa300007,0xe4700000000000,0xa09000,0x2032270003089079290,0x72400b00092100,0x30000000000050c16a]]
def g123D9 (j : Nat) := if j=0 then 0x1542317f else 0
def g123H9 := limbs80 #[#[0xeac88002402020800000,0xd4fb283]]
def g123L : Nat → Packing
  | 4 => (1,5,4,0,0,0,0,g123D4)
  | 5 => (13,4,4,0,0,7,0,g123D5)
  | 6 => (39,3,4,0,0,9,0,g123D6)
  | 7 => (18,2,4,0,0,10,0,g123D7)
  | 8 => (3,1,4,0,0,7,0,g123D8)
  | 9 => (1,0,4,0,0,0,0,g123D9)
  | _ => emptyPacking
def g123I : Nat → Nat → Option (Nat × Nat)
  | 5 => lookupWord 1 5 0 6 0 2 g123H5
  | 6 => lookupWord 7 47 4 11 4 3 g123H6
  | 7 => lookupWord 18 83 6 13 6 3 g123H7
  | 8 => lookupWord 8 127 2 12 5 3 g123H8
  | 9 => lookupWord 2 13 0 9 2 3 g123H9
  | _ => fun _ => none
def g123 : Forest := ⟨123,9,fun i => g123Y[i]?.getD (0,0),g123C,g123A,g123L,g123I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P4_0 : block g123 4 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B4 : block g123 4 0 1=true := g123P4_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P5_0 : block g123 5 0 13=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B5 : block g123 5 0 13=true := g123P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_0 : block g123 6 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P6_3 : block g123 6 3 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B6 : block g123 6 0 39=true := (@block_merge g123 6 0 3 36 g123P6_0 g123P6_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_0 : block g123 7 0 10=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P7_10 : block g123 7 10 8=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B7 : block g123 7 0 18=true := (@block_merge g123 7 0 10 8 g123P7_0 g123P7_10)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123P8_0 : block g123 8 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g123B8 : block g123 8 0 3=true := g123P8_0
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
  · exact g123B4
  · exact g123B5
  · exact g123B6
  · exact g123B7
  · exact g123B8
  · exact g123B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g123G : graphValid g123 (boundsBefore K229) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low123 : Lower true (varsX 123) (graphGoal 123) 10 := lower_forest (g:=g123) (i:=0) (hints:=65603) (before_sound K229 V229) g123G g123T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K123 := extendKnown K229 10 [(123,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V123 : Known true K123 := extend_ok (m:=123) V229 low123 (by decide +kernel)
def g187Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0x3fffffc1ffff64acc,0x4aee8000007f01fc07f])),(BitVec.ofNat 152 (word80 [0x280280084044060884,0xce80a142850a14285]))),((BitVec.ofNat 152 (word80 [0xfc003ffffffe029c28,0x13d9d30003f800003f80])),(BitVec.ofNat 152 (word80 [0x304b04500208229c28,0x3c940264c993264c993]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffc0001ffffbf0cb,0xa1210b0000000fe0007f])),(BitVec.ofNat 152 (word80 [0x420c2160909009c04b,0x212103952a54a952a54a]))),((BitVec.ofNat 152 (word80 [0xffffffffe0000824f7,0x491ab201fc0000003f80])),(BitVec.ofNat 152 (word80 [0x8090098004e04820d6,0x4012b258b162c58b162c]))),((BitVec.ofNat 152 (word80 [0x93710,0xa28774fe00000fffc000])),(BitVec.ofNat 152 (word80 [0xe00e010700803710,0x82821060c183060c1830]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x4c917,0x7e4005fffffff0000000])),(BitVec.ofNat 152 (word80 [0x30030021801004001,0x3c000581020408102040]))),(0x0,0x0)]
def g187C : List ColumnInfo := [(8,0,179,0,8),(1,0,186,0,7),(2,0,185,0,7),(16,0,171,0,7),(32,0,155,0,7),(0,2,41,144,6),(0,8,146,33,6),(0,16,41,130,6),(128,0,59,0,6),(1,8,146,32,5),(2,16,41,128,5),(18,0,169,0,5),(32,8,146,1,5),(128,2,41,16,5),(128,16,41,2,5),(33,0,146,0,4),(33,8,146,0,4),(130,0,41,0,4),(130,16,41,0,4)]
def g187A : List (List Nat) := [[],[65],[80],[80,65]]
def g187D5 := limbs80 #[#[0xd8b5150333dcf6254540,0x1832edd370595408ed87,0x1004003]]
def g187D6 := limbs80 #[#[0x276baec4a07395454140,0xf76e8a8281ee5515050,0x377b12a2a06ef624c54,0x40bf2e1a8a8177dcd515,0x5027ebb6a2a06ef62d45,0x150bf6e0aa2a1bedc165,0xb0027fba2c1a8f7b7055,0xc632c1448c3f1c0c4441,0xf142207803c687401e4d,0x68811004238040306071,0x81a882040707002a30,0x201100780402060]]
def g187H6 (j : Nat) := if j=0 then 0xa7e02c else 0
def g187D7 := limbs80 #[#[0xb54b50db54950bbd8940,0x58b51b7d8d51bb58b50d,0x9540fe54140bfd9110bb,0x150df55150fb54950bf5,0x51bf59350bfd9150dfd5,0xff54540ff4c540bf583,0xff59150ff55150ffd454,0x881198520a400ffd9150,0x1d066570555253f0d32a,0x70abdadba927b94a1b80,0xc63b10d202e3c5103411,0x843e01a2c11a3031a402,0x3c10468b2b1c210245c9,0xc160203478b80410143e,0x1b812411470d201870a0,0x1101878e13070241a38e,0x10840e386900f0070a0c,0x8a8a0c01614542131cac,0x2a2830100f1d1c180442,0x1040240402c02080624]]
def g187H7 := limbs80 #[#[0x1801e3c0495800007c04,0x515e6fb00050ba,0x830000000106513a,0x5800f5000000cf6a8000,0x382002d9a27900]]
def g187D8 := limbs80 #[#[0xf50fea87f503fa21ed52,0x685400ffa8ff547fa63f,0x2238d4069c439c8c0481,0x389020408a8c180d1e30,0x92388e04d80720714182,0xa40a180b34610e060345,0x12a38022079038458121,0x92]]
def g187H8 := limbs80 #[#[0x180d10001630021,0x0,0x1868000000000000000,0x88000000000000000,0xb0b20800000000,0x4000000c06c722200109,0x6040000000049,0x485a96000004090,0x30f41c00000000000,0x702f2600000000001ec,0x4900000000000c0e0000,0x503000000007,0x16700000000000306,0x50b0000004500000,0xd620]]
def g187D9 (j : Nat) := if j=0 then 0x41882017f else 0
def g187H9 := limbs80 #[#[0xb2803dd41000002,0x100000719300,0xdc80000004a000000000,0x71d120000180c800,0x0,0x4c00000000001c300000,0x4bc0000007]]
def g187L : Nat → Packing
  | 5 => (3,4,5,0,0,4,0,g187D5)
  | 6 => (14,3,5,0,0,9,0,g187D6)
  | 7 => (21,2,5,0,0,10,0,g187D7)
  | 8 => (8,1,5,0,0,9,0,g187D8)
  | 9 => (1,0,5,0,0,0,0,g187D9)
  | _ => emptyPacking
def g187I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 5 0 6 2 0 g187H6
  | 7 => lookupWord 5 37 3 10 4 2 g187H7
  | 8 => lookupWord 7 107 2 11 5 2 g187H8
  | 9 => lookupWord 3 59 2 9 3 2 g187H9
  | _ => fun _ => none
def g187 : Forest := ⟨187,9,fun i => g187Y[i]?.getD (0,0),g187C,g187A,g187L,g187I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P5_0 : block g187 5 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B5 : block g187 5 0 3=true := g187P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_0 : block g187 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P6_2 : block g187 6 2 12=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B6 : block g187 6 0 14=true := (@block_merge g187 6 0 2 12 g187P6_0 g187P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_0 : block g187 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_6 : block g187 7 6 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P7_15 : block g187 7 15 6=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B7 : block g187 7 0 21=true := (@block_merge g187 7 0 6 15 g187P7_0 (@block_merge g187 7 6 9 6 g187P7_6 g187P7_15))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_0 : block g187 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187P8_1 : block g187 8 1 7=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g187B8 : block g187 8 0 8=true := (@block_merge g187 8 0 1 7 g187P8_0 g187P8_1)
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
  · exact g187B5
  · exact g187B6
  · exact g187B7
  · exact g187B8
  · exact g187B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g187G : graphValid g187 (boundsBefore K123) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low187 : Lower true (varsX 187) (graphGoal 187) 10 := lower_forest (g:=g187) (i:=0) (hints:=65603) (before_sound K123 V123) g187G g187T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K187 := extendKnown K123 10 [(187,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V187 : Known true K187 := extend_ok (m:=187) V123 low187 (by decide +kernel)
def g219Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xc007ffffe0ffff72a6,0xa10baa00000fc003f03f])),(BitVec.ofNat 152 (word80 [0x82500a004204403202,0x21032a05145145145145]))),((BitVec.ofNat 152 (word80 [0xfff800ffffffe03d4a,0x8666308003f000fc0fc0])),(BitVec.ofNat 152 (word80 [0x602c02800082350a,0x844210030c30c30c30c3]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xffffff0000ffffad84,0xb85846c000003f00003f])),(BitVec.ofNat 152 (word80 [0x2084308b0489000d84,0x985804eaaaaaaaaaaaaa]))),((BitVec.ofNat 152 (word80 [0xffffffffff0000804d,0x6156adc0fc0000000fc0])),(BitVec.ofNat 152 (word80 [0xb01402c002e048045,0x2114a9dc71c71c71c71c]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x9171,0x18b1d83f00003ffff000])),(BitVec.ofNat 152 (word80 [0xc0180300830088071,0x20c010410410410410]))),((BitVec.ofNat 152 (word80 [0x4e93,0x4f80057fffffc0000000])),(BitVec.ofNat 152 (word80 [0x300600c010c0104880,0x4a800420820820820820]))),(0x0,0x0)]
def g219C : List ColumnInfo := [(1,0,218,0,7),(2,0,217,0,7),(8,0,211,0,7),(16,0,203,0,7),(64,0,155,0,7),(128,0,91,0,7),(0,8,146,65,6),(0,16,73,130,6),(1,8,146,64,5),(2,16,73,128,5),(9,0,210,0,5),(17,0,202,0,5),(24,0,195,0,5),(64,8,146,1,5),(72,0,147,0,5),(128,16,73,2,5),(144,0,75,0,5),(3,0,216,0,4),(25,0,194,0,4),(26,0,193,0,4),(65,0,146,0,4),(65,8,146,0,4),(66,0,153,0,4),(73,0,146,0,4),(129,0,90,0,4),(130,0,73,0,4),(130,16,73,0,4),(146,0,73,0,4)]
def g219A : List (List Nat) := [[],[16,67,118]]
def g219D5 := limbs80 #[#[0x55140443cc5515150110,0x443cc5514154110e3965,0x5537154140e396455150,0x50d50ccf73d89515034e,0x40b6785b54603c6e0154,0x40]]
def g219D6 := limbs80 #[#[0x3b4a92a08870d5450d52,0x9daebb1281ce5515050,0x43f8a8a808871d5450d5,0x10df2caa0221ee551404,0x442fcbaa80886fb65501,0x110ef2a8a8221fc50550,0x4437db22a0886f96454,0x5110d7ac8aa2217edd15,0x644427fbb2a8884fd765,0x545209faebb22213fdd5,0x951502fdb8aa0a05df73,0x3d8940e7aa8a8a81bbd8,0xc165503ddb82a8a06ed5,0x54505509fee2b2a81bed,0x55361543b6a92c2a873d,0xb70551509fae9b0aa19f,0xf5c764542fdb82c8a877,0x6f7155152edae2aa2a53,0x5a0f0160027eb8ec0aa7,0x123f0de340c22b0961c0,0xaa6518e5a15251136481,0x127d1e6781da731c6701,0x929f266962529121e862,0x1f8c605441a150ab6aa2,0x6c01a101b102c705150f,0x4041011511098e88204c,0x5086811a150854880430,0x30210541421504541150,0x1c0c2060208007060,0x1817150c541000a304,0x2050401a04643e8e8440,0x21a058c6820703086054],#[0x1c0c]]
def g219H6 := limbs80 #[#[0x35ce00e316590100008,0x8400902b0000520]]
def g219D7 := limbs80 #[#[0x350d52db54950bbd8940,0x90e52db55152f390d52f,0x4910fe54110fe50110f3,0x110bf59110fb94910fb5,0x40ef55140fe54140bfd9,0xf750d50bfd8550bf595,0xbfd9150df55150f790d5,0xfd8154fbd8552bfd8552,0x54520ff59110ff55110b,0x550ff54d40ff54540ff,0xd42ff59150ff58550ff5,0xffd8154ff58154ff54,0x1f8314550880da164180,0x686d001de35c5c0a712c,0x55962fc5a6a8d47a7b49,0x21c2180cf91e4b996fcd,0xc3003441a5eca291d1ce,0x19a2a118c38c795172e3,0x548483c38c795122a32a,0x841a18b914f8d1412a3c,0x4a5c4c72529510d98228,0x62c460870a0cb9522092,0xcc474a5442e1c2832a44,0xc60383025ca8d1d2950,0x6ca8468a846c3040468c,0x30260a8a623261f0120c,0x228d143838a2210d1838,0x2a4438a1c1812a2a3522,0x18a0c19628444224831a,0x52c242201c34708c9411,0x8a8664c111e8d08c68c1,0x52a118445431c182308]]
def g219H7 := limbs80 #[#[0xa4b0240f4c9690a40002,0x1da6323001c500068a,0xa27d1a00e9a00,0xec8000aa0000000,0x3a200000000000000000,0xf0000000071000162c00,0x9b704f10101c,0x290000003,0x93e00000000000,0x2e0000058f00000,0x0,0x147656000001638,0x3c2096d30000ce792,0x8403695000001a580000,0x640000004300000043be,0x38800000282800532000,0x120c003e3e2200000,0x3868000000000000]]
def g219D8 := limbs80 #[#[0xd30fe907f443dca5ed52,0xa5fd42fe997f543fa81f,0xd257240a82a007f553fa,0xf8e11551b557aae4fa04,0x22324024f8c28455c608,0x4b3c5961352111065922,0x81495c70a58e15472222,0x10c3492046009228633c,0x83e3842148347953388,0x218233e23451]]
def g219H8 := limbs80 #[#[0x998221021188101150,0x8859110e32c0a00f3e00,0xc7f07a4ba354af12d616,0x85ce4918001655852,0x2840074ba0487400000,0x6e0f0e1001817a442000,0xc200090c2464e000ac0a,0xa19626001e860700110e,0xee1c001cb610b89e6b86,0x29b36ad90b7ac0022904,0x8f3]]
def g219D9 (j : Nat) := if j=0 then 0xa4188201bf else 0
def g219H9 := limbs80 #[#[0xc8800000090,0x3200000000068401e7,0xd0000000000000000044,0x18000000000000000159,0x21200000,0x7e00000000cc00000,0x800750000159007952a0,0x1c0f80024600000022]]
def g219L : Nat → Packing
  | 5 => (7,4,5,0,0,6,0,g219D5)
  | 6 => (38,3,5,0,0,10,0,g219D6)
  | 7 => (34,2,5,0,0,11,0,g219D7)
  | 8 => (11,1,5,0,0,9,0,g219D8)
  | 9 => (1,0,5,0,0,0,0,g219D9)
  | _ => emptyPacking
def g219I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 2 17 2 8 3 1 g219H6
  | 7 => lookupWord 12 127 3 11 6 1 g219H7
  | 8 => lookupWord 13 67 6 11 6 1 g219H8
  | 9 => lookupWord 4 71 2 9 4 1 g219H9
  | _ => fun _ => none
def g219 : Forest := ⟨219,9,fun i => g219Y[i]?.getD (0,0),g219C,g219A,g219L,g219I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P5_0 : block g219 5 0 7=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B5 : block g219 5 0 7=true := g219P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_0 : block g219 6 0 1=true := by
  apply cellsBlock (ar:=5) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_1 : block g219 6 1 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P6_5 : block g219 6 5 33=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B6 : block g219 6 0 38=true := (@block_merge g219 6 0 1 37 g219P6_0 (@block_merge g219 6 1 4 33 g219P6_1 g219P6_5))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_0 : block g219 7 0 6=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_6 : block g219 7 6 17=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P7_23 : block g219 7 23 11=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B7 : block g219 7 0 34=true := (@block_merge g219 7 0 6 28 g219P7_0 (@block_merge g219 7 6 17 11 g219P7_6 g219P7_23))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_0 : block g219 8 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g219P8_2 : block g219 8 2 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g219B8 : block g219 8 0 11=true := (@block_merge g219 8 0 2 9 g219P8_0 g219P8_2)
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
theorem low219 : Lower true (varsX 219) (graphGoal 219) 10 := lower_forest (g:=g219) (i:=0) (hints:=65603) (before_sound K187 V187) g219G g219T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K219 := extendKnown K187 10 [(219,[]),(250,[80,32])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V219 : Known true K219 := extend_ok (m:=219) V187 low219 (by decide +kernel)
def g235Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xfffc01ffc3ffffffa2,0xa4b358000f8000f83ff])),(BitVec.ofNat 152 (word80 [0x2814028804002002,0xa0b1404210842108421]))),((BitVec.ofNat 152 (word80 [0x1ffffe0003fe1ff049,0x38c78e801f0001f00000])),(BitVec.ofNat 152 (word80 [0x42b0182b1028424209,0x38c78c9ce739ce739ce7]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1ffffffffc001ffffd,0xa141580000003e007c1f])),(BitVec.ofNat 152 (word80 [0x90c2210c02309080fd,0x140484a5294a5294a52]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0x1fffffffffffe00010,0xfe246883e007c0007fe0])),(BitVec.ofNat 152 (word80 [0x30040300040030400,0xf0242090842108421084]))),((BitVec.ofNat 152 (word80 [0xe0000000000000000e,0x1132807c0007ffff8000])),(BitVec.ofNat 152 (word80 [0x40080400080040000,0x21084210842108]))),((BitVec.ofNat 152 (word80 [0xc1,0x459c477ffff800000000])),(BitVec.ofNat 152 (word80 [0x1803018023011808c0,0x5104342108421084210]))),(0x0,0x0)]
def g235C : List ColumnInfo := [(2,0,233,0,8),(8,0,227,0,8),(128,0,107,0,8),(1,0,234,0,7),(32,0,203,0,7),(64,0,171,0,7),(0,2,41,192,6),(3,0,232,0,5),(33,0,202,0,5),(64,2,41,128,5),(65,0,170,0,4),(96,0,139,0,4)]
def g235A : List (List Nat) := [[],[80]]
def g235D5 (j : Nat) := if j=0 then 0x2f8e097350110 else 0
def g235D6 := limbs80 #[#[0x379b1a80887b14350110,0x9dee4b2261e650d404c,0x377b92c8987f1735011,0x471eda9652017bdc9635,0x2d03f211a0ae22790b61,0x2c98f970104f1e4204e,0x41622]]
def g235H6 (j : Nat) := if j=0 then 0x2 else 0
def g235D7 := limbs80 #[#[0xdd8d10bd58d10fc50110,0x59130fe50130fd50d10b,0x8d40bfd8d40ef50d40bf,0xa379688a331205400ff5,0x479122141e98e448d388,0x3298c79122e2a64388a,0x41656046588c52a4e391,0x618e450a5942e18e4a46,0x16522408a]]
def g235H7 := limbs80 #[#[0xe4e60000b55078e25190,0x5300]]
def g235D8 := limbs80 #[#[0x88a4b807f503fa61f510,0x1ca3846481807356838c,0x2a851c612]]
def g235H8 := limbs80 #[#[0xc800000020600,0x7a00001250000000,0x4d43e60100000000001c,0x128802]]
def g235D9 (j : Nat) := if j=0 then 0x5431201bf else 0
def g235H9 := limbs80 #[#[0x80000e00000000002849,0x6a5]]
def g235L : Nat → Packing
  | 5 => (1,4,4,0,0,0,0,g235D5)
  | 6 => (7,3,4,0,0,8,0,g235D6)
  | 7 => (9,2,4,0,0,9,0,g235D7)
  | 8 => (3,1,4,0,0,7,0,g235D8)
  | 9 => (1,0,4,0,0,0,0,g235D9)
  | _ => emptyPacking
def g235I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 1 2 0 4 0 0 g235H6
  | 7 => lookupWord 2 11 4 8 3 1 g235H7
  | 8 => lookupWord 2 29 0 9 4 1 g235H8
  | 9 => lookupWord 1 13 0 7 2 1 g235H9
  | _ => fun _ => none
def g235 : Forest := ⟨235,9,fun i => g235Y[i]?.getD (0,0),g235C,g235A,g235L,g235I⟩
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
theorem g235P6_0 : block g235 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P6_4 : block g235 6 4 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B6 : block g235 6 0 7=true := (@block_merge g235 6 0 4 3 g235P6_0 g235P6_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_0 : block g235 7 0 3=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_3 : block g235 7 3 5=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P7_8 : block g235 7 8 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B7 : block g235 7 0 9=true := (@block_merge g235 7 0 3 6 g235P7_0 (@block_merge g235 7 3 5 1 g235P7_3 g235P7_8))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_0 : block g235 8 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P8_1 : block g235 8 1 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B8 : block g235 8 0 3=true := (@block_merge g235 8 0 1 2 g235P8_0 g235P8_1)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235P9_0 : block g235 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g235B9 : block g235 9 0 1=true := g235P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235T : checkedTables g235 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g235 0 0 0 = true)
  · exact (rfl : block g235 1 0 0 = true)
  · exact (rfl : block g235 2 0 0 = true)
  · exact (rfl : block g235 3 0 0 = true)
  · exact (rfl : block g235 4 0 0 = true)
  · exact g235B5
  · exact g235B6
  · exact g235B7
  · exact g235B8
  · exact g235B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g235G : graphValid g235 (boundsBefore K219) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low235 : Lower true (varsX 235) (graphGoal 235) 10 := lower_forest (g:=g235) (i:=0) (hints:=99) (before_sound K219 V219) g235G g235T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K235 := extendKnown K219 10 [(235,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V235 : Known true K235 := extend_ok (m:=235) V219 low235 (by decide +kernel)
def g243Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff801ffffffff818e7,0x982a5000000fc003ffc0])),(BitVec.ofNat 152 (word80 [0x1505405024001118c3,0x982040c30c30c30c30c3]))),((BitVec.ofNat 152 (word80 [0xffffe007fe1fffbb0a,0x3491700003f000fc003f])),(BitVec.ofNat 152 (word80 [0x460182600841203a02,0x4817145145145145145]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffffff8001fffd03d,0x3b712000fc000000003f])),(BitVec.ofNat 152 (word80 [0x98260882b08a40403d,0x3b70069a69a69a69a69a]))),((BitVec.ofNat 152 (word80 [0xffffffffffe000462a,0x89c7903f00003f000fc0])),(BitVec.ofNat 152 (word80 [0xe0080300c003820628,0x1c3930c30c30c30c30c]))),((BitVec.ofNat 152 (word80 [0x4984,0x67ac8fc000003ffff000])),(BitVec.ofNat 152 (word80 [0x300c03010c044104,0x620c0410410410410410]))),((BitVec.ofNat 152 (word80 [0x2651,0x42404fffffffc0000000])),(BitVec.ofNat 152 (word80 [0x4010040010000000,0x820820820820820]))),(0x0,0x0)]
def g243C : List ColumnInfo := [(2,0,241,0,8),(16,0,227,0,8),(64,0,179,0,8),(1,0,242,0,7),(32,0,211,0,7),(128,0,115,0,7),(33,0,210,0,5),(129,0,114,0,4),(160,0,83,0,4)]
def g243A : List (List Nat) := [[],[80]]
def g243D6 := limbs80 #[#[0xe3c1243e437595354130,0x5]]
def g243D7 := limbs80 #[#[0xf54d50bf59530fe54130,0x42a00ff58d50bfd8d50d,0xc32187c70572186ae8a5,0x481c5c705328c82071b1,0x81c60d4c70c871]]
def g243H7 (j : Nat) := if j=0 then 0xf0 else 0
def g243D8 := limbs80 #[#[0xa38c2461a403faa1fd30,0x1e851c6121c]]
def g243H8 := limbs80 #[#[0x8300620000440000,0x910018]]
def g243D9 (j : Nat) := if j=0 then 0x5431021bf else 0
def g243H9 (j : Nat) := if j=0 then 0x2fe78000 else 0
def g243L : Nat → Packing
  | 6 => (1,3,4,0,0,0,0,g243D6)
  | 7 => (5,2,4,0,0,8,0,g243D7)
  | 8 => (2,1,4,0,0,6,0,g243D8)
  | 9 => (1,0,4,0,0,0,0,g243D9)
  | _ => emptyPacking
def g243I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 2 0 4 0 0 g243H7
  | 8 => lookupWord 1 17 0 8 3 1 g243H8
  | 9 => lookupWord 1 5 0 6 1 1 g243H9
  | _ => fun _ => none
def g243 : Forest := ⟨243,9,fun i => g243Y[i]?.getD (0,0),g243C,g243A,g243L,g243I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P6_0 : block g243 6 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B6 : block g243 6 0 1=true := g243P6_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_0 : block g243 7 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P7_4 : block g243 7 4 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B7 : block g243 7 0 5=true := (@block_merge g243 7 0 4 1 g243P7_0 g243P7_4)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P8_0 : block g243 8 0 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B8 : block g243 8 0 2=true := g243P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243P9_0 : block g243 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g243B9 : block g243 9 0 1=true := g243P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243T : checkedTables g243 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g243 0 0 0 = true)
  · exact (rfl : block g243 1 0 0 = true)
  · exact (rfl : block g243 2 0 0 = true)
  · exact (rfl : block g243 3 0 0 = true)
  · exact (rfl : block g243 4 0 0 = true)
  · exact (rfl : block g243 5 0 0 = true)
  · exact g243B6
  · exact g243B7
  · exact g243B8
  · exact g243B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g243G : graphValid g243 (boundsBefore K235) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low243 : Lower true (varsX 243) (graphGoal 243) 10 := lower_forest (g:=g243) (i:=0) (hints:=65605) (before_sound K235 V235) g243G g243T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K243 := extendKnown K235 10 [(243,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V243 : Known true K243 := extend_ok (m:=243) V235 low243 (by decide +kernel)
def g249Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xf801fffff83fffffc8,0xd60a4540007c00f83ff])),(BitVec.ofNat 152 (word80 [0x9024010090800102c0,0x8400054210842108421]))),(0x0,0x0),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xfffe007fffc1fffd97,0xa1015784000001f07c1f])),(BitVec.ofNat 152 (word80 [0x24090a412005020112,0xa10147025294a5294a52]))),((BitVec.ofNat 152 (word80 [0xffffff800001ff80d7,0xc5fc404800f800000000])),(BitVec.ofNat 152 (word80 [0xc1304c15c1085408c7,0x85fc4049ef7bdef7bdef]))),((BitVec.ofNat 152 (word80 [0xfffffffffffe000021,0x2ed47a201f003e007fe0])),(BitVec.ofNat 152 (word80 [0x4010060000181021,0x4843800842108421084]))),((BitVec.ofNat 152 (word80 [0x44,0x903f89b3e0003fff8000])),(BitVec.ofNat 152 (word80 [0x18060180210602004,0x103880a1084210842108]))),((BitVec.ofNat 152 (word80 [0x33a,0x528a034bffffc0000000])),(BitVec.ofNat 152 (word80 [0x60180600421804118,0x42020302108421084210]))),(0x0,0x0)]
def g249C : List ColumnInfo := [(0,16,105,128,8),(8,0,241,0,8),(16,0,233,0,8),(1,0,248,0,7),(32,0,217,0,7),(64,0,185,0,7),(128,16,105,0,7),(33,0,216,0,4),(65,0,184,0,4),(96,0,153,0,4)]
def g249A : List (List Nat) := [[],[101],[80],[80,96],[96,80],[96]]
def g249D6 := limbs80 #[#[0x27bb8ac8987994350130,0xdeee2b22617ddc5644c,0x820bc927187d86bf1180,0x3901e01e3e5c03e5d]]
def g249D7 := limbs80 #[#[0xfd9130bf59130fe50130,0x690884603600ff59130b,0x2481f2c761881c3cb157,0x78d1572c08572c761c5,0x92]]
def g249H7 (j : Nat) := if j=0 then 0x6e401c0 else 0
def g249D8 (j : Nat) := if j=0 then 0xf2a9071b0ffd30 else 0
def g249H8 (j : Nat) := if j=0 then 0x53c10000206248 else 0
def g249D9 (j : Nat) := if j=0 then 0x5423161bf else 0
def g249H9 (j : Nat) := if j=0 then 0x93c0000700000000 else 0
def g249L : Nat → Packing
  | 6 => (4,3,4,0,0,7,0,g249D6)
  | 7 => (4,2,4,0,0,8,0,g249D7)
  | 8 => (1,1,4,0,0,0,0,g249D8)
  | 9 => (1,0,4,0,0,0,0,g249D9)
  | _ => emptyPacking
def g249I : Nat → Nat → Option (Nat × Nat)
  | 7 => lookupWord 1 5 0 6 2 0 g249H7
  | 8 => lookupWord 1 7 0 8 2 2 g249H8
  | 9 => lookupWord 1 17 0 6 0 2 g249H9
  | _ => fun _ => none
def g249 : Forest := ⟨249,9,fun i => g249Y[i]?.getD (0,0),g249C,g249A,g249L,g249I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_0 : block g249 6 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P6_2 : block g249 6 2 2=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B6 : block g249 6 0 4=true := (@block_merge g249 6 0 2 2 g249P6_0 g249P6_2)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_0 : block g249 7 0 3=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P7_3 : block g249 7 3 1=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B7 : block g249 7 0 4=true := (@block_merge g249 7 0 3 1 g249P7_0 g249P7_3)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P8_0 : block g249 8 0 1=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B8 : block g249 8 0 1=true := g249P8_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249P9_0 : block g249 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g249B9 : block g249 9 0 1=true := g249P9_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249T : checkedTables g249 9 := by
  intro k hk
  interval_cases k
  · exact (rfl : block g249 0 0 0 = true)
  · exact (rfl : block g249 1 0 0 = true)
  · exact (rfl : block g249 2 0 0 = true)
  · exact (rfl : block g249 3 0 0 = true)
  · exact (rfl : block g249 4 0 0 = true)
  · exact (rfl : block g249 5 0 0 = true)
  · exact g249B6
  · exact g249B7
  · exact g249B8
  · exact g249B9
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g249G : graphValid g249 (boundsBefore K243) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low249 : Lower true (varsX 249) (graphGoal 249) 10 := lower_forest (g:=g249) (i:=0) (hints:=458755) (before_sound K243 V243) g249G g249T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K249 := extendKnown K243 10 [(249,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V249 : Known true K249 := extend_ok (m:=249) V243 low249 (by decide +kernel)
def g251Y : Array (Bits × Bits) := #[((BitVec.ofNat 152 (word80 [0xff000000ff00f,0xf00ff00864431431bf6b])),(BitVec.ofNat 152 (word80 [0x505050505050505050,0x50505008200114109d00]))),((BitVec.ofNat 152 (word80 [0xff000000ff00000,0xff00041b88498cdcf10])),(BitVec.ofNat 152 (word80 [0x313131313131313131,0x31313040a880984d8710]))),(0x0,0x0),((BitVec.ofNat 152 (word80 [0xff0000ff0,0xff491c018e30e73f8])),(BitVec.ofNat 152 (word80 [0xa8a8a8a8a8a8a8a8a8,0xa8a8a491c00881046210]))),((BitVec.ofNat 152 (word80 [0xff000000000000000,0xff0091e031f03f07c10])),(BitVec.ofNat 152 (word80 [0xc6c6c6c6c6c6c6c6c6,0xc6c6c91a031f03b07800]))),((BitVec.ofNat 152 (word80 [0xf000000ff000000fff,0xf00001e003e003ff80a5])),(BitVec.ofNat 152 (word80 [0x30303030303030303,0x3030140018002e90000]))),((BitVec.ofNat 152 (word80 [0xffffffff000,0xe0003fffc0000c6])),(BitVec.ofNat 152 (word80 [0x40404040404040404,0x4040800023640000000]))),((BitVec.ofNat 152 (word80 [0xfffffff00000000000,0xffffc0000000000])),(BitVec.ofNat 152 (word80 [0x80808080808080808,0x80806a5540000000000]))),(0x0,0x0)]
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(0,16,105,130,9),(2,16,105,128,8),(10,0,241,0,8),(18,0,233,0,8),(24,0,227,0,8),(72,0,179,0,8),(128,16,105,2,8),(144,0,107,0,8),(0,2,41,208,7),(0,8,146,97,7),(3,0,248,0,7),(9,0,242,0,7),(17,0,234,0,7),(26,0,225,0,7),(33,0,218,0,7),(34,0,217,0,7),(40,0,211,0,7),(48,0,203,0,7),(65,0,186,0,7),(66,0,185,0,7),(80,0,171,0,7),(96,0,155,0,7),(129,0,122,0,7),(130,0,105,0,7),(130,16,105,0,7),(136,0,115,0,7),(146,0,105,0,7),(160,0,91,0,7),(1,8,146,96,6),(1,16,104,130,6),(8,16,97,130,6),(16,2,41,192,6),(32,8,146,65,6),(32,16,73,130,6),(64,2,41,144,6),(64,8,146,33,6),(64,16,41,130,6),(128,2,41,80,6),(192,0,59,0,6),(11,0,240,0,5),(33,8,146,64,5),(41,0,210,0,5),(49,0,202,0,5),(65,8,146,32,5),(73,0,178,0,5),(74,0,177,0,5),(88,0,163,0,5),(96,8,146,1,5),(104,0,147,0,5),(152,0,99,0,5),(192,2,41,16,5),(35,0,216,0,4),(57,0,194,0,4),(67,0,184,0,4),(97,0,146,0,4),(97,8,146,0,4),(98,0,153,0,4),(105,0,146,0,4),(131,0,104,0,4),(131,16,104,0,4),(137,0,114,0,4),(138,0,97,0,4),(138,16,97,0,4),(161,0,90,0,4),(162,0,73,0,4),(162,16,73,0,4),(168,0,83,0,4),(194,0,41,0,4),(194,16,41,0,4),(152,64,0,35,2)]
def g251A : List (List Nat) := [[],[80]]
def g251D5 := limbs80 #[#[0xc29b56d1a62497558140,0xebc0661a62497558540c,0xfc5661a62497558540a0,0xb8ec1a75955358940a06,0x628ba065f8159540d848,0x6c1a62497559540a0e9c,0xc1a6209815d540cc29b4,0x1a6209815d540c8a9b46,0xa6209815d540c869b56c,0x658825d540c865b56c5,0x658825d540e429a5691a,0x182430300c469a56c3a1,0x12a2305490f,0x1ac30200]]
set_option maxRecDepth 16000 in
def g251D6 := limbs80 #[#[0x81b82691a05955358940,0x550307454740cbacab12,0x2eaa064a9a4681962097,0x6154110c8d34ad032c41,0xa2c4a8221b98597a2611,0x95458950443e155bac8a,0xd32a8b12a0887a2bb461,0x9da55916254110d8d16e,0x5dd30dba2c4a8221b1aa,0xa6bb5691865895044347,0xb8736d53ac8aa2a0885,0x22151e6da97655645411,0x60443a34bb2cbc9308a8,0xa2c0887a298561154589,0x95458110b8736b4bac8a,0xc8284b0a2151e6d69765,0x539050961443b90aa2a5,0xb53ac8aa2c4887631655,0x6d6a76595458910b85b6,0x1edd50eb2ac8aa22151b,0x7e216550961545404826,0x20eb12ebc9a84b0a8090,0x241d62dd79350961501,0x5404839c4c2f26a12c2a,0xb0a8090738b85e4d4258,0x96150120af136bc9a84,0x6a92c2a0241e8a615655,0xe4d5258540483b84aa72,0xeaaa726b0a8090734985,0x2553935096154120ea32,0x3a4d2f26a12c2a8241dc,0x754974e4d5258550483],#[0x120ea96e9c9aa4b0aa09,0xa8241cd2e13935496154,0x8551483a8cba2a9c9ac2,0x9c1ac2905c37b469d655,0xa1f8159520939f64d3aa,0x48c0ac2a828106fed1a9,0x4e4f7258550503718b2f,0x2a9c9f04b0aa0a075195,0x8c6d3a15956154140e63,0x3a1dcb2ecaa2e2a82817,0xa0723b96619546055050,0x4140f85362bb2a8b12a0,0x4a8281f0aec576551625,0x58950503d14d8b0caa2c,0xc8b12a0a07a2bb161954,0x15956254140dc534ad0a,0x742b2ac4a8281b8a691a,0xb4e856558950503714d2,0xd74ad0aecb12a0a05e29,0x71aed5a15d96254140d8,0x2d55da342c32c4a8281,0xa056abb466162545605,0x58140ad5369cc2c4a8ac,0xa2b02814ae6e39759151,0x554560502f18da742b2a,0xacaa8ac0a0563bb465d6,0x755917158140ac7369cb,0xaaeab22e2b028172aec9,0xbb469d6554d60503a1dc,0xc3369d3acaa9ac0a05e1,0x1b2a289a15d56458140b,0x503655d1342baac8b028],#[0xc0a06c68a26857559560,0x558140d8d744d0aeab2a,0xaeab028170eed1a15d56,0x925d560502a74db124c8,0x3124baac0a06ca9b4698,0x1a05956154540d8d36ad,0xd830eb2ac2a8a81b8c69,0x71b0e1d6558551502d39,0xb8cf64d3acab0aa2a05a,0x81b8a691a05956254540,0x1502f30d8742b2ac4a8a,0x2a2a05c65b7e85655895,0x6254540b1d760d42ecb1,0xb2caa8a8163a6c2a85d9,0x975e0d61502c3cd870eb,0xd0aeab2ac2a058cdb628,0x89a15d56558540b8e760,0x3d1342baacab0a81b192,0x4e5b6249915d56150363,0x8bcd7449322baac2a05,0xa8183b661a6249755854,0x615028f5d8330492eab0,0xaac2a0516fb5660925d5,0x5535894083df74cc124b,0xb2aa6b1281f82691a059,0x9d6554d62503f05da340,0xd3acaa9ac4a07c4bb06,0x6d3916416558940f0997,0x35d2f40cbacab12815aa,0x68e8a8e8197595625036,0x40d0d951d2b2eb2ac4a0,0x1281d2ae93a065d65589],#[0x562503a35d2f40cbacab,0xb2ac4a070e8a8e819759,0x5d6558940a9d760d0b2e,0x2cbacab128151bed5a16,0xe9597595625030765474,0x49d032abb2c4a0706ca8,0xa2a3a06557658940d957,0xb0cbb328c82caa9a81a3,0x6d48a2e819759553503,0x540f072ecbab08c02caa,0xb2a8187a28ba065f8159,0xd565502876db144cbf02,0x4baacaa0546db6249915,0x6458759540d8d360d312,0x24c8b0eb2a8187a24ba0,0xa2499161d655030b7d29,0x749d032dc12eaa041eeb,0x3a6d882e41815d540c75,0x3436d372a41302baa816,0xa060eda6e58826057550,0xd54083df75cb104c0aea,0x2baa81a3a6c1a6209815,0x60575503472d8b4c4130,0x4c0aeaa0686db569882,0x9209815d540c1dd72d31,0x72dc1302baa8107b6daa,0xa46819620975503076d3,0xd34ad032c412eaa065a9,0xd2a691a0658825d540ca,0x3a34d2b40cb104baa81,0xaa054cfb368596209755,0x5d540c8db4ad0b2c412e],#[0x4baa8153a6c3a165882,0x620975503236d2f42cb1,0xb2c412eaa0546db5e859,0xa3658825d540a9d361d1,0x4f40c3704baa8151b6d7,0xba4e8196e09755030f5d,0xad74bd032dc12eaa065a,0x183be9996647825d540c,0x543634b2f44ba2e2b02a,0xc0a87a29845516260560,0x158150b4d76ac22c4c0a,0x2e2b0aa1a9a597a25d38,0x9159561543632b2f44ba,0x2ecaa2c4a84e73b0693,0x1a15d95458950f85749d,0xd8748bb2a8b12a170bed,0x2bb46559059162543e15,0xdc5749d032ab22c4a876,0xa1b2ae93a065d6458950,0x254347454740cbac8b12,0xac4a868aca8e91975916,0x76589509cd760d2722b2,0x82ecb12a171aed594e41,0x3915d962543654d2729c,0xd2722bb2c4a864ada4e5,0x93a0651765895099d760,0x5d2f40ca2ecb12a1b2ae,0x8e8a8e81945d96254363,0xd85f4bca328bb2c4a86,0x2a1a1b2a3a5651765895,0x74543457d2150ca2ecb1,0x2aa2b0636ba5e8196e09],#[0x175589609ce760d2722b,0xc8aeab12c19aa69394e4,0x839159562546375d8349,0xb54722b2ae0b14e67b46,0xec1946416554d6294db6,0x25d8328c82caa9ac5792,0x62ada4e53816016558bb,0x7387086084a03382a000,0x289909609309008687d0,0x8ce8c50bb8b88b58ac0a,0xfd8f40f10e78d78d48d1,0xc92992011d11a1109008,0x93e93b93893593292f92,0x6095714d94a947944941,0xe1e11ca9ba99718d9639,0xa30a2da2421aa17a079f,0x52a4924624324023d233,0x4a6b26826526225f255a,0xaadaaaaa7a9e28e27e27,0xd62d32d02cd2c3ac0ab0,0xbafbaf8aef2e5adc2d92,0x33e334b24b14b11b0eb0,0x6d36a36735db5ab57b4e,0x5b8c38937fb7cb79b76b,0xbc1bb83b53b23a8ba5b9,0xfdbf43eabdabd7bd4bd1,0x6423420416c0d403c00b,0x48648346644943942942,0xbbcb24a8c9f495c92c89,0x14ee4eb4d4cd1ccecc54,0xd2a520d1750dd044facf,0x4c549546543539d36d33],#[0xe564d61d5855555254f5,0xd86d83d80d7dd7ad7156,0xc4fbc12e00359cd93589,0xc03d0fb0a080b4c4e623,0xc2c12ee1807a1e09770,0x4b0101c82a29040608f6,0x6520981410028200002,0x80000f4183e830400,0x201404080a0406c056,0xc080800760c1d0168,0xd8304000000000000000,0xc6be0df02a8518028783,0xf835820af810408e0412,0xc37c0a8a420250104b1a,0x45318dbc1880478c6de0,0x4100c237810a4520812a,0x40000820810,0x82000000615040287820,0xc0015a1bc0012a181187,0x161c00200000e000da1b,0x690c080000000510040c,0x1d0ee83080543034860,0x13821c00238000b42000,0x400293e0dc54c2011c54,0x40000b80020017000,0x1026093000ae000817,0x2d0d3820950c080064,0x7a080f41ac11c00200,0x56181ac3035860400,0x289f04dc305e85dc3040,0xee1be0821870c33b86f4,0x61504030e0200061c30a],#[0x203d05b0409e1c13c382,0x41c46f60c300001e8,0x4a06e000fa0c1643020,0x4002e000ec0012c202,0x102e0008000000000170,0x400000003800205c00,0x168238]]
def g251H6 := limbs80 #[#[0xb4000000301b7110b,0xb480000d4a3800002a00,0x1a8000000106,0xe600a8002e30100003c8,0xfc40000394000000000,0x2]]
set_option maxRecDepth 16000 in
def g251D7 := limbs80 #[#[0x50503c29765516254140,0xd16154110e8a61954589,0xa5915458950443c7165d,0x443a69865516254110f8,0x6254110b9a6995458950,0x1b7458950443c6965dd1,0x3479965977254110e3a6,0x54110e8e619645515044,0x76595504434799659774,0xe3745895158110b1ee91,0x110db8e516254560443c,0x54560443c7165dd15158,0xa5dd16258110d9c59794,0xb3ae917558960442ce9,0x56044347995597745811,0xe414254510b1ee917559,0x19597745895144375153,0x1443a6565e116254510f,0x77454510d1d65965dc95,0x5d965e11514434759659,0x42c77a45d96554510e1d,0x558510d1d65565dd1614,0x152e0142442c77a45d56,0x46d955977458910eca55,0x120b1be917559562443,0x258540483f0953509515,0x96554d4250120de2e4d4,0x20eca6156550940483f0,0x4d40483b298559152501,0x55956450120f86595645,0xdd2e4d5258550483a398,0x62482d3ba45977454120],#[0x5d6458920f13a9d6554d,0xb6969759562482cada4a,0x482d1fa465d6554d20b1,0x615414087b69b9261d54,0x95645895050371954e4d,0x3e29a45956254140f8a6,0x54140f1ae95765895050,0x54dc950503aaba461962,0x79965977254140d4e659,0x140cce65954e09505034,0x549605032b9965938254,0xa4e456258140f0e5d564,0xbaae918558960502ea9,0x160503e19a4595535814,0x5d56458140baae897559,0x2ae897559160503ca8a2,0x503c68a25d56558140f,0x97558140f1ae89755956,0xe8975e0d61502ce9a624,0x3e49a05955358940a73,0x558940f1369d6554d625,0x597595625036a9946416,0x4eba065d6558940b1be9,0x8940d1be959759562503,0x55d9625030eca865d655,0xd8659553dc940b3ae819,0x40dc6651905955350385,0x9553502d4fa265d6554d,0x62497559540b1769a975,0xc7a24b9061d65502c6da,0x755028eda6209815d540,0x18825d54087baa482605],#[0xbea586209755029eba06,0x5034e9a0658825d54087,0x7158150d1b6959620975,0x9594dc5605434b994593,0x3339945538158150d1e5,0x58150c9e59594e056054,0x915896054366995e4562,0x29845516258150b9a697,0x150b9ae958458960543e,0x55160542679a6e495458,0xa46595458150b8ee9196,0xb8ee91955916054363b,0x37154366965e49745815,0xe456254950e0f5958459,0x9e59590e0562542769a0,0x2543669656438158950c,0x95458950cda61590e056,0xe917655162543c6ba05d,0x43669956416458950f0b,0x458950b8be9195591625,0x39059562542cafa465d6,0xe69a4e416558950d9a65,0x8950b9ae819459562542,0x45d962542ce9a4e41765,0xfa56517658950b3ae819,0x60c9e59590e0564542c6,0x1151582ae9a0e1162545,0x6538158960c9e59590e,0x9ba693905d5625826eba,0x5358365992e416554d60,0x416554d60d9665390595,0x6e819259553582e59a4e],#[0x546e5ba06516554d60b9,0x62dc151e1d5958458770,0x83915956254786d65611,0xb26f9559580dc562b996,0x54d62d93651905955358,0x905955358b64f9464165,0x4da4e416554d62b93e91,0x110a9b69697e016558ae,0x58550443f61525096154,0x655096154110fcc55142,0xbdc6954258550443e71,0x550443d7374549615411,0x5516154110f9c5958258,0xf8e898458550442f73a2,0x443e71656116154110b,0x94254110f5a5d9525095,0x5d95450950443d6b7654,0x43d3b765514254110f4e,0x254110ece61954509504,0x99550950443c79765954,0x57b766554254110d5e5d,0x4110b5e69b7454950443,0x458950442d7ba45d9525,0xaa75916254110f9a6956,0x10eba6918658950443ce,0x8950443aeba461962541,0x65958254110eba2a5865,0xd5e5db9255150443c797,0x5044357b76e495454110,0x9154541109de69b92551,0xea9d6455150443e39865,0x442f3ba46195454110f4],#[0x5454110ecee918655150,0x958459150443578a7659,0x3ab9866116454110f8e5,0x54110f1ea5d655915044,0x865915044357a9765564,0xf9a6a5d6454110eaee91,0x1109dee959859150442c,0xdd150442779a5e616454,0xa961b745411097eea586,0xdda59792611504431fb,0x1504435e976e49845411,0xe498454110d7addb9261,0xfa69b92611504433e986,0x443c797659584541109,0x98654110aeee91926195,0xe899461950442b7ba564,0x42b7ba56518654110afa,0x158110fac59182505604,0x54254560442fb3a46094,0xee1845895158110f9c59,0x8110f9c5958254560443,0x4545604436f2a9591515,0x9545494258110f9c5958,0x10dbae616250960443f2,0x960443e396555142581,0x45515258110f1e5d5655,0x9eee919854960443e396,0x60443ea9845516258110,0x516258110f9a61554589,0xa5d58458960442ee9a85,0x443ae9856116258110f3,0x6258110bbae958458960],#[0xd16460960442eeba4615,0x36bb945918258110f2e5,0x58110d6ee51746096044,0x6560960443c797559582,0xf9a6e495458110d9ee55,0x110f8e61564551604426,0x55160443cba975915458,0x856115458110f8e59584,0xf1ea5d6555160443b39,0x1604434fa97659545811,0xa5d5458110d3e29d9655,0xfae899855160442d79a5,0x4426f9a6e6154581109,0x56458110dbc649915916,0x5d56561160442ebba461,0x4367b955958458110f1e,0x254510ddc59790509514,0xb90509514433f186e414,0xc75765954254510cfce1,0x4510f39a9d6458951443,0x559151443ae6a8591625,0x5a6a5d6454510f1da5d6,0x10abd69a9859151442cf,0x9614437e152e4142585,0x5e414258510dec553905,0x9fc69790509614436f16,0x61443f25545494258510,0x954258510f8d59554509,0xce819550961443c75755,0x443c769759554585109f,0x8050910b5d6969755161,0x9d65e0142443b3965553],#[0x3d2d765515250910a7ee,0x50910f4bdd9545494244,0x76e1542443c3d7659554,0xaea75915458910a5fe95,0x910d3b29d9655162443c,0x591624434eea76595458,0x97e116458910fa9e1191,0xf2ba5f8459162443cad,0x162442cefa95d5645891,0xa5d6458910d3ba5d9559,0xfa1d6559154442ceda5,0x4443c3e975956455110f,0xd6455110b4f696875915,0x6969759154442cbda6a1,0x42cbda6a5d6455110b4f,0x555110b1f69a87595544,0x7985d95444257da9a1d6,0x97da5a1d865511095f69,0x5110a3f69a8761954442,0x5a1d5444297da5a5d865,0x3a0609815911095fe999,0x10c7e61f9060964442bf,0x95644431fa87e4182591,0x9a1d6559110b1f696875,0x93f69b985d5644424fda,0x404828fda6a1d8559110,0x855150120fe850961545,0xa5954254540483e71655,0x4837a9965095150120fc,0x5150120deae594254540,0x98158540483e3965591,0x3ea9655096150120fe85],#[0x50120f6a5d5425854048,0x4258540483dab7550961,0xab855096150120eea615,0x120dea6614258540483b,0x585404837cb935496150,0x855496150120fca55152,0xde65539358540483b69,0x5404835d975e4d615012,0xe4d6150120d76dd79358,0xf6e1793585404833d985,0x4827d9a5e4d6150120c,0x16150120f8e595545854,0x6156558540483d397555,0x83ba9865098150120e9e,0x150120deae5942605404,0x563509404836bb965918,0xba98558d4250120f6a5d,0x120beae856550940483,0x354940482faba1619425,0x98558d5250120fca5516,0x20faa6856458940483b6,0x8d40483f19a459553501,0x26456450120f4e5d5545,0xf2e5d991591404837a99,0x504827b9a4e456550120,0x56154120fd854981585,0x2e4d4258550483e71656,0x483f29545096154120df,0x6154120f9a5954258550,0xd15258550482f69a5509,0x3d6b745496154120f5a5,0x54120edae11525855048],#[0x93585504837699854961,0xd974e4d6154120dd6553,0x120d76dd393585504835,0x585504833db84e4d6154,0x655d16154120f4e5d154,0xf1e5977458550483c79,0x550483a7965e11615412,0x5956154120f9ce856558,0xda6195260550483e69a2,0x48376b965498154120e,0xd4254120d9ee59656055,0x6556350950483f295458,0x83d697458d5254120dda,0x254120f5add163549504,0x56454950483b6b8458d5,0xf6ba16195254120bdae8,0x4120f9a6856558950482,0x458d50483e6ba1595625,0xba15915454120f4e5d15,0x20dcee919655150482f3,0x915048367965e4564541,0x459564541209de697915,0xbcee919559150483e3ba,0x50483d3ba45977454120,0x456554120dda64991595,0xa64b9159550483c79766,0x483c7976e456554120dd,0x6154520f995954258551,0x977458551483c75655d1,0x3a7565e116154520f1d5,0x54520f99689655855148,0x6558551483c75a759561],#[0x67a15956254520f1da9d,0x520f1ba9d6558951483e,0x595514829bfa461b7454,0xa465d6554520f1d5db91,0xe735d78350961482d3f,0x9614839cf75e0d425852,0xe0d5258520af36978350,0x735d38354961483b4d54,0x14839cf74e0d5258520e,0x38358520e575d554e0d6,0x65574e0d614829dda755,0x829dfa55d38358520c77,0x358520c7765774e0d614,0x175e0d614829dda5dd38,0x9dda4dd78358520a77e9,0x852097be899755161482,0x759561482cbfa465d655,0xda5a5d6558520b1fe959,0x20e3b6a16458b71482c7,0x9162482f2fa159154549,0x76456558920d3ba5d915,0xd3ba5f91595624834ee9,0x53483e1fa45956454d20,0x5d5458d20f47e9165dd1,0xf59791591544825efa26,0x48353d75e456455120d8,0x65dd120a6fe918760564,0x9187605654825bda1e51,0x29bfa461f8159520a6fe,0x5952087f6a687e056548,0x71585505029bfa465f81,0x71655c56154140fcc551],#[0x140bdce957158550503e,0x58550503f31546056154,0x656056154140bece9181,0xdd6e4d5258550503e71,0x5505035db93dc9615414,0xdc96154140f4e5537258,0xf6e4f8258550503c7965,0x503b3954e096154140c,0x16154140dce65d545855,0xe8565585505037399855,0x3e39a45956154140f9c,0x154140d9e65d65585505,0x1985855050277ba565d6,0xd397655171541409eee9,0x4140ece619545c550503,0x45c55050373b96551715,0xb955917154140f8e5956,0x40eae619645c55050373,0xc5505036bb9659171541,0x6e557154140f1e5d9655,0x9de69b955c5505035797,0x50502d7ba55d97154140,0x518154140d3ee59765c5,0xe6195460550503d39765,0x50373b965518154140ec,0x8154140bce6995460550,0x196460550503e3965591,0x373965e518154140eae6,0x54140cee61b946055050,0x65605505027b9a6e5181,0x7b965958154140f1e5d9,0x140cbee5986605505036],#[0x58950503ea9a15916254,0xa15956254140f9a68565,0xf3a6857658950503e6b,0x950503ceba15d9625414,0x6196254140eba6858658,0x4e55163dc950503aeba1,0x503b395458f8254140f,0x95454140ceee9196e095,0x6857655150502f3ba15d,0x3d3ba15d95454140f4e,0x454140bcee8586551505,0x58655150503b39a16195,0xb3ba76195454140ecee8,0x4140f8e5959159150503,0x15915050373995645645,0x9a15956454140eae6199,0x40f8ee856559150503e3,0x9150503e39a759564541,0x66556454140f8ee9d655,0xeae6858659150503e398,0x50503abba16196454140,0x456554140eaee9d86591,0xe5d99159550503739946,0x50373994e456554140f1,0x6554140bce6939159550,0xd99459550503c7976e45,0x2e7ba15d96554140f8e5,0x54140f1ee5d765955050,0x7659550503c79a15d965,0x3ba465d6554140f1ee85,0x140bce6939759550502f,0x5d95050357b956457654],#[0xa46458654140b5ee9591,0xaee6939761950502bbb,0x560503eb1645c5515814,0x5c55158140f9c5957154,0xb85898154560502ef3a6,0x503eb1646055158140f,0x95158140f9c595815456,0xe6162545605036e99858,0x36b9975915158140dba,0x158140daee5d64545605,0x164545605036b9985915,0xe73a15955158140daee6,0x8140f8e6916554560503,0x55456050367997595515,0xba465d5158140d9ee5d6,0x409bee9997545605027b,0x45605027b9a4e5d51581,0x8e5d51581409be69b975,0x9eee9198545605023f9a,0x605026fba66615158140,0x6151581409ee69398545,0xe591725c5605026f9a6e,0x503cb9755917158140f2,0x7158140eaee15645c560,0xd5655c5605036bb95591,0x2deba25d57158140f1e5,0x58140d5ee55755c56050,0x965c5605034fb965d571,0xa9a458981581409be697,0x140f3a5d56260560503e,0x60560503ceb755898158,0x646098158140eba61562],#[0xbaee896460560503ab9,0x560503cb975591815814,0x5918158140f2edd56460,0xaee956460560503ab985,0x503c79755958158140b,0x56258140bbae85855896,0x5939160960503eaba461,0x3e59a75955358140dae,0x458140f96e9d6554d605,0x58559160503cb9a15d56,0xebba76156458140baee8,0x8140dae6519159560502,0x159560503c7975645655,0x9a4e456558140dae6539,0x40f1e5d79159560502eb,0x9560503e397565165581,0x15d56558140f1ee5d755,0xbaee919759560503c79a,0x60502eb9a4e5d6558140,0x457558140d7a249915d5,0xee91915d5605035eb926,0x502cfba66457558140b6,0x61545409ee6939761560,0x816558551503c7565dc9,0x3a75875956154540f9c6,0x54540e9de1d655855150,0x65585515036759759561,0x76a75956154540f1d69d,0x540afce818758551503c,0x5c551502bf1a0e1d6154,0x965d97154540f1d5d965,0xf9a68165589515034f7],#[0x951503e67a1595625454,0x5d96254540f1b69d6558,0x3b6a17658951503ce5a1,0x15038eea85d96254540e,0x16554540d1f65965dc95,0x68391595515037399464,0x3c7576e456554540bdc,0x554540b5d69f91595515,0xd765955150387d875d96,0xc75a15d96554540e1fe1,0x4540adee818759551503,0x759551502b79a0e1d655,0xda6a5d6554540b5be899,0x40a3fe99875d951502c7,0xd9515029f9a0e1d76545,0x6617654540a3f69b875,0xa7ee81985d9515023fba,0x515029f9a0a617654540,0x4586545409fc68391619,0xc68391619515025f5a7e,0x5029f5a7e458654540af,0x87545408fe6839761951,0x9b9061d515033bb94e41,0x23fba664387545408fe6,0x58540f1d5d5655c56150,0x755c561502de7a25d571,0x5d75e0d5258540d5de55,0x540c7765783dc9615039,0xdc9615029dda5e0f7258,0xa25d78358540d1f65565,0xe7328975e0d61502bcf,0xd615039cfa25d7835854],#[0xdd78358540a77e8975e0,0xae65190595615029dda2,0x1502ef1a0e456558540d,0x56558540f1d5d7915956,0x61d7559561502cf5a7e4,0x3c75a15d56558540e1f,0x558540f1b28975595615,0x99759561503c6fa25d56,0xc7fa565d6558540b3be8,0x8540b1f6969759561502,0x75d5615031ed87e49755,0x3a06457558540a5fe958,0x40d79249915d561502df,0xd5615035e79264575585,0x82497558540b3b698925,0xc7b663925d5615031ed9,0x615035e5a1e497558540,0x617558540c7b6a3925d5,0xe68398595715029fba06,0x5021fda7e61655c5408f,0x755c540c7be1b925d571,0x9b855d5715025eda6e49,0x28fda5e19765c540a5f6,0x58940d3b68596dc96250,0x90595625036e99164165,0xa9946416558940dbae45,0x940faae919059562503e,0x59562503c6d756456558,0xa0e456558940d3b65d91,0xf1b5d79159562502ee9,0x5625034ed97e45655894,0x65d6558940b3b69f9159],#[0x1be959759562503ceba0,0x25038eca865d6558940f,0xd6558940d3b685975956,0x68596dd5625034efa165,0x34ed956457658940d3b,0x658940d3be55915d9625,0x1915d962502cefa56457,0x4ed95e457658940d3b26,0x8940b3b697915d962503,0x55d962503ceba0655765,0xca86557658940b3be859,0x40b3b687955d9625038e,0xd9625034eda1e5576589,0x859553dc940b3b684985,0x87f6a3915977250395da,0x535029efa164986dc940,0x416554d40fc665190595,0x65d99059553503f1ba46,0x503c5f975d96554d40f9,0x6554d40bd6e819759553,0x899759553503d5ba065d,0x3d4fa265d6554d40f532,0x54d40b576a6975955350,0x925d563502f59a0e5d65,0xb9a4e058059540b3b698,0x540ece5d58460165502b,0x60165503ab9766118059,0xa261d8159540f1e5d975,0xa7be8987e05655029ef,0x5655021fda9a1f815954,0x6438159540cee65190e0,0x7be8997e05655033bba4],#[0x55023fba065f8159540a,0xf8159540c7ee8197e056,0xe8997e05655031eca265,0x2c7fa15d97559540c7b,0x559540b5ee81915d5655,0x9915d56550356c926457,0xc7fa66457559540d5be4,0x9540d1fe55915d965502,0x55d965502c7fa5645765,0x892e418759540b1f6879,0x40d5ee579061d655035e,0x1d6550356f9524987595,0x4e418759540d5be57926,0xe7a24b9061d655033bb9,0x655039eb92e418759540,0x418759540e6ee539061d,0xee819161d6550397b95e,0x5031ec926458759540a7,0x8759540c7be499161d65,0x999161d6550297fa5645,0x31ec92e458759540a3fe,0x59540c7be4b9161d6550,0x9261d6550396f9524987,0xfba06628759540e5be57,0x540cee65190e1d655031,0xe09755029efa15db825d,0xa765b825d540cfae8196,0xc7be9d96e09755031ed,0x5755039e882e41815d54,0xe41815d540e7ae0b9060,0x5ee5790605755035bb94,0x55025f9a6e41815d540d],#[0x9815d540e5be54826057,0x69882605755031ef9620,0x29eea9209815d540a7b,0x15d540e5be5782605755,0xb82605755031ef96e098,0x9eba0618825d540a7b69,0xd540a7be858620975503,0x62097550396fa5618825,0x9a0658825d540c7bea58,0x40d5b69596209755035e,0x9755034eda1658825d5,0x3658825d540d3be85962,0xd3be8d96209755034eda,0x755039eba061b825d540,0x1b825d540a7be8586e09,0xbea586e097550396fa56,0x5035eba065b825d540c7,0x825d540d5be9596e0975,0x9991e09755031ed96647,0x29efa165b825d540a7be,0x5d540c7b68596e097550,0x90619755031efa165b82,0x7b95e41865d540d6ee53,0x940a7be8985605765035,0xe05765029fba060b815d,0x92e41855d940a7be8985,0xd7ae4b90615765035e8,0x5605435bb94e41855d94,0x5c97158150d9ee59525c,0x8e591545c560543c7965,0x54373b945517158150f,0x17158150d9ee59545c56],#[0x5d1645c560542e79a655,0x42deba25d17158150f2e,0x158150f1e595745c5605,0x7845c5605434fb965d17,0x67965e517158150e9e59,0x8150f1e59584dc560543,0x260560543e6962549815,0x9a65498158150eda6095,0x50f9a5516260560542e7,0x560543ceb7458981581,0x55898158150eba611626,0xe9e5958260560543e69a,0x60542b7ba56098158150,0x518158150f8e59154605,0xe6995460560543b39845,0x543c7965dd18158150b9,0x8158150e9e5958460560,0x5152e0560542b7ba5611,0x3a79655cb8158150cde6,0x58150adee8954e056054,0x74e0560542beba25d381,0x79a15978258150e9e595,0x150e9ee8565e0960543a,0x55160543679966455458,0x966115458150f8e69d64,0xf8ee919655160543e39,0x160543679a1659545815,0x6615458150d9ee859655,0x9e6559159160542f3ba4,0x543e39955d16458150d,0xd6458150f8ee91955916,0x68565dd160542ebba465],#[0x43c7ba15977458150f1e,0x458150e9e68565e11605,0x99159560543a7ba15978,0x679946456558150d9e64,0x8150d9e64b9159560543,0x15956054367994e45655,0x5655c97158550b9e6939,0x50dcde51545c561543c7,0xc561542de7a25d171585,0x5e517158550f1d595745,0xe57dd383549615436756,0x6154395d54e0f7258550,0xd38358550c7765383dc9,0x768b74e0d61542bcfa25,0x542b3fa461d5458550a7,0x7458550d9b597925d161,0x8565dd1615431ed87e49,0x2e75a4e456558550f1de,0x58550b9ee81925956154,0x8455171542e7ba065165,0x3da6e11545c550e4f5db,0x550e1fe197655171542b,0x5d171543c3d655d1645c,0x86e49745c550d5b59792,0x97b69b925d1715431ef,0x15254387f86595745c55,0x65b72589509de6839159,0x3be8596dc9625434eda1,0x2543e69a15958058950d,0xb8158950f9ae85656016,0x68576551625434efa95d,0x43c6fa15d95458950f1b],#[0x458950dba64590591625,0xd915916254366d956456,0xe6ba06556458950d3b65,0x8950f8be919559162543,0x759162543ceba065d645,0xca865d6458950f2be919,0x50f1b68565dd1625438e,0xd162543c6fa159774589,0x165b7458950d3b68596d,0xd9b65191595625434efa,0x6254366d94e456558950,0x516558950b9b69391595,0xa653905d962543e6ba06,0x543ceb94e417658950f3,0x7658950f3a263905d962,0x51915d9625434ed94645,0x2cefa46457658950d3be,0x58950d3b261915d96254,0x915d9625434ed94e4576,0xeda4e457658950d3be53,0x950d3b263915d962542c,0x5d962543ceba06517658,0xa56517658950f2be5194,0xe3b2a1945d962543c6f,0x962543ceba0e51765895,0xe517658950d3b687945d,0x4fe9186553725434efa1,0x25421fda8e4564dc950e,0x164dc950e2fe91865937,0xe9198593725429bfa466,0x4373b94e417655150c6f,0x655150dcee83945d9545],#[0x1915d954543d3b94e417,0xd3ba0e517655150b4fe9,0x9150e9e5958160164543,0x460164543e39655d1805,0x9765d18059150ece6157,0x50f8ee916560164543cb,0x164543b3ba461580591,0x261d8159150e9e5d9856,0xf8ee81655d1645429efa,0x64543c3d766157459150,0x1d6559150f2ee81765d1,0xfe918759564542e7ba06,0x54373b94e418559150b8,0x8559150d8f5db9461564,0x53905d964542e7ba05d9,0x3cbb94e417659150daee,0x59150b2fe91915d96454,0x9061d64543cbba0e5176,0xbb94e418759150d7a24b,0x150d6be509261d645435,0x61d645435af94e498759,0x95e418759150ceee5390,0xccfe579461d6454337b,0x974543b6ba0597825d15,0x5db825d150e7ae8176e0,0xfae8196e09745429efa1,0x454336fa565b825d150c,0x38159550c7b69d96e097,0xe9584e017654277ba065,0x433b994e13805d950ade,0x5d9508fee8194e05765,0x582e0176542dbba460b8],#[0xdeba2613805d950b5ee9,0xd950b5ee9584e0176542,0x2605765435b994e13805,0xfa2611815d950a6fe918,0x50a6fe9182e05765429e,0x5765429efa2613815d9,0x653815d950c6f65384e,0xd7a24b90611765425fba,0x765435eb92e41845d950,0x41845d950d6ee5390611,0xbe50926117654357b95e,0x54356f95249845d950d6,0x845d950d5be579261176,0x81625c55158353f95e11,0x3ce5745897154560fb8e,0x54560eb9e11625c55158,0x745c551583c75655c971,0x7565e117154560f1d595,0x560eba61f9058951583a,0x58951583aeb87e416254,0x875d16254560e3b61d74,0xabb69f84589515838ef,0x951582aefa461d625456,0x5977254560abb6938758,0xafe918759151583c77a1,0x1582abda4e1d6454560a,0x774545608bf6a7875915,0x6939159551583c77a159,0x82e7ba06496554560b9d,0x25c560b9ee8194595515,0x390589715825bfa465d5,0xee9a4e41625c560dba65],#[0xc560f3a5d79058971582,0x589715836e995e41625,0xfa55d1625c560bba6979,0x60bbae819458971582ce,0x8971582cefa45d5625c5,0x5595725c560bbae81955,0xd1fe55655d17158347f9,0x625829fba064984dc560,0xd78058960bbae8574e01,0xb69d94e0562582eeba15,0x5826efa95d781589609b,0x7458960f3ae81755d162,0x91755d162582cefa15d5,0x2eeba06557458960f2be,0x58960babe91955d16258,0x95dd1625834eda165774,0xe994e417558960d3be85,0x960dbae53905d5625836,0x5d562582ee9a4e417558,0xa4e457558960dba26390,0xbbae81945d5625826ed,0x5625836eba0e51755896,0x595535c960d3b68594dd,0x9ee179059572583e5ba0,0x3583e5ba05957454d60e,0x17559160f96e81945955,0xe83945d5645836bb94e4,0x83a7b85e41655d160dae,0x5d5609bee8194e05655,0x984e0175582bbba460b8,0x3b994e13805d560afae8,0x85518fee8194e0575583],#[0x5956154767592641655,0x5946416558551b9de899,0x51b9de91905956154767,0x162546e77a064965585,0xe456558951e9de8565e,0xf99e856560162546e75a,0x62547e67a15978058951,0x416558951d9b65190595,0xde9190e0565546e6fa46,0x5463f7a4643815d9519d,0x815956197de9190e0576,0xd5915957058a6f7a4643,0xba6f85645655c162f1bd,0x5c162f1bdd7915957058,0x915957058ba6f85e4565,0x4d946416554d62abbaa3,0xd62f93691905955358be,0x5955358be4fa46416554,0x946058059562f9329d90,0x2cbbe53816016558b2ef,0x16558aaeda4e05805956,0x6118059562bbae818460,0x9be95946016558baeba0,0x558ae6da0dd58159562b,0x381595629bbe9190e056,0x68375e056558b66f7564,0x4ef5ba06098059553b9b,0x59553bc7e9192601655,0x1846016554ef5ba06118,0xf4fa26518059553ed6e8,0xc565c6f65384dc570596,0x2603715969fba05c980d],#[0xba061180dc565a7ee818,0x65a6fe9192603715969f,0x13800029efa265180dc5,0x66005580450034802700,0xc180ae009d808d007980,0xff00f780f000dc80cf00,0x51814701398129011880,0x9b018a817a016c815f01,0xe781d101c381b601ab81,0x2b02208213020281f801,0x62825b024a823a023282,0x9d02958288027a826d02,0xfe82f402e382d002b082,0x480337832a031f830c02,0x8b838403738366035583,0xb103a983a2039a839303,0x83fc03eb83db03c183,0x4a043c842c0421840b04,0x8a847a046f8468045784,0xb904ae84a4049f849504,0x584f504e784d704c984,0x670559854c0538851305,0xb385a605958582057485,0xf705e985dc05ce85c405,0x5586450631861b060a85,0x9c068886810676866c06,0xeb86db06d086c906b286,0x2f071e8714070986fc06,0x90877d07698759074587,0xc507bd87b607ab879807,0xf987f507e487dd07d587,0x1f081a8816081187fe07],#[0x3b883708328828082388,0x6a085c8855084a884308,0x92888e08898885087a88,0xb208aa88a3089e889a08,0xda88d308ce88c408b988,0xf708f288eb08e388e208,0x1089090904890008f888,0x33092b8927091f891509,0x58894e09498942093489,0x8a097f89720967896309,0xaf89a809a0899c099189,0xea09dc89d209c789ba09,0x1b8a110a098a0509f789,0x350a2a8a260a218a200a,0x4e8a4a0a458a410a3c8a,0x740a668a620a578a560a,0x938a8c0a878a7d0a788a,0xaa0aa88aa40a9f8a9b0a,0xcf8ac20abd8ab30aae8a,0xf20af08aec0ae48ad70a,0x1a8b130b088afb0af68a,0x3a0b2f8b2b0b268b1f0b,0x628b5b0b538b4f0b478b,0x820b808b7f0b7a8b6d0b,0x988b910b8c8b880b838b,0xac0ba78ba30ba18b9d0b,0xbf8bbb0bb68bb20bad8b,0xf40be98bdc0bce8bca0b,0x1f8c1b0c138c060bf88b,0x420c3d8c3c0c2b8c270c,0x588c540c4f8c4b0c468c,0x6f0c6a8c630c5e8c5a0c],#[0x9d8c960c8e8c8a0c7c8c,0xcf0cc18cbd0cb88cb10c,0x68cff0cee8cde0cd68c,0x200d1b8d170d158d0e0d,0x458d380d338d2c0d248d,0x560d4e8d4d0d4b8d470d,0x7b8d6e0d698d650d5d8d,0x9e0d998d950d908d860d,0xba8db60dab8da70da28d,0xe30ddb8dd70dd28dc80d,0xff8df80df08dec0de78d,0x3a0e358e280e1d8e100d,0x628e580e4d8e460e3e8e,0x7f0e7a8e760e6e8e6a0e,0x958e940e8f8e8b0e868e,0xa30ea18ea00e9b8e9a0e,0xad8eac0eaa8ea90ea78e,0xcd0ec88ec10eb98eb20e,0xec8ee80ee38edc0ed18e,0x30efe8efa0ef58ef10e,0x1c8f180f108f0c0f048f,0x4b0f468f3c0f378f2d0f,0x738f690f5b8f570f558f,0xab0fa38f900f7c8f780f,0xdf8fcf0fc78fc30fb88f,0x810008ff90ff18fe70f,0x279020101b9014100c90,0x53104b903e1036902f10,0x75906e1063905c105790,0x9b108d9083107e907a10,0xd890d110c090b910a590,0x710f090e610e190dd10],#[0x38913411299119110e91,0x6d11659158114d914311,0xa4919a1186917f117a91,0xd611cb91c411b991a911,0xd91f411ec91e511dd91,0x3012289224121f921812,0x589251124c923f123a92,0x811279926c1267925d12,0xc192bd12b2929f129492,0xe712df92d512d092cc12,0x92fc12f492f012ee92,0x2f132793141306930513,0x54935013489341133993,0x86137b93711366935c13,0xc693b913ae93a4139993,0xf813ed93e613de93d413,0x2c942214179407140293,0x64145c94521447943d14,0x92948b14839473146b94,0xb514b094a6149e949714,0xe394d914d194c714c294,0x14f894f714f594ee14,0x3195241516950f150495,0x54154f95481540953f15,0x73956915679560155895,0x8d15889584157c957815,0xa695a2159d9599159495,0xc615c195ba15b295ab15,0xe895e115d395cf15ca95,0xff15f495f315ee95ea15,0xc960b16099605160395,0x411636962c1624961a16],#[0x6096591651964d164896,0x7a16759674166f966816,0xa5969e1693968c168196,0xbf16bd96b616b196ad16,0xde96d116c696c216c096,0x16170b970116f696e916,0x4497401732972b172397,0x73176897641753974c17,0xad97a9179e978b178097,0xe217cb97c417bf97b517,0x1980017fb97f717ec97,0x30182898211816980f18,0x4c984818409839183498,0x6f186a9863185e985418,0x9498901885987b187698,0xab18a698a2189d989918,0xcd98c318bb98b718af98,0xf018ee98ed18df98d518,0xc9905190098fc18f498,0x2c1921991a1915991119,0x3f993b19399938193099,0x5c19519950194b994419,0x72996e19699965196099,0x921981997d1978997719,0xae99aa19a2999b199699,0xd419c699b919b499b019,0x59a0119f699ec19e199,0x191a149a101a0b9a071a,0x359a341a299a251a209a,0x491a479a461a3e9a3a1a,0x659a5b1a569a551a4d9a,0x881a809a791a719a6a1a],#[0xb69aac1aa79aa31a8f9a,0x61af59ae21ad19ac11a,0x4f9b4b1b319b1b1b109b,0x961b859b7b1b6a9b5d1b,0xa69ba51ba39b9f1b9a9b,0xd51bc79bc31bbb9bb11b,0x99c021bfa9be71bdc9b,0x3b1c2d9c261c1b9c141c,0x759c681c579c501c429c,0xa11c9c9c921c819c7d1c,0xc09cbc1cba9cb31ca59c,0xd11ccc9cc81cc69cc51c,0xf69cef1ce79ce01cd89c,0x191d119d0a1d029cfe1c,0x2f9d251d209d1c1d1a9d,0x611d4d9d4c1d3e9d341d,0x959d8e1d809d731d689d,0xc41db69daf1da49da01d,0xec9de81dda9dd61dcb9d,0x1b1e169e0f1e019dfa1d,0x499e451e3d9e331e289e,0x691e649e5d1e589e511e,0x8e9e8a1e7f9e781e709e,0xa81ea09e991e949e931e,0xca9ec31ebb9eb41eac9e,0xf31ee89ee11edc9ed81e,0x189f141f099f021efd9e,0x3b1f369f321f2a9f231f,0x5a9f531f4b9f441f3f9f,0x6e1f699f621f5d9f5c1f,0x819f801f7b9f771f729f,0xa41f9f9f981f939f8c1f],#[0xba9fb61fb19fad1fa89f,0xd11fcf9fc81fc09fbf1f,0xe79fe01fdb9fd71fd29f,0xfb1ff39fef1fea9fe91f,0x20a016200ea0071ffc9f,0x522047a0402032a02b20,0x6ea06a2062a05b2056a0,0x852080a07c2077a07320,0xaaa0a02095a08e2089a0,0xe220d7a0ca20bfa0b220,0xda10c2104a0fd20efa0,0x2d2125a11e2116a11221,0x55a1482140a1392131a1,0x7e2176a16f2167a15a21,0xaca19f2191a18d2185a1,0xcf21caa1c621bba1b121,0xe5a1e421dfa1db21d3a1,0xb2203a1fc21f4a1ea21,0x33a2292221a21d2215a2,0x5c2254a250224ba24122,0x8aa283227ba2712266a2,0xbc22b1a2a72299a28f22,0xe4a2dd22d5a2ce22c6a2,0x102308a2fe22f3a2e922,0x2ca3282320a31c2317a3,0x40233ea33a2335a33123,0x2201d58df83f8103e1a3,0x740e5637e0fe040f860,0x40e4551f02dd8302910,0x84f010391449c873c0fc,0xe13c0fc040e4503201db,0x910b84b03a110391a49e],#[0xd077e0ee13a168446219,0x5d8200c503f01036160b,0xd84180766100cbc040e4,0xc3c4011510503f01019,0x350fd8581f10c40c0c07,0x75044641e1160d468682,0x112007643c202d90f080,0xff8302001d307785b842,0x17c04074c1c0b00f8582,0x80b0401101d507f01039,0x401a99761f0cc1fc0408,0xe0803912442c0c0e6844,0x540c0b3c000d84927f03,0x3c5510d8450301af001,0x20ff001549f821c0fc01,0xa7c0287c301c310303,0x2de08c402220ff00c1f1,0xf00020f01d841fe0fc04,0x8c1c0b00f85c2ff83507,0x8005a0459f03e0fc0408,0x39f03e1161e81361ac0b,0x3e0be0ee180f83040c04,0x6f02036140d81002b860,0x680361a830501901598,0x227c0d83c120360961f6,0xd8430f30703003613c0,0xf0002ac9f10c3cc1c0cc,0x4e00d8618043a142833,0xe7800488a987605d817,0x36c13e0f60be0508d864,0x2298df83f8103903e1a6,0xf0c077e0e0bda1411850],#[0x3c0336080a8481de8542,0x450f00c503d8202a194,0x5d820271005f60809c3f,0x70066a1b6080bc5015e8,0x2e14530f21189f03e100,0xfe0003e13080643801c1,0x40643236e16054502d89,0x3d0b2340f42c8d03d08a,0x268d03d0b2340f42c8d0,0x2d89f032f0417a1ae14,0x1c566140a980a27c8715,0xdc8d03903e140f7c13c0,0x3cc1c033c13c00542281,0x851c0f7c13c00303e04c,0x3f04f0022fc8df83f81d,0x19f02ae82141190740f8,0x2c000b727c0f84f04f00,0xc012345f04f0002ac9f1,0x8368d03d08c40c3fc13,0x87586f8303d17a1ba15e,0x5d820fe0f6040f43d81d,0x825b8603d0c0f41b86e8,0x8101df0516096e180f43,0xca41c07a43c4032507d,0x3c4f83490d81019e8614,0x830a002f1624006be0e2,0x846e040e40f84219982f,0xf81e00039215b0541d30,0x4642302231cc8df83d82,0x311c17e0f800642e1207,0x8ea180d84d84012b8202,0x44022039036e00100548],#[0xdd84419180540d808ac1,0xc807ba045890190e8368,0x5f83d8602f1281fc000,0xe0fa0806a03fe0c0f850,0xc0cba180bc4f8303903,0xd610403201dd8403913e,0x9022b8303e1bc000e50b,0xc0e428bc00581dc8d03,0xf307017f00f051c0dbe,0xe0c88ec000e46584e823,0x290383b0003914c56416,0xa43414e0ee11c007d05,0xf8381d7840390c4a708,0x6b6046f00b8409074ca4,0x85b841e24203fa13e0c0,0xa04712ff83287e81020e,0x80fbe0c06a21f61008b,0x3e1461c0480e43c1f03e,0x7c0b45312300c1f7820,0x300c1f02d10c54c000cb,0x1fb840cc0307c0f8303e,0x2bc07406ba0147c503ec,0xf8302001da07e8021a1e,0x1e00a40e0ec040b468af,0x6006f83487e8103e16c2,0x180b4c9cc8de1307ee00,0x8248532739578402dc1f,0x310b8002dc1f1b07c0f,0xd83080b48800f83c8512,0xfd83b821643f60c290f,0x3d830b60c800211e4119,0x447904643f60ee08582],#[0xfb84d83b821b60c1d83,0x43c11100543c111e4119,0x205d825100c0c8151005,0x8c084400302011040dc1,0xc60509847c040e43110c,0x629140c96098a7c04412,0x560bc04301d611784f01,0x8c211004440100c058a,0x3e30f08c3c141904044,0x643f01039080650a42,0x4b01a29e051840c8a407,0x442000758a4252c00508,0x4200014103e011080f80,0x2701098141605040c984,0x42d84d8201c0f814103,0x84000cbc042032040cbc,0x1212e000845a43ee0884,0x3ee08381f51a50f0ee08,0x46a43ee10302c0446a4,0x43fc043097182e018231,0x3f60b404312942308875,0x13290808fc04202f054,0x230ff0112e100e50743f,0xb010cc68c3d018302318,0x846e10c3fc044701329,0x60a048421130f784f011,0xd04b800250f0445943f,0x487410143c111a50fd82,0x918408077c044a4350f0,0x3e040e41529044a4112,0x4642e0c84430008fc042,0xf0446943c81b610430f0],#[0x7c161f6832000c0c8150,0x2c040b207c2d82510098,0xa0c1e8304041f040b010,0xe0613a0c161f211e830f,0x821303fa0c2c0fe83182,0x907a0f818281e40f206d,0x88260f10040103204002,0x30805d0422083707703,0xe4102c5050803c160f7,0x60212e0ec00458303904,0x2c048418082707703210,0x418302c305090b0c1420,0x2c50f884205100a583c,0x1004040a41000000f81,0x4000103e0060800,0x4040b01000041d8304,0x580980267c3005040001,0xf128096068004a84e040,0x7e80a8003583a02a0059,0x360dc0a619800412a056,0x60c8102d83a02a0059f1,0x85d830760c8082d8307,0x760c10161d60e800442c,0x2058101604058481d830,0x204d830b60c1e0404060,0x44902581a003021360c1,0x10251004048442c0a04,0xb0004406402b8e0ae39,0x81d02c0008e7c05c04b0,0x49440635e0c4b8e06e3,0x60014813638261203609,0x5012e0c521211098db83],#[0x618201211008848c4063,0xc1d83040186f0209802,0x8350f0b60d43c2d83076,0x5875831101021360c1d,0xd830b60d43c200060504,0x360c1d830643f60c290f,0xc096043510d83d816001,0x5440101200c1100e408,0x8e06e381b8e06e381b8e,0xe0c430f040480304403b,0x4125107810d049440635,0x10041000d82310076381,0x6081000d820360444019,0x48442636e0d8005f0203,0x1800321231018db83108,0x1310b02b814051084844,0x80f0807a03c291006c10,0xf4010f03f205c00341e,0xa0425100503f20427044,0x2ae8108c40100f0583f,0x14141034101504054101,0x1000000c8704000c1010,0x883fa0c2e83c9f0ba0c,0xcc043210040b0120fe83,0x60627c1b8389f0a236e0,0x110064401e8e040d8103,0x42c9f0760f27c2000041,0x60c0440545c9f0401000,0x44103a811d830c05a61b,0x40c044101a0119860c0,0x60a43c4e8504001a186f,0x101910d8390f0e44360e],#[0x561d60e8002146d8307c,0x1587583a001041811c10,0xd816001143f60c204a04,0x410410821560c3829d83,0x6a0003ed811410401020,0x8117860c0580f8250f58,0x4203e03a080ea0542816,0xa080e943c203a0405a05,0x3c203e01a08104103e03,0x16180f8203e01a080e84,0xf8044201a015d818111,0x88303e03c080f0103c04,0x40681041004080f80f00,0x418d7830470c0f0103c0,0x7816150c8a4635e0c128,0xc108635e0de05a146229,0x635e0dc1050467810811,0x6e38178162908128108,0x4730fc007810c09c1b8e,0x11c104c3ce35e0de0521,0x17000c3de04330f78108,0x50a4304a04138d783d04,0x636e0c11c303e07411e0,0x36e0c058398db830470c,0x48a4222918d78304a106,0x54102d02278203e11e0,0xf0635e0f4106504a0009,0x1d047816290c1281080,0x382998db8360004a1741,0x4360082908636e0c068,0x68002b8140508070846e,0x520056214230f7810921],#[0x4203a30f18d783781c8,0x8503e08c3f215e043047,0x40c1040e8201a040f81c,0x11015100f8104103c00,0x8109f0110a044109f016,0x410108198509f0110c10,0x180b1410204a58758350,0x8303f03c02f582a00086,0x7583a001041943e80021,0x40b2800410304a03c58,0xc1086060b3605800350f,0xf008c203e03c01d0d43,0xf0010200404003e01d08,0xa43e604400010103c040,0x5782a00886d811885c84,0x8117850c0ea054250f58,0x8202fc86080e943c2816,0x10c0f008c203a040e80f,0xe23760c078388dd8341,0xa23760c108388dd83041,0x389048d504304d839821,0x88dd8301e0e23760c0b8,0x4d830421223760c1043,0xe0c0f223760ec10488d3,0x81d08c3de04288dd8301,0x8203e0d80243ee043304,0xc78248603e15854102d7,0xd040f000c3de04303f03,0x6e0d80012a27c5385c00,0x8024a4388db8301e0e4a,0x5018202221189f0e27d,0x3e140562182486a000ae],#[0x218074203f03a7824860,0x3da860aa1810222150b,0x8103c03a02f0c0f00f82,0xc10101e01a91080f100f,0xd03fc00201a086f000d,0x9c0903d0043048f00042,0xf07207c00200040fc810,0x60ff000a0b3a05c10309,0x9f046100a940983fa044,0x8da1da0d20840480420,0x641c2c300080a903c201,0x86f00080f40a82005040,0xe040f810480420460c00,0x888c120f040aba04203,0x4000100004000103e006,0x27c289f1100a27c10000,0x3000400018a189f0a286,0xba0f207c004000040001,0xe141502040e83c86080e,0x40f000504103fa0c301,0xf0a727fa0cc004000302,0x30c01ba0c289f01de830,0x8215a0fc00304689fe8,0xf27c2e8307a0c120f49f,0x30883fa0c220fe830ba0,0xa860aa18100000168768,0x87683080f7a0da7c3009,0x201068608111a1da0c36,0x208000100005a1da0c,0x5e0de043223040000010,0xc10304a52978349f10a3,0x42270481d02d114a527d],#[0x8db8301e0cc10c020743,0xd30489f12e0d80a27c38,0x89f6020ae05018202d01,0x23150411884082627c4,0xa09e045b15210080f5c0,0xde043781048bd235e0d,0x4388db8368238110a35e,0x73043008a11a236e0ce0,0x6236e0da08304704138,0x4603d7000c11ae042682,0xc01e047223b8509e0410,0x7810c11c104e1cc10e0c,0x2a04e1ce0de04348d783,0x70c020640b440004010,0x8475216c10330481909,0x8103e072140f82f00885,0xe04c080f8230203e080f,0xa9f1005040fa1da38203,0x9f0b4101904900080f81,0x30100020010f27c1d83c,0x727c10040727cc10c00,0x40081010040001000,0xf6a182a86040fc0f82f,0xc43ee0c203f03c12f0c,0xc10443ce1c4047041387,0xe040f5c0027000400011,0x40f8178203e080f8103,0x6e0c3a8db830803c103e,0x4bc03c200f06a3402,0xf8104003e080f8103e04,0xc102f0408f609c103000,0x3c100f040f4103d0608],#[0x7c016185002040f4100,0x86080f4103d07a17c136,0xd04003d0402561820095,0x112e85f04b86100f4103,0x8103d10233c13c02e184,0x70de04e180f4339f7837,0x5e0ce180f4304c03878,0x4103d040f4103d04003d,0x378106e041386381080f,0x3e040f8100e35e0de04,0x6c002d850400323760c2,0x190f2869810c6401000f,0x80e40f0203e03c080f0,0x32c86080f143c2039011,0x43ca1a612e0921b60460,0x41141ab840c0f0103c06,0xcd83d811741ee101183,0x23443360d23c519048d1,0x10cd83d81190b8218243,0xe23760f6041040e4548d,0x23760c108388dd830410,0x10cd83d81600190b821e,0x5414c1760e60b604888d,0x604104401a0624223d23,0xc8dd8304148f1123760f,0x410c0e523760f6040445,0xc1760e23c108548dd830,0x3304240101a05234,0x8d7830340ee12e080f43,0xe080f8403f05e0603022,0x70390560008088075,0x4703f28d7836001808b8],#[0x3e0003e09e040e4204b0,0x8838866000a236e0c11c,0xd8004e0001d080738000,0x800478150f0811ca35e0,0x8578148f080fca35e0d,0x8304b10642236e0e800e,0x502d04640e08203988db,0x4860c0b4088070846e04,0xd2184c8604068109e80f,0x404001ab840827ae0a03,0xba0c104a04001e10178,0x22e830903fa0c2687683,0xf02e8328f0ba0ca3c20,0x3c080f00e4204a040f8,0x103c040000c9a182a0f,0xa0de04128d7837810c24,0x24c15e06414428d78311,0xc1040e4a35e0d610601a,0x11d235e0c37810390812,0x8c04404788db8303910,0xbc00302db050a236e0d8,0x1180f5c003319040b408,0x1ca35e0dc004b1921008,0x4a35e0de04378150f081,0xd06236e0c0e412c47810,0x700080b4088c46e04402,0x84080ca075a09e10402d,0xdb8368238111a08181d7,0x413840e236e0ce04388,0xe04268206236e0c204a,0xd70008a241039b8108e1,0x8ee10203d70008e10103],#[0x5235e0de04341db84088,0x7e820809c10009c17810,0xfaa10203e07a0809c202,0x84081280f02b00819080,0x904a36e0e23c11c4419a,0x124143d05284080f8111,0x9a10121c905d000c089a,0x4065c022183c8dd830,0xc8602d0887621b2103b0,0x2d040b4101c074140b42,0x1281042b0081d0807410,0x70009c00100041da8408,0x32040f8103e040f8103d,0x808f6096083000c810,0xf8101c011080c8182370,0x40c8103204014103e040,0x30b23760c20106410320,0x1010010403c1000c8dd8,0x5610100003db000b6,0x7f2150443000f5c0027,0x80f0e079268249a0420a,0x1d0826810a03c309a910,0x209a1da0c241208441e0,0x28405a1ca11a0c309048,0x40b0a10204a284081281,0xf04000102c04128100c0,0xe8308a3c128f04070140,0x832110f037a0c8443e0d,0xd48ce8311a068442c0de,0x28113037a0c8443090c0,0x3037a0c8443c0da84e83,0xa0ca044c0da85e832811],#[0x3fa0c240fe830b036233,0x8124604218f0463c1010,0x238504077610210019a0,0x89610241d04608075610,0x1e04104160d783781110,0xe12074203268204681d1,0xb810804ac00281d78409,0xde044b8405076e10202c,0x2e8288561210105835e0,0x3d848855150d214103,0x8506a10181d040b6e11c,0x1000c810320408b07c24,0x3c82422a3a013800c004,0xc0c85883c2a01380088,0x22900760128c221120f8,0xe4450f4093050f600c14,0x1630ff010ec05c04e000,0x30f08707c2c1f0406413,0xe436e0c2683c1f01df0,0x810ae05214290db8309a,0x402d784b800e47c1485b,0x3807840c0c8e55c09e10,0x80a1f0cc41215c08302d,0x2a1f3840a87ce102b839,0xee10102d58009075600,0xc21707c0743c0dd8309a,0x90b604a1421911109090,0xb46002419040c81e0541,0x40001000040001032040]]
def g251H7 := limbs80 #[#[0x8009044c0033200304,0x8a0b024188410200020,0x83990e000a540b479b08,0xd09044411d303058f2a2,0x63a2d79519cc686742a,0x5c0800e007,0x6ac8000c279d1fd30234,0xc51ba99ac3fc4ed56a15,0x3c4400062388ec000a2,0x3c600ba1000070ea3580,0x363e01b0000002cc61,0xc4d000164dcbe0004460,0xf1780008aefa48000001,0x161875299b6206000ac8,0x657400197251b000296,0xa2c2d49a48ab6a704400,0x249033042000db4b80c6,0x45d89241f25c2c2732b1,0x2925c67e890c508003,0x3c4800000019a88b0000,0xdba5000011c33ee25000,0xd2f3c0006c6000071ec3,0x9fb301ed3953667e11fd,0x34401120007ce30a24,0x6b673c16686f800074e8,0x2d1a46780f0006000cc9,0xb29a00049b800022be3b,0xa42008c400000068c4ce,0x3a31e2d1800247383a32,0x323fe7b3807d030398,0xeeea7d03e2ccca03c1c0,0x324d0092a31532a22],#[0xbb4f27160a4837e85412,0xc2cfbd0da962074540d9,0x222d761628ea09dd6746,0x940006054c9908b00058,0xa64830a218c4d3a9570,0x25a816fd37f6aa430,0x827882f7a8388f9d3138,0x3c2878bc12c001f57a57,0xc48f28ef406faab07bcc,0x90650252109b4ba68201,0x129948000835921d2c50,0x92a46505559bc880ea7a,0x104815b645a2f0c4ea47,0x588b67bd054a65c20737,0xe0007a2469000000001a,0xb0000059723122800087,0xb2619525b737e72eb132,0xad14f5e1a12e39e7423e,0xc01302f87ea8de967,0x8000000b78118000110e,0x1a855c3f14c001a7369a,0x7b9c1642354000065800,0xb588300009ff485d652d,0xcf4d8001ea0000715ec,0xb6ac68340f5340000008,0x3]]
set_option maxRecDepth 16000 in
def g251D8 := limbs80 #[#[0xa0aa0887d85492154110,0x21e716558550443e62a8,0x956254110eb4b92a4a82,0x4435d30cb12a08879a5,0xcbb2caa8221d39745515,0xac0887b85892158110e3,0xeb16450560443dc2c4a0,0x5158110f70b12a2b0221,0x43dc322b12c08879c595,0xa2c4b0221ce974589604,0x8873a5d56258110e75b,0xb85589604439d6eab12c,0x58110e5cba2c8b0221ae,0xccacab12a28871e5d565,0xe4a8a21d55535c951443,0x87555d15354510eaaa9e,0x659551443aaee8a9aa28,0x910e3abaacab0a21c757,0xb2db92c48853be597258,0xaa221c6d75595624429d,0xe254d42501208f7c930e,0x940483f14a6a1280907,0xed5baa84a0241da9755,0xaa1280906ea615425012,0x241da976509404837570,0x5515250120ed5bb284a0,0x404836d30aa9280907ca,0x75bb2c4a0241ea964589,0x22809074e5d55450120e,0x1d6952dc550483972ecb,0x54254120f94aa284a824,0x483ad2e8a92a0905da65],#[0xc22a4a8241d6b7454950,0xa09075a5d95254120db5,0x699654950483ad6eca92,0x254120f34b2ac4a82417,0x3a72e8aa2a09073add96,0xaa6b1241c79765955048,0x90733dd95358920f26b2,0x965d16248399eed29ac4,0x8920a77cb2eab12414ef,0xdb2bbb2c49053b653765,0xaa9a4155f955d1534829,0x47be498755120e2ebb2c,0xdc55050237f28c3aca90,0x40f94aa2c4a8281d3954,0xcab12a0a07aa59162541,0x8281ce97658950503cd2,0xa5526254140d74c32c4a,0x950503a72a9b92a0a07c,0xe9cbb2a8a8281b3954e0,0xaa2a0a074edd95454140,0x81b3b86551505036730c,0x196454140f1cb2ac8a82,0x5038f2ecb2aa0a06ae6,0xcb26e2b0281ce962dc56,0x2c0a07b254d6258140e5,0xea99458960503d94a6b1,0x6258140e74baac4b0281,0x35d70ab12c0a073add5,0x22a6b0281ab964e09605,0xa07965955358140f4cb,0x97559160503d32c929ac,0x58140e5dbaac8b0281cb],#[0x8f2eab2ac0a06aee1564,0xa7b8a818ed8658b71503,0x53b65b72589408eecc4,0x554d6250375308c02c4a,0x940e66bb2a6b1281e4d6,0xaeab2ac4a07335da5358,0xb12814ed97595625038d,0x7be617558940a77cbaca,0xd9625029db2dbaac4a04,0x8f7cc2eb312814ef955,0x4c3acaa07175d96554d4,0xa814ed96209755023df2,0xe4985dd9408f6cb704ba,0x605439d2c5b8ac0a847b,0x3cb2f02b02a1c7965dc5,0x92c0a879a5895258150d,0x1e695458960542cf32ca,0x16258150e75ba2c4b02a,0x543cd32ab12c0a86bae1,0xb22a8b02a1a7965e0960,0xc0a859e6595458150f1c,0x7965e11605438f2cbba2,0x558150b3dc92cab02a1a,0x38dacab16e2a859ee516,0x6e4b12a18ed8658b7154,0xa879a5958058950a76cb,0x76551625436d30ac02c4,0x8950e36b2ee8b12a1c6d,0xd720b2ac4a853b65b745,0xcb12a166f9459562543c,0x73ae417658950b75c82e,0x61d625429df28bb2c4a8],#[0x608f7c9309bb2a15af94,0xa7c02c4b05ba64780589,0x12c1eca53e0162583d92,0xa6538058960d74c2700b,0x1625835d30bc02c4b05b,0xb75c8302b12c16e995e0,0x29ac4b0733dd15358960,0xc14ed95dd16258399ee9,0x417558960b75c8308b12,0x25829db29baac4b05bae,0xeb2aa7b92c16eb906156,0xaa6b07175977454d60e2,0xe656558951487cb720b2,0x7558921e3abb2caa8a43,0x478eacab0ee0a8d3be59,0xb6e4b12a3c6d6558b705,0x4a8f995958158951a76c,0xd6554f7058bccf22b2ac,0x5c162f27c92caa9ac5c5,0x8deeab2ae0b179359553,0xa7b82c5a6f855957058b,0x171bdd5655c562f26b2a,0x5955358b4df0ab2ae2b,0x562f27c82caa9ac5e4d9,0xb21baacab14bb6538059,0xa822166d91dd56558acd,0xdc5496154110fb8a9282,0x8550443ee2a8b0aa0887,0xfb4a9284a8221df3745,0xaa12a0887ce551425411,0x221f696254950442ef32,0xdd15254110ebcba2a4a8],#[0x50443af2eca92a08875e,0xbccb2a4a8221d7b76549,0x12a08879e5956254110b,0x1f6954589504435f30cb,0x16254110f74b22c4a822,0x443ed32ab12a08877add,0xaa4c4a8221ee98658950,0xa08877add26254110fb4,0xf996dc950443af2cbb92,0x454110fb8c8aa8a82215,0x3e72c8aa2a0885dee495,0x2a8a8221d79765515044,0x886de6195454110ebdbb,0x96551504436f70caa2a0,0x4110bbdcb2a8a8221779,0xf30cb22a08879e595645,0x8a8221d7965dd1504435,0x67ee1b7454110cfcc36e,0x61150442bf32dba2a088,0x10afdca2eca82217eb92,0xe890ac0887bc59121581,0x221ef16250560443be6,0xc5895158110bf9c9282b,0x560442fe724a8ac0887b,0xef9ba2a2b0221ef16454,0xa12c0885fce515158110,0x216f99650960443dd2c4,0x595258110f74b12a4b02,0x4439f2e8b12c0885be6,0xdca2c4b0221cfb745896,0x2c08873e5d56258110b7,0xafb85589604439f6eab1],#[0x6258110b7dcaac4b0221,0x43dd308b12c0887ba551,0xa2c4b0221ee994589604,0x887ba6156258110f75c,0xb9558960443dd32ab12c,0x58110f5cb22a8b0221ee,0xdf32caa2c08879e59554,0xc8b0221ef19159160442,0x873e5d56458110b7dc92,0x5591604439f6eab22c08,0x110b7dcaac8b0221afb8,0x32bba2c08873e5977458,0xa0a215fb945d560442bf,0xfce414254510afacb6e4,0x8951443eaaa6a12a2885,0xf72b22c4a8a21e75655,0x8b12a288779dd1625451,0xa21de774989514437cf0,0x5977254510df3c24c4a8,0x51442beb2db92a28875d,0x3ab2ac8a8a213f596e09,0xa2a28875d5977454510f,0x19f786dd1514433eb0db,0x78454510afacb6e8a8a2,0x4433eaedc22a2886dd59,0xcb708a8a219f776e1151,0xa28857de5176545109fa,0xf390509614427ef28c32,0x458510f3ab2aa8b0a217,0x2beb2bba2c28873d5977,0x700a12215f7945d56144,0x886fa58b8050910df4a9],#[0x54e01424437b2a7c0284,0x9109fccaf00a1221bb9,0x5aa8a9284884fe65b805,0xaa1221aef8658942443e,0x4fee4186509109fdc830,0x551624438faeab2ac488,0x10f36b2aa8b1221ead64,0x22b22c4885bb65954589,0x1221eaf8459162443dcb,0xbdd56458910e76baac8b,0x162442ddf2ab22c48873,0xe774bac8b1221ced9759,0xba2c48873b5977458910,0x217eb9061162442bdb2b,0x517558910f37c2acab12,0x2442bdb2bba4c48857be,0xec22c9b92215ef945d66,0xee48847f66164dc910cd,0x8fd86597724432fb0ab2,0x64551108fecc2cbb9221,0x438faecb2aa88878f595,0xab0eaa2215bf9461d544,0x88855f6568755110abfc,0xf985d5644438faeab2ac,0x59110a7fcb30eb22211f,0x3fb2dc12e88853f65a87,0xcbba22197d8559774442,0x847f66165dd110c7ec32,0x45d5654423ff2cc2ee88,0x510a7fca2ecb2a2157f9,0xb29c3aca8847fe518759,0xbaa211fd96e09754423f],#[0x7f657845d9108fecb708,0x45404823ff28c2eec884,0xfaca9aa2a0241fa9425,0x6b0a80907ea509615012,0x241fa94260540482fb72,0x58d4250120fd4a9a84a0,0x40483f52caa1280907ea,0xd4b22a4a0241fa986509,0x9a80907e65915350120f,0x1f996494d40483eb2caa,0x95450120f9cb2aa8a024,0x483f5324b2280905ee65,0xbaac8a0241eb96559140,0x809076edd56450120edc,0xbb85591404837730ab22,0x550120bddcaac8a0241b,0x3ed2a4b0aa0906de6156,0xac2a82417db935855048,0x907da5498154120f3cb2,0x4354950483ed2caa12a0,0x4120fb4b1aa4a8241f69,0xd2c8a92a0907da60d525,0x8a8241f698654950483e,0x5de6595454120f9cb22a,0x5d150483cf2cab22a090,0x20ebcb2ee8a8241d7965,0x24b2aa0906de59784541,0x8a4177b9459550483ed3,0x354d4254520f3ab2ac2a,0x951483cdacab12a2907d,0xeaeba2a6a8a41cef7658,0xb2aa290757dd15354520],#[0x41bcf83509614838faec,0xd38358520de7c1aa4b0a,0x14833bee9c1ac2906775,0xfbaf06b0a419dd75e0d6,0x6e2904f76578358520ce,0x9ed8458b714839dac8b1,0x64dc520c7ec32c9b8a41,0x83e9acaa9a849047f661,0xbac8b1241f2d64551524,0x69073ba5d6558920e774,0xd6559153482b7f28baa8,0x54d20eaeb2ae8a9a41e5,0xe9b24b2aa69075759774,0xcaa9a41d5d9759553483,0x78f5956455120eaf4ba,0x461d64483a7aeab22a89,0x120adeca50eb22415bf9,0xf28c3aca9056fe5165dd,0xb2a4157f9561d65482b7,0x7f653815d920abecad0e,0x8550503e72a898aa0a04,0xf9caa2c2a82817db935,0x8b8aa0a079e595615414,0x28177b955c550503e72a,0xe518154140f9caa302a8,0x50503e72c8a92a0a05ee,0xbcb2ee4a8281d7976549,0x12a0a057e65b7254140e,0x13f996e0950503772c9c,0x17354140f9caa2c6a828,0x503e72a8c1aa0a07ce55,0xbb2a8a82817bb9460d50],#[0xa0a07ce6195454140f9c,0xb98659150503e732ab22,0x554140f9cca2caa8281e,0x2ef72abb2a0a079e5d96,0x30ca8281d7b955d95050,0xa06eee518654140bddca,0x6254560503d72c890ac0,0x8140f5cb22a2b0281ee9,0xd2c4b8ac0a079e595515,0x2b0281eb9645c560503d,0x7ba5898158140b7dcb2e,0x54960503d72c8c0ac0a0,0x40ebcbaaa4b0281eb964,0xab12c0a07bae4562581,0x281eb9645c960503dd3,0xee518258140f5cb2304b,0x160503d72eab22c0a05e,0xf5cca2cab0281eb98559,0xbaac0a079e5d56558140,0x81de8925d560502fd724,0x518558140ef5c92eab02,0x1502bdb2db9242a05eee,0xab2ac2a8a815ef925d53,0x2a2a07d554d7154540f3,0xced7658951503cdacab1,0x6554540eaea9ee4a8a81,0x27f720c3aa2a071f5d9,0x1ee4b0a813f990e1d515,0x2a06775d78358540cefc,0xd95e0d615033beebc1ac,0x58540e3ebaacab0a813d,0x9daecb12e2a057be4975],#[0xeab8a815ef925d571503,0x63fe19765c540cbfc2a,0x2e05625027f321c0ac4a,0x9408fecbf02b12819ef7,0xaedc0ac4a05fa6438158,0xb12819ee87e05625039d,0xba6416558940af6cbf02,0xd9625039db2eb2ac4a07,0xe77c8aecb1281ced915,0xabb2c4a073b655765894,0x281cec985d9625039df2,0x61953dc940eaeb2aa7b9,0x725033bb0d29ee4a0677,0x7ec32cbb928197d85597,0x36e4a047f66165dc940c,0x11ff9561b725033db24c,0x96554d40facc82caa9a8,0x503abb2eb2aa6a07975d,0xc92eab1a81d5e9759553,0xcaa057be49755cd40af7,0xf990e056550377308c02,0x5595408fecbf02b2a813,0x3ad924baacaa071f5d97,0xaecb2a81d6f925d56550,0xa057be498759540e3fca,0x9061d65502aff2ac3aca,0x9540cfdc830eb2a813fb,0xdf24c3acaa067b249875,0xeb2a8197f9561d655033,0x53f65a8759540abecad0,0xe1d655023fb3143acaa0,0x40cf6bb704baa813f990],#[0x2abb2eaa04fb65b825d5,0xaa815fb9060575502aff,0xbe09815d540cf641302b,0x9755033db0c412eaa067,0xcf6c1f04baa815ed9620,0xc12eaa067b61b825d540,0x811fd96e0975502bdb2d,0x4f825d540cf6c8f04baa,0x55033db2dc12eaa067b6,0xdc830cbaa815fb9060d7,0xaeca057ee41825d940af,0x5ef9261576502bf720c2,0x2158150fb4a9242b02a1,0x43dd2c4b8ac0a879e595,0xb2e2b02a1e79655c5605,0xa873e5937158150b7dc,0x96260560542bf329b8ac,0x58150f3cb2b02b02a1ee,0x6f2a9c0ac0a86de54b81,0xa4b02a13f994e0560543,0x879e5915258150fb4c12,0x454960543af6e8a92c0a,0x150f75c8ac4b02a1b7b8,0x2cab92c0a87ba6116258,0xb02a1e796560960543cf,0xdee495458150bbdcab04,0x5160543e7308aa2c0a85,0xf5cba2c8b02a1e79965,0x4ba2c0a879e655645815,0x2a1e79655d160542fd72,0xe558458150f3cb2b08b0,0x60543cf322b2ac0a85de],#[0x3cc92cab02a1e7b91595,0x2ac0a879ee496558150f,0x1e7b9459560543cf328b,0xd5258550f3ab2ae2b0aa,0x5433bf07b92c2a86d7e0,0xba706b0aa1b5d54e0d61,0xc2a871f5977458550cef,0x6d6558971543cef22b2a,0x45c550e76bb2c4b8aa1e,0x2bdf24ba2e2a86cfe115,0x2ecb8aa1a7f865957154,0xa866f61164dc550c7fc3,0x86593715438facab26e2,0xc5508fecc2c9b8aa18fd,0xdf22b12a4a865f59584d,0x2b12a177b905d952542e,0x69f59781589509fcc870,0xe05625426fb2bc0ac4a8,0x50f3dc82cab12a11fd97,0x21c0ac4a873ee4176589,0x12a1e6d65e0562542fd3,0xb6578158950db6c2f02b,0x5625439daedc0ac4a85d,0xf74c82c8b12a15ed97e0,0xb22c4a879b6556458950,0xa1e6d91595625439db2e,0x516558950f37c8acab12,0x2543cdf28b2ac4a879b6,0x6c8aecb12a1eeb905d96,0x2c4a873be457658950e7,0xcef945d9625439db28bb,0x81dc950e764c2ecb12a1],#[0x432fb0caa6e4a847fe51,0x32c9b92a19bd84593725,0x4a847f66164dc950c7ec,0xf9461b725433db24c36e,0x5cd50d9fc22a8b9aa11f,0xef720bb2a8a857be4974,0xecaa2a173f945d954542,0x874fe517655150ebdc82,0x560164543cf2cac02c8a,0x1509fcc8702b22a1b798,0xb2bc0ac8a869f5978159,0xb22a11fd97e05645426f,0x2f5d97459150f1eb2ae8,0x9564543cf720b2ac8a87,0xb9fca30ab22a1e3f945,0xbb2c8a85bee41765915,0x2a1cbf945d9645439f72,0xe518759150af7c930eb2,0x645427f720c3ac8a856f,0xdeca50eb22a137f9561d,0x3ac8a853f65a8759150a,0x137d95e1d645427f321c,0xb825d150db6b2f04ba2a,0x5427db2dc12e8a867b5d,0xc9700b2aa1b7982e0165,0xcaa86de6138059550bbc,0x7b9060965542ef329c02,0x5d950bbdc8308b2aa17,0x2bf329c02eca84fe6538,0x304bb2a11fd94e057654,0xa856fe51825d950afdc8,0x9061176542aff2ac12ec],#[0xd950af7c9308bb2a15fb,0xff28c0eeca855fe55845,0x2a8ac1e7565545215823,0x79d5957154560f72b12e,0x58951583dd720b12a2b0,0x60d77c22c4a8ac1cef74,0xeb12a2b06bb61d62545,0x8ac1c7d65dc9515835df,0xf65f82545609fcc8704a,0x1515838facbba2a2b047,0xd3eb2f08a8ac13f990e1,0xb2aa2b047f65f8454560,0xc12ff9661d51583cef22,0x41625c56097ecb70ea8a,0x15839dae8b12e2b07bae,0xeb2b09b8ac1ced755897,0xaa4b047fe5584dc560c7,0x3bf9461d525827f720c3,0x8058960b7dc82eab12c1,0x83dd2ebc02c4b07ba5d3,0xa702b12c1cef74e05625,0x4b073bdd78158960b76c,0xd95e05625835db0bc0ac,0x58960f66ba2a6b12c16e,0xddf22ba2c4b07b35d253,0xe8b12c1ced755d162582,0x5bbe458458960b77caa,0x15d562583dd720baac4b,0x960b77ca2eab12c16ef9,0xacaa9ae4b05bbe458558,0xb92c1abf8459172583cb,0x975957454d60d3fc2aca],#[0x9553583cbb24b2aa6b07,0xf2eca2caa9ac1e5f925,0xbaac8b0797e516554d6,0x2c16bf945d564582df72,0x60b8059560d3fc2acaba,0x655835f309c02cab06be,0x7dc8304b2ac16f994e01,0x2eab05bee418459560b,0x3b7565e01514867f329c,0x1535c151daea9f04b82a,0x5473eb08b0ee0a8ed7e1,0xc22c5b82a3c7d6558b70,0xe0a8e7b61262dc151cf6,0xff96613705472facac26,0x558551f3ac82cab0aa31,0x74facbc02c4a8f9d6496,0xb00b12a3e77915956254,0xa8f9b5978058951f36b2,0x90e0565547cdb20b2ac4,0xd951bbac9702b2aa3775,0xfb29c02eca8cfd643815,0x1bb2a35f590e05765463,0x5bd64381595618ffca30,0xe057654a7db21c0ac4a9,0x628ffca301b8ac51fd90,0x2ac06e2b163f59580dc5,0x9ac5e5d905955358a3ff,0xbe1b815c162f2fc82caa,0x37158a7db29c0ae0b16b,0xd76b2b01b8ac53ef9460,0xc06e2b167b5d580dc562,0xc5aed816016558a7df2a],#[0x118059562d77c0b00b2a,0x558b5df08c02cab16bb6,0x7bab00b2ac56ef946016,0x2cab15bb6538059562f3,0xaed94e016558bcdeebc0,0x8159562d774bf00b2ac5,0x8addb21c0acab179bdd5,0x8702baac5e6f75e05655,0xaa9ed760980595539f6c,0xf926016554f6bf04c02c,0x59553daec2300b2aa775,0xebf28c02caa9ed7e1180,0xb2aa7b5d82e016554e,0x9dd76538059553baec97,0xe096554eebf20c12caa,0x1108ffca301b8acb75d9,0x304b0aa0887fc5096154,0xa8221ff18458550443fe,0x7e5d94254110fbcb2a84,0x950443bf6eca12a0887,0xfbcb22a4a8221bf9865,0xac12a0887de619525411,0x221df97660950443ef2c,0x6198254110efdbb304a8,0x50443ef30caa2a0886fe,0xdcc22c8a8221f7996551,0x22a0887de6556454110f,0x1dfa9759150443df30cb,0x16454110bfccc2c8a822,0x443bf30dba2a0885fee6,0xbb308a8221f796561150,0xa08877edd98454110efc],#[0xfb94619504437f30cc22,0x654110dfcc930ca82217,0x37f328c32a0886fee498,0x242b0221bfb946195044,0x887fc6094158110ff8c2,0x8254560443fe284a8ac0,0x8110ff8c22a2b0221ff1,0xd304a12c0887fa549425,0x4b0221fb95450960443f,0x77e5d54258110f7cb2a8,0x50960443bf6eaa12c088,0x10bfccaa84b0221bfb85,0x30a12c0885fee5542581,0x2217fb9850960442ff3,0xe5515258110ff4c12a4b,0x960443df2c8a92c0887d,0xbfccc2a4b0221dfb7454,0xb12c0887be6116258110,0x21ef96460960443df30a,0x118258110efcba304b02,0x442ff728c12c0886fe6,0xcbab04b0221ef9656096,0x2c0886fe6158258110ef,0x7fb9255160442ff72ac1,0x5458110fdcc22a8b0221,0x43df32caa2c0887de615,0xc2a8b0221dfa97551604,0x885fee615458110bfcc,0x98559160443df324b22c,0x58110f7ccaac8b0221ef,0xdf2cac22c0885fee4984,0x8b0221df97561160443],#[0x85fee558458110dfcc2b,0x461560442ff724c2ac08,0x510fbab2a84a8a217fb9,0xeeca12a28877d5d94254,0xa8a21bf58650951443be,0x7da5d6454510dfbc3284,0x9614437ed30b22a2887,0xfdaaa284b0a21fe5525,0xaa12c2887bd595425851,0xa21df77550961443beae,0xe554258510bfacaa84b0,0x61443eeaa8a92c2885fd,0xfbc92a8b0a21df774549,0x2848877da5d5458510b,0x1bf975e01424437f2cbc,0x95250910dfcbb700a122,0x443bdeeca92848877b5d,0xbb2a8a1221f3d6555142,0x848876fdd95450910ede,0xfd7659542443afaeab2a,0x550910afecbacaa1221c,0x2bff2cbaa848857fe5d6,0x30aa12215fd96dd54244,0x8867fdd98550910cfebb,0x76e15424433faedc2a84,0x910affcaaeca12219ff,0x7ac8aa2a48857f657765,0x8a9221d7d7655152443e,0x57f65b7454910ebfbb2a,0x59162442bff28bb2a488,0x10e7ecbac8b1221ef591,0x2ab22c48873fa5d64589],#[0x92219fe9859172443ddb,0xf5db8255110cfecc2c9b,0x9544433feedc12a88867,0xedf43ac8aa2213fd96e0,0xb2aa88876fa5d6455110,0x215ff985d954443afd0e,0x5d8655110cff43b0caa2,0x44433fd2ec32a88867f2,0xac1302b22215fd96a1d5,0x2c8885fee418259110df,0x9fe87609644433fb0ec1,0x7559110e7f43acab2221,0x433fd0ec2ac88857fe61,0xb30bba2215fd95a1d644,0x9067f65b845d510cfec,0x96454540483fe2c2a8a8,0x50120fbcb2aa2a0241fb,0xff72ca8a80905fe65951,0xc2a0241ff18158540482,0x7ee5516150120ff4a92,0x558540483df2cab0a809,0x120efdbaac2a0241df97,0x70ab0a80906fe6156150,0xa02417f998585404837f,0xfe6198150120fdcb2302,0x4940482ff72cc0a80906,0xfdcaa2c6a0241fe9635,0xab1a809077e5d5635012,0x241fb991591404837f30,0xe456550120fdccaac8a0,0x40483f7328b2a80905fe,0xf8c0ac2a82417fb91619],#[0xaa0907fa5096154120f,0x1df97458550483ef2a8b,0x16154120efdba2c2a824,0x482ff330b0aa0906fee1,0xc3302a8241f796560550,0xa0905fee598154120dfc,0x795458d50483fd2c6a12,0x354120efcba2c6a8241f,0x37f708b1aa09077edd16,0xac8a82417fb915915048,0x907de6456554120fbcca,0x9459550483ef722b2aa0,0x4120fbdca2caa8241f79,0xca84b0aa2905fee45865,0x2a8a41df57458551483f,0x6fde116154520efbba2c,0x50951483edacaa12a290,0x20df7c3284a8a41bed86,0xcab22a2907d761153545,0x8a41d7d655d151483cfa,0xfe197454520cfec32e8a,0x151483afacbba2a29067,0xcffc36e8a8a419fd86dd,0xc22a2906df5978454520,0x41f7791595514827fb2d,0x5d6554520fb6c92caa8a,0x1483afd2eb2aa29075f6,0xbc8b0ca8a417f7916195,0x2a2904ffe518654520df,0xeed65509614827fb29c3,0x4258520ef6baa84b0a41,0x83edaa8a92c29077bdd5],#[0xa2a4b0a41ded74549614,0x2906f75538358520ef7b,0xd75e0d614837bae9c1ac,0x58520f3eb2aa8b0a41bd,0xbfb2eaa2c29075f5d554,0xe8b0a41cfd655d161482,0x73f5977458520affcaa,0x159561482bfb2bba2c29,0x520f76c92cab0a41ef79,0xd2eb2ac29073f65d6558,0xb0a415ff945d5614839f,0x7f66164dc520afeca6ea,0x9542483bdaeab1a84906,0xfb6aa2c6a92417ef915,0x8b1aa49077b5d1635492,0x2417ef9159152483bdee,0x6456558920f76c8ac8b1,0x53483ddf22b2ac4907bb,0xafca2caa9a41f5d94595,0xa2c69075f5d55458d20f,0x15fd95dd163482bfb2ea,0x56455120affca2eab1a4,0x483e7f28b2aa8905efe4,0xca30caa2413ff9161954,0xc8906fb6098159120ddf,0xfd87605644839faecc0a,0x159120cff43b02b22419,0x33faebc0ac8906bf5978,0xf02b22419ff75e056448,0x907afe5165591209feca,0x91e1564482f7f28c2ac8,0xd120affc8acaba2413fd],#[0x7f28b2ee89057fe4565d,0x2b2a41bed8260565483b,0x67f61d8159520e7ebb30,0xe05654833fd0ec0aca90,0x20e7ebb702b2a41bed82,0xfc0aca9067f61f81595,0x2a41bed92e05654833fd,0xf65f81595209feca702b,0x1654833fd2fc0aca9067,0xff8b8ac2a82813fd91e1,0xb0aa0a07fc6056154140,0x81dfb7258550503ef2a4,0x5d6154140dfdc12c2a82,0x502ff330b0aa0a05fe6,0xcb2ae2a8281fb9645c55,0xaa0a077e5d97154140fb,0x7fb965c5505037f30cb8,0x8154140fdcb2302a8281,0x3bf2ecc0aa0a07de595,0xb302a8281bf986605505,0xa07de58d5254140bfdc,0x963e0950503bf2c7b92a,0x54140fdcc8ac8a8281bf,0xef322b2aa0a07ee66164,0xcaa8281f7b9159550503,0x7dee5d6554140fbccba,0x15d950502ff722bb2a0a,0x140efdc8aeca8281df99,0x728c32a0a05fee458654,0xa8281bf99161950503f7,0xfee5d8654140dfdc8b0c,0x4560503fe2e2a8ac0a06],#[0xbfccbaa2b0281ff1815,0xa8ac0a05fee5d515814,0x2817fb9854560502ff33,0x5957158140efcb92e2b0,0x60503bf2eab8ac0a07be,0xfdcaae2b0281bfb855c5,0xac0a07be5898158140b,0x1ef965605605037f304c,0x58158140efcbab02b028,0x5037f30ac0ac0a077edd,0xc8acab02817fb9160960,0xc0a07bee456558140f7c,0xfb9759560503df32eb2a,0x558140efcc8aeab0281e,0x3f7728c2ac0a05fee458,0x2ea98a817fb976156050,0xa077be49754c540bf7c9,0x8758551503beee4b0aa2,0x4540dfbc3ac2a8a81bf5,0xeacab8aa2a05fd65d615,0x2a8a81df5765c551503e,0x6fde197154540dfac32e,0xdc951502fef2cb8aa2a0,0x40cfec36e4a8a81d7d65,0x2db92a2a067fe1b72545,0x8a81f5d8754d51502bfb,0xde456554540fbcc82caa,0x551503cfaecb2aa2a07d,0xdbfc3acaa8a81b7d8759,0xb2aa2a075f65d6554540,0x819fd875d951503afd2e,0x617654540cffc3aeca8a],#[0x1503beb22bb2a2a04ff6,0xf4c2eca8a819fd985d95,0x2a2a05fde458654540cf,0x3ff97619515037ef22c3,0x87545409fecbf0ca8a81,0x27ff2cc3aa2a06fee41,0x92e2b0a813fd96e1d515,0x2a07bd5957158540efab,0x7955c561503beaeab8ac,0x58540defc1aa4b0a817f,0x7bf06b92c2a075f5d552,0xe4b0a819fd875c961503,0x57f6577258540e7eb2e,0x595615037baebc1ac2a,0x540f7bc8acab0a81ef99,0xb0eb2ac2a079f5d56558,0xb0a81cfd97595615035f,0xfbe497558540e7f4baca,0xd5615033fb0ebaac2a05,0xef6492eab0a81df5915,0x4baac2a077be49755854,0xa819fd985d561502bff2,0xe558758540afec96eab0,0x715033ff0cb92e2a04ff,0x7ebb2cab8a81d7d75595,0x2ae2a057f65d655c540e,0x19ff865d5715027ff30b,0xb855c540bfdc830ab8a8,0x5027fb2dc2ae2a067f5d,0xcaf0cb8a815ff955d971,0xc4a075f5d563549409fe,0xff915d9625039fb22bb2],#[0x558940f76c8acab1281c,0x3ddb22bb2c4a07bbe456,0xac7b92815ff915d97250,0xa057fe4565dc940cfec2,0x9161b725033fb30b2ee4,0x4d40cfecab0db92819fd,0xbf2eb2aa6a07d765d655,0xab1a817ef925d563503e,0x77be497558d40ef6492e,0x60165502bff24baac6a0,0x40dfdc0b00b2a81bf981,0x28c02caa07ee61180595,0x2a81f797560165503f77,0xf5d58159540f7cbb300b,0x5655039faecc0acaa075,0xcff43b02b2a819fd8760,0xc0acaa05fe6438159540,0x81cfd76e0565503afaeb,0x1f8159540cfec3f02b2a,0x5502bfb2fc0acaa067fa,0xecbf02b2a81bf990e056,0xacaa04ff65f8159540cf,0xd7f875d5655033fd2fc0,0x7659540ebec8aeab2a81,0x39ff0ebb2caa05bfe45,0x8aecb2a81cfd915d9655,0xaa05fee418759540e7fc,0xb9061d655033ff0ec3ac,0x59540ef64930eb2a81df,0xaff2ac3acaa077be4987,0xeb2a81bfb9061d65503,0x67f64587595409ffc8b],#[0x8a1d655033ff22c3acaa,0x540bfcc870eb2a815fd9,0xb23c3acaa06fe6438759,0xbaa815ff915d9755027f,0x5fe55815d540efdc8302,0x5755033fb0cc0aeaa07,0xefdc830cbaa815ff966,0xac32eaa057fe45865d54,0x2819fd9161b75503aff2,0xe41855d9409fecaf02bb,0x76502bff2ec2aeca05fe,0xfec1302bb2813fd91e15,0xaeca067fe09815d940c,0x19ff85605765033fb0ac,0x9815d940affcab02bb28,0x5033fb05c0aeca073fe5,0xcaf02bb2819fd85e0576,0xeca057fe45825d940afe,0xfb9061576502bfb23c12,0x55d940affc8b0abb281d,0x3bdf24c2aeca077b2498,0xf0abb2815fd91e157650,0xa87de5497158150cfec8,0x545c560543bf2e4b8ac0,0x8150f7cb22e2b02a1f79,0xf708b8ac0a877e5d1715,0x2b02a17fb945c5605437,0x7de5498158150efcc26e,0x60560543df2c4c0ac0a8,0x50fbcaa302b02a1bf982,0xe8c0ac0a87be59181581,0x2a1bf98460560543bf6],#[0xe5d38158150dfcb9702b,0x160543ef308a92c0a86f,0xfbccc2a8b02a1f799155,0xb22c0a87be6456458150,0xa17ef925d131543df32e,0xc97158550fbaa92e2b0a,0x1543eeaa8b8ac2a877d5,0xbca2e2b0aa1df5745c56,0x2c2a875fdd15258550bf,0xbdf835c9615436fb0ea9,0x7258550f3eb2ae4b0aa1,0x43afaa9b92c2a867f61d,0xa706b0aa15fd94dc9615,0x2a86df61d5458550deeb,0xd655d161542fdf24ba2c,0x58550cfec3ae8b0aa1e7,0xcfb24b2ac2a857f64b74,0xeb0aa1e7d9459561543,0x875f5d9525c5509ffca3,0x55c9715436ff0ca92e2a,0x550cffc32e4b8aa1d7d6,0xf0caa2e2a875f5d9545c,0xb8aa177d96551715436f,0x9f595645c550edeba2c8,0x91715439faecb22e2a87,0xaffcbac8b8aa15fd975,0xcba2e2a875f595745c55,0xaa1b7d65e11715433ff0,0x65b845c550cfebb708b8,0x71542bff28bb2e2a84ff,0xbfba2c6a92a19fd98593,0x22a4a87de6416454950e],#[0x1f7b905d952542eff22b,0x56558950bbfc8aeca92a,0x543cff22b2ac4a879f64,0xc8aecb12a1cfd915d962,0xc4a87bb6456458950e7f,0xef915d962543ddb22bb2,0x65c950fbdc82cab92a1e,0x2bff22bb2e4a877ee417,0x2c7b92a1d7d5458f7254,0xa857fe4564dc950cfec2,0x9161b725433fb30b26e4,0xc950cffc8b0db92a19fd,0xff28c36e4a867f65186d,0x8b1aa17ef925d1635433,0x7dee417655150afec96e,0x5d954542eff22bb2a8a8,0x50ebec8aecaa2a1f3f94,0x2c02c8a875fe4576551,0x22a1fb974601645437f3,0xf5958159150f7cbb300b,0x5645436fb0ac0ac8a879,0xcfec3b02b22a1cfd7660,0xc0ac8a867fa1d8159150,0xa1f3d855d1645427fb2f,0x456559150f3ec8acab22,0x4543cfb0eb2ac8a879fe,0xfca30ab22a1f7b906156,0x2c8a879f5d98559150f9,0xebf945d964543df720bb,0x7659150e7ec8aecb22a1,0x42ff720c3ac8a873fe45,0x830eb22a17bf9461d645],#[0x8a877b2498759150efdc,0xf9461d64543bdf24c3ac,0x59150dfdc830eb22a1db,0x6ff2ac3ac8a86efe5187,0xecba2a1f7b9059574543,0x857fe45765d150efdc82,0x159774543b7f28bb2e8a,0x150ebfc8acbba2a1d7d9,0xf22c36e8a867f64586dd,0xb2aa1b7d82605655433f,0xdf60b8159550dbec2302,0x5655436fb09c0acaa86,0xfbdc8308b2aa177d94e,0x9c02eca86fe613805d95,0x2a17f994e01765437f70,0xe41845d9509feca702bb,0x76542eff2ac22eca85fe,0xfcc1700bb2a1bfb90e11,0x2eca877ee0b805d950e,0x1dfb84e0176543bf309c,0x9815d950cfec1302bb2a,0x5433fb08c0aeca867fe0,0xca302bb2a19ff8460576,0xeca867f60b815d950aff,0xfd84e05765433ff05c0a,0x15d950cffc2702bb2a19,0x3bf720c22eca857f6538,0x308bb2a1dec926117654,0xa876fe11845d950ef7c9,0x90e1176543aff2ac22ec,0xd950cfec8f08bb2a1dfb,0xff2ec2a42b067fe47845],#[0x2a8ac1ef5625c5515827,0x7bd5917154560efab92e,0x5c551583beae8b8aa2b0,0x60d7ec3ac4a8ac1bf784,0xe8b12a2b06bfe1d62545,0x8ac1e7d655c951583dda,0xfe1d7254560cfec3ae4a,0x1515827fb2fc12a2b067,0xd7fc3ac8a8ac1afd8759,0xba2a2b079f5957454560,0xc19ff875d1515833fb0e,0x4965545609fecbf08a8a,0x1583cfb28b2aa2b079f6,0xeca70ea8ac13ff9461d5,0x2e2b07bb589525c5609f,0x6fd9654971583bdae4a9,0x625c560afecbaa4b8ac1,0x82dff28b12e2b073f5d1,0xaac4b8ac1cfd75589715,0x2b07bb651625c560b7fc,0xd9558971583ddf28b12e,0x5c560f77caac4b8ac1ee,0xbff28b92e2b073f59172,0xe4b8ac1cfd655c971582,0x5bfe49645c560affcaa,0x5591715839faeab22e2b,0x560affc92e8b8ac16ff9,0xf2aba2e2b073f595745c,0xb8ac15ff925d571582bf,0x7f61152dc560affca2ea,0x13715833fb24c26e2b06,0xb7fc8ae8b12c19fd956],#[0x2baac4b07bee41755896,0x2c1eed74e0562582dff2,0x6457458960f76baf02b1,0x62583ddb2aba2c4b07bb,0x77c8aeab12c1eed915d5,0xaac4b07bb6517558960f,0x1eec985d562583ddf28b,0x3815c960d7eb2702b92c,0x5827fb29c0ae4b067f5d,0xc82cab92c15ff915d172,0xe4b077ee41755c960f7d,0xfd9159772582bff22baa,0x559160e7fc8acbb92c1c,0x2dff22baac8b07bee417,0x302ba2c1ebf945d56458,0xb05fee41825d160b7fcb,0x905d574583df720b2ae8,0xd160affc8aeaba2c1dfb,0xf720c2ae8b076fe51755,0xaba2c17ef9261574582f,0x73f64565dd160bdfca30,0x617745839ff22b2ee8b0,0x60cffc8b0bba2c19fd91,0x8c0acab06bf60981595,0x2ac1afd82e05655835fb,0xf6538159560d7ec2702b,0x175583df720c22cab05b,0xdfdc1700baac1bf982e0,0xc02eab06fe613805d560,0xc17f994e01755837f709,0x53815d560b7fcb302baa,0x5582ff720c12eab04ff6],#[0xdc8308baac17bf946097,0x2eab05fbe49845d560bf,0x9fd91613755837f721c2,0x6558951cfecb309b82a3,0x476fb04c02caa8f9f641,0x2300b2aa377f92601655,0xaa8ddfe518059551dbec,0xd8260165586eff20c12c,0x59561b7fc9300b2ac3af,0xdff28c02cab0ebf61180,0xcbb82c56ff9060965586,0x173fe4565dc162e7ec8a,0x56037158b3fb28c06e2b,0x562d7ec0b00b2ac59fd9,0xb21c0acab16bfe058059,0xb82c5eed915957058adf,0xbb64565dc162f77c8aca,0x37158bddf22b2ee0b17,0x2df6cab01b8ac5bed946,0x8c02cab17bb611805956,0xac5eef946016558bddb2,0x6098059553f764bb00b2,0x6554febb24c02caa9fd7,0xaec2300b2aa7f5f92601,0x2caa9fd76518059553f,0xb9ff825c570597ebf28c,0xb715c165cffc22e2b82c,0x5973ff09b8ae0b2e7fe0,0xc82e4b82cb5fd94dc570,0xe0b2defe51825c165bfd,0xfb905d170596eff2ac12,0x45c165efdc82e8b82cb7],#[0x6eff2ac22e0b2dfbe498,0x301b8acb5ff905c97159,0xb2cffe5180dc565cfeb9,0x8260371596bff20b96e2,0xc565affc9301b8acb9fd,0xff28c06e2b2e7f61180d,0x1b8acb9fd9260371596b,0xe7f65180dc565cffc930,0x60b715973ff28c06e2b2,0xd800428014c00015ff90,0x801c100c2004c4021400,0x63c02d6014700918042,0x244085003eb01d180d98,0x815bc0a3804df025c01,0x345019080c0a05d302d,0x7d103bf01d300e3406dd,0xd808ba043e8212c101c0,0x813c009ae04ad824a411,0x2c4415a80a8c05220284,0x1082fbc177a0b8b05b78,0xe069003360190a0c5306,0xe9e0720038381b8c0d7,0xf300f5b078f03bdc1da0,0xf820ec1039080903f541,0x848282384116f0888842,0x9b904ca825ae128f0923,0x1c0a6a051ac284613af0,0xe16aa0b41858102b0a15,0x306617eb0bc685ce82dc,0x69832a619160c6706218,0xf06cfc35ac1a620cf186,0xe64071a8382e1bda0dd],#[0xdd80ecd875783a581cfa,0x961f0e0f6887a243c561,0x4412e2039100387ea43e,0x88d843dc219b109e883d,0xda08d58463222c611448,0x612ac0939048e0240711,0x26b5134c899c84c1225b,0x9227f613dc89d6c4dfa,0x38520c28ea145c0a2185,0x8a960546229d314c00a5,0x5ca0ad0455dc2aa6153f,0xc516440b12c581c2be71,0xa2dfb16d40b5805a302c,0x5e6e2eef17538b9a85c5,0x1f8606c2fee17de0bdfc,0x78c59c625430f818688c,0x193b8c940643c31f718d,0x3b319c60cce465f832bf,0xc834b21a3a8d0e067f63,0x86b9a359b1aa98d45869,0xdbcc6d8236791b1e0d82,0xc8df186f2837571b980,0x21ca78e41c716838611c,0x3ab71d378e8f473d439a,0x8123bb61db70ecc475e8,0xc47a523cec1e578f19c7,0x8fa9c7cea3e171ee78f5,0xfe68fe147e903f0b1f6c,0x4b2087102ec80ba40201,0x8423f21069076c831041,0x86ca4328217b10b1084f,0x468898e4495221b90f0c],#[0xd11a1c8c6845e122d211,0x23fd11ec88ea84717236,0x98324929234891144842,0x684a8d252d927c8936a4,0x98b04bef25d392c7495,0x36d49ada4d0f26691328,0x9413b549d044e3a26fe9,0x282f1402c9f9c4f7b27,0x5163289894428a19a509,0x4ba522b28fc9471ca340,0xb4a68c52fe296b94a10a,0x9528ca85e53fd29da94d,0xb001565caaca551d2a75,0x9f2bb695c10ada456692,0x658b42c2b1600cafa257,0xb3ca59922cb016434b1b,0xcdcb5f45ad32d5096964,0x997104b81e5bdd2dca96,0x2ef597660ba325cd12e3,0xfc12fb717c40bd4e5e49,0xec614f307e182a4c06a5,0x8c558626f31191877cc2,0x8f48c72a636e319898b7,0x87192c0c912645732079,0x832eb196bccb10654032,0x671d335f99984cc5e660,0x9c681c33f519ee0ceca,0xf4d2426905345e9a200d,0x1a91cd41469cd34b79a4,0x6199aefcd6c26af83558,0x9b36a41b3a8d9446c5a3,0xa6efd374f9b95cdbc66d],#[0xe088701237f59beb8de8,0x550e21870b9384e9c1ac,0x71c844e3d471c338ce1c,0x39961cb90e564728b392,0x44739ff9cedce7367369,0x7475513a799d2d8e9087,0xcee0c76a83b359d834eb,0xe1b8f00a77a73bb51dd0,0xe01e5e0f28c79093c5b1,0xf3d809ea8cf48a79f23c,0x7c7f3e269f06cf7907b5,0xb1e7d313e7f9f360f94c,0xe4fdb67e933f1a9f7e0f,0x20088ffca7fbe3fc61fc,0xba2048501f480914035,0x84170a0a9104a281dd4,0xa83a441c420d59065e83,0xb0a8548426a21181081,0xcbd0d768673431b21811,0x7a2245109287e043bba1,0x45022277512fe894d447,0xb35457c22a9514e68a41,0x7c8c7645fba2ebd16ce8,0x51be88db746b7a347119,0x3e211e3e8ec14731a38c,0x67a42492094900d47dd2,0x148e1a4569220e90eb48,0x9336498224b492514922,0x92694564a17a4f4526fc,0x712b6695764aa2253f12,0xa5d752dfe96a14b37a58,0xc36a60c12fd097ab4bbc],#[0xeb4cc12651531fa98aa4,0x49b164d77a6a71349299,0x388e9c0a4dd626d91366,0x7f13b3c9d564e6ba7211,0x227c453d929e814f1ca7,0x5047a81a1406c9fcd4fb,0x22e50dd286214254a0d7,0xb0a36f518e28acd44c0a,0x94aa0a4dc523f290d947,0x9b654d0ca63352dfa960,0x41aa0ed4fe6a7ab53a6a,0xc54e7aa5f15252a8e154,0xab2c5577aaa4554a8aa0,0x8fcac4c55f72ae4156bc,0xe95b10ad4b56872b3195,0xaba615cccae3456f62b6,0x7d9abdad5e88af07576a,0x3c587a2c25960b2affb5,0xab30159622c9156376b1,0x6998b4795a18acf7966e,0x9816c04b5c55ab92d47d,0x92de2d6e70b6fb5b4ead,0x5c5e2e14d7042b7ef5bd,0xa875d0f2e72d72f0b925,0x20bbd35dbaaec8975cab,0x17a34bcc75e3a2f0dd78,0xf9b17c32bde75edaaf5e,0xe4afdad7e30bedb5f54a,0xe6048b017d805abff05f,0xc1d860b7b04f58216c0c,0x628c2c16137309498414,0x998852c3ec61d7b0d198],#[0x3169d8a66c4eb624c311,0x3ae31bf98d56c66e6308,0x11646fb2205901ac7af6,0xeca3164fa326019270c9,0x975ecb67658fb2b89951,0x3d9995ccc66661fb2fdd,0xeb37d59b86cd9166a4b3,0x67cfb3d059e08ceb1671,0x1496880b42e5a0ccd013,0x4cd25e690b34765a322d,0x1a7ced39469a0b4be5a5,0x55c1aa3ad4d56a413509,0x45b5965ac22d5df6ad6b,0x6bf6b5e11ae78d6d36b,0xd9606c81362e9b0fad84,0x614dab76d3236845b3a8,0xc9b86adbe26dd836d1db,0xb75f1ba68dd0d6e5d371,0xf40b793dbc3addeb6edc,0xb26fafb7c89bdcadea86,0x8e114706638211c036df,0xc48ae20870eb38665c2b,0xf0dc70ce333717038a09,0xf39285c8c8e42771fab8,0x72d3395fdca6ee505726,0x6f87358399cdcc56e5cd,0xe4e7b573c1b9d45ce3ee,0x9d15ee87d7430ba0bdcf,0xa64dd2c2e9457489ba35,0x30ba8e9d426e9e174e2b,0x1759a3ac35d58aea9375,0xec65760ebaf81d772eb7],#[0xaeaed3876783b2f9d902,0xbddc90ee1676f23b69dd,0x3bc01ddb2eeb27745bb9,0x802bbfa5df6eef7a77a4,0xa78613c215e0a6f0167,0x8f21478ebbc63de2a4f1,0xe6a0f31e7970bca65e4b,0xa5e804f3d079d4bce09,0x73d3f1e9c0f4ae7a38bd,0x7b00bd769eb3af56b7a9,0x7067b5f3da5deccaf63e,0x92f7977bb2bdd51ee70f,0x1f14ef8757c21be045ef,0xe601f2def9327c8b3e39,0x323e8f5f416f9d97cd93,0x87d85beb91f57afa8b7d,0xfc267df4bef09f720fb4,0xa40fce37e5e3f229f8c6,0x61fb78fda07eb73f51df,0xbfa55fcdcfe317efa3f7,0xfbcbfd1dfdfefee37f63,0x47801b4003dffd0ffb67,0x900b7804dc022a00dd00,0x363017f80ac4046e01e,0x922044301fa80ef4070a,0xac0b660565028b813240,0x81c340d7e06870332817,0x43381f5c0f6a077d03a2,0x450506827ac12b608e10,0x60ba905a282ad414fa0a,0x1a060ce10649831c4184,0x9cc1bf20dd706cf83544],#[0xc83f5c1f6a0f3b076b83,0x86c841d420a6103107f,0x28b091e8476423161111,0x46136b099984bec25861,0x42a0e14770a1f84fc427,0x5a8c2cd616070ac68555,0xf385ebc2eee17550b838,0xf0cb08644c318a184b0b,0x1abb0d41868d433fa19a,0x82a1bdd0dd286d5c35e6,0xc43ac61d150e63871e43,0x87ba43d361e4d0eff876,0x4d881343ffe1f9b0f90,0xf510e988564424220e91,0xe234311598893c445a21,0x4966247b121688fd4474,0x6d44b26255b1291893ac,0x589d6c4d962651130c89,0x14918a3ac510e284f13f,0xaa915228a72c5326295b,0xe2c2315d48acbc55ee2,0xc5c022db316a78b35459,0xbd145e1a2ebf17438b88,0xc88c45c6166304f17ea8,0x119a68cb4c64b231c918,0x35151a638d1e4685633b,0xd3636791b0a8d7746b1e,0xe46ffe376f1b858db4c6,0x8e7cc734a396d1c6e8e1,0xdf38edb4766a3ae71d4c,0x571e798f2ec78ae3c351,0xe3ea51f208f8247b4a3d],#[0x818a40351fe88fe0c7e3,0xa8c847e41db20bb904a4,0xb911248772436b218390,0x22dc9165c8a9244fb224,0x73f238391ae48caa4607,0x6e493d2456920cc8f724,0x4973e4b25254a9286c93,0x37ac9b0e4d23265f9306,0xef93d949e2e4eb327279,0xd28cd94484a17a502d27,0x534d296994a6ca44251b,0xb5e55092a3c950aca736,0xecaf02571d2b6795954a,0x967e4b2d258d92c2f95f,0xe2d96fdcb6ce5aed2d39,0x232eea97674ba1a5ca92,0x25fc92fbd97c04bd0e5e,0xc45661b1309b982f4c0b,0x7cc71e632b316398934,0x599874caee653f325799,0x341399f64ce9266e5333,0xa1b34e69a49cd1b26875,0x9a6b7f35a39abe4d5566,0x4db126cf9363f9b014d7,0xbc94ddae6e7337129b7b,0x6b9c27ce0a26fd737c49,0x339129c704e28e712538,0x73ab39a39cbe4e5ae727,0xbee757d3a979d224e81e,0xe4edae769f3b3e9d96ce,0x9e174f04a77953ba39db,0xd079e654f23678f93c55],#[0xd73dcf9ec3cf4fe7a473,0xa7d0f3e609f11cf81e7b,0xfee27ef73f1d9f6acfab,0x7fd036281214048a0004,0x9a0e9505fe829b411ba0,0x42aba126d08c6842b41f,0x777437ea1a0d0c6a85bb,0x288db4446a20a50fb68,0x517828b474550a289d13,0x36251a768cd7464fa309,0xd4a3dc51dee8e7d46f6a,0x7489ca42fd20b6900d47,0x93174959a499523aa918,0xa6e94914a0ba4ecd26f6,0xb52de696a54b15a56152,0xa644d313298354bf3a5d,0xd78a6a35342699c54cb0,0xa34e2aa6fc537729b3f4,0xa9e5f4efda765d3a0e9c,0x3f9e9f814fafa7c9d3d5,0x65d423aa0a35035a80cd,0xca8ead4662a2a1511ea8,0x528da938d492aa44751f,0x6cd5334a97654b42a569,0x22a7ad53baa9cf54e0aa,0x552eaa927544baa17d50,0xada5560aaa5f5508aa76,0x98ab3e55982ac5d55f1a,0x9574aab91d5b9aad9556,0xb09f57f1abe555e62aef,0x4a2b22f5906ac59d61da,0xfd668eb2f95960aca256],#[0xad2dd68feb41b59e6acd,0xb55ad8c56bf2b57f5a98,0x895c12ade556ebab7255,0xeb97f5c98ae3e57182b8,0x75b2baa15d13ae765736,0x43d78febc315dc5aecf5,0xafa257c4abded5ec4af,0x5fe6afe557ebabf0f5f6,0x1116056b017d804ec005,0x5ac25f60f2b06058292c,0xd8822c3c361a4b0bed85,0x17658b42c5696282b122,0xf1b1ead8e8ec6cd633fb,0xf64a3b23e5912ac81b63,0xcbd565adb2a7d941ec97,0xdface4166cdb342d98ca,0x8da27ad0d96824b3e359,0xb4fdda6fad303692eb47,0xb63b5935ab4ed52d6a4e,0x8f6c15b5fcdaf1ed7576,0x2da4b6cf3b6505b1bad8,0xba0adc756e13b6e05b5e,0xc3dbd56de316ef1b75a5,0xbb8225c076dfc16faeb7,0x7107b8705c2e6e10f706,0x3c171b9b8c3dc582e273,0x8ee4e3724ab911dc7f2e,0x5cd56e63172fcb95fdca,0xa2d5d0a2e7c173b9b9c9,0x33ba865d3c2e97d7497b,0x775c4bad45d606eab575,0xed0f7660bb11dd81eebd],#[0xddaee897712bb7b5dae6,0xdde0faf01977e5bbd9dd,0xbc9c5e446f1d578b8bc3,0xa5ebd0b5e73af3237954,0x857b1bbd7a5eb36f5377,0x2f8417be3bdde5edfef6,0xf496f9e77cb6be4d5f1a,0x155f7e2fba37d94beabd,0x8bf68dfad6fd337e67bf,0x7f94bfabdfcc2fe297ef,0x149807dc025e0066ffa3,0x47026b8119c0796032f0,0x3c18320520bc7c0b6e05,0x423c183e072208c21342,0x2360d0cf84f0447c1c8f,0x1f0390c0283207249c40,0xb80f08f060f81c8e47c,0xe0178478307c0e4503b6,0x540160cf84f0447c1c8,0xc0f839181602f2280c84,0x8740f8391ac238243a0b,0xa07c1f02c1b00782144,0x8f07e090e83919c121db,0x2114000bc1083217c250,0x42820b05801c241f0723,0x7c0b09842081c203e08,0x6082c170183bc23c1b85,0x283e072108307c0e4210,0x60e47145077c141f072,0xe0722784e03e0a0ef08f,0x5e0087c1b09e0f0403,0x83e0f8a0338021f06c2],#[0x834e1108c1f1815384e0,0x82c11e0f800391c1520f,0x2782e0107c1c8a0abc27,0x5487c4e0009c1541413c,0xe11e0c1f0391f800270,0x684e01a14160a08380f0,0x62383081011cf83e1408,0x9450200b0008a12a07,0x85f0de049503b1088786,0x4a81d8800820786a280f,0x9e0417b862543f86f02,0x48000edc304011c6f830,0x1a8a03e1013f86a28100,0xbe0fc08a205e0d86081e,0x31be0fc082f0240d8631,0xc1b1001013f86e281005,0x1004e04637c1f811440b,0x80abc35140802039080,0x885140802110f0d45020,0x24e2786a280cc9389e18,0x81064e18938fe1a8a033,0x1f8170c1006052e37c1f,0x3c083270c49c8052e37c,0xe0c19036181cb8df0600,0x20c809036181cf8131b,0x8f0c0ab8a04010c6f83f,0x805e05e04c6f830640d8,0xe0d8305bc004f8361014,0x5030178041406c1f0013,0xfc08270662a8df07e041,0x237c1f810600d8551be0,0x9300e46f83f020cc1b0b],#[0x2f02e0027c1b0a0ab4f,0x1fc3684021c0342b1418,0x1a37c1f81e01a1b42827,0x35802c4783f040bc1c9,0x8df06803c0d8607c382a,0xc98df07e049103e181cd,0x7c3039f02637c183e141,0x107c302203a637c1f810,0xd86080381d072637c1f8,0x1b032181cd8df06803c0,0x501b02f1414f86b05650,0xbe0fc0b8607c5582f0d6,0x7c3029244877c148571,0x8607c482971be0fc0b86,0x43a0e7c150471be0fc0b,0x89072e37c1f8170c0f86,0x39f0448bc0f8331a0f,0x68278331ba141f174130,0xf8b24407700039f05e0,0x491704f05217c098df06,0x9144f82f072181dc000a,0xb8513e3e00f040bc4f83,0xc28a11ec103284107617,0xbc19116081942083b0bd,0xc358291be0d0078183a0,0x5e382c83be07c1c8d07,0x3e181678183be0e46b85,0x7836181cc8df07e040e8,0x41f09f1546f83f028881,0xe0b8203e13e3f82c0161,0x16141f0a1150e82dc01,0x2f03e0dc2c8d07c5f82c],#[0x8152a110150590764378,0x283be07c1c8df040bdc2,0xf82f02e140e83e241642,0xc1c8d07c5c22073237c1,0x81905980243782f03c13,0x252c28a114178390a0e,0xf03c13800460543f04e0,0x81201a18178aa2146f83,0x6f0013e0f84d1a413c1f,0x420f844448744f83e101,0xcf03e0e4683e151121d1,0xe47005237c1f8107c282,0xa402091be0f8270045e0,0x1bc1f81021a3782700b0,0xa11946f83f03614178da,0x303d142348df07e041f0,0xb8003e13e468df07e074,0xa1b42904888ec85e09e0,0x7a268df07e0782700021,0x6e09c034290095c31940,0x700b0a401071be0fc0b8,0x1f0da1bc1f81021a3782,0x201c9007683f83b11604,0x23d07f080cbc121df076,0x1815784f04866c478307,0x2f1d46f83f028741902f,0xf0aa37c1d82f02874190,0x5c20321e46f83f030741,0x741f0a0b3c0c1df0723,0x30741902f2246f83f02,0x30640d87b0480246f83f,0xa8d07c4829019e0546f8],#[0xac01417c10a243be07c1,0x782b09803c0f8351a0f8,0xc1032b08064a43b41451,0xf880580890ef81f06a37,0x14f82b09e0546f8303a0,0x37c1839f030741902f1c,0x4e1246f83f020e41f132,0xf0581c1c83e0e43505f0,0x7c1f81e01c14138c0b01,0x417c0a8df060c81b10a3,0x1e074303214e4039d04,0xdf07e041f0a0e746f832,0x781f06a36c20321c0ea8,0x46f83f03610190a0b011,0x720f8491be0c1f03911,0xc1f039181c83e0a46f83,0xe0fc083e100ee8291be0,0x7e0743700e0a09c791b,0x1021a3780705b08468df,0xf8305e87c1907a1bc1f8,0x321a8022107c1d0043e0,0x20321f06f83f03075c20,0x4178e0b3c0c1df07835c,0xbc7041837c1f8183ae1,0x64182cf03077c1e0d70a,0x77096150ec1f1417c1f0,0xf8542ee12c2c2143a2a1,0xb610190e07706f83f020,0x3a0e46058877c0f83c1,0x83f020f86025e0f0683e,0x1e0db0a0bc708c07706f,0x38011f06c202c43be07c],#[0xf17c158407c4750f8a03,0x2c0643784f0447416c1,0x1b20f0643409c11e0c1b,0x413d850463209c11e0c,0x5e13c16800962f08f07c,0x2823181068007c12c406,0x80f8321b84783e0209f8,0xe0c1682c1c8d68220a0d,0x447c1f06417c2780611,0x8f836158103683e0c84e,0xfc0e8006c3085e05a00,0x3e0e86e8006c3039a1be,0xf832111011f07c182cf0,0x3e303683e0c8310a0da0,0xd83e2b02701c081683e8,0xf810720f85240e001f02,0xc0f83c1ae001b0f837c1,0x72303643e0c83058217,0x1f0522d08e0760d0c82f,0xcb8405347c5b06865465,0x1c25830220a68f8b60d0,0xf060f84e03e0c118401,0x70100008fc1840178084,0x2230f065e0dc308c05e3,0x918844178be0e4602f07,0x45832c7e46029100cf83,0x230178d067c1c8c4220e,0x60e41f0906408b86f06,0x303a0e780d8207c2f08f,0x238083907c2f830720f8,0x2f1fc1a11b0c0f84e07c,0xf0c23114a11f07618190],#[0x81c8fc200ef83e020e41,0x8447709c0d0e70143360,0x6c3219709e0ec1586d0a,0x206c382d433e0e08b860,0x83e19c370108203081d8,0x4e0231c0d308e06e0c1c,0xf81c8804780b82833e0c,0x9066c231f0523703e020,0x833e0ec2211072292703,0x81c8a0741f584e020e45,0xc041f039180cd84e020c,0x7c044e0391c08d84e07,0x2e11c041c900d811819e,0x701072303605f613c183,0xc183e072281de100cac2,0x741f584e020e45823613,0x8cbc1d8470d0450c8c8,0x32442c210370c047429,0x11e11e0ec27010643041,0x81922040c87d86d0a46,0x72238443b4501c88e102,0xd2280bc1c880468482f0,0xf8503b046c241f064281,0x8468178c0741601f7040,0x709614160e07743f8305,0x3eb0b07c505e0c90e81f,0x3b8407da188d10045c20,0x6c2114064381d82260f4,0x6128a032144bc11a1e87,0xfe0d0e98c05e2a1d023,0x1e0fe0ec121db0a0bc7e,0x501f0801a8a02f072201],#[0x2e120ed1407c281d4234,0x60e01b8082cb040f8602,0x6c103e101cd824220f84,0xc1ec17010720f85f0607,0x23c1dc3b83e020e41f11,0x5304089c202f084501d4,0x41f06440460590861038,0x1f090744bd82058845c2,0xcbc20390843c1d83e280,0x3c05c282f32c1182e020,0x81c3b2983a63383f8342,0xfc1f808391400f850580,0xe0e0c80ed87145c041c8,0x2fe0e076c3d84e020e47,0x1707b0800011f0107238,0x64282f83a08451039145,0x470a0b08023074513140,0x8391811032e1107780d8,0x808391a0ef0806561108,0x4510391b8403203b613,0x887e088391811819e0fc,0x3a41c088391c17a1db0,0x707d61416100f81e584,0xb21f06c203c709c040e9,0x508e08d0665c190bc000,0x450d58481f60b8021f2,0x7823c183907c2597a21,0xc2700d0b07c903e0b01f,0x1b429886907d82846441,0x93890c10e1381a83e016,0x342d8283e321141f608,0x7c02c1586d0a4a1a41fc],#[0x580d8642283f0470350,0xc43e0d8405ae1fc1f00,0x4608f060b34282f17800,0xb81832c1160ec2700072,0xe1ec203ef070441c8c0d,0x8a88d41e85e0003d0f8c,0x42a1f191180fe008690f,0xf800391ec201a220047,0xc03f428e06b0458407de,0xd0a844724f82181f0070,0x860343927c1003fc1b86,0x2c1f16c2090c1020c08b,0x7d86d0a3910e0003f4,0x844cbe1f1304090f07c0,0x8ba0ec270043e0e45828,0x14e1f0ec268382287c1c,0x12e280fe016170f88044,0x1f12e0c83f07c0411a8c,0xc85b89401c2c9763e23,0x7e0f8082316e2783e02,0xc1840e020f87d08c7c19,0x1a0a0970641882e0dc23,0x320fc1f07e0dc04118b7,0x3783d040b01f0da128f8,0xc51701e100e41f0cc1c0,0x725783e100f81c89c0,0x4488381f08b0820b80f0,0x6d05c005102107234271,0xb01f0c0885041f07c211,0x20e41f0808981f08e020,0xe11c07800a20724f0862,0xa283e0e4984f08046703],#[0x89210908303d0480b800,0x21420c174120283e2898,0x4449a220e50f83e10164,0x81010785ee17c1d84d0c,0x907c2097b0987c1909a0,0x907f060b01f09e0f8403,0x83b85f07613416862223,0x87d85f07a0b4338420,0x1406c251fe000d8320fc,0xf00d056181b0e107806,0xc20f0023e0d8440fe0f8,0x10780f0000e00f410361,0x6c0c817f08e03c001c94,0x4e004841c8c08b81f020,0xa84e020f81c8889c0e68,0xbe0f8083e178083e0721,0xd07c2380f00072404050,0x30040b01e0c08b42032,0x2110e0087c1c88040038,0xaa8a08884880a2084,0x307881f80f000724684e,0x700d0847ec28c0fb4278,0x80f00b0d617421610508,0xf070820f00800700600b,0x8401000e00c0168470c0,0xf1c202220fe0c1f70005,0xe07088384e01a160f900,0xf07e0b43685708484121,0x86d0a03c8e000400380f,0x3d821c08007005e0f806,0x6c215c0780007007a141,0x800700600b80f0070da1],#[0xb80f0070ba1ac2140f00,0x614160e1040800700600,0x100f8702001c01802e01,0xf07c1d8108161902783b,0x9104098008a59f270219,0xc3702d08381702a04ac2,0x188a03e170ae1230f802,0x8e21c2b8d0762a000616,0x303e1e0238e7100ec480,0xc1f0b011c0b8df06101c,0xe1a8602f0dc34047020e,0x83e178122242a67c1b0a,0x8121506c3040c09c08cf,0xc2038607c2386b0688b,0x1440d881440d82007e,0x3e100bc15b1be0fc0e,0xb8141570a09c61446342,0x607c1c154240d83b0c08,0xd83b0dc09c282f138158,0x1e0f8158607c24151440,0xb0960c09110400832cf9,0x87b03802c3702d0a4019,0x802d43267e8a0d867091,0x2c3783b100cc1f0e0a68,0xb11c37830541004b0280,0x40c710e384711015c683,0xf85a04e21c683e1200,0x71a0cc1f0ce0dc0b8d08,0x820041001f05409c1b81,0x6054418db061001f080d,0xa0b414f02f06866c238,0xc3032150cf8370d0481b],#[0x1cd8606c4f83e05611,0x40d8683363406781f078,0xe0027c902bc0c1cd86e0,0x14401681a10bc1207f02,0xa24a1688502e016114f9,0x86d0fe0f8068106c5517,0xf91206c182d43583f838,0x80d20f709c001549f184,0x6200d48541ee118949f1,0xdc080d687f07a078003,0x7a24a1e81686e0161071,0x51250fa0743700a18351,0x82b84e05c0340c87d0c5,0x1f43681624331762ac49,0x921f40e8661843057092,0xd0ce15890cc658970060,0x81d0ce178112c1243e81,0x9036144382b04dc13806,0x24f836060182230d0520,0xc280e43e016130a0391,0x9c20058101519f080203,0x828bc1f8191a8481b0e0,0x253e0fc0c8d4240d8605,0x3b0bc0b80688d07a346,0x60c1529f080189f06c10,0x80ce0127c1b0b4494f83,0x1b04067c024f8361416,0xd0e2181b040101549f08,0x8504561b8109ce0009c6,0xa18200843c83f001440d,0x70006c361206c110f20f,0x8068606c3781d1be0f43],#[0x1fc1e86080290f20fe0f,0x94178170005327c421e4,0x3704d0a4205609802c6d,0x2cf938670a987b03802c,0xe019b0760817a0405380,0xec182d053c110c99f1c0,0x5808f86b11e0c1f110b,0x80047c183a07c2840b02,0xab0c046c4783b020f880,0x840023e0c1e03e142001,0x2c0e4602f141cc8c07c1,0xf07609c3415054421d05,0x420760815120b414a19,0xc82719c368508c43c067,0xb428271c11386b048560,0x622c70ae1b8260002b60,0x10a16c683b1102b04c01,0x403604d82588b1a0f86b,0x75c303e1e09d8331a0f8,0x2e181f10089c6f83f020,0x2444504072075c6f83f0,0x1637c1f82f020e70003e,0x31b413c1f810720741f1,0x81f07802c303907c4922,0x81df060f87045637c17,0xe0ed8607c202231b217c,0x607c181df060f82309e0,0xf8383b61b4283e120ed8,0xb10e89f07c202cb280,0x3b60b0002cb0a0f84f9,0x8707c0b38221db024822,0xb41113e0f85f060b783d],#[0x7c2f8205e0544f908768,0x8740889f07430a122d04,0x4285107040844023142,0x2142c10210e08c46d853,0x839b180bc405e236c2d8,0x27c1f0ba18c603e0f83,0xf032340e83e18c141d14,0x41f12a181d83e0c1cf83,0x582825e0fc0a8d20807,0x32181f0e04a0e83e0c1,0x407c074970405646f83f,0x15e0fc1781073235c2d0,0x3f05e0646e000736141f,0xf8191b2181f0f0741178,0x46e86b0a0bc583a067c1,0xd0c0f43d1ba181e87877,0x24a02a12c283e83a1e8d,0x4e0027c9d15a342e09c0,0xf4bc16885e0406a07f0,0xa134a178041682227c1f,0x700435a1fc182cd020f8,0x8012fd0a27ca05bc1c43,0x7c5244474230a0205c13,0xfb4096a6a0782aa2aa,0x7507e8708c06bc1f04e0,0x3e142078307e0f842444,0x3d82a2a3040f06c03408,0xb40c87d0c5785d0da054,0x331c632c578270070ac0,0x4b0290fa05c2e8662a,0xac13702e09a05c2e86e,0x1fa0c8cf04e0127c910e],#[0x4e016174f8c0f51791c4,0x611e0027c1f1004341f0,0xc182fb0a40462444770b,0xe81f0985b08e81d0fa1b,0x24740789f0744040f060,0x8727c1f061191192214,0xc1f09c13800a093e0a85,0x10c1049f07c204908727,0x8c8890ec8214027c1f0e,0x1f082838270093e0a850,0x41cc8d07c304908727c,0x3e0fc0c8d07c301df07e,0x5042842404213e5a0225,0x461b82682e0011911b85,0x83e205091570aa244f8,0x878450754104691be0fc,0x302203b237c1f8108c0f,0x3e28a091be0fc084607c,0x233e0a8505ba08156153,0x704e000aa4a09c138068,0x3f04f07c02c36820544,0x3782203e01a08151083d,0xe00c00e82054484641e6,0x600a8408dc138000f00,0x3003a08150461f82700,0x2de080fa4f8a03c038,0x642f002444744f83e198,0xf07c1704e00c081f49f1,0x344585d1a3e88d1c149,0xc0e74283e2545f04d07c,0xe08422283ba37c1d00d0,0x203fc1b00121a1743581],#[0xe04342f83005a1ac09,0x87e00e0d0e83e1b82700,0xf44d1be0f4303d11115,0xfe0c1f0461b46f83d0c,0x3d0dc138002a1c1101d7,0xa85e09c034311e0746f8,0x8068607c183ef0643c83,0x7c4f04d0de0b4283e15,0xdc138068df07e0742b82,0xd0da37c1b82f020f86d0,0xf4303e1782700d0c0f84,0xc1081f00d0a490f20fe0,0x800f8751a0bc8810f50d,0x607c268601e01c018010,0xb837020bf42900e58068,0xc3685c2a432263ae19c3,0x181f0408dc6f83f03c01,0x8307a2840f060fc1f096,0x3d86f060f46b0361ec37,0x9c3b837020f45b02626c,0xd1dc6f83f02e181e8ae1,0x8da1782700316e21c1b8,0x1e8a081c3387706e041e,0x140858225c6f83f02e18,0x4704e0003c03803003a,0x5c3704f07c01c468502,0xbc138018271ae0dc40ee,0xf02e3782700d0a0407d0,0x2c303e0bc098d07c1f83,0x2d0d614643be0ec103e1,0xf8105f614808c0f90ef8,0xc482f171161dd0da37c1],#[0xc1658907c2e86d060c8,0x2876c47830720f87e0fa,0x10c0cbc18190725d1a82,0x3c1808d81235623c2782,0x2419210e811b11a0c1c8,0x8504562019507b02875c,0xe4210c07483d81d0c0f,0x3e0e4210d60dc122013e,0x3b02c320e8de12c1f821,0xa19b02e120e8e2410cf8,0xc1e86b03c14914e073c1,0x74179223f00019120e13,0x1cc19025a37c1f81a0a8,0xa180bc343aa368603e10,0x29032a0e8621d05e3019,0x138183ae23c18a007c38,0x411783f032340e83e20c,0xe2b41a8d0660f8408c0e,0x504bc1f8151a4140e83,0x7025e0e0e83e101c820b,0x81dd0da0dc141923808c,0xc1f82f020e68283e43a4,0xfc0e0051a0f87045a37,0x7e0646c8607c482243be,0x7c288807228a0e815f0,0x321a0ef83f05e0646e00,0x303e230ee8dd07a1ac20,0x4a0736080ca8df03e0d4,0x1f82f0361146b0507c07,0x7c1d8407d074407228bc,0x105a508d7078001c84b1,0xc415c2382422e23c1b8],#[0x1073e0e4690c07c38321,0xb8291be0c1c83e1c1078,0xc1c8dc000e41f1484882,0xf81c9028811782f02e13,0xe3086f0541646f837080,0xa18301af09e081c91913,0x86a32351950fa0743700,0x3384e00458250fa07c26,0x98c8cc718cc8760ba074,0x4654f8ee1181487d03a1,0xa4785e08a07e83b08,0x907c2886f060b741a88e,0xe810720f86435a23c183,0xd7830780f8523ba1fc1,0x743e86f076101910100,0x5a23c18390782e1ac23a,0x303e108ed830780e4403,0xac1e88e000e4840fa06c,0xc038282c2011607b080c,0x580f84421a2019583b09,0x7f07a05c303e18038030,0xe05703e0c5002f180f40,0xc2829307a081683e140c,0x720f8408603fc1e8607,0x86f07a181483e12c4783,0xf840860a403f83d0c0f,0x3a0e74103e1341783072,0x1f0810ec0f831400f850,0xcbc18a005e2d88f060e4,0x3907c37830720f83b020,0x1e8607c321d905623c18,0x7c18a207c404325241fc],#[0x2881f0a11bc083903b23,0x7e064683e23c0c8df06,0x7212c608c2890102cf,0x7007020b4b11ae0e1070,0x151221882b84841e0dc4,0x781f072341b039e00631,0x1c9741741420504289c2,0x6828400dbc1c8d709c00,0x46f830720f85140c5443,0x941042e0027c1c94076,0xe041c9212d11b84707a,0x1e0e919708e0f8028971,0xd0754103991be0fc083e,0xf0e0e60ec8df07e041f0,0x707307646f83f022801,0x3e8200e00ec0f00e0a0b,0xdc3505b0805f8068204e,0x83d03f00b0dc17410271,0xe8220c6f00e0ba08138a,0x5e0003c03803003c1413,0x141390e138070506609c,0xc280f00e00c00e82e01c,0xd07a347d0706d4428d07,0x3907c1a8be0bc02c2688,0x202df060a6c303e14c18,0xdc001f080741f684072,0xd51be0d8283e1444839b,0x22d080f89f05e041c81,0x828f07746839b0740343,0xe4712011b42783d0d607,0x23c23033c02c4783d080,0x2448684f07a1ac0f0005],#[0x804003803005a1814d81,0xf02a37c1a8607c4046d0,0x87f068741f0a0e45101c,0x2b83d07a101f0391c1cd,0xc1f022e0fc001c912348,0xe0f800a20722b8710de0,0x6840722c8d0720f8307d,0x8003983aa10703b23419,0x13f05944383e70fc17,0x5c0382e8623c1f81d1bc,0xd0c0f8507c43c83a84f0,0x5f07a181f08c0047883,0xc14510e43c83e8607c23,0xc0f85064a3543110e01,0x5f07a181f08c0047883d,0xc8771be0f423860642b0,0x2431d70ce1dc1b81d080,0x8d5138df03e0f42386c3,0x190720d85f060e41f060,0x2500f060f81c88033c1c,0x7a181f0ae13c183e072,0x9f07a1ac203e1414c0cf,0x101c894004183907c202,0x5a1b8280fb024c1d07ce,0xb040f84e000400380300,0x82d1be0fc083e1894a1d,0xc17435841ec103e0b0ed,0x3610190e8741f129f05,0xd0d6104c3ba1b46f83f,0x68601fc0382d81241f70,0x4483907c281000e00c01,0x79c16850581085911c0e],#[0x3e100f784f040e4210a0,0x2b8423b07c703a4820f8,0x3c1a9a07c31178404bf4,0xa148e82c83e501da0da2,0x34484b120a1141d82105,0x24142582105a23c191d5,0x19a1fc1e8123a0d88058,0x7d03c1b4282f140d40f0,0x68100e00f42d8205e388,0x43f8307d6134091d2025,0xc1f685b09c18703503f,0x3e0ec2700134403c10fe,0xe0da16c2140774403e07,0xf34084a02001c01802,0x10ae0d44703e000b4161,0x2587a23c182c0782032,0xa17424212401086121c0,0xb20a10982708108a81b,0x2072108508d08c9140dd,0x584e00e150f910374198,0xc2e8108c384681e06a08,0x1b4282f1408007005e0d,0x3c3417c8ca3a308f10fc,0x3a61c16e8207c3783f0,0x1d70ee0dc0c2007c302c,0x1b87702077c1c2007c30,0x2e4460f83e190ec1f07c,0x143be0e1003e18248201,0x588b02081c282f1ec3d8,0x46588f060e41f0de0e41,0x7c222243b07c1f08444,0x8283a87c1c8c8890ec21],#[0x1d817038341f1424044e,0x81f0e11a1103903b60dc,0xc8505808bc1f81c1a11,0x1a0741c90446c202c43e,0xd0585220d040cbc2783c,0x12610c1e82702e22c2c1,0xd059e0fc0e0d07c38901,0x388f076141602f1c16c1,0x9085d0447c1f0c44446,0xb091020d054341f0c883,0xc0b010783a1b0741f0c0,0xf0a48942f8207c87c8e8,0x60f83e1816b0011907c1,0xfb8041f19890857040b,0x7ce120f82d1dc102d708,0xd03ba101c8c215c17000,0x222c1b6160e8e0541960,0x1150dd09074707c0b416,0x770683907c2f8307c0b2,0xae101960da000e487050,0x445836800391d1141d22,0x1d2018341f0c0fa0eb84,0x160d43b613428e2a4102,0x9c2087a000e4507c2a61,0xf06c27830358241f080f,0x282d0083e8f8da02c131,0xc30afd0006a8f8906815,0x434481dc0fe0ec121a07,0x96081020715fe0f40586,0x40fe0ec1680b0c868670,0x3e03b01fc1e80034e189,0x180270da001f8e0fec20],#[0x1c138007212c502001c0,0xe19c23804280e4258ae1,0x2c23c1d80e0fc045003,0xaf09e0015308f060b741,0x2ce0fe0c8d701b000d8,0x83f011400f85b0e81b41,0x1c22820640e4258fe0f,0x4865c07838340b47e02e,0xf074234320c0643d0805,0xfe0a241c041f160d036,0x800700600b43705b0048,0xdc042101f07c4e021280,0x40038030056038282c1,0x82f1b81b8043a0b60f8a,0x17d811c47f83b03a1b82,0xf8218603c03e86f07c14,0x703f8101a43e0f86c280,0xf0801f40f8307c10c508,0x816c1f07c202de0507c1,0x6a3e221204e0a88f88c0,0xf8508787c1f0623f4003,0xe14178a10c1003943e0,0xd03e0c1f04317c1e8104,0x83b0087e810390963887,0x2b84a056010f82d260eb,0x70683907c4c1d322c254,0xf86445076c1b83b02e0,0x1a0f8683ae0ec1e0d072,0x94400f86153077c1f81c,0xe0d0720f85b0f60ec083,0xc3b87b060e41f0a88bc1,0x720f85c1be0c1c83e12],#[0x834400e4258a44b06f83,0xe91021261016c1f2206d,0xec45814400b47e04e010,0xe0f42d8105e3d84b01e0,0xe0b0f83e1447887e0d,0x1b080b4c961f07c202d3,0x101f580c3e2d8070587c,0xb601c202d07d87c505ae,0xf83e0ec07827080fb0f8,0x3e358041987c1b080b70,0xf07c1b843056001f02dc,0x1783100b70f83e0e0661,0xe368102001fc1f82b01c,0x704291e21ea16c1b8252,0x84b06e08623c84887d83,0x2211b040c8323c85487b,0xb6088809216c111040a,0x178b6090089706424854,0x6c103216062111180e4,0x40c908d82066240c052c,0x192c8248168089048060,0x20641c83e1419301066,0x1f048478083e072201d6,0x432209c423c041c88054,0x41f084b34284076c2039,0xe0c1f10fe02198221e40,0x211b096081f088758083,0x960b808d056c25820382,0xb04c041f064b20aa05b0,0x7808c0740890f7080f85,0xc0419060cc193847048a,0xc0f9c2382453c045705],#[0x17840740ca11453c05c2,0x110910f7058008b0a424,0xf705800683ee094b832,0xd21521ee10583e469091,0x82897c02610118907c8,0x13040c84046074097013,0xc832536090f823104be0,0x970641d820641206b040,0x25c19078045b8230ec10,0x4661cc183021fc046c02,0x809291411a1d21fc0440,0xb0083905e2023024633,0x87f011417820e417846,0xb0c170105e203304661,0x7011816301b040c80e8a,0x1161811812058074c2,0x700182160910f40d60b,0x26130010fe023184a02c,0x460480e92943e281202,0x4523504887a06b058006,0x617808c4a580e0030540,0x2044878a04808e0021e,0x403a057809291011886c,0x8b808390c0cd84072874,0x8221fc04407da1894862,0x289088c0f887f010c1f1,0x20e40e8a2804bf01058,0x242228b80839100c9846,0x140a81d25287c4e0208c,0x84a02211a82a43d03584,0xa81121e617808a4a5809,0x1fc05c20bc05c10230c0],#[0x880960a800320c0c8112,0x190fd822201a1f40b608,0x90110fa83b0540100090,0xb0183e0b0243f60a800,0xe06304240fd07818c208,0x7e83b054010f8d03f41,0xb04241e01f6090308846,0x83200243030907807a06,0xa4403c03f41997c0c2e,0xe061741c230b41982c0c,0x20c84052081e023a0c07,0xf08465c281a0d8f89722,0xd81a0f908211d610e0c0,0x760c0c8302e0424206c1,0x424106c1d81a0f904241,0x824202906d040c8302e8,0x3903d0403c623e41581e,0xf4160002e040402e0408,0x3d0405c080ba080b8100,0x837020c1d8180f148390,0xec0c0b82a10160110201,0xb810c28282a02e044360,0x5e1e8202e040320ea140,0x260ec0e4102913010290,0x21a30202003029040e4,0x3410a0880f383d0488c5,0xb1086820c2130760684,0x2c04e1701144c441c88,0xec0c8104101e304104e1,0x78a40816011020201060,0xc8302912810820460440,0x920c182c21fa14307c83],#[0x81f229b0c1829041f02,0x20282970c10390780839,0x7d09c04301f60e801111,0x8360ec0e80010b04289,0x307e4202c20a25000216,0x60c16385091658508160,0x10207903dc3061041e38,0x36c08199f4240d8333f8,0x67f020460ccfe040cc08,0x5830408e04b0661b810a,0x40ac199fc081a12b061,0x306c1a0209025830ac1a,0x84230f810c1910e04358,0x2c085424044c370205e2,0x108443810c0bf0250230,0x90958e09c70204808e04,0xc6b83190158e0ac72040,0x8b81036101382212c848,0x667c4201222181054242,0x61b810781011441001b0,0x3c382560c938760c1022,0x85b060d8321e1205b064,0xc081908108c3983221c0,0xa0ca81181604201130d,0xc0b8e040901110a44381,0x12c703638140b6382b1,0xc50800d8210b8080911,0x4e0415060a84d21231ae,0x10360c16a12e040d8442,0x8527d8205c0887840b78,0x7078078403e4f8403e4f,0x128353f41035020aa820],#[0x38c49c201a41e329fa08,0x4082a0816601054182a1,0x202030020a0d4f80f15,0x81388a041b040b14f81a,0x6054f8270241a8353e04,0x60025060541012020103,0x2a60883f408a0334082a,0x26888060a907e810c198,0x12020189a42827c313e,0x5a0d4fd040c090100982,0xa1341884134185a0c820,0xa0f0882e8341e1c12820,0xec5589384118e3120b41,0x268384e1b19624c30362,0x60780787210826830e8,0x4180fd3e1c0fd06a7c3d,0xd06078078703f41a9f0f,0x10868360127c5d0627c2,0xf93e1b04d0683e4f8808,0x780787a0c07e9f0f41a0,0x5b1c81020600b02d060,0xe0ac70267c0b81202181,0x4806600020258e0502d8,0x827846b83702849080c0,0x921013e1b834248404f8,0x4c11890360d89036090,0x401f470401f470441347,0xf101b038148805a1f470,0x50800d826020480800,0xa812c18c4480848db06c,0x60603ec08c2788911011,0x8db0603ec08923583d83],#[0x4041981001e209f82014,0x181b0404808040a80904,0x1010e20c078a1001b042,0x9c306067c0800f10090,0xc9f6002e1206c119f024,0x88205b0627c5224042c1,0x93e1b04b0603e4f88448,0x9f22404004b0016c180f,0x27d82064428120513e24,0x49f004c00078927c105d,0x100a4f81260818120201,0x901010f4104180f1a4f8,0x8201602261ac1a15140,0x3b06608148806808986e,0x102221a16c198221e282,0xe108c398310a8546b07c,0xf0a12821187307c10508,0x9c303e100b01102a6181,0x43cc3604b020f858220e,0x81170c0e838220581f06,0x20f8c3704141f4110781,0x303e081f411034181a02,0x4e381022216c083c10c,0xae0c2388e3b8205a15c7,0xa08e0b0004607c311631,0x44052268c6b83094282d,0xe0b0003e181488542ae0,0xc150e4283e081682290a,0x8798d706e07428e43dc0,0x702190f702118308e108,0x5c1f04160e83e0887f04,0xe05c0a29e08184a08463],#[0x44210427c0b01107c203,0x8607c183f3042181f080,0xc10209461cc1f0410878,0xc151417a1290c0c04059,0xc0c8607c209f8220e9c2,0x70a0e848220e81f06e0a,0x8de0960cc1042181f011,0x108391b60d8204210118,0x8904646d8303c208db06,0xc1b04084241191b60c20,0x13e260021fc11c089236,0x862528544f864a5c184a,0x854308c0b643382c000f,0x860fdc128607c2086b0a,0xc0904833074321fc11c0,0x1687d141f00d0fa28307,0x218303444007c9f108,0x42f0013e280fe00101ae,0xfa0b386e010445090108,0x15184d00fe000f84f8a0,0xac11144fc16507c02088,0x808f0013e209f82dc000,0xf188328105406a078a05,0x1014252831040414f80,0x1501a01e2a9f1040b00d,0xb40f000780f87904a7c,0x90b00ce81608203f90ae,0xf0023a220fa0c217800,0x203e035c02c30848b4,0xe60483f40880f907d86e,0x1f586141f20fd02183,0x181f00fb0c181a505c],#[0xf846102502310e20c417,0xc0d287506a0850901084,0x513e26807f001007820b,0x3f80042844d00fe0027c,0x3e0c1f823105c001e0a0,0x1882e000f1c30c1001d0,0x7218601fc01c3060fc1,0x3e01044713cc5d8900fd,0x486902383a13f059c2e8,0x80011144f00fd06e0b80,0x1380515a18181610ce17,0x12e016085847a0e41102,0x2a87506042c10945e8ad,0x3c03c682041741c0f53e,0x2e00e146020e1741c820,0xe8393ec105638c658ab8,0x7d05d07c004f8b0a40e,0xb0a311cd07c024f91915,0xf93e2048084a0f8009f,0xa7c4d0683e4f87a0d812,0x760b805851a0ae83e01,0x41e9f0c07a9f080f2875,0x20283dd0640b4f880f7,0x87506a085d0607807a82,0xe146d0607807860bc0f2,0x2040408e10443f00942,0x6d03c001d03e14100829,0x4513f2178003a41e2c8,0x3a17800260b8003e01fa,0x7e810742204b040b3800,0xa37000520f81d088440,0xe01e304710e20f80041b],#[0x3cb0c301a90c2078003,0x43a02b1c103f04620b80,0xc2404211ae0dc0a23d0,0x944a44f8ae0511e82,0x1086e000b44fb1511c1f,0xc618311ae0dc0f00090,0x4101011c2807b1c18099,0x7023846d040a8333e03c,0x2a0c1d01001e635c1e82,0x3485705c001f0c11b410,0xfa38390bc001f060b6c,0x81687d1c1e87d1c1700d,0xa08e0d4f84a1743e8e08,0x46452a7c08915a082a29,0x64483a870802228320b,0xd040c0c83e0a0e90403b,0x4189a91b60c0f08a140e,0xb06c0807c9f12c189f03,0x64f819e082d8301f27c3,0x513e1085b02818303a0b,0x93e2c9f041d49f6041a0,0x1fc10408c0a88103d,0x20b800927c0ab020e4f8,0x485e000f8393e082301e,0xbc004f880e9c128607c2,0x2a21942f0090a290fd0,0x480840e887b8313fa147,0xa158003e148789f08c18,0x211ac170007c2022d0d,0x8307c090207c103e041f,0x11b8000f70218460800f,0xb81081f00f51ae0dc138],#[0xac001f06a188103e0c07,0x3883e0003dc08a0f8103,0x7c101a90da0b80186144,0xc303eb02304007c10400,0xbcc103a70c300fb04e08,0xf702104007c103f0780,0x3cc6b83702284007c10,0x21d07c1f000536043074,0x106c28c11b8003e0c23,0x70660ac09011c43883e0,0x83304281001f234c4583,0x1b8230b604602123404d,0xe46d83302e14601f236c,0x1041d187942e14603403,0x90118210a101e27c608e,0x2201a7041009310e0c30,0x5f609c08811807b85b0,0x2f01e61cc1982702380f,0x3dc0841181f5850c1d0,0x4c2906081f056141f04,0x220470820e807987306e,0x90c608190a03d46b8370,0x81f0a0ca430330c0d200,0x6041e039141c81a02321,0x6e0ac0c8607c2411709,0x1f0117080f0407d0441e,0x46e0a0e8e11a8383e0c,0x81704108782323486583,0x188f084282311bc16c1d,0x2c1d810820e4791ac16c,0x236c1d810842c1191ae1,0x8421608c8db061044072],#[0xa2212066148d60b60c47,0x43b4301786855c238207,0xb0003e181f0292340fc4,0x235c1847141101da0ae0,0xce0b0004607c282c13c,0x1181a6012184d0fa2829,0x34046430827807c860d,0x4313c03dc14869022829,0x21a11e83904181a70804,0x50c0c25a875074004808,0x4202913da0c860946689,0x789a0dc204a1d41810b0,0x58ab827082b84d060780,0xa543a83a002107638c6,0x9191f41e9f832184b082,0xc20a2788e683b040a740,0xc0f00f0c0f28750760a,0x391410683601a041c8ba,0x50417081822d06c03408,0x200305304a0419482102,0x4064a18198606a802001,0xe54303e0c10082902040,0x11101c81ad028001e0a0,0x2e810780f8307c0e60d0,0x780e424356134083c072,0x7e810cc103e01fa0440,0x783582d02a181f080f8,0x84078202240b60940a00,0x18229020f81e080f80d5,0x2d2184080f1425041b08,0x80bc3b1c082c07c103e0,0x90580080090018211dc1],#[0xe4258b8001485a081,0x3504e078002d1446b83e,0x84211ae0dc0a23d043a2,0xe0e46446e07410391025,0x96108513c235c1b8108,0xc383ae041c86235c1b81,0x60c1911d0661832d040c,0x1ec706e12c7040264318,0x46d0409c202003c27080,0xe04407803cc6b83d04e0,0x270b41027080800fd04,0x191003e8e0b43e8e0b41,0x16007020a4305a0741f0,0x820e4c6b83d08302d07c,0x2388f1342381072184b0,0x3aa10302a0f8251ae0c,0x8db07607800470723d05,0x58591b60c23839104f0,0x403ec08a0e44f08db06,0x291b60c07d811246d836,0x7212c40380f8208c0a4,0x5c103e15c082d0846b83,0x1016b00838182290d41,0x104509400205a0701170,0xb54241d0c1681d033a,0x840f01c88d706e07421,0x18003e1742381072184b,0xc1542700144382dd0da1,0xf8207c083e041f02d03b,0x830800f8208c0f822040,0x207c184007c10401440f,0x8c3084774103e0f4268],#[0x836002e8207c101690da,0x290541ee04308e468c6b,0x1ee04207803cc6b83702,0x258a0e646d8360012c50,0x98002d0a46d836000e4,0x2203844780581198002d,0xf8205b6120e30010168,0x4383a0f8203a0f82704,0x307c0a1d07c10220536,0x75c2382066283e43b61,0xb847040f8483a0c82065,0x660ac08f0760cb840e0e,0x1360c302003e46b84b0,0xf91b60dc1184b02348d,0xe10402c03e46d8330228,0x5811004b840825041078,0x9604302ce08202003cc1,0xf584081cb84b02180f30,0x3e04c103e0ac203e081,0x81110ea19b08183eb081,0x8c201ee04201ea35c1b,0x910140f81d70448c4058,0x1601e0841c1f13403e42,0x83c0760886268078420c,0x2c10612d43a831216085,0x48a0f82c534474505824,0x582109009a059a048e8a,0x408c2021608250ea0c08,0x780b143a83a00210709,0x34091d1416500108184b,0x6943a83b0821221340b,0x41c8a1281e0403ec204],#[0x8c0340839101500c601a,0x302c708104a078e10303,0x1e321e41ba0f40890318,0xb044010c1a230c2e834,0x8a8790688cd07a048009,0xc10421b06984d0603f40,0xe416811e11c0dd07208,0x4608210c29e0f40d709a,0xd022aac10f08e06e8390,0x83d02844883d035c2e83,0x39201a0f097121035c26,0x4818c220f40dd07a045,0x480683d03446683d02c0,0x6108483d03741e81154,0x4d072084080f1d06984d,0xe8381e614210a05b06a8,0x6e83904204c280f1d06,0x160f40dd07a04170a06b,0x81b08383981a61341842,0x1010181e03983d03741e,0xcc28421706809309a0d4,0xa0c4098501e3a0dd0703,0x1321741985140d60d909,0x6c1b2174188101e360d0,0xc083007042010018101,0x90703a08160811814841,0xe074102c100e832d0418,0x44c564158143b0807120,0x240f6050ec8207220464,0x7060820b20ea0d706e04,0x212c705f08a0ea8208c6,0x72184105907506b8370],#[0x3283ae114119c1a0eb81,0xa08505b076c2b8410230,0x16041606242c2a2083a,0xc08805808482e00a0856,0x10049849081f000920b2,0x85601a08506484a4281d,0x47c3013214c2860748cc,0xe8403a240c23e1383068,0x90743c00e0416060b40c,0x7860b11158143a202d10,0x8221590a074343b6081,0x202d214c2860748cc85d,0x5e1a1508c874303aa10,0x8f888890aa840f1161d,0x37022a0f23e103f706c0,0x2c501ee04208203d86b8,0x307c258a0e6c1b0083e1,0x68707d8002d0ec1b0007,0x80e111e0107c683ec001,0x31416d84844c00405a08,0xb820641843065075c203,0x3074208d075c103e120e,0x83943a1c19709074303,0x3b6081906070165810ec,0x41219b088743c3a0c824,0x6b837022a19b08161d06,0x64204a07ee18308203d8,0x1602600190a0e5417010,0x4c0039138082a081cd0,0x11140cf0121e4584a02c,0x39c3e200cc0bc04879,0x7387c421fc0f0f87c0cc],#[0xd309c0c87e1f17819800,0x7c4041c0cc010fc3e281,0x688d8491f0d11b836044,0x12c50860a42046124218,0x5408168ae0d0fd02072,0xd2124420ff021891a1f6,0x210707a008f89a181681,0x2309d0047e429851509,0x23e2661006e0d1191f84,0x4218a970a184932a10c3,0x232a2a2205b075c25801,0x82d83ae103065075c230,0x830644044142c1d6042,0x660c840550670282db0,0x5c258015c103209c2382,0xe11c158007c221c05b06,0x51f500282db01065c208,0xc1c80a3e03c501360e40,0x5086104a3e040c10605a,0x1f02261040284168f811,0x87419048750cf0550025,0x243a86540076081905,0x19d016103c3a0c8205aa,0x6005023a0e4161f01e2a,0x187c0c8d87c04882020,0xf01260140080740b384b,0x41c10787c08182b00261,0x7081e1f3086003c3e0,0x41c104041c23820f0f8,0x9c00603dc204e09c204,0xc3e0]]
set_option maxRecDepth 16000 in
def g251H8 := limbs80 #[#[0x69c1870e080020e0c001,0x2420a3264908000c0000,0x82000a00186022808106,0x160018100001800a0,0x604005000001c040c,0x22008300021808100081,0x6200000400381000018,0x60018508208800058007,0xadb922a4120b04180020,0xc28a00341a00a4003808,0x115024400200044830a0,0x4022801606000824408,0x28c681000859c5a302,0x1c5000c1470981037478,0x40008454005b60c4c088,0x1980042008910106800,0x800f26240224e1018510,0x1000604104060489f1e5,0x1d2e5c68000380010604,0x51a00008020098c0004f,0x7e0c9073c0008,0x10000020010d0630205,0x9120c202864871d0,0x848b4210902000010038,0x1062a1368008ac480040,0x700010071a049804408,0x6120810d03b0b1c24001,0x30b0f0c0200d080a3802,0x64c9834a3020d060c037,0x15201c82801000040811,0x528d1a10c1102404ae10,0xc33703a550de0550bee1],#[0x54af6133847b648c0001,0x64b7677576e200000000,0xc10e0000000107bb26c6,0x232000000000e16e0001,0x2791040db34c0001f56e,0x65aac14200000000044f,0xa81f680e00000000e387,0x20d4000042a3e0a00000,0x371f6136c35600002769,0x425f347d404de3060001,0x1a6ee,0x134620000,0x1522400000000a2fe,0x7320d6360000,0x101a80000,0xd71991ee0001e0d80000,0x685f21640001984d14b3,0xe3e6000135f0024b,0x327c00016656a0a2e17a,0xb34286e60000000053cf,0x86a1a3d9744ec7ae5244,0xc2f8857b048400006249,0x119e0000a4b01740e65f,0x14a80001c4eb0278003f,0x1b1b00000149ff60c,0xa480b28ae1bc0000670e,0xf3f961f7034c86e12779,0x1a1c00001a01a0001,0x267f664a00000001a0ac,0x1327f61ebe45e0001,0x1d433b38e0000,0xa41f015c225c8600],#[0x5c2a68b20b5a39a,0xe7ce0000000146f6b40c,0x198000186bd2102e369,0xf7b6835d042e20883528,0x535e850884232834,0x44320001459e00018122,0xa09850bc0000c2cec523,0xe45da14400000001c548,0xc6b6a771a67267aa0748,0xa678a5ff04365122a58d,0xd25ed662e343b4dd8474,0x4002a4ecc801a6d44477,0xa50b27dae28be2fde466,0xc10605fd614600009367,0x739da497001882f60000,0xd55a20b1e5bdc3f7a792,0x2de00000000b5167028,0x1807c52101fa22d7,0xc6da62d17319c1700000,0x11371c637131a05ca,0x10254311200001420,0x50d56810000000000000,0xe38e000153d36764808f,0x44e3c31a2505a63040fb,0x725c80ea000152f880bd,0x17194818551760001,0x2389485a0001238ca550,0x546400000001,0xe37dc5ea240706d00000,0xf2a1c7efe84570b94370,0x510d205fe36765c8e76a,0x1581cc77e00000001],#[0xb3c5a55662000000,0x253023f80000224d3832,0xa284271e0000f04a,0x10241341ba70a90da,0xa6afb81f62f3c5a00000,0xc82e000046078323c39d,0xd0694235f38c2797,0x1e611221fb188,0x2112000000000001e21c,0xe190000000000000,0x2470a1e7d1aac1dc0000,0x10e80000000183d2c2c1,0x67e7e66585fa347b46ba,0x156cd67b400008208,0x535724d3353b180a5a4,0x23600001f4820001b3e9,0xe4a2300001d436e744,0x22a18575063d67b00000,0xc169e04400000001,0x262a31ee27c00000000,0x6721f3de63a103269235,0x46d8e462000171d80000,0x4b966cf43da000191e0,0x1738c302a5d014b140dc,0x7368000010e3e4d71748,0x540448217425a20ac09c,0x17ffe74a00000001b4ac,0xc72b67720000a06c65df,0x69a4d88852a01ec542,0x4780e06fe7560001e141,0x3155761056f8461a131,0xc44a26de000176e00001],#[0xe77da19b4478504cc507,0x5262e7c801a0c67a1844,0xa2daa558661364c8663e,0x1d65230c20001c7bd,0x65c5c26000000000,0xc6ed63520000000183a2,0x7ca00000001c1a20001,0x47be000000000000,0x651d686000002784,0xc8300001833423de,0x235e0001e498000142c8,0x21260000d5f8e2900001,0xe24e0000a57600000001,0xa7666108e6a40001e104,0x8654039f02ca0001,0xe2c6a7980037a52e60b8,0x378262ed4046328c001c,0xe0495664083e46187564,0xf3cc13dde12a46760001,0x209566ace56c000080e7,0x1a3100000000182e8,0x2156e7500001a6b5b42a,0x96a05514c2fb6193,0xc2d3077652c600006694,0x717ba44000000001a661,0xe490818a0000674c220e,0xa20785cc84420000c7d8,0x93957279a30b107dc689,0xc421e06a625707a20001,0xe66223ae000105f943fb,0x83ba679f872c00007226,0x43dcb5ca040f82960001],#[0x96cf6210f08d24100000,0xa595e2ea85b44740271c,0x805800008150e04366f5,0xa041e17c23cda459c304,0xe3ea046565260001d33c,0xe1aed82fe74200f8e214,0xf3ae000187f3e2dc0001,0xa7e0000000000000f2c4,0x44b3c6a882a520ba0000,0xc5d9e4fd166111ece21a,0xc3bd822a447302226029,0x27ad85f2017800012050,0xa732213a454e0000e5a6,0x665d2038c2f4e086827b,0xe1fc724e00000000,0xe203c395073f27959070,0x1726000195060001c517,0xa42ae717,0xe68ef6660000230d10ea,0x62be51cae08a,0x85860001145882800000,0xd29763e80000000185c6,0x64f0257fc181a2520000,0xe4df46ea431da2b7c408,0x5a280a6b44795e5a29b,0x92e940ef2159300a0001,0xe70d518da2ae435485ed,0x788c62c448a,0x4826433dc81c000130a4,0x7dc00019092a671e6d6,0x66049375c3e4f2b3a272,0x105b6060c023d446b],#[0xa1c5960800008242,0xf401a3bea84931e60000,0x2425a583928e47340001,0x31a200000000284c0001,0x84c00000f6b6e4dc0000,0x16de00000000614a20ca,0xa5cf85b9181a00000001,0x128600014283,0xa7cc6017e1f9055c6312,0x535961180000a3800001,0x110f0597049a936e0001,0x51840000307e0001c805,0x482e495e836832984ae,0x18419,0x1a53b7350,0xa7b9269c000023852148,0x165c000161d80000b43c,0xb43ba61560747349271a,0xe620000087820001c186,0xe6b8000046ab67f48012,0x13ba0000a1fe0001c449,0xa55561b3454593c66687,0x2703105e06839468,0xc28e000187a1264ff77c,0x143c1a251a077d1c7,0xe34e878bc42932538718,0x145a24d0000127f7a318,0x3272213516cb15c58572,0x93d75338745e0001657d,0x91ff2627b0c131dbc54c,0x4fe0001a308c36f41e3,0x333a1193e2a688584715],#[0x18359e66867fd0727,0x800cc37ae501a6cde698,0x146e0000e183a842b61b,0x875c23b60001e1b90375,0x45dd474ef049844de3ee,0x632a82a000120c22638,0xc07c44cd84a0f250966b,0xe3a80000609be1d4a348,0x22696646278ee2e54730,0x71780001e3cbe693c3c7,0x86fd426aa32c70bea4f4,0xc758000027d290a9,0x22d95329e2bac4e65298,0x669e412f9062f59e2455,0x9127213e52b591a94117,0xc1ec000042874057c54b,0x80216514c3d705e92034,0x500781ba000183380001,0x32fe0000000000004722,0x1a43ce0c6e02c0001,0x46c178500001a350450c,0x18110000000002054,0xa5414822d075a7f0,0x61f3c4120001633a0000,0xc6b09460000000000000,0xa0f2e55f83e0c4a2c62e,0x31c8c5d60001c071,0x9145a19c0000637e0000,0xe7d1e4b4a38a00018645,0xe598000000000000c33e,0x162760000a80bf818,0x136a85da00000000609e],#[0xf85a35c793b3140320de,0x3586e8246258c23ea6d2,0x82b5e578616a644701f5,0xe24483aa402ac7b3d128,0xf3fde115010bc06302e7,0x288a29467879610a538,0x139331de24ce82993355,0xe1cfb3d9c6caa510435a,0xc26e0001337a823b042c,0x67a5b0818197a4014696,0xe552e20db6e4b5ccc7ea,0x661f013de724000086f3,0x51d7261bb0e775a14011,0xb492000072f32293f36c,0x2707646d56460000,0xa1be266bb3b66274a120,0x43a700b6a40441cb5255,0xe2ee0000464ca022e439,0xd142913fb274084eb457,0xb190b0ffb258c0e00000,0x4f34378436a55a40864,0x4129e4e883b800004392,0x6561e73de07e243a84e1,0xc3e204aa11f5,0x75b65f00001123c0000,0x52c0001461601b4666c,0xe4acb0f9a47c0001,0x450e0001a160c537b454,0x564521520001659a42bd,0xa77a0000,0x1a502000003b00000,0xc3b4000023f1c45ba642],#[0x24bd88694469,0xe0b200000000000042ac,0x1486200012571a713,0xe1da161367f80000,0x18265b1d0610170ec,0x26fb2648000000008226,0x237230f408373ac615e,0xa377059c000171be0000,0x25894841d3da01d06529,0xa71141ee00000000c0c8,0x1e17e00000001,0x4c3429e8061e4c6,0x140c00000236cc332,0xb03ae7040000260fb3c2,0xc2d5b2760000000057b2,0x6221b44400000001c1c6,0x11280000006a3c78d,0xe85c0000000042a9b6d0,0x44e5055bc2b08025f3d0,0x51860000000000000000,0x54f40000211c00012067,0x51b232a002e0001,0x14b7e29c000000000000,0x8546000171e40001065b,0x83d622d63314073a3b2,0x46250015c43ea2aa0001,0xe4148752000116a4e56a,0x121b0000000000001,0xb4260001a533e2b8,0x47e0001c6a664a8246e,0x103c20000a0ae0001,0xe7d601cc3269048833b0],#[0x185e030d60000d505,0x62c40001b1ae0000c700,0x746600000001e1e113d5,0x87080001d85865e565d5,0xc52520f620ce7642d1cc,0x23d1a59000000001b085,0xf4bbe1d261a6,0x448ef3ca572800000000,0x46e20001a00bc1675594,0xc4020001a5afe846,0x526047e20000436281c2,0xb0b0a3fdc05cb2000000,0x628d608000006204140a,0x95bf26f946c3618ff033,0x6239e7fef86501720001,0x2681957e41aca004,0x164fa0001e3252266,0x187fa865213b8,0x43f321380000f2ee0000,0xc0db25640001e851a027,0x53b42364000000000000,0x6270000000000000a2f1,0x5450c818769143d5,0x276c000002c3d0f2c04e,0xc195e16c21c888080000,0x641d902c27b6210d,0xe175462a223304300000,0x47c107c764ba6457512b,0x44f7c4dbc58e27a6,0x2e20000000160d60000,0x231603c846e821244635,0x12163c5be0000c25b],#[0x1d34400007520,0x614d076e2747c03127e4,0x44bec0cd679b0486,0x160a85848000141aa,0xe300f31644a60000125a,0xa052a219c7a952e00001,0x881a000145b132e5c513,0xa15be73712f44452e7e9,0xe6c447542382711e60d2,0x623a1f0a1b7e6f091bc,0x43ad00fc4628a096c5ac,0x476192420000000114a0,0x1b82135b844eee729,0xc763f1046815c69120fe,0xa2120000766e00006651,0x187380001e24680f1,0xa5f5458a0000b55c4838,0xe5c0000016c6c3ecb596,0x24d2000003457061e417,0x7408000145180000,0xa5e788060000e61da078,0x817d85311bad57c0001,0x229c091127a,0x85920001080c8867449e,0x22b3a397b4520001,0xfa05a000113e72562,0x43ce258000016444603b,0xa684b1f1666676680001,0xe11e8828000025660001,0x618c00000001c27eb327,0x7d5a854e813032ea658,0xc41bc188e0be843473e3],#[0xd362a584049d12e3e19e,0xd41e00000001,0x21d60001e0060001f390,0x1a52a66c9282db364,0x93720000000000016568,0xc5ba0000463b24c5e492,0xb4238001c6bf45e3c5b2,0x6427e1e4000000000000,0x83fe0001e1de00000000,0xc032000150020001651f,0x822e5541208c00000001,0xc7c4911126fe0001f5dc,0x64f80001f01200000000,0xc857145c034000000001,0xe14e00000000a60a0000,0x181a40001066e,0x7556318ba5ee653c0000,0x95a7a6dd411ae0c4e69a,0x1875ec6b3,0xc0655118000080080000,0xe2cd4398a26c00000000,0xa0aa80ed84cbc40a,0x7357c04a000083f5c67c,0xa7c20000c372f3fe234a,0xc224c5a8d1e3283bf3fb,0xc5d2064084a593ec6216,0x879cb1dda0d00000,0x2390,0x72fe2e00000,0x0,0xa0e360a4f811284a,0x9568c085c092c3465406],#[0x90d14802000004508603,0xc07b,0x268c000160e800010154,0x144d40001253e96c8,0xa3c587ede675c6080000,0x73a00f40000c03c109f,0x526a812cf3c800013847,0x15434217600000000,0x832c1e9c7de00000000,0x106e4000165f60000]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0xee96258110e4d6554d62,0xfa94250120f555354510,0xcef7658920f695254120,0xee96258140f395454140,0xced7658940eb96458140,0xee962581509ef825d540,0xe6d6558950e796558150,0xeeb8058960ced7658950,0xece5358960ecd5358960,0xcef7558960cef7458960,0xf555354521e5d6554d60,0xe6d6558951e756558551,0xe5d6554d629dd85dcd61,0xe6f7559562aef8059562,0xff14154110ff12154110,0xf795254110ff16154110,0xfea6254110fe96254110,0xdfb7254110df97254110,0xdf97454110f795454110,0xf796554110dfb7454110,0xdfb7654110df97654110,0xbfb8654110bf98654110,0xff14158110ff12158110,0xef96258110ff15158110,0xdf97458110ef96458110,0xef96558110dfb7458110,0xdfb7558110df97558110,0xfe55248510bfb8558110,0xfd55348510fe56248510,0xdf77448510df57448510,0xdf57548510bf58448510,0xbf58548510df77548510],#[0xfe56250510bf58648510,0xdf77250510fe66250510,0xfd65350510fd55350510,0xdf77550510df57550510,0xdf77650510df57650510,0xfe66254510fe56254510,0xdf77254510df57254510,0xdf57454510bf78254510,0xbf78454510df77454510,0xdf57654510f756554510,0xbf58654510df77654510,0xdf57458510bf78654510,0xef56558510df77458510,0xdf77558510df57558510,0x9fd8750910bfb8050910,0x9fd8754910ded7254910,0xdef7258910ded7258910,0xfe581589109fd8758910,0xded7458910eed6458910,0xeed6558910def7458910,0xdef7558910ded7558910,0xdee8758910ded8758910,0xdef7498910ded7498910,0xdef7598910ded7598910,0x9ff845c910ddd535c910,0x9ff865c9109ff855c910,0x9fd84dc910ddd53dc910,0x9fd86dc9109fd85dc910,0xddf7454d10ddd7454d10,0xddf7494d10ddd7494d10,0x9fd87591109fd8755110,0x9ff855d1109ff825d110],#[0x9fd82dd1109ff865d110,0x9fd86dd1109fd85dd110,0xcfd7659510d7d7559510,0x9ff87595109fd8759510,0x9ff845d5109ff825d510,0x9fd82dd5109ff865d510,0x9fd86dd5109fd84dd510,0x9ff845d9109ff825d910,0x9fd82dd9109ff855d910,0x9fd85dd9109fd84dd910,0xfe96250120fe95250120,0xfda5350120fd95350120,0xfb96450120fb95450120,0xdfb7550120df97550120,0xbfb8550120bf98550120,0xdfb7650120df97650120,0xfe94254120dfb7154120,0xf795454120fe96254120,0xdfb7454120df97454120,0xf796554120bfb8454120,0xdfb7654120df97654120,0xbdf8358520f5d5354520,0xded62dc520ded52dc520,0x9fd84dc520ddd53dc520,0x9fd86dc5209fd85dc520,0xfce5350920fcd5350920,0xdef7550920ded7550920,0xdef7650920ded7650920,0xded7454920f6d5454920,0xded7654920def7454920,0xbed8654920def7654920,0xfce5358920fcd5358920],#[0xded7458920eed6458920,0xbef8458920def7458920,0xded7558920eed6558920,0xbef8558920def7558920,0xddf7454d20ddd7454d20,0xddd7654d20f5d6554d20,0xddd7494d20ddf7654d20,0xddd7694d20ddf7494d20,0xd7d7555120ddf7694d20,0xcfd76591209fd8755120,0x9ff815d1209fd8759120,0x9ff865d1209ff855d120,0x9fd85dd1209fd81dd120,0xcfd76595209fd86dd120,0x9ff87595209fd8759520,0x9ff845d5209ff815d520,0x9fd81dd5209ff865d520,0x9fd86dd5209fd84dd520,0x9ff845d9209ff815d920,0x9fd81dd9209ff855d920,0x9fd85dd9209fd84dd920,0x9fd85dc9309fd84dc930,0x9fd85dd1309fd82dd130,0x9fd84dd5309fd82dd530,0xf795254140dfb7154140,0xfea6254140fe96254140,0xbfb8254140dfb7254140,0xf796554140fb96454140,0xdfb7654140df97654140,0xbfb8654140bf98654140,0xef96258140dfb7158140,0xfd95358140bfb8258140],#[0xef96558140fda5358140,0xdfb7558140df97558140,0xdef7248540bfb8558140,0xbdf8358540f5d5354540,0xdee62dc540ded62dc540,0xddd53dc5409fd82dc540,0x9fd85dc540dde53dc540,0xd7d75549409fd86dc540,0xcfd7658940def7258940,0xfcd5358940fe98058940,0xeed6558940fce5358940,0xdef7558940ded7558940,0xded8758940eed7658940,0xfcd5398940dee8758940,0xded7598940fce5398940,0x9fd81dc940def7598940,0xdde53dc940ddd53dc940,0x9fd86dc9409fd85dc940,0xddd7654d40f5d6554d40,0xddd7694d40ddf7654d40,0xd7d7559540ddf7694d40,0x9fd8759540cfd7659540,0xbef825d5409ff8759540,0xdec825d5409ff815d540,0x9ff825d540def825d540,0x9fd81dd5409ff865d540,0x9fd86dd5409fd82dd540,0x9ff825d9409ff815d940,0x9fd81dd9409ff855d940,0x9fd85dd9409fd82dd940,0xbfb8158150dfb7158150,0xef96258150f795258150],#[0xf795458150bfb8258150,0xdfb7458150ef96458150,0xf6d5248550bfb8458150,0xe7d6558550bdf8358550,0xdee62dc550ded62dc550,0x9fd84dc5509fd82dc550,0x9fd86dc550d7d65dc550,0xd7f7454950f6d6254950,0xdef7258950b7d8654950,0xcfd7658950e7d6558950,0xf6d5458950fe98058950,0xdef7458950eed6458950,0xeed7658950f6d8558950,0xdee8758950ded8758950,0xdef7498950f6d5498950,0xd7d54dc9509fd81dc950,0x9fd86dc9509fd84dc950,0xd7f7655150d7d7655150,0xcfd7659150e7d6559150,0x9fd81dd150bef825d150,0xd7d65dd1509fd82dd150,0xf7b80595509fd86dd150,0xb7f8459550b7f8259550,0xdfb805d950bfb805d950,0x9ff825d9509ff815d950,0x9fd81dd9509ff845d950,0x9fd84dd9509fd82dd950,0xeed6254560eed6248560,0xeed625c560e7d6554560,0x9fd84dc5609fd82dc560,0x9fd85dc560cfd65dc560,0xafd8654960eed6254960],#[0xede5358960edd5358960,0xaff8458960cff7458960,0xaff8558960cff7558960,0xeef8158960eed8158960,0xeed8458960eed7458960,0xeed7558960eef8458960,0xeef8558960eed8558960,0xddd53dc9609fd81dc960,0xcfd64dc960dde53dc960,0xcfd65dc9609fd84dc960,0xedd6454d609fd85dc960,0xedd6494d60ddf7454d60,0xcff7559160ddf7494d60,0x9fd82dd1609fd81dd160,0x9fd85dd160cfd65dd160,0xaff8259560efb8059560,0xbfb805d560aff8459560,0x9fd82dd5609fd81dd560,0xbf780545219fd84dd560,0xf756554521fe56254521,0xded7654921df57654521,0xeed6558921bed8654921,0xbef8558921ded7558921,0x9fd8759521cfd7659521,0x9ff805d5219ff8759521,0x9ff805d9219ff865d521,0xf5d535c1519ff855d921,0xded62dc151df561dc151,0x9fd82dc151dee62dc151,0xd7d65dc1519fd84dc151,0xdef72589519fd86dc151,0xfe58158951e7d6558951],#[0xdee8758951ded8758951,0x9fd80dc951f5d535c951,0xf7781595519fd86dc951,0x9ff805d951bf7815d951,0x9ff825d951df7815d951,0x9fd82dd9519fd80dd951,0xef78159561ddf7354961,0xbef8158952bef8058952,0x9ff815d9529ff805d952,0x9fd81dc162def825d952,0xdde53dc162ddd53dc162,0xcfd65dc1629fd84dc162,0x9fd80dc5629fd85dc162,0x9fd85dc562cfd65dc562,0xeef8259562aff8059562,0x9fd80dd562bef825d562,0xbef815c1629fd81dd562,0xfce535c162fcd535c162,0xdef745c162ded745c162,0xeed655c162bef845c162,0xdef755c162ded755c162,0xeef865c162bef855c162,0xfcd53dc162bed81dc162,0xbed84dc162fce53dc162,0xded75dc162eed65dc162,0xbef805c562bed85dc162,0xded755c562eed655c562,0xbef855c562def755c562,0xeed65dc562bed80dc562,0xbed85dc562ded75dc562,0xeef8059562eed8059562,0xeef8159562eed8159562],#[0xbef815d562bef805d562,0xbed81dd562bed80dd562,0x9fd84dc1539fd82dc153,0xbdd82dc1539fd80dc953,0xbdd80dc953bdd84dc153,0xf5f8059553f5d8059553,0xf5f8259553f5d8259553,0x9fd82dc1659fd81dc165,0x9fd80dc5659fd84dc165,0x9fd80dc9659fd82dc565,0xff942541109fd81dc965,0xff98254110ff96254110,0xff98454110ff96454110,0xff94258110ff98654110,0xff98258110ff95258110,0xff98458110ff95458110,0xff56448510ff98558110,0xff56250510ff55250510,0xff56254510ff54254510,0xff54258510ff56454510,0xff55458510ff55258510,0xfed6250910fed5250910,0xfbd5450910fdd5350910,0xdff7550910dfd7550910,0xbff8550910bfd8550910,0xdff7650910dfd7650910,0xbff8650910bfd8650910,0xf7d5454910fed6254910,0xdff7454910dfd7454910,0xdff7654910dfd7654910,0xefd6458910bfd8654910,0xdff7458910dfd7458910],#[0xefd6558910bff8458910,0xdff7558910dfd7558910,0xfed5458910bff8558910,0xfef8458910fed8458910,0xfef8558910fed8558910,0xdfd645c910fed5498910,0xdfd65dc910dfd64dc910,0xbff8255110ff58155110,0xf7d6555110fbd6455110,0xdff7655110dfd7655110,0xbff8655110bfd8655110,0xdfe8755110dfd8755110,0xbff8259110ff58159110,0xdfd7559110efd6559110,0xbff8559110dff7559110,0xdfe8759110dfd8759110,0xdff825d110bff825d110,0xbff825d510dfd65dd110,0xdff825d510bff845d510,0xff95150120dff845d510,0xff98150120ff96150120,0xff96350120ff95350120,0xff98650120ff96550120,0xff98154120ff96154120,0xff96354120ff94354120,0xff96454120ff98354120,0xff56154520ff98654120,0xfed6254520fed4254520,0xdff7454520dfd7454520,0xf7d6554520bff8454520,0xdff7654520dfd7654520,0xbff8654520bfd8654520],#[0xfed5258520fed4258520,0xdff7458520dfd7458520,0xdfd7558520efd6558520,0xdfd64dc520dff7558520,0xfed6350920fed5350920,0xfed4354920fed6550920,0xfed6454920fed6354920,0xdfd7454d20dfd7550d20,0xbff8454d20dff7454d20,0xfdf8454d20fdd6454d20,0xdfd7458d20fdd6494d20,0xdfd7558d20dff7458d20,0xfbd6455120dff7558d20,0xbfd8655120f7d6555120,0xfed8259120bff8159120,0xdfd7559120efd6559120,0xbff8559120dff7559120,0xdfe8759120dfd8759120,0xdfd65dd120dfd655d120,0xfed8259520bff8159520,0xdfd8759520bff8459520,0xbff815d920dfe8759520,0xf7d5454930dff815d920,0xbff8255130dff7454930,0xff93154140dfe8755130,0xff97154140ff96154140,0xff96354140ff98154140,0xff98354140ff97354140,0xff98654140ff97654140,0xff95158140ff92158140,0xff98158140ff97158140,0xff97258140ff95258140],#[0xff97558140ff98258140,0xdfd7648540ff98558140,0xdff754c540dfd754c540,0xff57154540ff56154540,0xfee6254540fed6254540,0xf7d6554540dff7254540,0xdff7654540dfd7654540,0xbff8654540bfd8654540,0xbff8754540bfd8754540,0xdff7258540ff57158540,0xdfd7558540efd6558540,0xbfd8758540dff7558540,0xfee625c540fed625c540,0xfdd535c540dfd725c540,0xdfd755c540fde535c540,0xdfd765c540bff855c540,0xdfd7654940bff865c540,0xfef8158940bff8158940,0xdfd53dc940dfd765c940,0xdfd65dc940dfd63dc940,0xfdd7654d40bff8754d40,0xfdd7694d40fdf8754d40,0xdff7558d40dfd7558d40,0xff98059540dfd755cd40,0xf7d7559540bff8159540,0xdfd8759540efd7659540,0xdfe8759540bfd8759540,0xdfd765d540bff8759540,0xdfd835d540dfd815d540,0xbff815d940dfd865d540,0xdfd815d940bff855d940,0xdfd825d940dff815d940],#[0xdfd855d940dff825d940,0xff92158150dff855d940,0xff98158150ff97158150,0xff98258150ff97258150,0xff98458150ff97458150,0xdfd7648550f7d6548550,0xdff744c550f7d544c550,0xf7d5258550ff57158550,0xf7d5458550dff7258550,0xbfd8758550dff7458550,0xfed625c550f7d525c550,0xdfd725c550fee625c550,0xdfd745c550f7d545c550,0xf7d655c550bff845c550,0xbff865c550dfd765c550,0xf7d6354950dfd64dc550,0xf7d6454950f7d7354950,0xbff8158950f7d7654950,0xdfd735c950fef8158950,0xdfd765c950f7d655c950,0xdfd64dc950dfd63dc950,0xdff7458d50f7d5458d50,0xdfd745cd50f7d545cd50,0xf7d7655150bff845cd50,0xbff8159150ff98059150,0xf7d8559150fbd7459150,0xdfd8759150efd7659150,0xdfe8759150bfd8759150,0xf7d655d150bff8759150,0xf7d8159550dfd765d150,0xf7d8259550f7f8159550,0xf7d8459550f7f8259550],#[0xffb805d950f7f8459550,0xbff845d950bff815d950,0xdff815d950dfd815d950,0xdff825d950dfd825d950,0xdff845d950dfd845d950,0xfed5248560ff55148560,0xdff7448560efd6448560,0xdff7548560efd6548560,0xbfd8748560bfd8548560,0xefd6254560ff57154560,0xbff8254560dff7254560,0xdff7454560efd6454560,0xbfd8754560bff8454560,0xefd625c560bff8754560,0xefd645c560dfd725c560,0xefd655c560dfd745c560,0xdfd52dc560dfd755c560,0xefd6454960fed7254960,0xbfd8754960dff7454960,0xefd7558960efd7458960,0xfdd535c960bff815c960,0xefd645c960fde535c960,0xbff845c960dfd745c960,0xdfd755c960efd655c960,0xfdd7454d60bff855c960,0xefd7559160fdd7494d60,0xbff825d160bff815d160,0xdfd755d160efd655d160,0xefd8159560bff855d160,0xefd8259560eff8159560,0xefd8459560eff8259560,0xffb805d560eff8459560],#[0xbff825d560bff815d560,0xbff825c151bff845d560,0xdfd62dc151bff845c151,0xfed8058951bff8058951,0xf7d8059551fef8058951,0xefd8059561f7d8259551,0xdff815d952efd8259561,0xefd8059562bff815c162,0xefd8159562eff8059562,0xbff815d562eff8159562,0xfef815d562fef815c162,0xdff715c165dfd715c165,0xdff725c165dfd725c165,0xdfd745c165bff825c165,0xbff845c165dff745c165,0xbfd82dc165dfd72dc165,0xdfd82dc165bfd84dc165,0xdfd725c565dfd84dc165,0xdfd72dc565bfd80dc565,0xdfd80dc565bfd82dc565,0xbff805c965dfd82dc565,0xffd6550910bfd80dc965,0xffd7650910ffd7550910,0xffd8655110ffd6454910,0xffd8559110ffd8259110,0xffd8454520ffd6454520,0xffd5458520ffd8654520,0xffd7558520ffd7458520,0xffd7558d20ffd5458d20,0xffd8559120ffd8159120,0xfff8159520ffd8159520,0xfff8459520ffd8459520],#[0xffd7654540ffd754c540,0xffd8754540ffd8654540,0xffd7258540ffd5258540,0xffd655c540ffd7558540,0xffd865c540ffd855c540,0xffd7558d40ffd6354940,0xfff8159540ffd8159540,0xfff8759540ffd8759540,0xffd855d940ffd815d940,0xffd7258550ffd744c550,0xffd645c550ffd7458550,0xffd7458d50ffd635c950,0xffd8759150ffd8159150,0xfff815d950ffd815d950,0xfff845d950ffd845d950,0xffd7548560ffd7448560,0xffd7454560ffd7254560,0xffd7454960ffd525c560,0xffd825d160ffd815d160,0xffd815d560ffd855d160,0xffd825d560fff815d560,0xffd845d560fff825d560,0xffd725c165fff845d560,0xfff825c165ffd825c165,0xffd845c165ffd745c165,0x8800700000fff845c165,0x6a802d001300077002,0x1b600c80056c02560100,0x100267011b8083003c20,0xc062c02f0016500aa405,0xf640752037401a980cd,0x3f01174088c042501fd0],#[0x60295013fc09a804a402,0x5f202e3816840ace054,0xd6a068f0332018f80c26,0xf40e9a0718037901b440,0x202c0fac07ba03cf01d,0x43c8219c109608390411,0xf10468022f8114e08950,0xa096104a5024a4121a08,0x142009ef04e20267812f,0xa8415000a640521828b0,0x102d3416300aed056382,0x60a82fa817920ba305c,0xcc40651831f418a40c36,0xaa0d34068e8340419c00,0x41b800d9f06c1835b01a,0x3a5c1cce0e41070d837d,0x8f03c081dd60ed4075c0,0x7c483ddc1eca0f4907,0x100107ed83f101f640fa,0x12e107b082a840d02026,0x542268110908768431c2,0x847a0237a119c08b6045,0x97384ab4250412520909,0x9109bd04d64266613170,0xc140b09f504f4c276413,0x296014990a3c05134286,0x5542a72151d0a8085330,0xb857002b5c15970ab885,0xb23858c02c2815fd0ae,0x7000b6a85ae42d261663,0xf017660baa05ce02e561,0x42fb217c20bd305e3c2e],#[0x6194309c18370c0885fd,0x8c863b83190189d0c408,0x40cc9865a03284192b0c,0x1a470d13067ec33aa19b,0x5b01ac60d5006a2434da,0xdc36401b090d7b86b943,0x6f28372a1b6a0da986c,0xe23870c038321bfd0df3,0xa0e798732039301c6d0,0x61d750eaf075083a421d,0x3c2a1e030eee876dc3b3,0xac03d281e730f29078c4,0xf87d203e301ef20f6b07,0xff407f1c3f421f800fa,0xdd10540823040a42022,0xe216610a28847c42062,0x4498221710ec086a043,0x8bec45c822b91149889f,0xc108d70468a232411890,0xc120088f6c4760239911,0x249c123b09140487c242,0xad2254d1291093b44984,0x604be425d612d5896144,0x89ae84d32265f1317898,0x3b709cd04e3026f7136d,0x5e14148a0204fc427a81,0xe28e714608a24450ea28,0x5372298914b40a4cc522,0xa6854ca2a3f150a0a7cc,0x60acf056362af515650a,0x16110b00457a22b9c15b,0xcc716558b25058f02c4d],#[0xec2d5a169c8b43859d02,0xc5c122de816e38b6705a,0xbae05d242e6c17258b8b,0xbb0bd2c5e5e2f04176a0,0xc18138bfc85f842fa117,0x30f9186e8c2a060f0305,0x39631aa18bd0c5146252,0x4c64c6323d190e0c7b06,0x8cd4c665032f3195f0ca,0xa0d8cfd46780339019bc,0xd41a598d22068ce34371,0x353a1a8c8d41c69ea34,0x6bdc35c81ad38d6046ac,0xb286d3e36741b298d88c,0x38dc986e2837021b758d,0x1bf20dee46f26376d1ba,0x8a71c408e14470603805,0xf239531c990e40871a43,0x743639f01ce50e6a472,0xeb0075483a881d360e94,0xa60ecd476283afd1d6e0,0x71de30eebc77123b631d,0x3c571e1b0f04077f23be,0xa163cf41e620f2a07904,0x387b503d871ea68f49c7,0x8f9207c6c3e101efa0f7,0xf830fb807d6a3e991f39,0xbf1fcf0fde07eae3f311,0xa403e2013900187fc03f,0x8176409a203a1018880a,0x54482604114208110384,0xd9077c837c419820b690],#[0x213310914843e420d20f,0x33d218910bb085824291,0x9c43a321c890dfc86c64,0x8889a4436220590fa887,0x1378897a44a12247911b,0xcb915c48a784520227a9,0x52315118248bbc45bd22,0x46d4235991a348ce2465,0xede474e239691c448dd6,0x4902247e123dd91e548,0x123789184489c243b121,0x4df9262892aa492a2487,0xbe254212950943e49ef2,0x84b42259092c3c95dc4a,0x97f64bcb25cd92e1096a,0x2e499124c68262113070,0xe1356c9a6a4d0f266f93,0x270f138089bcc4dbb26b,0xed2275393a189cd44e44,0xc64f47279813c649de64,0x89f9c4fad27c613dd49e,0x41b8a0725022280313fa,0x7d1438ca19850ab28479,0x28d5945eca2a0511b28,0x5296293a948eca40251e,0x6da5333297f14b88a578,0xc0a82853e929df14e38a,0x952e4a92654722a26150,0xab695530aa4c54fb2a6a,0x122af395718ab4055892,0xc56a02b4215978ac7a56,0xaec657422b8e15bc4ad8],#[0x98b01457c62bd295e10,0xc16334b14458772c1e96,0x2ce116620b2ba59372c7,0xa762d28168e4b41259e8,0x365aff2d6f16af4b5425,0x4b75c5b7e2db616d04b6,0x70d4b83c5bf82dee16f1,0x771730cb9305c772e2b1,0x12ebe17508ba4c5d0a2e,0x5e442f0a177ccbba45db,0xe045eeb2f6297a54bce8,0x74bef85f562f9a97c64b,0x98174c0505ff32fe197e,0x90183d4c18a60a43041,0xed30e39865cc2c4613c3,0x662943132188d0c41261,0xc690630e316f18b1cc55,0xf4c7fc63b531c018d90,0xb99430c9b864ac323699,0x330319708cb246571329,0x6ce335199a1cccd66631,0xb8678933aa19c40cdd46,0x4d0ca684e341b9a030cf,0xa48cd1fa68c834561a20,0xe41a6c4d3026965349f9,0xe353f1a94cd44669ee34,0x6b5f359c9ac60d5d06aa,0x8626c0635f29af10d746,0x70d9f66cc636501b184d,0x9b7c0db626d9036b01b4,0x7701ba98dce26e41370d,0x7b37aa9bcf8de306ef73],#[0x6701337f41bef4df426f,0xe1ac70ab38451c1a4e08,0x7cce35e717538a29c418,0x39ca18e4d4724e39119c,0x39891cbece5be72c3395,0x3d039d51cdc0e6a87333,0xea744f3a149d034e7d87,0xea74750f3a6f9d2a8e8,0xd81cebcc75c53acd1d58,0x7b9db1ced24766c3b1b9,0xe3bcf1ddccee9077133b,0x78983c341e0cceffc77c,0x2d4794e3c9b9e3f4f17c,0xf3aa79b43ccc1e618f,0x1e9fcf4c67a473d109e8,0xdb29ecd4f6007ad03d50,0x5f3e0d9efc0f76c7b903,0xa7d013e689f298f9007c,0xfb747d993eb99f50cfa3,0x9e0fc867e0e3ef91f758,0xf1fce0fe1a7ed83f519f,0x40001ff54ff687f843fa,0xff406a202cd0106803a,0xca81bf40c7a0555025e8,0x1052c827541202085503,0xc9d062082f4417120af,0xeda0ee90732837341a6a,0x5422fa10e5083a83f741,0x851d4276a13090956848,0xc4285d842d6a16310aae,0xe10d9a86a74345a19450,0x21e410eca873a438a21b],#[0x424a20790ffa87dc43e0,0xfd4470a22c5111688654,0xa897c44ada24fd123288,0x144c8a0544f2226f9133,0xb0515368a89452f22909,0xba2cc5160c8aef456ea2,0x45fca2f3917468b7845a,0xcd04657a31fd18948c24,0x88d6d46a12348519f68,0x51c2e8df646e8236bd1b,0x3b411d4a8e7f4731a38f,0xb5a3d511e7a8f26477da,0x647f023efd1f328f8247,0x908f4839a4121203a900,0x24091044879243452174,0xd92320917e48b1244dd2,0x442f09c003e2c8e9246,0x40164220ef0bc203e56,0x883507e000f8e10b0500,0x2284207c1d8dc27050,0x24370c092280607c2f0d,0x7021f1010703c191a1b0,0xe87c400bc1209c370700,0xa92c1041c0e09c191a0,0x1103bc2f0500703c191a,0x4016098011bc1f021f14,0x7c0e098050a38440ed0,0x83bc191b8287c4021c37,0x1703c191a0c90c1041c0,0xc191b8007c403bc2401c,0x38060a1f134104082f03,0x7c100c0ed040111bc1f0],#[0x30a1f03e3703c1c1a0e8,0x1600c287c108d0ed0580,0xc241bc1f021f03a3c3b4,0x906f07c0b0a1f03a382e,0x8a8e90bc27058003e301,0xd0720f8d078341f4120f,0xc0707840725709c17000,0x383134120a10235c2603,0xc0385613709c1700c2e0,0x87c4709c010b8107c0f8,0xc0941bc1f02c050a1c,0x1c87c210bc0f070687c1,0x9007068407c1c8cc1a10,0x700433c270414a3e3b0,0x5308e11c187d809184b,0x603847061f0724033c3,0x84706c10801c9102b050,0x6028641c86c2c0b00603,0x16c1611c18640886c320,0x70d8405308f06c26021f,0x2b09c187c1c8e0c823c1,0xc27074287c0891006100,0x9c10328f872370dc1610,0x10cf09c10528f9008f0,0x70408e11c1872385402c,0x270580f07840724433c2,0x19611c18321c8e0e833c,0xd0ec01c22281c8b80f04,0x8583f050043ac203e1c8,0xf2285401c27050eb0a0f,0x2f09000400f8590883a1,0x5103bc2f0508b080f93c],#[0xb00704c243e1c8c10858,0x8722c43c2f04c20842c3,0x4706c28585709c103a0f,0x210803401c2603c143b8,0x7c27041c8842709c1072,0x8121783e190b0405e1c8,0x160530a0b4103e1f0608,0x28148808c281f06c2600,0x907234121607c1e00160,0x46058178a08c13047061,0xcc30000a052178b04106,0x722508c16000f85e1c8,0x7c2d800281b0b026000a,0x2386c195098003e148c0,0x58442d08d080a600c284,0x8c1904f047078030b420,0x852286504707420221c,0x420220f872204f805081,0x582b058050a0f87c160d,0xe001606c3600c150a0f8,0xd411c18221b0f0400a81,0x8c11c1834178ec101f0,0x1c1b098050a1610c101f,0xb047061f022505e1541,0x87c0d150d01fc3704c25,0x42207f0d80704c2411c1,0xf8fc270504707800723,0xe160c15709c16014281e,0x783e4709c150a0883,0x834160c11f0841f0542e,0x260014c3e2f09c16000f,0xc2d07c130808c3e4506c],#[0x941f058003e1c8e17c43,0x9c1600c281f0f8c08f0,0xbc283709c102214c3e2f,0x16428148a80223c370a4,0x4e300b8004e1c8942600,0xc3e1508038078050a160,0x148b8004e1543e260013,0x17842190c01e0013c3e,0x45803081f03e522204a0,0x85e1c8e1084141622161,0x887d0f8e10504c26010f,0x1f03e1c8f10841413088,0xbc187c16121020a41600,0x221c8c1050580e018430,0x4f0f8542d05847061f2,0x1c898004e1543e220780,0xac242888c3e2b0980428,0x3847078030b41058420,0xb0784707412221c8a826,0xc17090a05c1b078023e1,0x86c1c28170721e11c186,0x1b0e036010a06c26008f,0xc2106035058470780e00,0x5481309800530f8d0a06,0x8ec220542a221f43e30,0x108a8b22a88e010a50b1,0x98050a1612c242942a23,0x3e148e0860201611c1d0,0x548a0a0800601509804,0x4707426001c900350980,0x426008f8723020016038,0x224a2942054170808005],#[0x794270dc1610c2f061f0,0xc9090821c2f054208430,0x400dc270580e11c1e001,0x1500bc2207c16000f872,0x984707c16014350a0798,0xd4281e48200380780f0,0x84e4021c270584707805,0xf16033058470780e0142,0x3601c150b84706c26021,0x847078050a16121e01fc,0x74284e170a08603c2705,0x11c1f04c20221c8f8470,0xfc2007c1052210c086,0xc1308210d8004e1543e2,0x910f041488434420870b,0x8723600138550f8803f0,0x2822161008004c243e08,0x8a0802021c270584706c,0x702702c305e1b1013f0c,0x8c1e04cf87c302ac6f0,0xa07c2c088a06c1d88204,0x51424c307c50242070d8,0x8200a0902ac6f0781702,0x9c086c1d8a13f0c0262,0xd8a2070d816281f0bc30,0x17b0c1b0fc305fc0b0a1,0x81db0c2008c6f0602702,0x70c8a08022061c880180,0xc840c6f06c30641b0e15,0x58a0802f0c206281f081,0xbc36281986c200bc305,0x930c1f1219f0d8a30819],#[0x1b0f81073c0832c6f070,0xc200a1480ac6f061930c,0x9816004f9014b1bc1b0,0x90f8050c4625078544d7,0x287220058970bc260540,0x64f8801c061b0244f872,0x8730a080200d0a080183,0xcf8802809804281c8803,0xb0202815076230615408,0x8541d8a0870c02428200,0xb0d80508150fc3009c0,0x24001db0c2008c6f07c,0xc08428200bc304f0a08,0x391c342809418138a02f,0x3852c6f07c0b0d804181,0xe4052c6f0700702c3080,0x61cb1bc1f02c30198004,0xd0d800281b098013e1b0,0x402451703c191b8006c3,0x1651bc1f02c260143054,0x6c351bc1f03430241b0c,0xe001b0f46f07c0e00100,0x3018139009073c0f0646,0x906c305946f07c0e014,0x3800401b0f46f07c0d0c,0x61553e200a1cd1bc1f0,0x113e3d074fa241b0802d,0x4f86c185b89055c26018,0x70a0541d864f8801600,0x230d804281b08894281b,0xfc3628200b0a30d42876,0x6c470c0862820080204],#[0x51402605c0945c191b80,0x6f0603807c0d09436001,0x6200f8005814a28281f4,0x21db0c200bc37021507,0x38662600160528a08078,0xc1f02c68241b0fc36281,0xbc0f0646e001b1007b0d,0x38050d4284e48538100,0x50d4284e401e0251bc1f,0x1858200807d1bc1f0380,0xc200dc362813866200e0,0x581505c281ec6f07c0b0,0xb0fc3702150762311c18,0x4f8a07b0dc1f02c68241,0x3436001b0e0260580052,0x3436001b0e07d1bc1f0,0xa1493e170607d1bc1f,0xc0d0c200c078021dd0c2,0x10441a1384a301f46f07,0x78041106854128d81e0,0x68503b0504601068542e,0x684e28200130b040270,0x904027068563e010450b,0x32c47060a87248200130,0x118ca07c205481f0417c,0x3072c6c09c1b0c1f0dc3,0x8190e1cb1b02706c3080,0x32178c14d0bc3304ca60,0x50ac307c5e08c170cca0,0x8321c82bc131bc1f0291,0x1073c0b1bc1e08c307c4,0xc0b1bc1b0d4287c5833c],#[0x6c307c28529103bc1609,0x342b0d8207c5052c6f0,0xb0c1f0e0e872c6f07c17,0x793e1c8a1cb1a02707c0,0xc191ac103a1f0f827041,0xbc1f021783a1b0d82703,0x8dc143b8230a1f13e351,0x287c4f050ee08c287c50,0x60720ef05c0f0646e08c,0xc17038270746b0b4307c,0xf4330a0a950e8320a859,0x3a4859c0c3bc1d1bc105,0x7346f07c17038230a1f0,0x7c4f8f826001512820,0x43e01431107935c16098,0xe17872262bc2f0582502,0x601c0f801281c890193,0x50370130b0a93e312815,0x178723928c2c2a50881,0x5e4f872200e01f058260,0x3054470c465281f08010,0x1f0e1651bc1f03826014,0xe1b101103a46f07c0d04,0x7c184146f06827034305,0x687c3e005087c1e004f8,0x4307c3a0b80073c0f064,0xb4305e38581051bc1f03,0x64687c405946f07c0b0,0x50c1514236001103bc0f,0x5946f0683a07c0e0980,0x651bc1f0343609800544,0xa4a0b82600c2d044f8a1],#[0x7c0d0c200f826014330,0xd0d4130a8a901600546f,0x5814928285946f07c0,0xdb074133f0a8543e098,0x281513030550a9282052,0x160780ec2d05c3609805,0x60980707c0b1bc288d41,0x16098007c4f8c0801ec3,0x9123bc150a1f13e305bc,0x7c508c1520542a2a4f8a,0x50a8a9422a448ef05428,0x2601c1d1b4307c585481,0x4287c58380c859c17038,0xe853c0f058260046f07,0xd42f05c1f034687c5844,0x61f072380407e098050,0xf034285e36080160146f,0x16098050a16158070dc1,0xca07a2020c470603807c,0x20170dc1f021e8a12f0c,0xfc330582600ca50a081,0x804c6f07c0b0c1f0e078,0xb11c1e098050a161207,0xc37020850a1d8a08004c,0xdc1f03c105ec6d0a0a95,0x5826001493e308c07b0,0xf07c0d0d826001512080,0x1f02c2d0c1f1607b0546,0x4f8c2301f80609c151bc,0x14305440200160980052,0xc1f0e07d1bc1f038260,0xd0c0c940780546f07c0d],#[0xa0fc27041943bc1b10c0,0x27050cb11c1e0ac083a4,0xed1bc1d0c1f2184055c,0x3c191ac103a1f0e0cf03,0x5346f061903a1b0d82f0,0x70346c3bc1b094307c48,0xf0646b098287c4833c1,0x1950cc203251440ef05c,0xc0e92167030ef0746f04,0xc14f05c0d1ac27078287,0x50c40194470619112178,0xf918cf09c160b4090f80,0x2865418728cf09c16004,0xc4a080240f01d02c307c,0xd447074084e198b03b0,0x72388003511c1d021f,0x19058440fc1065447078,0x4178c02511c1f058060a,0x280c85e2b1a06706c306,0x31bc1864c305e3f0d065,0x1f038050d8284e450400,0xc091bc1d041f0c1651bc,0xe0e91bc1f034107c3601,0xa1c84146f07430641b0,0x191a1f0c8051bc1d0c1f,0xc0b0943064394411703c,0xbc1d0c1905e385946f07,0x3bc0f064687c28188051,0x51bc1f03436018284e48,0x1f03436018284e405882,0x8051bc1d0c200a1651bc,0x946f07c0b09435048c90],#[0x2c47078060b41058405,0xb094170d4a6001b0c023,0x3b094170d4a6018284e4,0xc0f08c360182d04501e0,0xc35081f140801ec6f07,0x7c2c0a8eb1bc1f05c0e0,0xd098007c4b1bc1f02c30,0x207c520a51705c0f0646,0x103bc0f07c111b8060b4,0x81613c3703c1d08190a5,0xa08004c0b11c1e0182d0,0x30c0c95c3020ca508198,0x85811702c6f07c106542,0x6f07c0f0419508c30324,0xc270546f060c872301ec,0x7c487346f061950c178d,0x5c0d1ac27078050c1c8,0xc8f46f07c10640c87237,0x7920ef080cd1bc1f041,0x8709c1311c1e014360a,0xf46f07c0d0d8060a1390,0x782f05c0b094307c501,0xe0b43064079407e0146f,0x304e4008c0f0580311c1,0x1f0e07d1bc1f038060b4,0x819080780546f07c0d0c,0x3b42e001f03e4a0c1792,0xd11800725040c1534162,0x10e42f09c15028e935c1,0x4a0a1181ac1043c2f082,0x58008d0f938360013854,0x3e1c8d1081e0870ac270],#[0xe01830524055c2705800,0x6918178c08709c1511c1,0xc1a1a4605e323bc0f068,0x281f074103e1f068ef03,0xc1bc1f034103a1f0d031,0x3309417030ef070687c3,0xa1f0f06f07c0d040e87c,0x3e190d0eb0bc0d05c1c1,0x7c0f8403b0644a00178,0x1c1a1f03a50424143b80,0x1912410442330941703c,0xe82f417028070706b08,0x3a443bc0f07068401f0d,0x9041504c2f03c1c1a1f0,0x43a467028070706b0a17,0x21090ef03c1c1a1007c3,0x6c1e008f86c180e4a052,0xa45c1a1a0e86c36004a0,0x7e1bc1f03836001b0fc0,0x14819c0a1bc183a1b0e0,0x7e1bc1f03836001b0e,0x448eb09c150b8007c0f9,0x90c220542a3a1f43e32,0x32448eb09c150b8007c1,0xc0e92c22054287d10a3a,0xf11509c1703c1c1ac287,0x100800601509800528f8,0x81f86f07c0e0d8050815,0xa1bc1f054230a1f03a4,0x4261bc1f021f03a4853c,0x5c1c1a0e872301ec2f05,0x730ef0706d0a178fc270],#[0xf0706b09428721f13c08,0x17078683a1c8d80705c0,0xc2007c101f428843f09c,0xbc1f03836014284e400f,0x7c17034287c0e9407e1,0xc120d07c288cc201f86f,0x28340486c0f8642c11c1,0xe0f8642c13c1c101f072,0xc0484f06046280a1b01,0x90843b0c138190484633,0x4304e0604634121b03e1,0x6426021b040190881e11,0xd0d4284e118e0f86c8a0,0x84f4350a118e0380780,0x83611c185e1a08038078,0x3e190601611c185e1606,0x7a3e38061b43e190817c,0xd23e30320d709c15010,0x6c307d0d1019709c1500,0x4c34343840c15018470,0xd00138682c0984707403,0x1501847061f0344e11c1,0xc270540096207ec270dc,0xa118e08709c1500258b,0x87d049683f0780d0c13e,0xf0980f0010235847061c,0x3a3404a0a1b03e190c82,0x63a0e81e034360a13846,0x682a0fc1d0d8084f8284,0xe038285e38181f41e8f8,0x400417896180d41611c1,0x2f09c17008470616858],#[0xa15709c17000d01e0f8e,0x81e0f9008709c1300258,0x284638420d709c170182,0xd058400fc1d0d8084f8,0xa118e0870984707c1300,0x3460c0380780d0c13e0,0x5a0f8523f09c020f836,0x8410605e3607c2705c0,0xc185ec0841060d46f07c,0xf46f07c0d0d8285e3b11,0x88c47074360a1781e301,0x18528f85e2018138461c,0x643e0c8a07c1a3e1f040,0x87c301f86f07c0b08100,0x2840178f407021070686,0xc007d0f8c07e1bc1f02c,0x52287c0f872181e21c28,0xe041c87c3511c1e0c1f0,0x1c1a1b072190b06f07c0,0x86f07c0e0c13d0a1190c,0xf86f07c0b001006c3859,0x8a03806c086d83064301,0x23e1b078106d4023e1c,0xcc2500150f402421b074,0x3400401b0d86f07c0e0,0xf07c0d018306c461bc1f,0xf0686d001b121602586,0x4030a13901c8258110bc,0x1006c387386f07c0e0d,0x18306c407386f07c0d0,0x824150e1602586f07c0d,0x7a3e190a10703c1a1a13],#[0x21f070123e1f06049061,0x1bc1f02c204019110124,0x703c1a1a1007c28580be,0x179186f07c0b0a1005e3,0x420580661bc1f02c2840,0xa1b03e190c0485f0f86,0xe0d4084ec28463507049,0x1b43e190a1b43e1906c3,0x221b001007d0f8c04906,0x85e10101007c0f872244,0xf072293486503c1d10c2,0xc1c1a1c87c5041447061,0xc1c8e8103ac060542f03,0x72258e10605c1c1ac007,0x3e168cc1e05c203fc00,0xe0d4285e410a84f09c0,0x4285e160c1601986f07c,0x7c0b001006c4604c4707,0x61b23e190a1602586f0,0x20f4041b82c10138a049,0x128c08004c24100dc1a1,0x1206a260782c1b04046,0x4c241106836120f06c1,0xf8c0d84b0441a190a151,0x16c3e303216f09c13010,0xa0607d0f8e02f09c1300,0x41f05b0f8f02b08c005,0xf0407d00258e02b08c03,0xe0d4060a139203f0801,0x400721f1207b0586f07c,0xd40958360bc1703c1e1b,0xe08709c1511c1b0182e0],#[0xe01e0c13d0382846381,0x80e01f038360a1c85e38,0x19080480e0181e178962,0xc2c234390ac112fc1e02,0x21987c4305847061c87,0x7c1c940942384305c1e,0x2302c00c1309c1e0384,0x8b0cc2305847078087c5,0x19707808321c922002b0,0x28a3090f920ee11c2704,0x181c9411b0a1643a4bc2,0x3b83b0ec23070050f80b,0x40010024c2b088a08448,0x3b06c130980872588616,0xc208448238387c0ed0ec,0x4308c164420ab0ac1044,0x281c860ce03c27041c88,0xe0741b0704072178c17c,0x41c101908048281c85e1,0xe1607c243508b0480607,0x58050a1f03e1612c103,0x828c26010f920d022c23,0x643e148ccb920c2c2207,0xc26010f8523b0941e00c,0x9c1e1011880382341b04,0x1f08d088f86436038310,0x853426014130a8f920bc,0x4706206021f0f11d2f08,0x83a0dc18642013831058,0x619222200e8d22341602,0x784046200e83a0d4170,0x7078412e190d80801837],#[0x801f805088fc28660383,0x88908ea2220d0a8282e0,0x42a0a0b82142d088fc28,0x1e8f880281e08d088f86,0xf078430c4605e392e088,0x3611c19198087c384087,0xe320f467061787228538,0x18149083a0dc1a234605,0x87230214220881e008fd,0x3118178f42611c1d1888,0x114281f080881fc1e10c,0x3e1f0a10428178722058,0xf085043e1f061050488c,0xc1d041607c35040f8721,0xf41d04888721f0c10611,0x87c2823847061c87c2d0,0x8b090f8642a23847061c,0xa1794411410f87c20588,0x81011888a53c1e114330,0xa88905847061c87c305,0x23e1b0c88e11c187220,0x116008f86c205c160458,0x61c87c36008f86c1c88,0x7078093811940d02c847,0x72410c08e0c07b0584,0x1c9381e04516038407d8,0x8360580f07845098007c,0x681039415098023e1494,0x114270688872308413a0,0x707846021f6001c97416,0x1381c96515098102241,0xb04608e0441707846038],#[0xc382281611c18721f0c1,0x72388014e11c37068887,0x864285e0b70580144108,0x26000f872502207d090f,0x16161b05e82e04191454,0x11505c1e0384600c287c,0x7416101f2221c8d42204,0x23847061f600510724d0,0x7058043e510724604410,0x2f04512230f9013a0621,0x885814a28284f10859c,0x723d09800588a0522d09,0x5e3404c107d4223f088,0x2c22160e01611c1d0a16,0xc18581f0a11906416114,0xec1b04c20581e0e01611,0x2c3605c1b101f101930,0xc2b092294233e3881023,0x840808b0c8a07c3220c2,0x1d8902310c2b1a1d8a1,0x1bc1880c307c3c08c731,0x408c083a1d87c3408c0b,0x20530cc248a50acf9100,0xc3605c1b101987c4220c,0x2c423142b1a1d8cc0822,0x330940142e04c431c3c3,0x7c382781310c687c2c,0x1987c430d01306c0b1a2,0xa4f91814000eb06c0b1a,0x803a218213407e058050,0x86c35021550c82707440,0x4054200d0d41e096004f],#[0xc1d028906c3503437074,0xe437061b134200d43511,0x544d7078160140b0c690,0x86c285b83d0ec3e08160,0xd01e4f880203407e004f,0x902007d0b8013f0a160,0x58013e4d104d09582108,0xc253e4108090218260,0x2194f9142a2e890200a6,0xa53e6225425060902180,0xaa240850a07a0ac26010,0x82c28c22254f8e1822e8,0xb824298030a4f9007d0a,0x1e826008653e58530805,0x53e38668ca2408509418,0xa072301f4220941b0a89,0xc1d08c69303844c26010,0x1d880842f09310c2e00,0x3c1b1a150803c08c731,0x311803090631a430d023,0x9600c4418c70a0830709,0xe3400c1b02c684e200d0,0x1a1d8a0c600865114684,0xd1b41a25440e01d10155,0x43098011a4d900db0942,0x6486c4f8801824086044,0x8822581110c26004693,0x5101d88c34281b076205,0x3a0ac251c895102a0b47,0x6223289600822194451c,0xac306c200cc2d1d4407,0xc09c1b0c1b080314543c],#[0x4144439064086c200d43,0x4f90a0960a086008a144,0x1c1f020bd1b801441b10,0x88029454191a1b080284,0xd1a8906c2d0740d1a13,0x80902096005106c5d074,0x5106c50738390f81907,0xc1620fc186081f0346e0,0x80305813f021d944200,0x6c241b0cc3303c1b1a15,0x42e018113e4b0cc0f06c,0xd8006c481f8210809021,0x803041c087346819c1d0,0x6001b128210e419021b0,0xe14a0819f0346f0743,0x150814855c0d1bc1d0c2,0xb8004e4f85426001393e,0xd18898c4e1198461a1d8,0x46004e61a3820c221086,0x42a1086876302009b058,0xb0050b8231aca0e15851,0x530cc2b8250acf930cc2,0x2cc47061f1417b06c10,0x87c50801d02ac0823c3,0x7982022c3034c4706c,0xcc2b0050b82310c70e2,0x7c3432c402742b1a1d8d,0xb0c1f120d82782310c68,0xf10230440eb1bc1f020a,0x283a1c832c6f03c1b0c1,0x81f13e38590eb124f87c,0x5e0a93e53050e858c2e0],#[0x121d1430e8228b70bc10,0xc2a0891ac2b0450e0821,0xcc3b83a0943318178e17,0xa1f110e825430761f0a1,0x7c484009209c1f034683,0x3a0cb040ad1bc1f03430,0x7021cd1ac287d8203a4c,0x4a0a9123b4a07c2707c1,0xa8ad1b4a088e2328ad1b,0x40d01f8250b8013e4b0,0x2c08911c187c5a5e4d6,0xf87c28801d135c350b80,0xd0584f8802e010d0584,0xec1511c1d028a8545601,0x980502c31c830354301,0xf43b0f8107c16135c1e,0x60007d0a1f13e603416e,0xf929123a235048103582,0x52040d5049781f42a2a4,0x4109607d0b826004f981,0x4f9344934119420ae04,0x7c48460a905810598260,0x758013540881c3511c18,0x1f80511c37064d07c40,0x1f058002c08a2a4f9620,0x4a22b4f8c1d05e50f0b4,0x582600c293e482007f0a,0xc2d3e6c5f4185a14e0,0x388ca2b41d0407a05826,0x20407b0a8ad3e407a17a,0xf0bc122a4f9617d0741,0x1f0a2307580090210465],#[0xd0893e200b8042d0893e,0x2508d0c181281f118042,0xe010b4224f87c2a2f0b2,0x6e010b4224a30b0a9423,0xc33058050f437074087c,0x61d07c50801d42d08b0e,0x2002c08e01c330b4470,0x142b0b413041782a4fa,0x8c1d24450a3b0b42207e,0x82c08e01c2f044f87448,0x4a0e81a034605e404650,0xc26005013e1f089123a1,0x3ac08761f0b801404f87,0x3074131ac2c2ac410912,0x5505c2b1d0ab10283608,0xc085b4131bc1b0d0a854,0x9801104d91a1d8e14c02,0xf802448e93e1f0a1404,0xf0a14049801364411a1f,0x815114713802448e9421,0x1d888e2328ab0b82600,0x330c511468763b0b4751,0x87342d0d8207c507a8e2,0x26004f93c17020ed1bc1,0x1f1011e044102a07d0b8,0xc4839c0e000cd1bc1d0c,0xdc0e001103b42f064687,0x346f0742e014307c588,0xf034307c4a0414e09c17,0x307c308c16e002051bc1,0xc0d1a1f0e14f0346f074,0x6c0b0c1f1a1ce0143707],#[0x48ed0f41d0540e00c3b0,0x22070dc1b101f0c2324,0xf0c12b0418b10c687c33,0x4f88c4080c6f07c0b0c1,0xc1f121194207e01c2f04,0x81103b8030bc1f034688,0x8c17943c2f04240844f9,0xf044f88c3c2a07e09800,0x1f02c107c505e5081fc2,0x1f0d1143a46b061851bc,0x21f30a6d1bc1f02c108c,0x42350d8260146f07c170,0x5c087cc288c4c450eb0,0x872c487c30440ed1bc1f,0x3065c18321c990ee0f41,0x443a08b028d311c27044,0xc823c2307c113e1c884,0x30e82546d07430661f0f,0x400920bc1f034683a1f1,0x3346f03c1d0c1f141c8,0x687d8283a58730e82ac1,0x208c1c945c1f05c0b094,0xe81d121f0d447061c87c,0xac260146d283a3a1ca0,0xf8ec251a8cd2822388ca,0x4f8e0d023c270414a324,0x34f8a11d0941a3380219,0x32c26014f9007f084a23,0xb088cd3e405f41d048e2,0xc8524f9217d074120407,0x1f0e2588411907c27048,0x21f0d4083543511c1a18],#[0x61c880343508d11c187,0xd0dc18661f110d423447,0x47074087c4c3508d0343,0x4087c60801e035430234,0xd422c3b0cc150f43707,0xcc2511c18781f1220079,0x65c18321c962003408f0,0x9a0d02340d1043709c10,0x30ec2304197060cd021c,0x18721e128ed0e4350941,0x1f100d023c27054410dc,0xc2c0f01b061151140b0c,0x10c687c2c33803110631,0x303c1b1b0607c3037413,0x1f0ac0f06c6c181f0ac3,0x3c19401f0ac4303c1940,0x87c3066c431a1f08c430,0x8661f0cc6819c1b0c19,0xc23110cb1c2a3ac3b06c,0x6c0d041131b0c84e5d05,0x14451c3858c340700b0,0x5108cd1c2a388ca0ac26,0xd826c25114687c330881,0xa1f0e01b054451a1f0a0,0xc1f0ec243709d064411,0x60a51140e832c6f03c1b,0x8dc17021cd1a0ef061f,0xce04c4706c0e01829445,0xad1bc1d0c1f12119040,0x61f60051101c9440e702,0x64687c3a0bc170346f0,0xe0a1f1445945c083b427],#[0x8dc1059c1a05c0e0146,0x525151bc0f074307c4,0xc3059c1f03469441f0c2,0xc1f1214d1bc0f065107,0x141c83941032c6f03c1b,0xd0f41502c3b03c1b0c1f,0xc91ac1e001c89638728e,0xcb11c1e00c085a50350,0x9c18721f121910cc2305,0x721f0a1050c807034681,0x7061c87d8014c151bc18,0x72414543705c0d1ac2,0x1c904370546f061f3098,0x2483b46f09c1065c1832,0x6c0b11c2705c1d0c14c3,0x530ed1bc0f074307c484,0x601c27044f872505ac20,0x13021c94258650cb0621,0x48650ec3380311c2707c,0xeb0819d1bc1f02c107c,0x30ed1bc1f02c107c3873,0x1b82f07c1702c207c607,0x7cc2170eb041cd0d805,0xc3b4351bc1f038060bc1,0x1c85e29121603e1f081c,0x48ea0d4a07c2e0644d10,0xd120f87c2a3b4a07c1a4,0xca0e81a3b4487c323a1c,0x4183b81d10c285817901,0xe2285c4a05f0f8643068,0xa0f709c10221650a210,0x43e1b0a1603ac103e1f],#[0x4470783134178c0d01f8,0x48ed0ac26001f03e483b,0xac207d0fa3a48594124,0x7d8313452040d50407d,0xf924103b81601c1d10c2,0x190625f09c150a1623b0,0x16709c1f05441348e901,0x69003fc2f084a0843846,0x1b42d08c2b084a084584,0x42c208440869022407c,0x1308211a17a4406d0b41,0x122a07c1b42d0510b0ac,0x41f040f872210c2305e9,0x306d06c23041c8843f09,0x808511c1d030eb18423,0x707c0e1a8e9181793023,0x123a86d18178a1c84009,0x14a0e81a028ed18178e9,0x842707c0e1a8e9181792,0x7c0c1a0ed041f0e1985,0xf07c0c1a0ed041f0c117,0x8f87c2e01c243a4a0722,0x10960c4a07c2c4109504,0x25c1f024221a0e87c544,0xb0386d041f1491041414,0xe87c4244425074083ac1,0x1f141604009707c0e1b0,0x1050509707c090a8683a,0x20eb06c0e1b4107c5072,0x386c3a1f101c90b41d0,0x87d0fa3a385810025c1f,0x287d10a3a3e009170542],#[0xc287d4203a4e00917054,0xa8f8723445c1f05c0c1a,0x1b4243a191011d09c143,0x87cc283a5859c1b05c0e,0x8c1c845c1f05c0d0886,0x1502c0e1b4207c0eb0a7,0x2312234441cd06c1d04c,0x16045c1f05c0e1a1f30a,0x5a443ac183f80072258c,0x121910ac23050ee000f8,0x43a807021cf07069181f,0x2b050ec1bc18721f0e10,0xc270706d0a1c87d80164,0xb803081c930e845c1702,0x3a1c8f0e90bc17061f41,0x8590e920cf09c1f05868,0x79011b03c2704c470742,0x5058c1707c0e1b42c3a1,0xc1f0386f041f30942c3a,0x7843050d0581b0c16859,0x5441905845010d058390,0x84184706c33050d07c38,0x8d3010f86c29410f87c1,0x72258e411410f87c2058,0x72258f80832c2304c00,0xec3e1c8f02e02c230006,0xfa281c8d81b00c23040,0x6c404f060463040c2301,0xf4004f100548a0b4370,0xf0a0ef03c187306e041f,0x1ca28258f81707068721,0xfa12168f10709c003e],#[0x4f42c40118e15441c270,0x50013a3e15098110fc18,0x631183706c084f428464,0xc1d008fd094107225930,0x1425044885a8f970ec32,0x181f141943b0cb08c150,0x3b83302405021ce1bc1a,0xb110e92586f061c87c34,0x705383703c1e1b403041,0x8360bc187386b081f500,0x81c929143b4130540b03,0x70eb054150186f061f30,0x386f07c160b8307cc21,0x61bc18721f0a14c3b407,0x1986f074006c1c8e09,0xc270586f061f5001c901,0x72380586f061c87c2a44,0x896461bc1f054007cc20,0xf90905070fb08c02181c,0x48548ea33c2704c005b0,0x8650940308c01130f85a,0x3e30408606d0f8642a40,0x1f0f8d82f09c130007c,0x1e1b0607c460bc2700c1,0xc18721f0a1484183703c,0x48fc224ba22190f4161b,0x344bd048c81e888f0bd0,0xa10c1d048e81e889211a,0x622246072178a11a3c4b,0x2510e516021f2221c8b0,0x221c8a505098092e1622,0xc244d2241b0c4e602512],#[0x51388912c4d01e31444f,0x43854893064d01e4f8c1,0x2035061393d092384e22,0x224080c8bd061822a890,0x390e8951c2a334186686,0x442328921943d1c2a390,0x64f11ac1e041392c8914,0x5a152244f8e510801b0,0x105a890544f8a4d30781,0xc820801b08510801b078,0x328ab058030b43d14410,0x2448ee004d07c4f8e8e2,0x4134c1e002501e4f8c23,0x1f8781d50ac16004d07c,0x78005211c3c8a9188610,0x468bd07802248ad3e450,0x506c16008ca2b4f90180,0x8e001d0724f87c387a8e,0x7b0540e001d134542d0,0x2407421121e85f0b422,0x18c70c2301e4430740e0,0x30b43d1c46010aa0e43c,0x48944f8e8e2328ab0580,0x8005a4f8c4d608c1e001,0x54350b8007c422a42e09,0xd8050a1f082305b8230,0x11ac1e002408d0a88441,0x388d113058043a1f0c1d,0x232388ca2ac130943d14,0x334f8e8950614a194fa3,0x8781c8e8e506c122a14a,0x630ec70a1f43508b0940],#[0x8ab04c250f470f0cc250,0xac1e00c088e1c908e232,0x8c16005107c413c4b11,0xb06c087221102350d82d,0xec32c087220961e43246,0x90e87c2144c143a1f090,0x86422448ed12178816b0,0xfa24161348e8e8e87344,0xfa2a161348e8c906010,0xd06d07088470eb183a45,0xc3a24109123b4605e243,0x805e40821642a86b06c0,0x1f0a21c450ea1ac1b041,0x6c0c3a2591113042343a,0x32c087220821643286b0,0x88619c3ac2064460d0ec,0xc23050e87c2c3ac10641,0x861016c3b0cb08208c,0x8642854904338285b0ed,0x3c3ac10641c3ac230419,0xc2a448e05b0ec32c2500,0x3b0cb082c3ac23054007,0x5b404]]
set_option maxRecDepth 16000 in
def g251H9 := limbs80 #[#[0x40b1201080114000b2c,0x10051809000a00000000,0x1e0d0007221910000006,0x22c0c00000001090001,0x100403012e000c150201,0x2030a03200003060300,0x3b020000040a00000800,0xc100900000016133610,0x6040201002a022004,0x705001b250003040028,0xb060507050f20011509,0x1030000003a2f010439,0x37003900030b0407050b,0x207011100000300000e,0x2c0702250029070f0e,0x11005000a04011e1e00,0x1a420220060f01090600,0x6d0a01070001051f0027,0x1508082d00030f090696,0x20c290f070e08011d14,0x110a0602631355700c0c,0x2506078f00033507,0x110000010218010a010c,0x1031000000605022205,0x924070b0e00003f0418,0x91206410813030005,0x550b0039210600010001,0x210f0004070004040505,0x70e13011e03000931,0x407130a0700044300,0x1a110d1b050a08203b06,0x8040212053b0e030e07],#[0x112010a1106180d0b2d,0x120c291a6f3d41180126,0x2f15040d051403030512,0x42091c051b0400081003,0x604087f0e01020e3805,0x150a044106000300001e,0x3e000543010208142d01,0x80c030e0700014d00,0x503001b211749070405,0x10022600100a5b022229,0x1f0000000c0b2e000c18,0x10a0209020b2a0e31,0x20528001f06031c002c,0x8210a120f1603010911,0x2a25130f551e06010f5b,0x81e03bd45011c2d0e0e,0x114d3f0d010601390c08,0x20040053000600000200,0x21a0408030d06d32433,0x11c1302072700030800,0x1816100959012215030d,0xf072109020b060d0705,0x1a553c010100001f0b0d,0xb9fc014a3708070021,0xe1733850fc759e726500,0xd51a848ac653e3f77b,0x93e0eb00007c24000000,0x5270980000000021c1b1,0x7e98f294d73d7c000055,0xf9449591f2d01b703773,0x77a53a0000594dd0d079,0x419436515e4bee9e60d5],#[0x9af574b4550398499363,0xa30b8b7fc5474324f3,0x56a2d35bd784fb004200,0x91634c6e57e20cf2f213,0x64b0c5ee40f8a32371,0x33a3ccb43788c1b25c00,0xd242dc70e9b4530498dc,0x77b331483b10da0000c1,0xbfb03b507c00006e4c56,0xcc413b6609f619025f45,0x1c4b0000260505,0x3d767e70b39865f2f400,0x5e76730000424b95f296,0x7028403fb334b2,0xc7e65ef3970000000000,0x704204616a00000000d1,0xb09e7e00001a0f0000d0,0x28d4cc7089a3d152a902,0xe2f24d1234c00200004d,0x52b3cf609f0000c29f05,0xbabdf49025d61a7595e3,0xfc54daa0f574ce814c89,0x88847c553630d4f24f8a,0x604de42267584378bb3c,0xdc811916224518000003,0x1b5206c217910000003b,0xb47bd41b0971f1000064,0xae620d30cffc70718a88,0xa420228703e7000031,0x15aa80d3475641000000,0x800161e17fe3bd610834,0x3a05a543c5a4ae058b03],#[0xbb058a02bc13ade0b84c,0x9bec71b1d9b6460000a1,0xdbf08f2531f160000058,0x33ec1472e207fa9e22,0x56500004583000000,0xcf70000558500,0xe005511a00,0xcd0664d3960000000000,0xe45307947bc0758243a5,0xb60201ac20f1953f25,0x5ca49685fa8599144600,0xae00000000004b000098,0xe51ee5fbeb7cd2,0x7a413a00006480442d00,0xc510d2f08e8066e5ec90,0x34920000a1aab2d2d5,0xc0e80000043cd00700,0xab0000000044b9000000,0xf2e700000000000003,0x66000000000000000000,0x25430000000065acd5,0x13c700000000000000,0x80bc810000a4ed518b00,0xbbb213e4000070365d,0xd3d28f64399522b8fc00,0x798556e11049630000fb,0xc246e98b3434e214c2,0x64c9fc46fc3921fa00,0x4ad3f643df00005d9e00,0x9273bc11108565,0x59615b53d8d4ec12de00,0xa830f2962f0000b06381],#[0xfe796ebc5485058b6884,0xf5b3a1d3be743ba52c60,0x4df59a01ef0000702342,0x2344481bb6e3b140726e,0xc674b9831c4e000075,0xff655300000000c4ac00,0xbea00b00000000000033,0xc1c4eaf539d0df096c3a,0xa5b6733eec690000e4,0xd920c000000000000000,0x2105330000f0416b660b,0x88da24a3f9d786,0xd7a590ba84c4bee59100,0x6359210000d0b0268440,0xe8d90324f5a0ab0000b3,0x72d63c0000349e218748,0x1761a4009c44c5c20096,0xf181c2a473425a1e35,0x1d0000821c52e903b700,0x577e52914e0000639f03,0xa3048fe58e29e3a0940c,0x22c2dd5029d80000e2,0xd48408c45161c90a8100,0x460000d4cbc4752148e5,0x823f98ad000080f3b5,0xf246400000000000000,0x7ba70000e625c4bf91,0x5f29d30c5b0000b50c00,0x237bbe0000506eb4163e,0xdb3c1471a5202d332d61,0x5ad182945b00000000d1,0x40882c318991b442e658],#[0xa500000000b5114c16fc,0x24e54400005b2d057a09,0xd28600000000e1,0xf2ce00008af9d4d300,0xd32c350d912e000000,0x500000a1dd0000a0aa00,0xf3621f0000517ebc9754,0x225907530c25d30000c3,0x204d55a4a1026e2309d4,0x538b7ac3a9f66dac44c6,0xcaf1e8a294a228a1e483,0xc90000e348b5b8000032,0x95656441d4cb80000030,0x743d4fb0098bd1743f81,0x1a0000000095b35aec44,0x370000000000002379c3,0x5d65f7000029c46657a9,0x49040f9188d09a012733,0x65514b5dbe7c7684e972,0x6000008310631300006a,0x957f00000000fe7696,0x64a2b3654bb134317600,0x264c2c0000700f784878,0xe1401d1000000000b8,0x996830712fe315d1b000,0x157626f427c3b5327f60,0x671296fc56b4c0ab10c1,0x117022b19cf2cbe3378b,0xa406000032100000d3,0x263316b88e243321cb00,0xc800000000000064ff2a,0xda54d000000000a22ef1],#[0xe2618e70670000297d81,0xa1b61746116384000033,0x2f71c5007dc3ead0d5e0,0xa9356b051de53b120130,0x1af021022100007c4c39,0x69f485cd9c00003c4312,0x5c020300005b62215331,0x6b8d9d3081492301b7b6,0xb200008291eaf3714919,0x15e0f08020d48e645621,0x6224dfd81b00002339ab,0x91000071cec94c308012,0xa139e2b6de7a94,0xce142114d632f000000,0x9a000003f40000000001,0xa00000266f980ec0e411,0xe37b8f13e5000082cd70,0x2a0000f859027d8374c0,0xa5c0fbd084f102b06fb6,0xaab7f0739035d8b57a,0x327440000000005c6700,0xe4b1d15a33d091e080,0x612405bbf6387e000000,0xa674655ba861b5e1a2f4,0x71b59ccbe36114f53402,0x51f975235a444c0000a3,0x488248d60de1a08858f3,0x8b1b718c05f9a3c440,0x9950cea50bb147e36200,0xe462a5dfc106d2d581,0x36de3bb2bd492c193d00,0x7600006560c63400004c],#[0xcd167ded65e633460e05,0x699d0358274f00000f0,0xaa0000117400003a3925,0x37f2ef7284209b648435,0x1370b6a5888bc90b9815,0x8392290000aaf2e276b0,0x7f945ef1774226ed1bd2,0x51f4cfc3d602f1f4fcba,0x2b2512860161a600005e,0x506608047a1532fb6a95,0xd185c354ebec7972dfa6,0x30a26de8bf631cb5ad54,0xcac1b3e38d341a1117c3,0x9254828b615083c25b41,0x32084a70009d16c51452,0xf301e5a2fceafe201e79,0x828c8b83751290127ec1,0xd8f033557162bea05fc3,0x37a1856399b29c106184,0x2a32af950f8598b53ee6,0xabdc93347780ef000038,0xce161200000000059f55,0xa91500000000e01cd8,0xa2d4e1000062ee000000,0x47715fe8a3db160b2f4b,0x3a55fd925dd2f32bb116,0xc80000c3af01be5266eb,0x8d00006aa3947f718095,0x330000f25a0000b655f2,0xfa0000a0d30000132a93,0x3a34c65458b011000014,0xf1482da2e2b5e9ed9ff6],#[0xd7ce3d58bac31f085685,0x22b0ec6e56b11342e1c2,0x22757b5dee9318226c91,0x30a578f56222a7660c23,0x75730000000010e1b0,0x9dc1685e8601ea63ef00,0x5fe92e7675ab600000db,0x84636e028e662c7368ec,0x4373b2612a4014000051,0x1a1004b648434d705af4,0xd50000e05e659d0a5078,0x5d3be71bf7051b72fd45,0xd96614e2953049352424,0xf1c63b292d5a37c2e5f8,0x8fe5ce0bc894786aced4,0xd28668bcdf0b9b9defd3,0x689703c3c21c3f2b834,0xda436f000002bf11a329,0x8679845b18465d40adbb,0x724b83c15d706a93a4d1,0x298b1fb278e138b2aac9,0x3ea92f02c4b4018b3624,0x1860034b23a996636772,0x769905501a6b73593422,0x5df4b36101d0ee702426,0xebf3c30c73205711bd6e,0x31545c253851f0bac7d5,0xe2d04092c9000093815b,0x86e852612601a963501b,0x9700000000d5cff917d3,0xf624cd1173916eb6060b,0xa1894228d30000d5a28c],#[0xea00005369b2380000ea,0x7da231f6436156426bab,0xf4aab424bbb3a5a30dcb,0xbc09fc480000527130,0x30ac4233d3f0546d00,0xb6a2090000c8f191e200,0x28d183216ced47000081,0x1632470000548c20db86,0x21a18d044fb19b80f6b1,0x5db930000335b906013,0x58f473fbe52e0a0bad01,0x5bd0e56e3ce319855f02,0x8d32080000a563237778,0x36f1bc00000000243139,0x94e5d6d2a5c0ea432761,0x3400004365e5e524c431,0x3a7e7712700000000080,0xcda9db36d83bba33f54,0xa7566b0000c5c20000b4,0xc236000081cd009754,0xc67c38d9bb0000000000,0x7d0000855910bb2308a3,0x306bec326058ee801215,0x5773fddac2c67873bf25,0x92dda9314be9d09195,0xfe54d4cc7bb22b539e00,0x6a8269abd6229e70c613,0xf5fb07f36a5305e04d25,0x2013b0f54062cfb468f3,0x45e43842eb8373421dc3,0xc5afb2810000ea,0x6b908000000007d3600],#[0xae0000261035e3a05d9d,0xb499155a1934e4c9523,0x2fd5250000b076c5bc7b,0x2505a97a76aa7e906265,0xf1afb2a281039095c4,0x8900002618461cf3f200,0x3ec535000011e733de92,0x2524e800000000392b06,0xc114e6752eb41fa4a0ab,0x2cbe6d53ce1f6b3b652,0xe60000120fcd1c52ab72,0xa962428b2090775b6370,0x5e467b70798c53764a30,0x2f73cac25311e1f2f8be,0x8974bca8f513c813ac74,0x613b6d09b7a5d9c2b154,0x3a1171b5f39d99fa9b03,0x6ae4996e7b4395002b83,0x4e1cca0cab92eadda684,0xd830319257f1ed21eb44,0x45a0f1291345000030,0xd004c20bbc6441e8ae00,0x330b29d4a6d2f0229802,0x51116da4830000143051,0xe2520000211e000005,0xa412800000e018000000,0xf5bb000031cc00003d,0xdd000000000000207400,0x606d00000000f07f63,0xe449425a64649e5fc00,0x55c33200000000e4c7d4,0x9b604792fe000041f4e0],#[0x870000c50a502e1e7245,0xc700008681559665b134,0xba83000004f780,0xa5fc1c0000ac96219e00,0xa151370000333c0bab80,0x3b720e000000000000d1,0x8f1366c22263c16c41ac,0xb8d016647d99c991d185,0xc1fc7500000000756174,0xa25326327a316b78ebfd,0x2b92a01700009d2380,0x520000c2f9421b322000,0x589232545c64db5de4,0x3545db0000852d566500,0x72dba3e24e22ed03e831,0xb7a951756cc5ca05ed02,0x7c050e4bc7f5b5000058,0xd2ca5491dcec1bc9b4e3,0xe27c5260bcc815f4aafb,0x6e3d5db54e491bd1def0,0x10b4196adf0000027484,0x4b3d5e51c3b6400c3e4,0x435006303a5118316571,0x8c209d30dc7027629b70,0xf71175847e52cc83eb60,0xb4e581b67000002054b1,0x1e1884540d94f3000004,0xfb80650000a1902c8f28,0xc2edc3000013e335207c,0x54e30128b225930b4293,0x56b04c0663144bd65ab5,0x3d15280000621130ddb2],#[0x494b8ef4f98090649da3,0x45b150c13c3388744563,0x5b6b1a05a4b39b636bb2,0xcc0000a2272488e46936,0x97c0f930fd000051c620,0x5500007c42000000006a,0x5400000000000022d401,0x8713eea3894340d21693,0x516413758d00000000d5,0xff3daf0000502a517c51,0x520000828c00000000f2,0xdb40cabaf1267ffc134a,0x138a1fa0b47630f44243,0xdd642835d060686519d6,0xf513fd6084c3000004,0xc1d00009223f54d00,0x97000074470000000000,0x84b534b2000034ef75,0xc8bb918570c198393e00,0x92b700005503560429,0xf224e285150cbc722d00,0xba5c801107b8deb8df14,0x395e5c7973805c631e41,0x7a30ffd50231a700f75e,0x44489ed1a85331796,0x742bb64ce10924e300,0xf540e00000b5b4000000,0x9ca6690000aa7da5e821,0xc2b000059b26c5ef3,0xb56df84b12d9232800,0x3ea9dbc46f013f12d800,0xeb4a1bdecb8bc61ea0],#[0x985ae20000e5c03a7100,0xdf89d562750000e58959,0xbcfae1e1ab19110000e9,0x927cb346000052c5c3,0x7254b7e686ada7a48100,0xf72d1a2e0327b128bd5,0xbaa93600002ba5528226,0xde80c2b3fbb6428392c2,0x467404ac49a4189015b4,0xa801782459b8091a60c0,0xde588dc2a60a3aa2d1,0x702c6131ffad842a3800,0xb101fb117943b9c385b4,0x707be1721c62f0,0x5e437f42fa2ba0165100,0xd1f297ba4800000e6135,0x5d00007162e1d724add5,0x6f104fdb94ae3af96d35,0x6302b9c25124576c77b9,0x10d1574d12137da47144,0xc002f7e403764462c669,0xdc608d9235231b61d5c2,0x167638b5c194d990fa34,0xef4268249b74ba197e98,0x1f79cad454565f7259c5,0x54e27735c651b8950050,0x40000f5c7d36cb14418,0xb9000011d86b30b4dbc9,0xb4002594f20ba38e95,0x3f00008387c1d650d100,0x84ba0020cbf5c93c7a66,0x4f00008549e306b00c95],#[0xae11e32656d00a81bfc3,0xd4095325741790,0x83000000003424b8d800,0x6e420a194343dad35763,0xa0fb0200000000000035,0x2a93cb726a0000b16793,0xd3e23b641e4bdd0000f2,0x8230000d378a23211,0xd63600000c17000000,0xe500007b3f000079ce00,0x264639e4b6000003ed84,0x5288c40391751f000035,0xa800000000f0deb12c31,0x3099e0b8c562da221ea2,0x5febe8a6151376322c81,0xc8cb2219711965d66743,0xf59568b044d10e02a182,0x150000a4974af425d7dd,0xbd511ff5f4b045b10a92,0x430000484ed1df30b9e8,0xa0d5ae0000e096845aa3,0x22b5505414b64d000082,0x664312a3550000f0d6f8,0x260000000022d69bd55c,0xbb9575450000000060,0x1205070000867903e600,0xd0607123f881970000f4,0x2fac5c054250af219f2a,0x4100001c5a0640693a32,0x4a6c84bc238c127111b5,0x4e840b68490000000064,0xc9b0a320b254d59170bd],#[0x4f6c3791cfb5e06b1253,0x69c3e050b7c49a000025,0xa7c5f534a2109e00008b,0x9d862d2e68462ecd8130,0x828344861dd244cc7882,0x74254cc508864f4a16f0,0x4074211a7afb7bc652ea,0xe4297739a6e43e935ea2,0xad954891b1103983b37b,0x930000000070d9c46bb2,0x201009860000014632,0x5513a80000642c000023,0x902c5866820000000032,0x2a85c433943e08c62913,0xbd00004b0dd28a602904,0x36d9128b5cb00d000030,0xc2e2b200000000a06923,0x100000f22433b4d03d41,0x6cc17b0000255b9c2a2c,0x5024661828f9c5e2c32b,0x3d91fc439d390b09eef2,0x53e5107c4561f9dba652,0x904299a1fd61e9000088,0xb5f3fc00004051d61b14,0x523935c30e7d6eeb0ef0,0x2d04d6b9b6603c562b40,0xe95cba3ba71ad93f991,0x69f37bd623040abc1880,0x2743cd0b3cf11de143d5,0x38e059000000000000eb,0x8fe4e48008000093e120,0xa822889654a600293351],#[0x7529bcd120a4e7432e25,0xa1f854f8b2b4fb34f5,0x16238b71c44c2095b000,0x78826100000000f5bd56,0x58000004a5908b0000e9,0xa40000d3a2d314000070,0x333b000063a7658c44,0xe9a42e1bdfe0c4414100,0x86558634760000ba9c53,0xaf9624113200000d0040,0x43a680a8541d4c1954,0xd8c300,0x2bf5c5f8fb148a2a00,0x7081d0000000a4000000,0xde207eec6800000d1f43,0xb705dda2e81426b52ad5,0xa7f61f14f4000075ba4b,0x50b2acc3c065b7219dc5,0xdae17d00000000e212f0,0xa363d78196848d966675,0x4e0000c99e7dbfb46cbd,0x93a35c0000285e066a40,0x3113d25b8c64490000c4,0x24a9000000000000b6,0x426484f6457e000000,0x923c00007ae8809300,0x295053b364743580be00,0x9accc01955,0xaa610d06614927d65800,0xc70239664b3303711cc3,0x5a7a7c65800000517a09,0x843d50e7748b99e2b5],#[0x3942c7cdc0000050a600,0x33fa84bd00005b,0x7bd55c0000f939d15c00,0xed402c13b81bb9b14f1a,0x4926f1467a3350000eb,0x986083d4d504bc,0x27c8ea3a820cfa000000,0xd8f29a43dc0000ca99e6,0x300000a66c71540000fb,0x31f230bc6aa112e5b249,0x9a1432f67c51c0912568,0x81280000914500008a,0x67366e016fc38c651600,0x6938030ab607000005,0xf19402c4070000000000,0x920000a57c00001855a3,0xf056000092ec22e441,0x41eee13e1241a30f00,0x249c000000,0x800000000000085f600,0xab0000a12b253d4a750c,0x1d000003cef56fa32904,0xb2e3c5dcf486000060,0xc0920225724cb8c700,0x13a6804e7d706c000000,0xbf0000b9200000335802,0x21000060c8f60b6393a0,0x7985a384c89c4dabe085,0x85b372359219e1e9b9a4,0x3dc0ede49f0000967196,0x3a006b5632c5f015e131,0x8a7a36000000006411a2],#[0x450000c04a9166632bc0,0x1d7de087000056,0x1b03d300000b4060c500,0xfd8ad26326627a51c1,0x63e2fb83040d66f65900,0xec5c894925b8d724ee51,0xbb14ca36350000ac3111,0x210976a07800002ad1a2,0xa24a000005ff71,0x7a79deb64ee34b446000,0x262f600003603000023,0x13d4fe3555a99fb827a3,0x58000008510000838a29,0x125e648290000050951,0x644d821995e770,0xfd31312237541c220500,0xb5f0c10000042315d254,0x791a05d8c064c1fe32,0x26a5580000ac83e08800,0x640000893b0000034ae9,0xd135feb1b939c113d9f1,0xe6000000000000510b99,0x8100004c94000004e011,0xa32e38ab99a0ba00003b,0x15eade5ba45f157973,0x165be4b0c0000828500,0xa8605bcacfb9a2d35965,0x36833c87152779]]
set_option maxRecDepth 16000 in
def g251D10 := limbs80 #[#[0xf73587aea9aa3bb58960,0x2ac5f394d62f9aa6b15d,0x53f9ca7317cd5398b76b,0x7f960443fca8221d7595,0xaa8a21fd50510fea4288,0x8910fdac4887f561443f,0x885ff72442feb9221fb9,0x2feba221f794d10fbaa6,0xfdd510bfaea885ff7444,0x80905ff76442febb2217,0x482ffb8a41fe54120ff2,0x1fb58920fdaa4907ed42,0xfae8907de53483eea9a4,0x75482febaa417fdd120b,0x2617fdd920bfaec905ff,0xbfeea985ff744c2ffb9,0xff71503fcb0281fe5414,0xb9281fb98940fdac4a05,0x540fbca6a07dd53502ff,0x5fd76502ffbaa817f5d,0xffb8aa1fe58150bfeeca,0x98950fdac4a877d52542,0x8a877d54542ffb92a1fb,0x42febb2a1df59550bfee,0xbf58960bfee2b05ff765,0xca6b07dd53582ffb92c1,0x5582ffba2c1bf59160fb,0x43fd54521bfeeab06fd6,0xfbaa690fed62487f6a92,0xf70546febb2437f5d521,0x12a3fb58951feac2a8df,0x51efacaa8dff72547f73],#[0x6fd65586ffbb2a37f5d9,0xfb82c57f5d952fdac4a9,0x4d62fbaa6b15ff7158af,0xb15ff7558b7eb2ac5f79,0xbf6b8ac5fbdc162fdae0,0xbdd562fdaeab17ef7158,0xe0a9dff7254effb82a7f,0x596ffb82cbf7dc953fbe,0x1ff50910bfee4b2dff71,0xfae4887fd62443fea922,0x74443feb2221ff55110f,0x221ff5d510ffaca887fd,0xffac2907fd51483febb,0xfd53483fea1a41ff5c52,0xaa241ff5cd20ffac6907,0x520ffae8907fd64483fe,0x87fd76483febaa41ff59,0xfe90a81ff55130ffaa49,0x58540ffaa2a07fd31503,0x4a07fd32503feb8a81ff,0x3feb9281ff58940ffaa,0xff5cd40ffac6a07fd535,0xaeca07fd75503feb2a81,0x1543fe98aa1ff48550ff,0xa1ff4c950ffae2a87fd6,0xffac6a87fd72543feb12,0xd74543feb22a1ff5cd50,0x8ac1ff48560ffaeca87f,0x60ffaa4b07fd71583fea,0xffd75583feba2c1ff5c9,0xeb12a3ff5c151ffaca90,0x4961ffaeca8ffd72547f],#[0xb17fd7058bfeb1aa5ff5,0x7feb82cbff5d562ffae2,0xfdc565ffae2b2fff7059,0xc0007ff72597feb92cbf,0xbd026a081019e045009,0x7a058213984260f0035a,0x6092a22807f21d106841,0x8cd23120b642b68a5027,0xb04098f783c00e4036d,0x6a4f8133249c91e84531,0x5fd17105a195c655394,0x6de1aca6829980642189,0xda1ecc78c1db87429c4a,0x5a31689a21cc83ea05e7,0x26f498d25bc943a44e8f,0xad2a84a99aa3fa83e9e4,0x32b65ad0cb17abe6adba,0x6c3db07ebf42f58baf2e,0xd27b414cde32eec9931b,0x11b798dc3b6a8d7eb53a,0x9baf8ea03a08e6438f4e,0x3ee8f9c3db0f40bc42ee,0x23706fc147033c056fea,0x6f16bc4ef107435d0b94,0x3275494b22bc7dd1b9c6,0x3684d3b330cc272c7ca8,0x68d1074044f873bf4e73,0x754f751253bf4c452874,0xd8d561bd78b5b2d5d555,0xca17015b7b6aeda1f657,0xd980adfb37cede5775cd,0x38f9635b8b4621186f60],#[0xa14e7939bde64995de49,0xc6bddad06a81a6768ef,0x8ef3dbb5ee3bb67ecdfb,0x72c1c8df165c36f063be,0x7060d8011d29f3d5cd7,0x84c16003e32083b85c26,0xe1305808081e0c381435,0x14422c0b09804287c5c2,0x81c060c1a851e0584c02,0x417098042c083e2c0b09,0x1305800f8b84c04190a1,0x86c260a118380a14a02e,0x8470b84c107c81486423,0x111f400721414422c0e,0x505823820460d09001c9,0x9820d044118307c010a,0xc2e13040f08c003e4e1b,0x5911c2e12001f244283,0x1c2e1200140f8e214108,0xe40a04c34006c1424591,0x5026186c14088c12088,0x11c5311c260a00850f8e,0x72609a2384800510a2,0xa8440c0580e0b0708424,0xd85c14230684088e160,0x80e130583844010a2c33,0xa11834284470d0642206,0x1c260a00290f9586c260,0x1304110f8c1d089080a2,0x8681451083e1d9221c2e,0x40824858a0f870a84801,0xe0602e107214091019c3],#[0x285c24100a4010841000,0xd84080482900060f86c,0x100491b83c0a1a00362b,0xa2584804090a9f260b04,0x2c361200850a0e830d8a,0xb0c84800aa283030551,0x144204860b854240702c,0xe1a00278a030a03e1b0b,0x9144284870c8480e0419,0x1e050d001b183b03e1b0,0x2440803a1202812048dc,0x98c0502237078120218,0x100d098c05020206c0d,0x21da14100d098f85c121,0xb0d81c1c110a3e28080,0x81c1a360886243215006,0x60d10390a961d0ae1705,0xc3e280e060280d022fc1,0x5042082a370781824010,0x5822370781414010c402,0x1f1007c361504940a8d0,0x476420c3782824010a9f,0x11f1a3e4a20e090050a1,0xa0203e0a0900c3217078,0x360f05814285480e0642,0x782c0c1200862c0e2fc,0xc0a182a40883a15c2a37,0x7068682922fc2a370782,0x240864a0e8670982c0a3,0x3060380c6586c2223078,0x430f8a0ce1a00941f0,0x100941082098146e0e0b],#[0x23413028dc1c15050043,0x24007c501f0c82c22503,0x3240703205c161b03834,0x4312071961b0782c0a10,0x8a028670982c0a370700,0x867088dc1e0b030082a1,0x58446e0f05814306480e,0x3e284385c26083a1f186,0xb8410077038306c0104,0x2811050dc1e046c1d23,0x288468ee1305004287c6,0x60d4240098ee1305004,0xc0a103a38883b85c1607,0x7060d802148c2c370782,0x3c16050a1d1c3b84c160,0x6b0608428f81246121b8,0x86c1c205e09060d86078,0x820b04800c83e2f0a13,0x24a824010b091f07c61b,0x60680800c3423060c178,0x4032020030a141787c91,0xc36130508c1a003438d8,0xf9184c16001e1a8287c7,0x3e3a08402c8d61301050,0x1786881646b098082a08,0x10c39280800c320a1183,0xf240b84c1602021ac1c2,0xa1a1092c1f84c16020a1,0x804287c7c260b001a0f8,0xe050c2f0613031ce1305,0x28617830982400408dc1,0xf8404080080046e0f0],#[0x200f8c050243707814,0xc04090a3e0f8c14c2e13,0xf1384c04190a3e0a0d84,0x8c26004181c18350b021,0x28080086e0f02851f080,0x85420821b83c0c190036,0xa1b83c0a007c202604,0x88010824642f0f948542,0x2e1300200f8c36102150,0x190dc1e060c85179421c,0xc1e050a3e10128440080,0x900080686c642009010d,0x6020001a2f0406c6c260,0x406c6c260900080686c,0xf0506400e49422001a3e,0x2c04143e36060b8486e0,0x1b070d828bc72503f098,0x8542400285a080800c0c,0xa30a0bc441e1111a5f0d,0x8c445386c2423070080,0x70820800b2221f1f050a,0xd090445814148b8608e1,0x1b0500c1c210885808f8,0x82802103e5872221114e,0x8a48108454422888b30b,0xe391c2c15412104c2c08,0x28445848142384c14003,0x5242203419c260b07084,0x890a8e0e8470883c107c,0x1a8161b0881c1a160088,0x61709000a27c8092681e,0x41113850542e18241089],#[0x854697050c2211a3b142,0x37121504b08838140110,0xe3c130b02800ed108e1c,0xa10070982d102a092344,0x1b00139a870e61824368,0x884502c2a1b078142449,0x15096190981150ec8092,0xa1b068589236002a302e,0x914138cc7090e60584c0,0xa344e12151219096181,0x10d464207102183b83c,0x80212103e869213c240e,0x60d004a0f858184f0485,0x7c6c570b048023528305,0x6b0d8240a17070480220,0x85c1412009f282a9a078,0xe0d1015305ea10aa0e2b,0x800e82c1140e1b0b8217,0xa2305e3c01108b468f85,0x282430f8a83c002b864,0x1d8f8810412008dc1857,0x4768d282e12800570c94,0xe1c5e1b8141107004421,0x3476440b0b04800ed108,0x861f161809e160083442,0x2a39c16051b838221600,0x43a0a0085c360f023e30,0xf058143054c200703215,0xe1a0046110770a8dc18b,0x11a941a0c194460d123,0x84c14020a9f26338482c,0x60d10390c98320ca0e33],#[0xc20f0341143207098219,0x6e0d04861f148845a347,0x66941f0e2082c0302194,0x82c01108e1c321206618,0xc6582440651a4c670982,0x482c010c3e303613c220,0xf8b0ca884582c0a37068,0xe0642a87412130d81c18,0x6582c0a3706860c92400,0x42476001f1f25080ee10,0x85984c1216001f283a85,0x510e13044220351d0ea6,0xf030d8023090e8441b8,0x83868f83a60763b06c26,0x94438008024854220b03,0xa91b0b82c0e0e1a840e,0x70982c0e0e1a850e9022,0x1a16123e0fc2472206,0x1f07ca0c8470982c1c21,0x80d6130020828b23482,0xb20340cc1826103e160d,0x7c50d20f0982c007c1e4,0x8047431102c0f0980464,0x43707814009c402a2b09,0x141388c3e2a183a1281,0x5c3707811383040231c4,0x306c260a0b8386a0072,0xc260b070d400e470e867,0x90784c107f0039259005,0x1858170982c007c5a306,0x81088083607070d1c8f8,0x844043706821f0e48828],#[0xa]]
set_option maxRecDepth 16000 in
def g251H10 := limbs80 #[#[0x5140500484287000000,0x1820072882401820470,0x10108200404108c48008,0x1cb1491c104001d,0xe04c1c500b0000850430,0xda0401c808b00100,0x862839c9044500242,0x20000100100a1400800,0x14211000504108814100,0xc801a04224200b08210e,0x10400c00800463002422,0x300b04308305200110,0x60c21070cc3db18f103,0x14c00072030171d73834,0x4412300710400340000,0x470440445020c504000c,0x20c008604058004d0842,0x1c300020100600004814,0x4220064028b0021010c2,0x80830d70450012c52804,0x1c019f04534028700a34,0x820010c808958094114d,0x24369f08300f30b0822,0x78a0800c10d300810b04,0xd1d500110218a3c1144,0xc01604511419,0x81175e600000002ac800,0xc000000000000002665b,0x2c6cb253d000072d3bc2,0x5f00000000052e000022,0x24668000a38b757c0007,0x22f880000000cf5],#[0xe65c85abea9000000,0xef9df113f0b1f55b0190,0x524d9aa10d7,0xd5920003c20800000,0x543831810000605c5b28,0x6a6814000519410a728f,0x139a3be60f40007c3cdd,0x9672,0x35850000b7d6000,0x91a40002790a87e00,0x320b923a000066d8,0x712558100000000ea7,0xac500000000000700f00,0x11862311c1d80002,0xa009dec0044c0778e000,0xc03d3ec10855c057e8b,0xc643a63a8242a46d51c7,0xba00035118000137cd9a,0xab0b64658c8000311520,0x38a1c5dfb295a19f90ab,0xf500389516f33f2c0c35,0xeb300006b919f3800019,0x39dd0977dc27fd74c4dd,0x64099000000000000000,0xb3d60003f0480004d,0x298df1b4314211809b08,0xb2fcf605d42fd0000000,0xd00c5ec49e05618000ab,0xdb384810903302fa43e3,0xf0e1981b30000c4fd65b,0xe7a00000f31278aa3cc3,0x231600006563ed4d334e],#[0x3a00000000000b482ad9,0x34f62a60000000014b90,0xfa4d1396b1dc00000004,0x2f8a1c000000065fcc56,0x3340001b9a2864000074,0x1b03c38600000003,0x81a64000000000000000,0xaca0000a940000000017,0xe85e8000056edea51238,0xc600000002c5c000126f,0x2880000e600062488b24,0xf59e0003836a,0xf888ba5c579deb09e000,0xfaa0000a41ff77c45163,0x2a3f000000000005,0x215ae19e000,0x453b3de0000000495700,0x24905170b1cc00000005,0x0,0xa3400000000000000000,0xa8a632be0000423c0003,0x118d41146a1c92b0867,0xbb095d14ef32a701d100,0x835d9b0e141800003dc1,0x6c2069dd78000a79fa14,0x97fc88d9d39cba07b001,0x4412238fce300c108f94,0x31cda05107abd104cd31,0x8465d6c0001097db79e7,0x614c8000e976e1c5c41f,0x31e7d9414ce51a584057,0x4b607b99cc214e8000c5],#[0xd9aa0e40e4bf29fe9396,0xbc86466a144ff002bac5,0x424530b72814cb852,0xa153acc737c4e7200000,0x5fe5ef61253471399062,0x2aa00000000000436c73,0xf35feaa0003c55c,0x2c000000000000001e77,0x505eb5,0x54224cbc0000,0x1ea34c00000000000e9f,0x39c68000e3,0x800000007f6b2f588548,0xb540e67362151d5d6e4e,0xe0480000000b7,0x5cd3f792e4b80000,0xfdafcfe85010000000,0x31ac800000,0xcde2d30700010b440000,0xb6c5400000006114ede,0xafc41478fb4d4378cbab,0xc000013c305d53753279,0x6c000000063e836eaa7c,0x3ef000023818baca3584,0x400018e3000103a00004,0x78b30000997,0x160618c9d07300,0xc0000000000058a40000,0x1cce54c17e5000004a0,0x10dd00,0x3851000000035c80,0xc7aa800000000c18a000],#[0x7a60000749bb9e3b,0xc98b62ace96e0001c4a8,0x15b8a8dd200000000cb5,0xde00012d4a55e38db8e,0xc0001b2a5334a1171693,0x61c7fbc0089e10001001,0x8f849080003ce08000cc,0x40000caa3c8de2e62c63,0xdc8c00000000000cf0,0xd76c0c80d98284e00,0x80b6a0d701d8,0x0,0xc25013b1924000786300,0x7b4903ca8bef0bf0,0xee00025384f4bb290000,0x1e224000000025,0x0,0xf588fa8124fd2d8000,0x39184ecc3f7825682f00,0x3974a9793666062ed166,0x596c0000000674644b,0x1ee3b826097d00,0x8000044864340003d5c8,0x14c440ede4f7c4b1900,0xe18400076a200,0x4000000002e28c2343d8,0x5cccdb4aa67870001591,0x839600001f213d9a5,0xbd76800022932f780000,0x3202c8000000036fee84,0xbf,0x1425a35a0000eb100000],#[0xb7ec2ca7ce225c25acd3,0x5565e4437c00022d836,0x888e54a0001268d,0xc1cd9da2380000000000,0x5e20000000362d3044d5,0x75f90e4a000000000002,0xc3880007a930001cf4,0x253f4120000000006900,0xb40e0000596c,0x276cf800000000000000,0xac4353c0000000016,0xacfc0000,0x3edd8000e1a0956,0x9bab5b2cda80004a7400,0x56a00000003,0x5edaa020000000,0x8227006dc0935000000,0x80000e24000063a4411a,0x6e0000000631c95f57af,0xb783b40000519e8fef0,0xb2f394f6e48720fc0000,0x4ccb589221295e0d7ce6,0x5e8c2da0001ceafead57,0xa1518000b797c92c0003,0x105dbc7000010d3,0xe008d3a0000000000000,0x1e55d6b000000001,0x70de000,0x919e13c2394000000000,0x72b300000001ae18,0xf3bd289f533249986000,0xe02b93200000000000e0],#[0x5fa70000b1a1c639,0xcc000000061470000000,0x8990000e3bf2cf800015,0x3024800070adc74c0000,0x16d5416d3ab293ee000,0x2010649c000000000,0xe03f49c5d3e8,0xc4000000000005bf0000,0x490e3c6fcba97270,0x25413462cc0d16d94488,0xb84f199b7b90a0001636,0xa681adafdf04d76b6,0x14acd8ad000124e00000,0x355e2cf2100000000000,0xe518000fd,0x66e6cf2920c00018b20,0x108600000000e3a1e33,0x18500000000c02000000,0x1c300000001cc340003,0xd20000000646eeb06000,0x38c9000076,0x5b2b0000000000000000,0x43ec880005b3c04550d0,0xbca90b4f61c000093,0xd30f0000000000000000,0x1278,0x14dd0978000000000,0x303e800083a9e0c559c0,0x1800018f5577ce69a000,0x495d12eeb8882ba4f301,0x8000000061b30c993da3,0x2d009db57eb0491],#[0xb9ded78000290762cc00,0x1,0xd80e000,0xb6e000166ad05a000000,0x5354000289b7,0x19af0c0000000ad42000,0xc9d0000000000005b743,0x974c80000000a73c0007,0x18ea44cc8000b4e70ad,0xa2817537ea900,0xc00018aa3f5715b1dd68,0x85d103d84a12595bd991,0xb930000efb15a58abfc2,0x1da16132e4b72be28144,0xaef85418fa684d266000,0x1e00001f58ee7ea65a03,0x155200000001ed4248ff,0x74000000071bd2380000,0x785000000000000000f5,0xdedc000074db329141f7,0xce8000000000004e1,0x972a00033274a2200,0xc00030d687672cc80000,0xcf26c800000000b12917,0x1ae0000836a832900a64,0x40000000000012600006,0xd699a1c08000c254c62,0x1917a96e40e1e6,0x198c0fc64268b9fcb98,0x4dd55b1a000,0x5b63f16484e230100,0xe8f10000000000000000],#[0x7a620227a00003442ef7,0x1068c000373e3f,0xc00051a43235c2580000,0x21c800022240000ec3,0x0,0x40000131000021b211f0,0xaef54ec,0x725400,0x0,0xad6c940000000c18c000,0x95fbca400000000e6a72,0xd8e8000000089740006,0x7aee52b46000077b0000,0xa65851200008f38000a8,0x2bb00006,0x7187a051c8a370000000,0x318e2dc0003318d9a7d7,0x4000000047542c840002,0x78000151df6910001050,0xf24b1840001980000041,0x1012f07462ce0000c8c0,0xc40000bc4da300000000,0x808600000001786c6,0x194d000000008760,0x157cbd470000642,0xc6761712d2b84fb22f00,0x2118c98e47432db40003,0x58cb0000000000000000,0xadd41020835468800023,0x80000000d43a2a6c0007,0xbe0000000560a993da73,0x4b400000000000000080],#[0xfc7b8e810001b6cc0000,0xe7aeec0000000b3f6c09,0x2d5aba96b6cab2eb99ee,0x1dcd893d476aea87d404,0xe400038f200000000000,0x109c7ba0000c0316afb6,0x365ae31a833f8f090de5,0xd4b90608780008b32851,0xb820000ea53f1e6aafa1,0x9a32976108e3a52978e,0xea3e400041970000000,0xb780000000022621031b,0x399bb73c14acc3afda88,0x7600000001de99352000,0x53,0xaeb8000ff5c0001c280,0x4ba23400019553125abc,0xda5914c283d5047bb951,0xe41733da,0x0,0xd1e0000057f800000,0x78bd0000d4a543d40000,0x16000316a7bbeb0a87ec,0x291a51c0000ebc0000b5,0x23d2000090c40e16,0x310348a70000000,0x65e106d441324bc20400,0x66f80df5d70a,0x1925a055a31c957e0000,0xa2b9e0799d58000a0,0xc0000000828d58a30420,0xdcced0000462733f3f82],#[0x9faaf648f8526532a807,0x41af432b076447bb4306,0x36000194839a0237348b,0x3b778a5bae3524f87f1d,0xb1ce5b77e0b80002e0a3,0x74a71c1608000d5eac8c,0x91234af86985ab0000f0,0x89ba6a5a82ca1e70c4a4,0x7e893bc8bdf1fe2472bb,0x371d3364bd2de6e1e66d,0xb8db1692f73e000084d6,0x754c200,0x10a496075a8a00,0x403a8000215cba5f5cb8,0xad9b573aa6ba93d9f28,0x3a20000606c00077b326,0x48354995c2c680140ec8,0x3a92fc00000000000667,0x13bc71631a8000328458,0x2e262d6201e80005,0x5a6f5cce000,0xe11623c0001858800000,0x426a0002e08e,0x8effd8900001090000,0x877487200000004aab00,0xcb879d53ad3c32700000,0xb403cbfdf532746ede53,0x240cab426355bf4a0050,0xb1b280dff2d6e20315c,0x5bb25b1f34d8a2068e08,0xcfc8b8ee088796000023,0x814f2a14628ba6a0d946],#[0xa0001bbe8c6464aa672,0x4d0fc428000cd,0x80005aea81b80f3bceb0,0x7bf73a0b580009b020f2,0x9dd000043059bd000057,0x750856a8033077f00004,0x90c6dfce31952d18667b,0x71e7a540ce9000026,0x49400000001ecec9718,0x14b7e5288000542c000,0xe774e6200000004a6200,0x38108000901200006d06,0x18b618000000063b0000,0xe3d42c5506981e0000c5,0x1c167c4300017a2c0007,0x5f7e904672a60da82244,0xd2696a5c0005bc88f,0x28515310274f82400000,0x12bb8013416a000,0x9f0bf302735935800000,0xf89c8e140005,0x17318c0000f8f53e2000,0x1860d65f69b8b0,0x374e0,0x2200024860000d688000,0x2b16bbc472,0x19548000940739f91658,0xf60003208444ab21a000,0x1628000043c090091,0x22ee0000c14800af4340,0x16e8000047bf0000000,0x93e00008ca4000000000],#[0xa5ab812917a188678c22,0x4b40ba9800044d38a6,0x7e36cf7f97800000,0xcd40d2cd73e8000249f8,0x85b31309243ae0001a61,0xf7e32c3c964000384db4,0xe9f492858bfaf2f44faf,0xdc0000914ea68b7aa5cf,0xd03ab0126cfd0f000040,0x400025ee93d240e1b12c,0x1ef2d27948abc3b,0x132d221c000000000,0x2242d8f4f89600036b20,0xb200025c200007d1a000,0xa8d00013fb48934be56c,0x49ff000000000006,0xcc000354780000000000,0x11d66d6df2,0xb93d921fb44f8a7c0000,0x58fef00003ccf0001b8b,0xf3cde42cdaa2c771,0x3cbc00002192c5f210d8,0x134aec0002fd80000000,0x75180003e3447,0x3ae5510bc229e0c00000,0x5400014724c3711f4000,0xbe30001ab1a4ce014e80,0x2873e2e5000143d8e7c7,0xfe0002b0db0caeef2000,0xafa362c40b2bfbb926c,0x17538ba500000000e1ff,0xc6000000066440000610],#[0xf8800000000a4a5c30c6,0xedc1d23aef7418ded8f6,0x6b92acc16cfbbc41443f,0x59126320e31c0a412b46,0x11d40000e44d40580001,0x3800000a00000811d82c,0xa4c00014914000601c32,0x400073600000ad779ebb,0x820000000000022618ab,0xf40000094481b980005d,0x22f98000cc9600000005,0x1e432ded91ae000,0x129b0000000000,0x62184540,0x56e9d5b47000018ac000,0x9c4321c19f244988d534,0x2880a0598618c2fc206d,0x61a984419d77b1495a26,0x9cb15922001faefb3,0xb34a00000000,0xa26e000,0x1a8a0002832000000,0x53440000da28]]
def g251D11 := limbs80 #[#[0x10f794fdd53fb98bed62,0xfd50ff503fd30ff483fd,0x87fd51ff4c7fd21ff583,0xf54ffd62ff54bfd32ff5,0x8423023000ff597fd63f,0xad133218394630a30f81,0x22b4087a4e71af3105c4,0x1610360e060018899525,0x85840d8381800602200a,0x10514180e120a00147c6,0x1208220c000490384802,0x2868584001420461a16,0x6140e120800203470712,0x90715868583828104002,0x241c661a120a060c1400,0x51d85848281830d0006,0x584800d14161a1612005,0x6a1a120a00220c140498,0xc2062103858482801f1c,0x68480140c1a161200342,0x1a16120e060034089078,0x868482800305080d1c80,0xd8305062216120a00203,0x848281800]]
set_option maxRecDepth 16000 in
def g251H11 := limbs80 #[#[0x3641100010102020020,0x2010142201000c006211,0x50510313111300010000,0x7cfe2380dc000400,0x0,0x1a000000000000006400,0x6073a619,0x8be0000dafdc4000aa60,0x21360000007052,0xc0000000000000001370,0x90000000000000704e0e,0xd878000a79a5,0x9a0004dd400000000000,0x2cc00000070d1888eff0,0x1,0x70260724ae,0x66470000000000000000,0x154,0x7000000000000014b800,0x61db0b800000000030,0x1896cc400d0,0x197bc720004bb8000,0xa53a845c3a10561144ae,0x426000000048558055c,0xebcce00058f892001000,0x980000000001e1e00050,0xc6634980000001,0x2814300000c93c6823a8,0x1f870000000000,0x24fa000000,0x380014a6ea259d800000,0x2da6c0003690743e01dd],#[0xa50e6800000074139c30,0x1824000c,0x65c95100000000000000,0x1a30,0x4a898000000000f48800,0x51300000018b,0x1e2e00000,0x24000000079000000,0x0,0x8000000000000660b848,0x65ec000b7e2ce,0x22c4001818650000000,0x31e9ce9c1800000,0x3f800000000000000000,0x1938000000000e,0x0,0xc56308000000170b,0x3e13ad3689247800,0x20000000000000000000,0x4b180000003a59ba02,0xc01588c0000,0xd13800000126d0178,0xe4380007170001548000,0x5490000001483f26,0x35e9229e9400fe23000,0x22000434b5b400188600,0x1500000360008a000002,0x633,0xbbe800315114630e8000,0x0,0x74a800000002d000000,0x764000000000000000],#[0x7131bba70886a0000000,0xc8452e49efae80035210,0xb19607f8a000000023c6,0x202e0000000000001,0x1a1a00035b,0x322c000000000000000,0x9dab2537896c00000000,0x52000000138800015928,0xb10001436daa76,0x6ac30956960001154,0xc00007e0003a84000000,0x185a00039e,0xb34ee000605290488800,0x66,0x8c8ce400000000028b00,0xc2b0006,0x151c0002abeb5f0d7302,0x7a362420000000000000,0x1154000000481a89,0x0,0x3c8800019c0001a640,0x1eba00000000000000,0x68c6c840000006984,0xe4f8000000000,0x9e90d6f25c54800,0xe582ac00038d347c00,0x43980,0x20310e00000029500000,0x8b7152984c001411f5aa,0x0,0x9968000000000000,0x9000207927c000000000],#[0xb419880000000e4f22,0x408400000000000000,0x0,0x18a7a360000000000,0xc00002c000600dc666af,0x18230000000000000181,0xb4001e7900070fc00025,0x50000202c00199900012,0xc2ea8640010,0xc350,0x2194000]]
def g251D12 (j : Nat) := if j=0 then 0x305080c101003ff else 0
def g251H12 := limbs80 #[#[0xc280000000704000002,0x3440,0xa600000000000000,0x1c00020e000000000,0x581c0000000000000000,0x3e,0x38fd18000000,0x2400000214000000,0x30000000000000000000,0x35,0x3c800000000000000,0x0,0x7a40030c00000000000,0xb4800000000010b0000,0x893390c13c9000cd0000,0x42000000012]]
def g251L : Nat → Packing
  | 5 => (11,7,7,0,0,7,0,g251D5)
  | 6 => (183,6,7,0,0,12,0,g251D6)
  | 7 => (1077,5,7,0,0,16,0,g251D7)
  | 8 => (1671,4,7,0,0,17,0,g251D8)
  | 9 => (1011,3,7,0,0,17,0,g251D9)
  | 10 => (187,2,7,0,0,14,0,g251D10)
  | 11 => (20,1,7,0,0,11,0,g251D11)
  | 12 => (1,0,7,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 4 43 4 9 4 1 g251H6
  | 7 => lookupWord 63 317 7 13 8 1 g251H7
  | 8 => lookupWord 359 1973 7 16 11 1 g251H8
  | 9 => lookupWord 555 2741 8 16 11 1 g251H9
  | 10 => lookupWord 343 2203 6 15 10 1 g251H10
  | 11 => lookupWord 63 641 4 13 8 1 g251H11
  | 12 => lookupWord 6 127 1 10 5 1 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P5_0 : block g251 5 0 11=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B5 : block g251 5 0 11=true := g251P5_0
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_0 : block g251 6 0 4=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_4 : block g251 6 4 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P6_100 : block g251 6 100 83=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 183=true := (@block_merge g251 6 0 4 179 g251P6_0 (@block_merge g251 6 4 96 83 g251P6_4 g251P6_100))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_0 : block g251 7 0 2=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_2 : block g251 7 2 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_98 : block g251 7 98 36=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_134 : block g251 7 134 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_230 : block g251 7 230 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_326 : block g251 7 326 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_422 : block g251 7 422 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_518 : block g251 7 518 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_614 : block g251 7 614 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_710 : block g251 7 710 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_806 : block g251 7 806 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_902 : block g251 7 902 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_998 : block g251 7 998 79=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 1077=true := (@block_merge g251 7 0 422 655 (@block_merge g251 7 0 134 288 (@block_merge g251 7 0 2 132 g251P7_0 (@block_merge g251 7 2 96 36 g251P7_2 g251P7_98)) (@block_merge g251 7 134 96 192 g251P7_134 (@block_merge g251 7 230 96 96 g251P7_230 g251P7_326))) (@block_merge g251 7 422 288 367 (@block_merge g251 7 422 96 192 g251P7_422 (@block_merge g251 7 518 96 96 g251P7_518 g251P7_614)) (@block_merge g251 7 710 192 175 (@block_merge g251 7 710 96 96 g251P7_710 g251P7_806) (@block_merge g251 7 902 96 79 g251P7_902 g251P7_998))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_96 : block g251 8 96 95=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_191 : block g251 8 191 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_287 : block g251 8 287 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_383 : block g251 8 383 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_479 : block g251 8 479 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_575 : block g251 8 575 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_671 : block g251 8 671 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_767 : block g251 8 767 61=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_828 : block g251 8 828 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_924 : block g251 8 924 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1020 : block g251 8 1020 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1116 : block g251 8 1116 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1212 : block g251 8 1212 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1308 : block g251 8 1308 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1404 : block g251 8 1404 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1500 : block g251 8 1500 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1596 : block g251 8 1596 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 1671=true := (@block_merge g251 8 0 828 843 (@block_merge g251 8 0 383 445 (@block_merge g251 8 0 191 192 (@block_merge g251 8 0 96 95 g251P8_0 g251P8_96) (@block_merge g251 8 191 96 96 g251P8_191 g251P8_287)) (@block_merge g251 8 383 192 253 (@block_merge g251 8 383 96 96 g251P8_383 g251P8_479) (@block_merge g251 8 575 96 157 g251P8_575 (@block_merge g251 8 671 96 61 g251P8_671 g251P8_767)))) (@block_merge g251 8 828 384 459 (@block_merge g251 8 828 192 192 (@block_merge g251 8 828 96 96 g251P8_828 g251P8_924) (@block_merge g251 8 1020 96 96 g251P8_1020 g251P8_1116)) (@block_merge g251 8 1212 192 267 (@block_merge g251 8 1212 96 96 g251P8_1212 g251P8_1308) (@block_merge g251 8 1404 96 171 g251P8_1404 (@block_merge g251 8 1500 96 75 g251P8_1500 g251P8_1596)))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_0 : block g251 9 0 1=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_1 : block g251 9 1 27=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_28 : block g251 9 28 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_124 : block g251 9 124 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_220 : block g251 9 220 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_316 : block g251 9 316 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_412 : block g251 9 412 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_508 : block g251 9 508 25=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_533 : block g251 9 533 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_629 : block g251 9 629 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_725 : block g251 9 725 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_821 : block g251 9 821 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_917 : block g251 9 917 22=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_939 : block g251 9 939 72=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 1011=true := (@block_merge g251 9 0 508 503 (@block_merge g251 9 0 124 384 (@block_merge g251 9 0 1 123 g251P9_0 (@block_merge g251 9 1 27 96 g251P9_1 g251P9_28)) (@block_merge g251 9 124 192 192 (@block_merge g251 9 124 96 96 g251P9_124 g251P9_220) (@block_merge g251 9 316 96 96 g251P9_316 g251P9_412))) (@block_merge g251 9 508 217 286 (@block_merge g251 9 508 25 192 g251P9_508 (@block_merge g251 9 533 96 96 g251P9_533 g251P9_629)) (@block_merge g251 9 725 192 94 (@block_merge g251 9 725 96 96 g251P9_725 g251P9_821) (@block_merge g251 9 917 22 72 g251P9_917 g251P9_939))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_0 : block g251 10 0 9=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_9 : block g251 10 9 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_105 : block g251 10 105 7=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P10_112 : block g251 10 112 75=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 187=true := (@block_merge g251 10 0 105 82 (@block_merge g251 10 0 9 96 g251P10_0 g251P10_9) (@block_merge g251 10 105 7 75 g251P10_105 g251P10_112))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_0 : block g251 11 0 4=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=0)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P11_4 : block g251 11 4 16=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B11 : block g251 11 0 20=true := (@block_merge g251 11 0 4 16 g251P11_0 g251P11_4)
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
  · exact g251B5
  · exact g251B6
  · exact g251B7
  · exact g251B8
  · exact g251B9
  · exact g251B10
  · exact g251B11
  · exact g251B12
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251G : graphValid g251 (boundsBefore K249) = true := by decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem low251 : Lower true (varsX 251) (graphGoal 251) 13 := lower_forest (g:=g251) (i:=0) (hints:=65603) (before_sound K249 V249) g251G g251T (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
def K251 := extendKnown K249 13 [(251,[])]
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem V251 : Known true K251 := extend_ok (m:=251) V249 low251 (by decide +kernel)
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g255R : Impossible true graph 13 sevenInputs.toFinset := by
  change Impossible true (graphGoal 255) 13 sevenInputs.toFinset
  exact cut_root (m:=255) (before_sound K251 V251) (4, 0, 251, 0, 13) (by decide +kernel) (by decide +kernel)

end PEqualNP.Outside.L_meta_51786

open PEqualNP.Outside.L_meta_51786 in
theorem PEqualNP.Outside.L_meta_51786 : ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 8 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = decide (∃ i < ([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).length / 2, (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 3, 1, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 2, 6, 3, 6, 5, 6, 0, 7, 1, 7, 2, 7, 4, 7, 5, 7, 6, 7] : List ℕ).getD (2 * i + 1) 0) false = true) := by
  intro gates o fit _ correct
  exact replaceShort g255R gates o fit correct
