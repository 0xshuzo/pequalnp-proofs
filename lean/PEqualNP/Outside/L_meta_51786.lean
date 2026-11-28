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


structure QuotientSpec where
  a : Nat
  b : Nat
  rev : Bool
  z : Nat
  o : Nat
  extra : Nat
  fl : Nat
  sw : List Nat
  single : Nat

def quotSpec : Nat → QuotientSpec
  | 0 => ⟨0,7,true,8,0,0,1,[80, 97, 116],3⟩
  | 1 => ⟨0,7,true,40,0,0,1,[96, 80, 81, 116],1⟩
  | 2 => ⟨0,7,true,72,0,0,1,[80, 97, 116],1⟩
  | 3 => ⟨1,3,true,144,0,0,2,[96, 80, 81, 117],1⟩
  | 4 => ⟨1,6,true,16,0,0,2,[112, 32, 81, 99, 82],1⟩
  | 5 => ⟨1,6,true,17,0,0,2,[112, 81, 99, 80],1⟩
  | 6 => ⟨1,6,true,24,0,0,2,[112, 80, 97],1⟩
  | 7 => ⟨1,6,true,48,0,0,2,[112, 80, 97, 83],1⟩
  | 8 => ⟨1,6,true,144,0,0,2,[32, 81, 99, 117],0⟩
  | 9 => ⟨3,4,false,33,0,0,0,[33, 83],0⟩
  | 10 => ⟨3,7,false,64,0,0,0,[16, 33, 115, 84],0⟩
  | 11 => ⟨4,5,false,9,0,0,0,[33, 84],0⟩
  | 12 => ⟨5,7,true,8,0,0,32,[97, 81, 84, 117],3⟩
  | 13 => ⟨5,7,true,9,0,0,32,[96, 81, 64, 117],1⟩
  | 14 => ⟨5,7,true,72,0,0,32,[81, 100, 117],1⟩
  | _ => ⟨0,0,false,0,0,0,0,[],0⟩

def quotDom (b : QuotientSpec) : Sig :=
  let d := (inputs.getD b.a zero) ^^^ (inputs.getD b.b zero)
  subcube b.z b.o &&& (if b.rev then d else ~~~d)

def quotSteps (b : QuotientSpec) : List Move :=
  let a := inputs.getD b.a zero
  let dest := inputs.getD b.b zero
  let want := if b.rev then ~~~a else a
  let move : Move := (want &&& ~~~dest, dest &&& ~~~want, Fin.ofNat 512 (1 <<< b.b))
  let flips := (List.range 9).filterMap fun i =>
    let w := inputs.getD i zero
    if b.fl.testBit i then some ((~~~w, w, Fin.ofNat 512 (1 <<< i)) : Move) else none
  b.sw.map swapRows ++ flips ++ fixRows (b.z ||| b.extra) b.o ++ [move]

def phaseFree (roots : List Sig) (w : Sig) := freeWord roots w || roots.contains (neg w)

theorem phaseFree_ok {xs w} (h : phaseFree xs w = true) :
    Available true (xs.map observe) (observe w) := by
  simp only [phaseFree,Bool.or_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  rcases h with h | h
  · exact freeWord_ok h
  · refine Or.inr (Or.inr ⟨rfl, ?_⟩)
    rw [← obs_neg]
    exact List.mem_map_of_mem h

def signedMap (ms : List Move) (raw : List Sig) (base : List Sig) :=
  raw.all (fun a => phaseFree base (movedWord ms a))

theorem signedSlice {ms raw T base d L} (h : signedMap ms raw base = true)
    (all : movedWord ms d = one) (pr : proper (movedWord ms T))
    (low : Lower true base (movedWord ms T) L) : Slice true raw T d L := by
  have he : restrictRows (movedRow ms) (observe T) = observe (movedWord ms T) := by
    rw [moved_eq_rename, observe_rename]
  refine ⟨movedRow ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [← bit_moved, all, bit_one]
  · intro a ha
    rw [← observe_rename, ← moved_eq_rename]
    exact phaseFree_ok (List.all_eq_true.mp h a ha)
  · rw [he]
    exact observe_proper pr
  · rw [he]
    exact low

def quotientCheck (u : Bool) (raw : List Sig) (T : Sig) (b : QuotientSpec) (q L P : Nat) : Bool :=
  let ms := quotSteps b
  let G := movedWord ms T
  let bs := varsX (q ||| b.single)
  let xs := supportPairs 0 b.single
  u && signedMap ms raw bs && (movedWord ms (quotDom b) == one) &&
    properB G && properB (graphGoal q) &&
    checkLift (fixRows b.single 0) G bs (varsX q) (graphGoal q) xs &&
    decide (L ≤ P+(xs.map Prod.fst).toFinset.card)

theorem quotientSound {u raw T b q L P}
    (low : Lower u (varsX q) (graphGoal q) P)
    (ok : quotientCheck u raw T b q L P = true) : Slice u raw T (quotDom b) L := by
  simp only [quotientCheck,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at ok
  obtain ⟨⟨⟨⟨⟨⟨hu,hm⟩,hd⟩,pg⟩,pq⟩,lift⟩,hle⟩ := ok
  subst u
  apply signedSlice hm hd (proper_of _ pg)
  intro p bank reach hit
  exact hle.trans (lift_ok lift (proper_of _ pg) (proper_of _ pq) low p bank reach hit)

def fieldDomain (z o : Nat) : Sig :=
  if o < 512 then subcube z o else quotDom (quotSpec (o-512))

def fieldCheck (u : Bool) (m : Nat) (c : ColumnInfo) (prior : Nat → Nat) : Bool :=
  if c.2.1 < 512 then colCheck m c prior else
    let q := c.2.2.1
    quotientCheck u (varsX (rawMask m c)) (chartGoal m) (quotSpec (c.2.1-512)) q c.2.2.2.2 (prior q)

theorem fieldSound {u m} (c : ColumnInfo) (prior : Nat → Nat)
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : fieldCheck u m c prior = true) :
    Slice u (varsX (rawMask m c)) (chartGoal m) (fieldDomain c.1 c.2.1) c.2.2.2.2 := by
  by_cases h : c.2.1 < 512
  · simpa only [fieldDomain, h, if_true] using
      col_sound c prior low (by simpa only [fieldCheck, h, if_true] using ok)
  · simpa only [fieldDomain, h, if_false] using
      (quotientSound (low c.2.2.1) (by simpa only [fieldCheck, h, if_false] using ok) :
        Slice u (varsX (rawMask m c)) (chartGoal m) (quotDom (quotSpec (c.2.1-512))) c.2.2.2.2)

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
    materialize g.mode (varsX (rawMask g.mask ci)) (chosenSteps bank ops paid d) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2

theorem buildRule_sound (g : Forest)
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2)
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
    (cols : ∀ ci ∈ g.cols, Slice g.mode (varsX (rawMask g.mask ci)) (targetOf g) (fieldDomain ci.1 ci.2.1) ci.2.2.2.2)
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
  g.cols.all (fun c => fieldCheck g.mode g.mask c prior) &&
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
      (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact block_at (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply nodeVerified_sound g _ i (chart_pairs geometry.1.1.1 geometry.1.1.2)
      (fun x hx => fieldSound _ prior lower (geometry.1.2 x hx)) geometry.2
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
    (ok : fieldCheck u m ci prior = true)
    (cut : (decide ws.Nodup && poolCut u (fieldDomain ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (rawMask m ci)) ws)=true) :
    Impossible u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact poolCut_sound (fieldSound ci prior low ok) [] rfl cut.1 cut.2

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
def K41 := extendKnown [] 4 [(41,[]),(73,[101]),(97,[83,67,100]),(100,[32,16,83,67,100]),(104,[48,16,33,82,66,100]),(146,[16,67,117,101]),(161,[83,67,116,100]),(193,[99,67,117]),(194,[16,99,67,117]),(224,[80,16,33,99,66,116])]
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
def K179 := extendKnown K173 8 [(179,[]),(182,[16,32,84])]
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
def g251C : List ColumnInfo := [(1,0,250,0,10),(2,0,249,0,10),(8,0,243,0,10),(16,0,235,0,10),(32,0,219,0,10),(64,0,187,0,10),(128,0,123,0,10),(0,16,105,130,9),(2,16,105,128,8),(10,0,241,0,8),(18,0,233,0,8),(24,0,227,0,8),(72,0,179,0,8),(128,16,105,2,8),(144,0,107,0,8),(0,2,41,208,7),(0,8,146,97,7),(3,0,248,0,7),(9,0,242,0,7),(17,0,234,0,7),(26,0,225,0,7),(33,0,218,0,7),(34,0,217,0,7),(40,0,211,0,7),(48,0,203,0,7),(65,0,186,0,7),(66,0,185,0,7),(80,0,171,0,7),(96,0,155,0,7),(129,0,122,0,7),(130,0,105,0,7),(130,16,105,0,7),(136,0,115,0,7),(146,0,105,0,7),(160,0,91,0,7),(1,8,146,96,6),(1,16,104,130,6),(8,16,97,130,6),(16,2,41,192,6),(32,8,146,65,6),(32,16,73,130,6),(64,2,41,144,6),(64,8,146,33,6),(64,16,41,130,6),(128,2,41,80,6),(192,0,59,0,6),(11,0,240,0,5),(33,8,146,64,5),(41,0,210,0,5),(49,0,202,0,5),(65,8,146,32,5),(73,0,178,0,5),(74,0,177,0,5),(88,0,163,0,5),(96,8,146,1,5),(104,0,147,0,5),(152,0,99,0,5),(192,2,41,16,5),(35,0,216,0,4),(57,0,194,0,4),(67,0,184,0,4),(97,0,146,0,4),(97,8,146,0,4),(98,0,153,0,4),(105,0,146,0,4),(131,0,104,0,4),(131,16,104,0,4),(137,0,114,0,4),(138,0,97,0,4),(138,16,97,0,4),(161,0,90,0,4),(162,0,73,0,4),(162,16,73,0,4),(168,0,83,0,4),(194,0,41,0,4),(194,16,41,0,4),(152,64,0,35,2),(0,512,224,3,6),(0,513,224,1,5),(0,514,224,1,5),(0,515,224,1,5),(0,516,228,1,8),(0,517,224,1,5),(0,518,224,1,5),(0,519,224,1,5),(0,520,228,0,7),(0,521,228,0,7),(0,522,182,0,8),(0,523,228,0,7),(0,524,224,3,6),(0,525,224,1,5),(0,526,224,1,5)]
def g251A : List (List Nat) := [[],[80]]
def g251D5 := limbs80 #[#[0xc29b56d1a62497558140,0x48b8ec1a75955358940c,0x9c628ba065f8159540d8,0xb46c1a62497559540a0e,0x46c1a6209815d540cc29,0x6c1a6209815d540c8a9b,0xc5a6209815d540c869b5,0x1a0658825d540c865b56,0xa1658825d540e429a569,0x2479848c180c469a56c3,0x358604000000003ee]]
set_option maxRecDepth 16000 in
def g251D6 := limbs80 #[#[0x81b82691a05955358940,0x550307454740cbacab12,0x2eaa064a9a4681962097,0x6154110c8d34ad032c41,0xa2c4a8221b98597a2611,0x95458950443d15da30ca,0xc36e8b12a0886c68b769,0xd5a46196254110d1d774,0x4bb2cbc9308a822169ae,0xa29856115458960443a3,0xb8736b4bac8aa2c0887,0xa2151e6d697659545811,0x61443b90aa2a5c8284b0,0x8a809076316555390509,0x96150120fc42caa12c2a,0xa12c2a0241d625d79350,0x4d4258540483ac5baf26,0xbc9a84b0a8090738985e,0x6d7935096150120e7170,0x14c2acaa12c2a02415e2,0x770954e4d5258540483d,0x20e6930bc9aa4b0a8090,0x8241d465d554e4d61501,0x550483b84aa726a12c2a,0xb0aa0906749a5e4d4258,0x496154120ea92e9c9aa4,0x6a92c2a8241d52dd3935,0x55393585504839a5c272,0x68d3acab0aa290751974,0x3ec9a75538358520b86f,0xdfda35343f02b2a4127,0x6e3165e918158550502],#[0x140ea32a9c9ee4b0aa0a,0xa8281cc655393e096154,0x8950502f18da742b2ac2,0x8b12a0a07c2bb15d9545,0x5956254140f45762c32a,0x42b2ac4a8281b8a691a1,0x4e856558950503714d27,0x369cbacaa8ac0a05e29b,0x2aec9755917158140ac7,0x3a1dcaaeab22e2b02817,0xa05e1bb469d6554d6050,0x8140bc3369d3acaa9ac0,0x8b0281b2a289a15d5645,0x59560503655d1342baac,0xeab2ac0a06c68a268575,0x15d56558140d8d744d0a,0x124c8aeab028170eed1a,0xb4698925d560502a74db,0xd36ad3124baac0a06ca9,0xb8c691a05956154540d8,0x2d38d870eb2ac2a8a81,0x2a05c67b269d65585515,0x54540dc5348d02cab12a,0x6b0a8161e6c3875d965,0x559561502c66db144baf,0xaeab2ac2a05c73b06857,0xa15d56558540d8c944d0,0xb124c8aeab0a81b19e89,0x9a46816554d62502a72d,0xc1768d02caa9ac4a07e0,0x1f12ec1a75955358940f,0x503c265c34eb2aa6b128],#[0xc4a056a9b4e459059562,0x558940d8d74bd032eb2a,0xacab1281a3a2a3a065d6,0x97595625034365474acb,0xa320b2aa6a060eca8e85,0xba065d6554d40ec32ecc,0xbb2eac2300b2a81b5228,0xe8a2e8197e0565503c1c,0xa1db6c5132fc0acaa061,0x8151b6d8926457559540,0x5503634d834c492eab2a,0xaeaa063aba4e8196e097,0x815d540c1db4dcb104c0,0x1302baa81a3a6c1a6209,0x88260575503472d8b4c4,0xd3104c0aeaa0686db569,0x91a0658825d540c1dd72,0x4d2b40cb104baa8196a6,0x4a9a468196209755032b,0xe8d34ad032c412eaa07,0xa81533ecda1658825d54,0x75503236d2b42cb104ba,0x12eaa054e9b0e8596209,0x8825d540c8db4bd0b2c4,0xcb104baa8151b6d7a165,0x8d9620975502a74d8746,0x3d030dc12eaa0546db5e,0xe93a065b825d540c3d75,0xb5d2f40cb704baa8196a,0x6c6965e89745c5605432,0x50d4d2cbd12e9c0ac0a8,0xaa1b19597a25d171585],#[0x562542739d8349c8acab,0xbb2c4a84e6bb06939159,0x457658950c95b49ca722,0xcb704ba2a133aec1a4e,0x693915d5625831b5d2f4,0x6b54722b2ae0b146ebb0,0x2ec1946416554d6294db,0xb25d8328c82caa9ac579,0x62ada4e53816016558b,0x71e8384608940ce1500,0x2b05149f93924c44c869,0x774de9b7348678c596b,0x9d10a1b42a83cfe1f63e,0x28a4b48a8fd1ca3345a8,0x30a5d4b5d4ea7d4d495d,0x469cd21a132f652c5988,0xb2f4de03a0700db5ad35,0xde12411817015ffbdf7,0x26b4d097b2764546a895,0xd534a5d46e8acf59df37,0xccb7369ac9d8dadb5369,0xd25a334364cc257cae95,0xbc2b7bee4da3afb55ea5,0x87adf55e9fcf394f23e3,0x5c006f4de4fc077aee9d,0x6141016989cc4789f782,0xdc300f43c12ee1807a1f,0xe4151482c11ec185825,0x418200032904c0a08000,0x14080d80ac0017a0c1f,0xec183a02d0004028081,0x1810100],#[0x151484f8107b06080000,0x520812a45318dbc188f8,0x8050f04000c237810a4,0x25430230f04000000c2a,0x1c001b4378002b437800,0xa4302000060b0e001000,0x8e0002d0950c0d2181,0x837153080471504e0870,0x3049800405c001000a4f,0x69c104a8604003200081,0x8606b0c0815823800568,0xb860bd0bb86080ac3035,0x430e186770de8513e09,0x61c04000c38615dc37c1,0x60813c38278704c2a080,0xc16430200003d0407a0b,0x8e0010003800200007a0,0x5a0]]
def g251H6 := limbs80 #[#[0x498e000028003,0x80000000064801d10072,0x69c000030,0x34000000000158,0x20800040008f6a]]
set_option maxRecDepth 16000 in
def g251D7 := limbs80 #[#[0x50503c29765516254140,0xd16154110e8a61954589,0xa5915458950443c7165d,0x443a69865516254110f8,0x6254110b9a6995458950,0x1b7458950443c6965dd1,0x3479965977254110e3a6,0x54110e8e619645515044,0x76595504434799659774,0xe3745895158110b1ee91,0x110db8e516254560443c,0x54560443c7165dd15158,0xa5dd16258110d9c59794,0xd1e65565dd160442ce9,0x95144375153e41425451,0xe116254510f195977458,0x1d65965dc951443a6565,0x1443475965977454510d,0x96554510e1d5d965e115,0x65565dd161442c77a45d,0x43b295454b8050910d1d,0x150120d1b65565dd1624,0xd4258540483f09535095,0xf096554d4250120de2e4,0x120eca6156550940483,0x454d40483b2985591525,0x9855956450120f865956,0x20dd2e4d5258550483a3,0x4d62482d3ba459774541,0x4a5d6458920f13a9d655,0xb1b6969759562482cada,0x54482d1fa465d6554d20],#[0x4d615414087b69b9261d,0xa695645895050371954e,0x503e29a45956254140f8,0x6254140f1ae957658950,0x5954dc950503aaba4619,0x3479965977254140d4e6,0x54140cce65954e095050,0x64549605032b99659382,0xa9a4e456258140f0e5d5,0x140baae918558960502e,0x59160503e19a45955358,0xa25d56458140baae8975,0xf2ae897559160503ca8,0x560503c68a25d5655814,0x2497558140f1ae897559,0x73e8975e0d61502ce9a6,0x2503e49a05955358940a,0x16558940f1369d6554d6,0xe9597595625036a99464,0x34eba065d6558940b1b,0x558940d1be9597595625,0x1955d9625030eca865d6,0x85d8659553dc940b3ae8,0x4d40dc66519059553503,0x759553502d4fa265d655,0xda62497559540b1769a9,0x40c7a24b9061d65502c6,0x5755028eda6209815d5,0x618825d54087baa4826,0x87bea586209755029eba,0x755034e9a0658825d540,0x937158150d1b69596209],#[0xe59594dc5605434b9945,0x543339945538158150d1,0x6258150c9e59594e0560,0x97915896054366995e45,0x3e29845516258150b9a6,0x58150b9ae95845896054,0x9655160542679a6e4954,0x3ba46595458150b8ee91,0x150b8ee9195591605436,0x5937154366965e497458,0xa0e456254950e0f59584,0xc9e59590e0562542769,0x56254366965643815895,0x5d95458950cda61590e0,0xbe917655162543c6ba0,0x2543669956416458950f,0xd6458950b8be91955916,0x6539059562542cafa465,0x42e69a4e416558950d9a,0x658950b9ae8194595625,0x1945d962542ce9a4e417,0xc6fa56517658950b3ae8,0x4560c9e59590e0564542,0xe1151582ae9a0e11625,0xba06538158960c9e5959,0x609ba693905d5625826e,0x955358365992e416554d,0x4e416554d60d96653905,0xb96e819259553582e59a,0x70546e5ba06516554d60,0x1162dc151e1d59584587,0xbe55656037158b86d656],#[0x58b64d946416554d62c9,0x6554d62d93e519059553,0x93905955358ae4fa4641,0x2a6da5a5f8059562b936,0x54110fd8549425855044,0x4258550443f315450961,0x71a55096154110f9c595,0x110f5cdd15258550442f,0x58550443e71656096154,0xa26116154110bdce8954,0xf9c5958458550442fe3,0x950443d6976549425411,0x5514254110f5add95250,0x4edd95450950443d3976,0x443b39865514254110f,0x54254110f1e5d9655095,0xdd995509504435797665,0x42d79a6dd15254110d5e,0x254110b5ee9176549504,0x18658950443e69a55916,0xaeba46196254110eba69,0x4110eba2a58658950443,0x255150443c7976595825,0xb76e495454110d5e5db9,0x109de69b925515044357,0x5150443e398659154541,0x46195454110bcee91865,0xd5e29d9655150443b3ba,0x50443e39656116454110,0x196454110eae61984591,0xee959859150443abba46,0x442779a5e6164541109d],#[0x745411097eea586dd150,0x9792611504431fba961b,0x35e976e498454110dda5,0x54110d7addb926115044,0x92611504433e986e4984,0x797659584541109fa69b,0x110aeee919261950443c,0x61950442b7ba56498654,0xa56518654110afae8994,0xfac5918250560442b7b,0x560442fb3a4609415811,0x5895158110f9c5954254,0x9c5958254560443ee184,0x443e71656115158110f,0x94258110fca551525096,0x59554509604436eb9858,0x43e39645515258110f8e,0x2581109eee9198549604,0x55458960443ea9845516,0xee9a85516258110f9a61,0x8110eba6158458960442,0x558960442eeba5611625,0x9745918258110bbae918,0x10daee516460960443cb,0x9604435bb945d182581,0x6e495458110d9ee55656,0xf8e61564551604426f9a,0x60443cba975915458110,0x115458110f8e59584551,0xea5d6555160443b39856,0x4434fa976595458110f1,0x5458110d3e29d9655160],#[0x899855160442d79a5a5d,0x26f9a6e6154581109fae,0x58110baee91855916044,0x905095144367b9559584,0xf186e414254510ddc597,0x510cfce1b90509514433,0x50961443c75765954254,0x54e414258510df854b90,0xdbc59790509614437b1,0x9614427f1a5e41425851,0x5514258510fc95515250,0xfce819550961443e3565,0x1443c769759554585109,0x38050910b5d696975516,0xe9d65e0142443b396555,0x43d2d765515250910a7e,0x450910f4bdd954549424,0xd9655162443c3d765955,0xc3e875956455110d3b29,0x5110b4f6968759154443,0x761954442c7da6a1d655,0xfa66568755110a5f6968,0x20fe8509615454048257,0x4540483e716558551501,0x65095150120fca595425,0xdeae5942545404837a99,0x40483e39655915150120,0x96150120fe850981585,0xa5d54258540483ea9655,0x483dab755096150120f6,0x6150120eea6154258540,0x614258540483bab85509],#[0x37cb935496150120dea6,0x50120fca551525854048,0x9358540483b698554961,0xd975e4d6150120de6553,0x120d76dd793585404835,0x585404833d985e4d6150,0xa5e4d6150120cf6e1793,0xf8e59554585404827d9,0x540483d3975551615012,0x5098150120e9e6156558,0xeae594260540483ba986,0x483da97558d4250120d,0x54250120eea615635094,0xe858650940482faba159,0x83f295458d5250120bea,0x350120eda61563549404,0x55458d40483f19a45955,0x7b9a4e456550120f4e5d,0x4120fd85498158550482,0x258550483e7165605615,0x9545096154120df2e4d4,0x20f9a5954258550483f2,0x8550482f69a550961541,0x45496154120f5a5d1525,0xedae115258550483d6b7,0x50483769985496154120,0x4d6154120dd655393585,0x6dd393585504835d974e,0x4833db84e4d6154120d7,0x6154120f4e5d15458550,0x977458550483c79655d1,0x3a7965e116154120f1e5],#[0x54120f9ce85655855048,0x5260550483e69a259561,0x6b965498154120eda619,0x120d9ee5965605504837,0x50950483f295458d4254,0x7458d5254120dda65563,0xf5add16354950483d69,0x950483b6b8458d525412,0x6195254120bdae856454,0x9a6856558950482f6ba1,0x483e6ba15956254120f,0x15454120f4e5d15458d5,0x5979159150482f3ba159,0x82779a5e456454120d9e,0x454120f8ee9165591504,0x99159550483d3ba45977,0xc79766456554120dda64,0x4120dda64b9159550483,0x258551483c7976e45655,0x5655d16154520f995954,0x20f1d5977458551483c7,0x8551483a7565e1161545,0x75956154520f99689655,0xf1da9d6558551483c75a,0x51483c6ea75956254520,0xd4258520b4fe9197595,0x3dd783509614839cd75e,0x482bcda5e0d4258520e7,0x5258520ed35538354961,0xd383549614839cd74e0d,0x395d755538358520e73d,0x58520a7769d54e0d6148],#[0x74e0d614831dd955d383,0xdd95dd38358520a77e95,0x520a7769774e0d614831,0xe0d614829dfa45d78358,0xa265d5458520a7769375,0xb2fe9197595614825ef,0x561482c7fa565d655852,0x5915454920b1f6969759,0x3ba5d9159562482f2fa1,0x34834ee97e456558920d,0x77454d20f87e91655915,0xe899755163483d1fa459,0x8363d65e45645512097b,0x5dd120d4f5d791591544,0x187605654825bda1e516,0x9bfa461f8159520a6fe9,0x952087f6a687e0565482,0x1585505029bfa465f815,0x1655c56154140fcc5517,0x40bdce957158550503e7,0x8550503f315460561541,0x56056154140bece91815,0xdd6e4d5258550503e716,0x505035db93dc96154140,0xc96154140f4e55372585,0x6e4f8258550503c7965d,0x503b3954e096154140cf,0x6154140dce65d5458550,0x85655855050373998551,0x3e39a45956154140f9ce,0x54140d9e65d655855050,0x985855050277ba565d61],#[0x397655171541409eee91,0x140ece619545c550503d,0x5c55050373b965517154,0x955917154140f8e59564,0xeae619645c55050373b,0x5505036bb96591715414,0xe557154140f1e5d9655c,0xde69b955c55050357976,0x502d7ba55d971541409,0x18154140f4e5d9546055,0xe595460550503b398655,0x2f39a65518154140dce,0x154140f8e59564605505,0x79460550503ab9865918,0x3b986e518154140dce59,0x41409ee69b9460550503,0x560550503c7976595815,0x9a15916254140d9ee596,0x40f9a6856558950503ea,0x8950503e6ba159562541,0x16196254140f3ae85765,0xf4e55163dc950503aeba,0x50503b395458f8254140,0xd95454140bcee8576551,0xee858655150503d3ba15,0x503b3ba16195454140bc,0x6454140ecee9d8655150,0x199159150503e3965645,0x3e39a15956454140eae6,0x54140f8ee85655915050,0x6559150503e39a759564,0x39866556454140f8ee9d],#[0x140eaee858659150503e,0x59550503abba76196454,0x766456554140dce65191,0xdce6539159550503c79,0x550502f39a4e45655414,0x6516554140f1e5db9159,0x9ee857659550503e3976,0x503c7b975d96554140b,0xd6554140f1ee85765955,0x6939759550502f3ba465,0x2bb9a4e5d8654140bce,0x158140fac59171545605,0x97154560503e71655c55,0xee1626055158140bbce9,0x8140fac5918154560503,0x454560503e7165605515,0x9a45955158140daee5d6,0x40d9ee5d6554560503e3,0xc5605027b9a4e5d51581,0x55917158140f2e591725,0xeaee15645c560503cb97,0x605036bb955917158140,0xd57158140f1e5d5655c5,0xee55755c560502deba25,0x5034fb965d57158140d5,0x8158140faa6916260560,0xd56260560503ce975589,0x3cb9755918158140f3ad,0x58140f2edd5646056050,0x6560560502ebba559181,0xeba16156258140f1e5d5,0x140dae5939160960502e],#[0x54d60503e59a75955358,0xa15d56458140f96e9d65,0xbaee858559160503cb9,0x560502ebba7615645814,0x6456558140dae6519159,0xae6539159560503c7975,0x502eb9a4e456558140d,0x16558140f1e5d7915956,0xe5d7559560503e397565,0x3c79a15d56558140f1e,0x558140baee9197595605,0x9915d560502eb9a4e5d6,0x5eb926457558140d7a24,0x8140b6ee91915d560503,0x761560502cfba6645755,0x565dc961545409ee6939,0x40f9c6816558551503c7,0x8551503a778759561545,0x75956154540d9d65d655,0xf1da9d6558551503c75a,0x51502bf1a0e1d6154540,0x956254540f1d5d9655c5,0xb69d6558951503e69a05,0x50347d965977254540f1,0x6554540dce6519059551,0x83875955150387f875d9,0x2d6fa265d6554540ade6,0x54540b1f69a975955150,0x90e1d515029f9a0e1d76,0x757559571585408fee99,0x540b79e89755c561503c,0x54961503577955d57158],#[0x95e0f7258540e575d783,0xa7769783dc9615031dd,0xd6150347d95597725854,0x5d78358540af3e8975e0,0x73e8975e0d615039cca2,0x15029dfa25d78358540e,0x16558540a7768b75e0d6,0x68391595615036b99464,0x3c7575e456558540bbc,0x558540b3d69f91595615,0x5755956150387d875d56,0xc6ca25d56558540f1d68,0x8540f1be897559561503,0x759561502cefa265d655,0xda5a5d6558540b1fe959,0x40c7b61f925d561502c7,0xd56150297fa561d75585,0x26457558540b7ce81915,0xd79e49915d5615035e49,0x61502ceda62497558540,0x497558540c7b663925d5,0xb6a3925d5615035e5a1e,0x5029fba06617558540c7,0x655c5408fe6839859571,0x1b925d5715021fda7e61,0x25eda6e49755c540c7be,0x58940a5f69b855d57150,0x90595625036e99164165,0xa9946416558940dbae45,0x940faae919059562503e,0x59562503c6d756456558,0xa0e456558940d3b65d91],#[0xf1b5d79159562502ee9,0x5625034ed97e45655894,0x65d6558940b3b69f9159,0x1be959759562503ceba0,0x25038eca865d6558940f,0x57658940d3be85975956,0x657915d9625034ec9864,0x2ceda5e457658940d3b,0x658940b3be85955d9625,0x16554f72502ceda12617,0x1fda8e4565dc940e576a,0x4d40a7be859261b72502,0x59553503f1994641655,0x9766416554d40fc6e919,0x40f17e5d7659553503e5,0x9553502f5ba065d6554d,0x265d6554d40f56e81975,0xf53e899759553503d4ca,0x53502d5da9a5d6554d40,0x497558d40bd668397595,0xe6938160165502ceda62,0x503b39756118059540ae,0x8059540eae5d98460165,0x898760565503c79765d5,0x29efa261f8159540a7be,0x5954087f6a687e056550,0x90e05655033b99464381,0xefa265f8159540ceee91,0x5408fee8197e05655029,0xe05655031fba065f8159,0xa265f8159540c7b28997,0xb1fe85765d5655031ef],#[0x565502d7ba0645755954,0x6457559540d5b249915d,0x1fe99915d56550356f92,0x55035e892e418759540b,0x98759540d5ee579061d6,0xe579261d6550356f9524,0x33bb94e418759540d5b,0x759540c7b24b9161d655,0x190e1d655031ef92e458,0x9efa15db825d540cee65,0xd540cfae8196e0975502,0x605755031efa765b825,0xb94e41815d540e7ae0b9,0x40d5ee5790605755035b,0x5755025f9a6e41815d5,0x6209815d540c7be58826,0xe5be5782605755029eda,0x755031ef96e09815d540,0x18825d540a7b69b82605,0xa68196209755029efa16,0x50356da5658825d540d7,0x825d540d3b6859620975,0x8d96209755034efa1658,0x34efa3658825d540d3b6,0x5d540e7ae8186e097550,0x86e09755029efa161b82,0xefa961b825d540e5be95,0x540d7ae8196e09755031,0xe097550356fa565b825d,0xa6647825d540c7b65991,0xa7be8596e09755029ef,0x9755031efa165b825d54],#[0xe41865d540d6ee539061,0x7ee8182e057650357b95,0x5429efa2617815d940a,0x17158150f1e595725c56,0xe51545c560543e396455,0x4367b965517158150dce,0x158150b9e699545c5605,0x9745c560543cb9745917,0xc79655d17158150b7ae8,0x8150d3ee59745c560543,0x45c560543a7965e11715,0x9656137158150d9e5979,0x50f9a5516260560543c7,0x560543ceb7458981581,0x45518158150f9a695626,0xb9e6995460560543e396,0x60543c7965dd18158150,0xcb8158150cde65152e05,0xee8954e0560543a79655,0x542beba25d38158150ad,0x8258150e9e59574e0560,0x8565e0960543a79a1597,0x3679966455458150e9ee,0x58150f8e69d645516054,0x9655160543e399661154,0x7ba16595458150f8ee91,0x150bcee9198551605436,0x59160543e39955d16458,0xa15977458150baee9197,0xf1ee8565dd160543c79,0x160543a79a1597845815,0x6456558150e9ee8565e1],#[0x9e651915956054367992,0x54367992e456558150d,0x56558150d9e653915956,0x595725c561542e79a4e4,0x43737945517158550f1d,0x158550b79e89745c5615,0x7945c561543c75655d17,0x95f74e0d5258550d9d59,0x8550e5755383dc961543,0x4e0d615431dd94e0f725,0xda2dd38358550af3e897,0x50acfe9187551615429d,0xd16154366d65e4974585,0x15977458550c7b61f925,0xb9d6939159561543c77a,0x61542e7ba06496558550,0x11545c550b9ee8194595,0xf69b845517154393d76e,0x543c3d655d1645c550ac,0x745c550d5b597925d171,0x9b925d1715431ef86e49,0x387f86595745c55097b6,0x589509de683915915254,0x65601625434efa165b72,0x6ba15958058950f9a685,0x950d3bea576e0562543e,0xdd162543c6fa15d95458,0xa15977458950f1b68565,0xd3be8596dd162543c6f,0x56254366d94645655895,0xe456558950d9b6539159,0x9ae819459562542e6da4],#[0x2543ce898e417658950f,0x57658950d3b261915d96,0xe53915d9625434ed94e4,0x42ceda4e457658950d3b,0x658950d3b263915d9625,0x391593725434efa1e517,0x73b94e41765515087f6a,0x9150dcee83945d954543,0x460164543e39655d1805,0x9765d18059150ece6157,0x50e9e5d98560164543cb,0xd164543e3ba059574591,0x5d97459150f0f5d9855,0xb9ee818759564543cbba,0x64542e3fa461d6559150,0xd98559150d8f5db94615,0xee53905d964542e7ba05,0x5433bb94e418759150da,0x8759150cdee579061d64,0x8165e097454333f95e51,0x39eba05db825d150edae,0x5d150a7be8576e097454,0x96e09745433eba065b82,0x7ba06538159550cdbe95,0x950adee9584e01765427,0xe05765433b994e13805d,0xa460b815d9508fee8194,0xa7be8984e05765429bf,0x5765431bd94e13815d95,0x589715456097ee8194e0,0x9d597845c551583ae784,0x1582e7ba06496554560e],#[0x984dc560b9ee81945955,0xe8574e01625829fba064,0x82eeba15d78058960bba,0x4589609bbea575e05625,0x595dd162582cefa15d57,0x6e898e417558960d3be8,0x4d609bb693915d562583,0x4e0565583e5ba0651655,0xba0653815d5609bee819,0x51d9d64990595615463f,0x9561546e77a264165585,0x46416558551d9d651905,0xb9de819259561546e77a,0x6254766d946416558951,0x438159561b9be9190595,0xbdd5915957058a6f7a46,0x58ba6f85645655c162f1,0x655c162f1bdd79159570,0xa3915957058ba6f85e45,0xbe4d946416554d62abba,0x54d62f93691905955358,0x905955358be4fa464165,0xef946058059562f9329d,0x562cbbe53816016558b2,0x6016558aaeda4e058059,0xa06118059562bbae8184,0x2b9be95946016558baeb,0x56558ae6da0dd5815956,0x64381595629bbe9190e0,0x9b68375e056558b66f75,0x554ef5ba06098059553b,0x18059553bc7e91926016],#[0xe81846016554ef5ba061,0x96f4fa26518059553ed6,0xdc565c6f65384dc5705,0x182603715969fba05c98,0x9fba061180dc565a7ee8,0xc565a6fe919260371596,0x400b400029efa265180d,0x501bc02f404e007500b,0xd8019502dc053409601,0x8090c108020103e4072c,0xeb05940abc14a027904c,0x1c5035d06840cb418602,0xc0ffc1f803db07800e7c,0x8f08e8117c228042f081,0x28e04fb09a8131425504,0x816bc2c4056d0ab0150c,0x570c78186c30005df0b8,0x35a06a50d2c1a1c33c06,0x1d1c39306f30da41b0c,0xf50fa81efc3c607770ed,0x438085b109820ac40807,0x4233445c08af1134222c,0x7b12b424fc48f090311c,0x50409ed13a426dc4cb09,0x42a845430a65147c288c,0x4916502c1c5790ad7158,0x6060bdf177c2e5c5b50b,0xc32646360c451860306c,0x471a58342c6750cd5198,0x6f00dbf1b2435c46ae0d,0x39e47320e3d1c5c381c,0xf71dac3b1c75c0e971d1],#[0x7a10f391e603c247800e,0x83dec7b90f5d1ea83d2c,0xf91fb03ef47d10f931f0,0x81c10292040405c8070f,0x420c837105f20a04104,0xd1219c431485b10a7213,0x885110121e443a487010,0x845248a31137225c447c,0xbb234c46448be117322c,0x909120323f447ac8eb11,0x84a049331251246c4884,0xdb25b04b3c96012b7253,0x98d131126044bb497212,0x4d1c9a2133526584c8c,0x8f27004ddc9b1135926a,0x9ed13bf276c4e849cc13,0xc5034a02140127f04fa4,0x7928bc5154a231431282,0xa5c14a329405244a4414,0x5454a8614f729b85304,0x7b2ae4558caad154b2a6,0xadd15b12b50567cace15,0x45784aec15d52b98570c,0x472c705874b0115f92bd,0xb4f16952d1859f4b2b16,0x85ba4b6d16cb2d785ab4,0x252e2c5c1cb7f16f52dd,0xbac17552e985d24b9717,0x45e44bc417792ed45d6c,0xf12fd05f7cbe517b52f3,0xc1518153018600cbfd17,0xc61d4c361863309c60cc],#[0xdb3180627cc48188730f,0xc96191d3228642cc7818,0x4660ccba196532a064ec,0xb9336066b4cd2199b332,0xcea19cb33906714cde19,0x67a4cf019dd33b4675c,0x37345c687cd0b1a0733f,0xd321a5b34a46924d201a,0x6a5cd471a7f34ec699c,0x935e86bacd6b1acd357,0xda71b4536606c54d861b,0x86f3cdda1ba536fc6d5c,0x4d3864708cdfe1bed37c,0xe491c8338f471ace2e1c,0xc7374e641cb939547284,0x433a5c747ce8b1d0d39f,0xecd1d7f3ac8756cea91d,0x8777ceeb1dcd3b7c76bc,0x4b3c6c78b4f0c1e033be,0xf571ea53d1479ecf301e,0x7c44f7e1edb3da47af4,0x713ec47d4cfa21f353e4,0xfe11fa73f3c7e54fc31f,0x88004ffc1fe33fb47f2c,0x9140d4813d01d2031403,0x7120d3418882d505020,0x884fd0952115420083ad,0xbd4350864d0c2216f42a,0x119221143f8879d0e321,0x88a55143227744b8891d,0xfb45d88b8d16a22c5454,0x1a6234346508c7d18522],#[0xc8e5d1ca238546e08d6d,0xf747e88f951eb23bb474,0x21824274830903d20023,0x491bd233245d48b4912d,0x9f4938924d248248748e,0x27b24e149a492f525124,0x494ed29625234a34942d,0x834ae895c52b425594a9,0x2f025d14b8496b52c925,0x4981d30226014be497a5,0x7f4cd4995531d26254c1,0x37a26d34d889ad534a26,0x49ce5392271b4e189bf5,0x814ef09dbd3ad27514e8,0x3e927c34f5c9e7d3c227,0x4a04540127f34fd49f85,0x5f50aca11d41f2829503,0x45528a15118a1dd43728,0xa35d46728c55178a2cd,0x1f5238a41d47c28ef51c,0x4a329435274a4ad49129,0x8a5cd4b5295552a4a525,0xcd5340a6454c7298552f,0x50929f753e8a7954eb29,0xcaa3553c2a63549ca8b5,0xbd5568aaad5512a99552,0x57b2aed55d4ab855692a,0x4ac8d58d2b055604abfd,0x9556dcad7d5a82b41566,0x5fc2bd15778ae9d5cf2b,0x8b22d63b2c555874b035,0xcd5970b28d6502c9d592],#[0x6922d0f5a00b39566e2c,0x4b5ed6b02d515a84b4cd,0xff5be0b7556da2da55b1,0x7282e475c7cb8a57042d,0x4ba3d7432e7d5cf4b9ad,0xc55d6cba9d74f2e955d2,0x7852f015de4bb8d76a2e,0xbcdd7972f2b5e50bc65,0x8b5ef8bde57af2f495e8,0x7f12fd95f7cbed57d32f,0x4c0cd815301b6024bff5,0x6f60ccc18d82d3051608,0x854309f6120c21d83f30,0x4c3e587530db618cc2f5,0x2f624cc47588a310b620,0x8b431596288c50589c31,0xc6558c931896300c5dd,0xd16390c6e58d531a1633,0x8ff31ef63ccc7758ed31,0xc90d917321f6420c81d,0xa36528ca1593b326164b,0x98932fd65d0cb4d95c32,0xccd8d9a73345666ccc9d,0xdb6798cef59d4339366f,0xa1c341d6810cfe59f533,0x8d1f5a3a346b68b8d135,0xb96960d29da4f3495691,0xeac6fc1fc081f0fa5e34,0x1bf07f0207c382781100,0x16ec18148809c03a072b,0x24e439e07e02072328f8,0x81900edc278081c8a0b6],#[0x1c8d24f709e07e020722,0x422310cc885c2581d088,0x81b0b05e83bf07709d0b,0x5e020722ec1006281f80,0x1f8080cec20c03b30806,0x2060603861e2008a8828,0x6a343411a87ec2c0f886,0x6c878403a822320f08b0,0xbc2dc21089003b21e101,0x20722c17fc181000e983,0xd4cbb0f8602203aa0fe0,0x1c89221606073422200,0x6059e0006c2493f81f04,0x2a886c228180d7800aa0,0xf800aa4fc10e07e0081e,0x3e0143e180e188181907,0xb083fc1f8085bc118805,0x785ff06a0fe00041e03,0x9b0d605c002d022cf81f,0x18206021cf81f08b0f40,0x8015c301f05f0770c07c,0xc80acc378101b0a06c0,0xb04b0fb03401b0d41828,0x1b09e0113e06c1e0901,0xe60e06606c2187983818,0xd0a1419f8001564f8861,0xb02ec0b827006c30c021,0xc438c000722440b42cc3,0x18114c6fc1fc081c81f0,0x40ef42a178603a09e08c,0xc10150ca1e019b040542,0xb0404e1f82287806281e],#[0x5e280af42ec10138802f,0x4f81f0803803350db040,0x321c00e0970a2987908c,0x2a2816c4ff0001f09840,0x4681e8452032191b70b0,0x7a164681e8591a07a16,0xbd0d70a134681e8591a,0x513e438a816c4f819782,0x7be09e00e2b30a054c0,0x2a1140ee4681c81f0a,0x2681f0461e60e019e09e,0x6c282691e09e0009a18,0x7c1917e46f827c1fc0f8,0x800cf8157410a08c83a0,0xf8960005b93e07c27827,0x9e0091a2f8278001564,0xaf041b4681e8462061fe,0x12c36c081e82989d0dd0,0x7a0dc3742ec107d0a0a0,0xb70c07a1c12dc301e860,0x2019283ec080ef828b04,0x80cf430a06520e03d21e,0x35f0711e27c1a486c0,0x210ccc17c18500178b12,0xa0e8278a42370207207c,0x170809f03a201c90a982,0x6c26c20095c10118832,0x1c81b7000802a44750c,0xc8c02a06c04560a2011,0xd022c480c8741b46ec22,0xec30178940fe0006403d,0x403501ff0607c2802fc1],#[0xd0c05e27c181c81f07d0,0x9c281902701c87f06065,0x6c81f0ab09233e000720,0x72145e00281ce46dc18,0x98380bf807828e06df06,0x644760007232c2741187,0x81c1d8001c8a62b20b70,0x21a0a707708e003e8294,0x207c182701c842538405,0xb023026f805c20609a65,0xdc20f12101fd09f06035,0x23897fc1943f40810742,0x7df0603510fb08045d0,0xa30e0240721e0f81f04,0xe05a298918060fbc101f,0x60f8168862a60006583,0xdc20660183e07c181f18,0xe03a035d00a3e281f60f,0x181000ed03f4010d0f15,0xdf0690fd0207c2c57fc,0x16993991bc260fdc00c0,0x90a64e72af0805b83e30,0x2170005b83e360f81f04,0x6101691001f0790a2406,0xb077042c87ec18521fb0,0x616c19000423c82321f,0x8f208c87ec1dc10b047b,0x709b0770436c183b0608,0x822200a878223c82321f,0xbb04a20181902a200a87,0x108800604022081b8240,0xacb08f8081c88221918],#[0x80b148a064b04c53e022,0xc52b05e02180eb08bc27,0x22046108802220080602,0xca148407c61e120c820,0x191480e00c87e0207210,0x22100eb1485453c0a308,0x210000a081f0088407c0,0x938084c0a0b0282064c2,0x216c26c100e07c0a081,0x4200065e02101902065e,0x9097000422d21f70442,0x1f7041c0fa8d28787704,0x3046208d487dc2062352,0x110ea87f808612e305c0,0x84047e02101782252846,0x808970807283a1f80994,0xe0265360218118c1187f,0x9e022108dc2187f8088,0x8b287ec14090842261ef,0x80a1e0a0970004a1e08,0x403be022521a878243a,0x20720a948225208948c2,0x78261e080047e02101f0,0x3e0b0fb41900060640a8,0x61f4183d060ec128804c,0x305c0c274182c3e423d0,0x7c0c1607f418581fd06,0x788020081902001483d,0x2e8211041b83b81c413,0xb07883080720b07b8184,0xc10148209c07c1027014,0x202c04c0133e18007c00],#[0x2cf89404b03400254270,0x2b3f4054001ac1d01500,0xf89b06e0530cc0020950,0x83b0640816c1d015002c,0x16042ec183b0640416c1,0x183b06080b0eb0740022,0x30102c080b0202c240ec,0x609026c185b060f02020,0x2224812c0d0018109b0,0x1c15c720204024221605,0xb8096016000880c8057,0x71c0dc703a0580011cf8,0x8804409b1c130901b05,0x200c378104c0130c1009,0xb06a1e16c183b060ec18,0x88808109b060ec1a8785,0x6a1e10003028202c3ac1,0x18321fb061487ec185b0,0xa886c1ec0b0009b060ec,0x900608807204604b021,0xdc70371c0dc702a2008,0x820240182201dc70371c,0xc086824a2031af062187,0x220098803b1c0a092883,0x2f8101b0406c088803,0xc6dc18842422131b706c,0x288424220c0019091880,0x4880360809885815c0a0,0x2e001a0f4078403d01e1,0x9021382207a008781f90,0x2055d021307f408481f,0x2028282068202a080a82],#[0x18200000190e08001820,0x61107f4185d0793e174,0x4f8370713e11080241fd,0xc8803d1c081b0206c0c,0x2164f83b0793e100220,0xdb0602202a2e4f820080,0x22081d408ec18602d30,0x78206022080d008cc306,0x730521e274282000d0c3,0xe080c886c1c8787221b0,0x82b0eb0740010a36c183,0x20ac3ac1d000820c08e0,0x1ec0b0008a1fb0610250,0x208208410ab061c14ec,0xc35002c08278c0820081,0x8bc30802c07c101f287a,0x1d0407502a1027c0b40,0x4a1e101d0202d02a101f,0xf00d04082081f01d0407,0x8272c301f0607c034101,0x88409c03402bb030222,0x7c078101e02078081f0,0x2082008101f01e01106,0x2d0c6bc182388078080d,0xb0a8645231af0609420,0xbc0b148408cf021114bc,0x461f800f021dc70371c0,0x48780061ef021987bc08,0xdc18238607c0e823c0a1,0xc18250831b70602c18c6,0x101f08f0245211148c6b,0xa825000482a08168113c],#[0x942e8203a08f02c521,0x6dc180d0705331b706c0,0xe108dc086c0105210c,0xef021242d000570280a1,0x61f90af02180ac428461,0x2a201f0207c0e4281f04,0xe02214088213e02c0220,0x10330a13e02218210213,0xb0006a1f40009c10c202,0x2701f00e86a1e0c166c0,0x36c08c42e42521f30220,0x7502a1287ac2bc150044,0x4074a1e140b408bc2860,0x181d0207407c1017e430,0xc46ec180f0711bb06822,0x46ec180f0711bb060821,0x6ec1d820911bb060821c,0xbc08511bb0603c181e44,0xc101f06c0121f7021987,0xe3c124301f0ac2a0816b,0x6820780061ef02181f81,0x3706c0009513e29c2e00,0xc012521c46dc180f0725,0xc146a811108c4f8913e,0xa02b10c1243500057028,0x3a101f81d3c124301f0,0xd430550c081110a8590c,0x1e01d0178607807c101e,0x80f00d4884078807c08,0x91e000841a07f8004e08,0x81f9021381207a00860,0x2416740b8207903e0010],#[0x1520784054a04c1fd02,0x157408407c0818586001,0x8000081f0030441e08,0x81d0790c101d741e40f8,0x8207f418603c282a040,0x198008000604081e000a,0x8513e03bd061e14e4ff4,0x800608d13fd061803741,0xf418241e93e1042b41f,0x8441fd061741e4f85d06,0x406c102d0ed061107f41,0x1b4f8801350c10285430,0x4088d0ed06182681ef4,0x82682d0ed061008343,0x1a4f8800000080010400,0x88a5293ee081825294bc,0x860103a1a1138240e816,0xc0513e1c46dc180f0660,0x46a81680e98244f8b706,0x313e2c4fb010570280c1,0xe00118a831aa08c42041,0xb4106f020d8a9080407a,0x208235c084d040c46dc1,0x80205409c39c1bc086f0,0x32120e18040c81688000,0x110a108ea42d82066090,0x101f0207c0e4281f05e0,0x407c098101f0460407c,0x1f0353e200a081f43b47,0xb0793e16820320920010,0x180060200040021e4f83,0x20000e4f820080e4f982],#[0xf05e0008010202008000,0x5e181ed430550c081f81,0xae0013800200007e0782,0xe0818007c080001f0207,0x8078207a0c1182047b04,0x802c30e0a000410001e0,0x7a0828026f42f826c0f,0xc20009ab0c12c302684,0x827805c308225d0be097,0x9a73ef06f0207a28467,0x98070f0e1bc09c301e86,0xa08007a0bc19c301e860,0x702181e8207a081e8207,0x80f020826dc08409a70c,0xe50d302180001f0207c0,0xc81e0407c078101e0321,0xc101e28784072022101,0x434c25c12436c08c0659,0x835708181e020780c879,0x820723683dc202306822,0xc18208609f11bb07b020,0xb07b02c003217043c46e,0xa46ec1ec08208911a219,0x208607291bb07b020222,0x1800019821200a46ec18,0x146bc181a0770970407a,0xaf0407c201f82f030181,0xc000381c82b000404403,0x5c0007c13c081c84045,0xc1b0009c0003a1443300,0x1b0008f02a1e1023946b,0x1c10af0291e101f946bc],#[0xb70609620c8446dc1d00,0x8a05a08c81c10407311,0x1e90c181681100e108dc,0x7a430990c080d0213d0,0xf08080035708104f5c14,0x617418209408003c202,0x4045d061207f4184d0ed,0xf01e05d0651e17419478,0x64d0c150781e04094081,0x41bc082120081e020000,0x4982bc0c828851af0623,0x1af06e0023c081c84034,0x2588f020bc0a878408e5,0x8dc08805a0c46dc181c8,0x20b405ae00181681118,0x870213410311b7061341,0x3c082512081cdc08470,0x7c088c8207d508101f02,0x8044306d080e82942040,0x110ec4364207600080cb,0x8205a0e828168590c05a,0x1f0207c081f0203a0816,0x1ec12c10600190206408,0x7c080e00885046e00101,0x208078200000a081f020,0x78283c03a140f24d0400,0x3410c78231e08051e094,0x958004f0209c2822003,0x1816dc23800605970210,0x27001800838aa04583e,0x54027001107904845474,0xc8842241f018190b1078],#[0x2c61fe021d80b809c001,0xb7061341e0f80ef81866,0x70290a1486dc184d0721,0xbc25c00723e0a42dc085,0xc20606472ae04f082016,0xf8662090ae0418169c03,0x9c20543e70815c1cc050,0x8101682c8483ab00150f,0x3a2606ec184d0609b70,0xc8888484878aa10b83e,0x20640f02a0c85b0250a1,0x8190205a300120c8,0x2000080002]]
def g251H7 := limbs80 #[#[0x105801420060a40ad042,0x700608506410b3032000,0x41400c41e90020110e,0xdd19321810004dbe15,0x1f04fd9d27ec8c3a0000,0x66e3e31e10005f,0x48b1e035bd49509ec901,0x3749662c7100046f6906,0x76a000d9100046c2b3a6,0xccee9000000a2f0000ea,0xbb3fb72000422db45690,0x952a11000b34a08d5f01,0x26500074ce2e44e056,0xe000000000241024f390,0x440000a6700062004ab0,0x8d0c600000065752bf96,0xfd1920f87025ec43000f,0xa6400038a0000003a,0xbe0bc4b649b04f000000,0x5e0062ce9891c7aa8c7c,0x60cb4213b9a414550b5a,0xae85df47018166f388de,0x5000000102000e3e9135,0xc51f1741f25c00025,0xe6b000797e5a536000,0x316085841d11a0000000,0xf280007f000000060,0x29b9a130000000b16000,0x400000070d74d9536b9e,0xa370000000002c,0x233a8000d0a35b000a31,0x5ab7b1494400072d2ce0],#[0xe6d9b2783000109d596e,0xab954061c05512e46d26,0xa607f2528eb10d3d268d,0x2a904b000233b060b512,0x83cc21000]]
set_option maxRecDepth 16000 in
def g251D8 := limbs80 #[#[0xa0aa0887d85492154110,0x21e716558550443e62a8,0x956254110eb4b92a4a82,0x4435d30cb12a08879a5,0xcbb2caa8221d39745515,0xac0887b85892158110e3,0xeb16450560443dc2c4a0,0x5158110f70b12a2b0221,0x43dc322b12c08879c595,0xa2c4b0221ce974589604,0x8873add56258110e75b,0x974591604435d70ab12c,0x54510f32b2ac4a8a21cb,0xaaaa7b92a28875554d72,0xa6a8a21d557454d51443,0x871d5d96554510eabba2,0x6dc9624429df2cb92c48,0x120fc4a9a84a02414ed9,0x2eaa1280907e294d4250,0xa0241dab7550940483b5,0xeae154250120dd4c2a84,0x940483b52eca1280906,0xf94aa2a4a0241dab765,0x8b1280906da615525012,0x241ceb7658940483d52c,0x5d96450120e9cbaaa8a0,0x50483ad2a5b8aa09072e,0xb4caa84a8241f2954509,0x92a09075a5d15254120b,0x1b6b8454950483ad6e8a,0x95254120eb4bb2a4a824,0x482ed32ca92a09075add],#[0xbb2c4a8241e696558950,0xa09074e5d15454120e75,0x4d6554d624838f2ecb2a,0x358920e67bb2a6b1241e,0x29df2cba2c490733dda5,0x6ecb12414ef965d56248,0x9053b6577658920a76ca,0x7659553482abf2aba2a6,0x95208f7c930eaa241c5d,0x72a9b8aa0a046fe51875,0x4a8281f295458950503a,0x79a5956254140f54b22c,0x589505039d2ecb12a0a0,0x40f94aa4c4a8281ae986,0xa9c12a0a074e55372541,0x8281d397655150503672,0xe6195454140e9dbb2a8a,0x1505036770caa2a0a06c,0xd5cc32c8a8281e396559,0xb8ac0a071e5d96554140,0x81cb964dc5605039d2c5,0x4d6258140f64a9ac4b02,0x503d5328b12c0a07b29,0x5baac4b0281ce9755896,0x2c0a06bae156258140e7,0xe996454d60503572c9c1,0x5358140f2cb2aa6b0281,0x3972eab22c0a07a6592,0x2ac8b0281cbb75591605,0x2a071e5d56558140d5dc,0xd9894f715031db0cb16e,0x58940a76cb6e4b12811d],#[0xc9acaa9ac4a06ea61180,0xa6b1281ccd7654d62503,0x71b5d56558940e66bb4,0x7595625029db2eb2ac4a,0x9408f7cc2eab12814ef9,0xf2abb2c4a053b65b7558,0xa9a811ef985d6625029d,0x7be498759540e2ebb2ca,0x9755029db2c412eaa04,0x8f7c930bbb2811ed96e,0xbb8ac0a873a58b715815,0x2a1a7965e05605438f2c,0x6595258150f34b12a4b0,0x60543cd2a8b12c0a859e,0x75c22c4b02a1ceb74589,0x12c0a879a6556258150d,0x1e3964551605434f2cbc,0x77458150b3ccb2a8b02a,0x5434f2cbc22c0a871e59,0xca2cab02a167b9259560,0xe2a871b59562dc550b3d,0xed96dc9625431db0cb16,0x58950f34b2b00b12a14,0x38daecaa2c4a86da6158,0x6e8b12a1c6d65dd16254,0xa879ae416558950a76cb,0x905d962542cdf28b2ac4,0x8950e75c82ecb12a16eb,0x5f28c3ac4a853be51765,0xb12c11ef9261376542b,0x7b254f8058960b74c8f0,0xe0162583d94a7c02c4b0],#[0x60b74ca700b12c1ae984,0x2bc02c4b06ba61780589,0x12c16eb9060562582dd3,0x3dd25358960e67ba2a6b,0x1625829db2bba2c4b073,0xb75c82eab12c16eb9061,0xc2ac4b053b6537558960,0xc1c5d6554f72582dd720,0x416554d60e2eb2ee8a9a,0x1487ccacab12a290f96e,0xab2ac3b82a3c75765955,0x2c4a8f1b59562dc151e3,0xe6565605625469db2db9,0x535c162e2eb2aa7b82c5,0x8b8deeab2ae0b1793595,0x2aa7b82c5a6f85595705,0x2b171bdd5655c562f26b,0xd905955358b4df0ab2ae,0x59562f27c82caa9ac5e4,0xcdb21baacab14bb65380,0x82a822166d91dd56558a,0x87dc5496154110fb8a92,0x458550443ee2a8b0aa08,0x110fb4a9284a8221df37,0x32aa12a0887ce5514254,0xa8221f696254950442ef,0x5edd15254110ebcba2a4,0x4950443af2eca92a0887,0xbbccb2a4a8221d7b765,0xcb12a08879e595625411,0x221f6954589504435f30,0xdd16254110f74b22c4a8],#[0x50443ed32ab12a08877a,0xb4aa4c4a8221ee986589,0x92a08877add26254110f,0x15f996dc950443af2cbb,0x95454110fb8c8aa8a822,0x443e72c8aa2a0885dee4,0xbb2a8a8221d797655150,0xa0886de6195454110ebd,0x7996551504436f70caa2,0x454110bbdcb2a8a82217,0x35f30cb22a08879e5956,0x6e8a8221d7965dd15044,0x8867ee1b7454110cfcc3,0x9261150442bf32dba2a0,0x8110afdca2eca82217eb,0xe6e890ac0887bc591215,0x2b0221ef16250560443b,0x7bc5895158110bf9c928,0x54560442fe724a8ac088,0x10ef9ba2a2b0221ef164,0xc4a12c0885fce5151581,0x2216f99650960443dd2,0xe6595258110f74b12a4b,0x9604439f2e8b12c0885b,0xb7dca2c4b0221cfb7458,0xb12c08873edd56258110,0x216fb95589604435f70a,0x116258110f74aa2c4b02,0x443dd328b12c0887ba6,0x4c2ac4b0221eeb945896,0x2c0887ba6556258110f7,0xeb96455160443dd72ab1],#[0x5458110f3cb2aa8b0221,0x43de322b22c0885be659,0xaac8b02216fb92591604,0x886bee156458110e7db,0x965dd160442df72ab22c,0x50510afccaee8b0221cf,0xfe720a12a28857d65b72,0xc4a8a21f555350951442,0x87b95916254510f3ab2a,0x458951443bcee8b12a28,0x510ef3ba4c4a8a21be78,0xacbb92a2886f9e126254,0xa8a215f596dc951443ae,0x9d59564545109facb704,0xd151443aeacbba2a2887,0xcfbc36e8a8a219f586d,0xbc22a28857d65b745451,0xa219f576e11514436eac,0x65b8454510cfbbb708a8,0x51442bef28bb2a2884fd,0xf9c8284b0a213f794619,0xa2c28879d5955458510b,0x15f595dd1614439eacbb,0xb8050910df4a9700a122,0x4437b2a7c0284886fa58,0xcaf00a1221bb954e0142,0x84884fe65b80509109fc,0xef8658942443e5aa8a92,0x6509109fdc830aa1221a,0x3d5ac8aa2c4884fee418,0x2a8b1221e6d655516244,0x887b96456458910b76cb],#[0x7559162443d5f08b22c4,0x8910b77caac8b1221cef,0xdd2eb22c48873b65d645,0x8b1221ced65dd1624439,0x5fae418458910af6caee,0xdd262443cdf0ab2ac488,0x10cdec22c9b92215ed95,0xab2ee48847f66164dc9,0x92218fd86597724432fb,0xf59564551108fecc2cbb,0xd544438faecb2aa88878,0xabfcab0eaa2215bf9461,0xc3ac88855f6568755110,0x214fd96a1d644429ff2c,0x1565dd1108fecb704ba2,0x44431fb0cb2ee88865f6,0xfcb30bba2211fd985977,0xaca8853fe5176595108f,0x1fd95e11764423fb29c3,0x5150120fd4a12a2a0241,0x83f5284b0a80907d654d,0x1302a02417db93585404,0x907ea54d4250120fd4a,0x96550940483f52c6a128,0x50120fd4c3284a0241fa,0xf32c8a9a80907ea59152,0xa6a0241f596554d40483,0x7ce5955450120fccb24,0x259140482f732caa2809,0x120f5cb2ac8a0241fa99,0x6eab22809076e5d56450,0xa0241bb98559140483b7],#[0xeee556450120dddc2ac8,0x85504836f30ab2a80905,0xbedc9ac2a8241f69525,0x4c0aa09079e595615412,0x241f696550950483ed2a,0x58d5254120fb4a1aa4a8,0x50483ed306a92a0907da,0xb4c32a4a8241f6964549,0xa2a0907ce5915454120f,0x1e796559150482ef32ca,0x77454120ebcb2ae8a824,0x4836f2cbc22a09075e59,0xca2caa8241f699259550,0xa29079d5956154520bbd,0x6d6558951483e9aa6a12,0x354520e77bb2c4a8a41e,0x3abee8a9aa2907575d15,0xa84b0a41c7d765955148,0x906f3e0d5258520de7c1,0x74e0d614833bae9c1ac2,0x8520ceebaf06b0a419df,0xbb2bc1ac290677dd7835,0x5b8a41ced6458b714827,0x63f61964dc520cf6c22c,0x54d424823fb30b26e290,0x20f96b22a8a9241f4d65,0x2eb2ac49073ba5d64589,0x9a415bf945d5434839dd,0x75957454d20f2eb2ac8a,0x553483abacbba2a69075,0xeaecbacaa9a41f4d9259,0xb22a890757a5d6554d20],#[0x41d3d7559154483c7aca,0x528759120adfca30eb22,0x5482b7f28b2ee89056f6,0xfcab0eb2a415bf9461d6,0xaec9055f6568759520ab,0xf39544c5505023fb29c0,0x6154140bedc9ac2a8281,0x3cf2cab0aa0a07ce551,0xaae2a8281f39545c5505,0xa07ce5518154140bbdc,0x96454950502f7728c0aa,0x54140ebcbb2a4a8281f3,0xbf32db92a0a075e59772,0x4a8281bb964e0950502,0x7ce55163541409fccb7,0x460d50503e72a8b9aa0a,0x140bddca306a8281f395,0x30caa2a0a07ce5d95454,0xa8281f399559150503e7,0xce6516554140f5cc32c8,0xd950503cf2ecb2aa0a07,0xebdcaaeca828177b955,0x8c32a0a05eee51865414,0x281eb964485605037772,0x5915158140f74b12a2b0,0x60503cf2caa8ac0a07ae,0x5cb22e2b0281ee9625c5,0xac0a05bee597158140f,0x1eb96460560503dd2c4c,0x55258140f5cb22a4b028,0x503dd722b12c0a075e5d,0xb22e4b0281ee98558960],#[0xc0a07ae5918258140f5c,0xb97559160502f7728c12,0x558140f5cc2ac8b0281e,0x3cf2eab2ac0a07ae6516,0x2eab02817eb925d56050,0xa077ae497558140ef449,0x96dc921502f7728c2ac0,0x4540af7c92ea98a815ed,0xaaa6b8aa2a079d595615,0x4a8a81e6d6558951503e,0x75754f7254540e76bb2c,0x61d515038faecb2aa2a0,0x409fcc870ea8a813fb90,0xebc1ac2a0677e0f72585,0xa819df75e0d615033ba,0xf5d565585409eecaf06b,0x971502bdf24baac2a071,0xaf7c92eab8a81ced7658,0xbb2e2a065fe15755c540,0x813f990e05625031ff0c,0x5f8158940cf7b9702b12,0x2502fd321c0ac4a047f6,0x743f02b1281ced76e056,0xac4a057b65f8158940cf,0xced9759562503dd320b2,0x7658940e76c8aecb1281,0x39db2abb2c4a073be45,0xc2ecb1281cef955d9625,0x4a075759553dc940e764,0xd8694f725033bb0ca9ee,0xdc940cbec2acbb92819d,0x3fb30b2ee4a063f61965],#[0xdb92819ed9261b72502,0x7d66416554d408ffcab,0x759553503cbaecb2aa6a,0xd40eaf4bacaa9a81d5d9,0xf24baae6a057be497558,0xb2a81bb98460165502bd,0x7f65f81595409fcc8702,0xd5655038faecbaacaa04,0xeb7c92eab2a81d6c925,0x4c3acaa071fe55765954,0xa8157f9561d65502bdf2,0xe4187595409fdc830eb2,0x655033d924c3acaa067e,0xbfcab0eb2a819ef9261d,0x3acaa055f6568759540c,0x11fd98a1d655029fb2d4,0xb825d5409fcc870eb2a8,0x5027db2dc12eaa067b5d,0xc8302baa8157f955d975,0xeaa067b209815d540afd,0xed86209755033df04c0a,0x25d540af6cb104baa819,0x33db0dc12eaa067b60f8,0x704baa815ed96e097550,0xa067b647825d5408fecb,0x96e09755033db27c12ea,0xd540afdc8306baa819ed,0xf720c12eca057ee41865,0xabb2815fb9061576502b,0x7da5492158150af7c930,0x5c560543cf2ca90ac0a8,0x50f3cb2ae2b02a1ee962],#[0xc9b8ac0a85bee5971581,0x2a15f994dc5605439f2,0xe5958158150f74b1302b,0x5605436f2a5c0ac0a879,0x9fcca702b02a1b7954e0,0xa92c0a87da6095258150,0xa1d7b7454960543cf2c8,0x456258150dbdc22a4b02,0x543dd308b12c0a87bae,0xcb2b04b02a1e79655c96,0x2c0a85dee558258150f3,0xf398455160542ef724aa,0x6458150f3ccb2a8b02a1,0x43cf32ab22c0a87ae5d1,0x2ae8b02a17eb925d1605,0xa879e5958458150f3cb,0x99159560542ef72ac22c,0x58150f3dc8acab02a1e7,0xcf724b2ac0a879e64965,0xcab02a1e799459560543,0x879d5957158550f3dca2,0x3dc9615436bf06a92c2a,0x550daeaa706b0aa19df8,0xacbba2c2a8677dd38358,0xb8aa1e7791595615438f,0x3b5d9625c550f36b2ac4,0xd17154367f08aa2e2a87,0xd3fc32cab8aa15ef925,0x8b26e2a863fe19765c55,0xaa1c7d655937154337b0,0x66164dc550c7ec32c9b8,0x525432facac26e2a847f],#[0xbdc82eca92a176f91589,0xac4a84fe6438158950b,0x137d95e05625434facbc,0x165589508fecbf02b12a,0x5439f720bb2c4a879ee4,0xb2f02b12a17e990e0562,0xc4a86db6178158950f36,0xed76e0562542edb2bc0a,0x458950af6cbf02b12a1c,0x3cdb2ab22c4a87ba6416,0xacab12a1ced975916254,0xa879be456558950f36c8,0x9459562543cdb28b2ac4,0x8950f75c82ecb12a1e6f,0xdf22bb2c4a873b645765,0xcb12a1ced945d9625439,0x73b2617658950e77ca2e,0x553725423ff28c0ee4a8,0x50cdec22c9b92a197d86,0x30b26e4a863f61964dc9,0x92a19ed9261b725423fb,0xfe11545cd508ffca30db,0x954542bdf24ba2e6a86c,0xb9fca2ecaa2a177b905d,0xbb2a8a875ee417655150,0xa1e796560164543a7f28,0x438159150dbcc2b00b22,0x45434facbc0ac8a84fe6,0xecbf02b22a137d95e056,0x2c8a878f59574591508f,0xe7b905956454397aecba,0x8559150f1fca2cab22a1],#[0x42df720bb2c8a85cfe51,0xa2ecb22a1cfb905d9645,0x8a857be498759150e5fc,0xb9061d64542b7f28c3ac,0x591509bfcab0eb22a13f,0x9fb2d43ac8a856f65287,0xeb22a13f990e1d64542,0x86db597825d1509becaf,0x6e09745433daedc12e8a,0x550dbcc1700b2aa13ed9,0x309c02caa85de64b8059,0xb2aa177994e01655436f,0xdee418459550bbdc8304,0x1765427f329c02eca85,0x8feca702bb2a15f994e,0x8c12eca857ee41825d95,0x2a157f9560976542b7f2,0xe49845d950afdc8308bb,0x21582aff2ac22eca857b,0x72b12e2a8ac1e7565545,0x12a2b079d5957154560f,0x1cef7458951583dd720b,0xd6254560d77c22c4a8ac,0x5838facbb92a2b06bbe1,0xcbf04a8ac13f990e0951,0xa2b071f59774545608fe,0x7d65e11515827f321c22,0x7545608fecbf08a8ac1a,0x3dd720b12e2b04bf65b8,0xac4b8ac1ced745897158,0xb063f59584dc560e76ba,0x9061d525823ff2ac26e2],#[0x89609dfca30ea92c13fb,0xd2e9c02c4b05bee41755,0x2b12c1ee975e0162583d,0x5bb6538158960e77ba70,0xe05625839deebc0ac4b0,0x60b76caf02b12c1aed85,0xe929ac4b07b35d153589,0x12c16ef915d162583d9a,0xbe557458960e76baae8b,0x562582ddf22c22c4b05b,0xb77c8aeab12c1eeb905d,0xc2ac4b05bbe517558960,0xc1e5d6554d72582ddf22,0x15655c960d5fc22c8b92,0x3583cbacaba2a6b069fe,0xfc92caa9ac1e5d925955,0xaa6b07976516554d60f2,0x6fb905d564583cbf28b2,0x655d160b5fca2eab22c1,0x835f305c02cab069fe15,0xa700b2ac1af984e01655,0xab05bee418259560b7cc,0x994e0175582df720c22c,0xdc151dbab2f00a8a433f,0x8facab16e0a8e7d61161,0xc5b82a39ed8458b70547,0x8e5f59584dc151cf6c24,0x595615463ff2cc26e0a,0x951f3ac92cab0aa3e759,0xacac02c4a8e9f5978058,0xb12a3e6d65e0162547cd,0x7f653805d951f36c82ca],#[0x56254adeb21c0acab0c,0x28fec8702bb2a53ed90e,0xac06e2b147fe5180dc56,0xac51ff956037158b1fac,0xe416554d62f2ec82caa9,0x7058b5df0dc0ae0b1797,0xf7ca301b8ac53ed94e05,0x6e2b16bb59580dc5629,0x53ef956037158b3daeac,0x58059562d76c0b00b2ac,0x58b5db08c02cab16bbe0,0xca300b2ac5aef8460165,0xcab179bdd58059562b77,0x6f75e016558addb29c02,0x59562d76ca700b2ac5e,0xbcdeeac0acab16bba5f8,0xf02b2ac56ed90e056558,0xa9cfb643815d562f37ba,0x826016554f6bb04c02ca,0x9553bafc9300b2aa7b5f,0xbf08c02caa9ed7611805,0xb2aa775f946016554f6,0xdd764b8059553daec170,0x6096554eebb29c02caa9,0x65baec8704b2aa775f90,0x84b0aa08847fe5180dc5,0x8221ff18258550443fe2,0xe5954254110ff8c22c2a,0x950443bf2eca12a0887d,0xdfcc3284a8221dfb7650,0xa92a0887de5915254110,0x21f796560950443ef30c],#[0xd98254110efcbb304a82,0x4437f30cc12a08877ed,0xccb2a8a8221f79865515,0x2a0887ee6116454110fb,0xef98659150443ef32ab2,0x6454110bfccc2c8a8221,0x43bf30dba2a0885fee61,0xb308a8221f7965611504,0x8877edd98454110efcb,0xb94619504437f30cc22a,0x54110dfcc930ca82217f,0x7f328c32a0886fee4986,0x42b0221bfb9461950443,0x87fc6094158110ff8c22,0x254560443fe284a8ac08,0x110ff8c22a2b0221ff18,0x304a12c0887fa5494258,0xb0221fb95450960443fd,0x7edd54258110f7cb2a84,0x9604437f70aa12c0887,0xbfdcaa84b02217f9955,0xa12c0885fe661425811,0x221fe98254960442ff73,0x5915258110fbcaa2a4b0,0x60443bf6e8a92c0887be,0x7cc22c4b02217f998549,0x12c0887be6156258110f,0x1df97460960443df2c8c,0x18258110dfcc2304b022,0x443df2cac12c0885fee5,0xcab04b0221bf98560960,0xc0885fee495458110bfd],#[0x798555160443f7308aa2,0x458110f7ccb2a8b0221f,0x2ff330aa2c08877ea5d5,0x2c8b02217fb985516044,0x887be6156458110f7cc9,0x9261160443df32ab22c0,0x8110f7cb2b08b02217fb,0xf72ac22c0886fe615845,0xab02217fb9261560442f,0x7dd5954254510bfdca30,0x50951443beaeca12a288,0x10dfac3284a8a21df776,0xa4a12c2886fde1942545,0xa21fb55450961443fca,0xddd54258510f7ab2a84b,0x961442feb2aa12c28877,0xfbaaa2a4b0a217f79550,0xaa2c28877ddd15258510,0x21df69755161442fef24,0xd78050910dfcb2f00a12,0x24437f2edc0284886fe5,0x7bb2a4a1221ded765494,0x284887cf5955450910ef,0xdbf7655142443b7aecaa,0x6550910e7ebb2caa1221,0x42bfb2dbaa848857fe5d,0xb30aa12219fd76615424,0x48867fddb8550910cffb,0xd6455152442bff2abb28,0x54910ebebb2a8a9221f3,0xbfb2dba2a48875fdd954,0xc8b12215ff945d952442],#[0x867f5db8255110f76caa,0x6e09544433feedc12a88,0x110edf43ac8aa2213fd9,0xf30bb2a88875fa1d6555,0xaa2219fe8761954442bf,0x7f65a8755110cfe4bb0c,0x4540482ff720c12c8885,0xfdcb22a2a0241ff1615,0xca8a80907de595515012,0x2417fb9654540482ff32,0x5496150120ff8c0ac2a0,0x40483f72a8b0a80907fa,0xfcbaac2a0241ef965585,0xa809077edd56150120e,0x1bfb85585404837f30ab,0x18150120bfccc2c2a024,0x4837f30cc0a80907ee59,0xb1aa4a02417fb9660540,0x80907ee5516350120ff4,0xf98558d40483bf2eab1a,0x550120bfdc8acaa0241b,0x2ff722c3280907ee6516,0x2c2a8241ff1815855048,0x907de5516154120ff4a1,0x7458550483bf2e8b0aa0,0x4120dfdc22c2a8241dfb,0xf2cac0aa0905fe661615,0x2a8241bf98660550483e,0x7fa58d4254120bfdcb30,0x58d50483ef2a8b1aa090,0x20efdba2c6a8241df974,0x22b22a0906fee1163541],#[0x8241f799159550482ff7,0xe6516554120fbdc8acaa,0x950483ef728b2aa0907d,0xff2a12c2a8a417fb9161,0xb0aa29077d5d16154520,0x41bf78458551483beee8,0x194254520fb6b2a84a8a,0x14837df0ca12a2906fb6,0xeb2ae8a8a41e7d655915,0x2a29067f6197454520eb,0xd7d65dd1514833ff0cba,0x7454520cfec36e8a8a41,0x836facbc22a29067fe1b,0x92caa8a413fd96e11514,0x29075f65d6554520fb6c,0xf9461951483afd2eb2aa,0x58520f76b2a84b0a413f,0xbdeeaa12c29077b5d542,0xa4b0a41f6d5454961483,0x77bdd15258520ef6ba2,0x4e0d614837baa9c1ac29,0x520deebaf06b0a41bdd7,0xaeaaa2c29079f5955458,0xb0a415fd9755161483af,0x7fe557458520e7eb2ae8,0xd1614839facbba2c2905,0xf7bc8acab0a415fd95d,0xeb2ac2907bb649655852,0xa41cfe97595614839fb2,0x6537558520affca2eab0,0x42483bdaeab1a849057f,0xb6aa2c6a92417ef91595],#[0x1aa49077b5d16354920f,0x17ef9159152483bdee8b,0x56558920f76c8acab124,0x483ebb28b2aa6907bbe4,0xbaaa8b1a41f5f9459553,0xc69057f65d5458d20ebe,0xff945d563482bfb2bba2,0x555120bdfc8ac8aa2415,0x27ff22c32a8907cfe516,0xf02b2241afd65e056448,0x9067fdd78159120cfeba,0x94595644827fb2bc0ac8,0xd1209fec8f0ab2241ebf,0xff22b2ee89057fe45655,0x2b2a41dbf9459774482b,0x73f5d98159520df6c130,0x605654833fb0ec0aca90,0x20df6c1702b2a419fe87,0xfc0aca9073f5db81595,0x2a419fe87e05654833fb,0xf6538159520df6c9702b,0x5654833fb2fc0aca904f,0x9fec8f08b2a419fe97e0,0xb0aa0a07fc5c56154140,0x81f795258550503fe302,0x96154140efdb92c2a82,0x502ff32eb0aa0a06fee,0xcb22e2a82817f9985855,0xaa0a07de5957154140fd,0xbf9865c550503bf2ecb8,0x8154140bfdcb2e2a8281,0x3ef2cac0aa0a07ee591],#[0x3302a8281df976605505,0xa05fee598154140dfcc,0x963dc950503ef2c6a92a,0x54140dfcb1f04a8281df,0xf7330b22a0a07ee64564,0xcaa8281f799159550503,0x7de65d6554140fbdc8a,0x15d950503ef72eb2aa0a,0x140efdc8aeca82817fb9,0x728c32a0a05fee458654,0xa8281bfb9161950503f7,0xfc5c55158140dfdcbb0c,0x4560503fe302a8ac0a07,0xefcb92e2b02817fb975,0xab8ac0a07be595715814,0x281bfb855c560503bf2e,0x5958158140bfdcaae2b0,0x60503bf2eac0ac0a07be,0xfdc8b04b0281dfb75605,0x2ac0a07be6456558140b,0x1ef99759560503df722b,0x57558140f7dcbacab028,0x502ff722c2ac0a077e64,0xc92ea98a817fb9761560,0xa2a077be49754c540bf7,0xf78758551503beee4b0a,0x154540bfacbac2a8a81b,0x3beaecb8aa2a07dd5957,0x2e2a8a81bf5865c55150,0xa05fde597154540dfbc3,0x86dc951503afacbb92a2,0x4540cffc36e4a8a819fd],#[0xf320b2aa2a057f65b725,0xaa8a81e7d7659551503e,0x75f65d6554540dbfc3ac,0x5d951503afd2eb2aa2a0,0x409ffcbb0ca8a819ff87,0xe4b8ac2a04ff65b87545,0xa81ef5655c561503bea,0xde557158540efabaae2b,0x9615037bf06a92c2a05f,0xdefc1ae4b0a81d7d7554,0xb92c2a067f61d7258540,0x815fd95dc9615039facb,0x416558540deebaf06b0a,0x1503def22b2ac2a07be6,0xec3acab0a81e7d755956,0xac2a073f65d6558540d7,0x7ef925d5615039fd2eb2,0x7558540cfec3aeab0a81,0x3bd924baac2a077d645,0x92eab0a81def925d5615,0x2a067f6617558540affc,0xf9561d61502bfb25baac,0x5c540cffc32e4b8a813f,0x9faecb2ae2a075f5d565,0xcab8a815fd9759571503,0x67fe19755c5409ffcc2,0x6e1571502ff720c2ae2a,0x5409fecb70ab8a819fd7,0xaeab1aa4a057fe55765c,0xb1281cff915d962503af,0xbbe456558940f76c8aca,0xd972503ddb22bb2c4a07],#[0xcfec2ac7b92815ff915,0xb2ee4a057fe4565dc94,0xa81f5d97595535033fb3,0xe497558d40fafcbacaa9,0x63503bd924baac6a05fb,0xffc92eab1a81def925d5,0x2caa06fe6058059540a,0x1fb984601655037f702c,0x58059540fddca300b2a8,0x503df2ecc02caa07de5d,0xbb302b2a81d7d7560565,0xcaa067f61d8159540e7e,0xf990e05655033fd0ec0a,0x159540ebebaf02b2a817,0x33fb0fc0acaa073f5db8,0xf02b2a819fe87e056550,0xa06fe6438159540afecb,0x97e05655033fb2fc0aca,0x9540cff4bf02b2a813fd,0xfb22baacaa075fe1d755,0xcb2a816ff915d965503a,0x73fe457659540e7fc3ae,0x61d65502ff720c3acaa0,0x40efdc830eb2a819ff87,0x24c3acaa077b24987595,0x2a81d7f9561d65503bdf,0xfe458759540dfdc830eb,0xd655033ff22c3acaa04f,0xbfcc870eb2a815fd98a1,0xc3acaa06fe6438759540,0x815ff915d9755027fb23,0x55815d540efdc8302baa],#[0x55033fb0cc0aeaa075fe,0xdc830cbaa815ff966057,0x2eaa057fe45865d540ef,0x3fd95e0576503aff2ac3,0x855d940bfdc830abb281,0x27fb23c2aeca057fe5d,0x2f02bb2819fd82e05765,0xca057f657815d940cfec,0xf9161576502bff22c12e,0x58150fbca92e2b02a15f,0xef2a8b8ac0a877e5c971,0xe2b02a1ef9645c560543,0x86fee117158150efcba2,0x4dc560542ff728b8ac0a,0x150fbcaa302b02a1df98,0x6e8c0ac0a87be5918158,0xb02a1bf972e0560543bf,0xde6455458150dfcba702,0x9160543ef330aa2c0a87,0xf7ccbac8b02a1ef9915,0x4b8ac2a85fbe49744c55,0xaa1df5725c561543eeaa,0x5d17158550fbaaa2e2b0,0x61542fef28b8ac2a877d,0xbec3aa4b0aa1d7f74549,0x92c2a86f7e0d7258550d,0x19fd875c961543cfacab,0x37258550ebeaa6e4b0aa,0x5437bae9c1ac2a857f65,0xc92e8b0aa1b7d8755161,0xc2a879f5957458550bf7,0xfd92dd1615433fb0eba2],#[0x558550f3ec92cab0aa15,0x27ff28c3ac2a879f6516,0x2a4b8aa1d7d765497154,0xa875f595725c550dbfc3,0x76551715433ff0cb92e2,0xc550dbfc32a8b8aa1d7d,0x7ae8b22e2a85df659545,0x8b8aa1e7d6559171543b,0x57f65d645c550e7ebb2c,0x5d171542bff2eb22e2a8,0x50cffc32e8b8aa1d7d65,0xedc22e2a86df597845c5,0x8aa13fd96e11715433fa,0xfdd16354950affca2ecb,0x952542eff22b22a4a875,0xbbfc8aeca92a1f7b905d,0xb2ac4a879f6456558950,0xa1cff915d962543cff22,0x457658950f76c8ac8b12,0x2543ddf22bb2c4a87bb6,0xdc82ecb92a1f7b905957,0xee4a857fe45765c950ef,0x9fd8458f72543afaa8b1,0x86dc950affc8ac9b92a1,0x42fdf24ba2c6a867fe45,0x82ecaa2a15fd92dd1635,0x8a85dfe457655150fbdc,0xf915d954543e7f28bb2a,0x59150fdcba300b22a1d7,0xcfacac0ac8a87be5d980,0x2b22a1cfd7660564543,0x87cf61574591509fecbf],#[0x159564543cfb22b2ac8a,0x150f3ec3acab22a1e7f9,0x720bb2c8a879f5d98559,0xb22a1ebf945d964543df,0xfee418759150e7fc8aec,0x1d64542f7f28c3ac8a85,0xddfca30eb22a1bfb906,0xb2ae8a86dfe55875915,0x2a1dfb905d974543ef72,0xe51765d150affc8aecba,0x74543afb22b2ee8a876f,0xffc8b0dba2a1d7f91597,0xacaa86df6098159550c,0x1b7d82e05655436fb08c,0x38159550dbec2702b2aa,0x543ef720c22caa85df65,0xc2700bb2a1bf984e0176,0xeca85fe653805d950dfd,0xfb90611765427fb29c0a,0x45d950bbfcab08bb2a17,0x33fb05c0aeca86fee438,0x702bb2a19ff82e057654,0xa867fe13815d950cfec2,0x91e1176542bfb29c0aec,0x4560f7ab22e2a8ac19ff,0xdae8b12a2b06fde11715,0x8a8ac1e7d655c951583d,0x79f6496554560f3eb2ae,0x58971583cfb28b2aa2b0,0x60f77ca2c4b8ac1eed94,0x2ab12e2b07bb655625c5,0x8ac16ff9559171583ddf],#[0xf64984dc560cfec22a5b,0x1625833fb2ac26e2b067,0xb7fc8aeab12c16ff915d,0xc0ac4b07bb5d38158960,0xc1eef915d562583ddaeb,0x93815c960f764c2eab12,0x25833fae9c0ae4b06bf5,0xfc8ae8b92c13fd94e057,0xee4b057fe45755c960af,0xcff91597725839fb22b2,0x755d160b7fc8aeab22c1,0x839fb22b2ee8b057fe45,0x8b0bba2c1cff91597745,0xab06bf6098159560cffc,0xd82e05655835fb08c0ac,0x59560d7ec2702b2ac1af,0xdf720c22cab05bf65381,0xcab12a33fd94e0575583,0x8edf6098059551f3ec82,0x460165546eff24c02caa,0x551bbfca300b2aa3b7d8,0xb04c02cab0ddfe418259,0xb2ac36ff92601655875f,0xbfe518059561d7ec2300,0x977058adff20c12cab0d,0x2e7fc8acbb82c5cfd915,0xac06e2b167f65180dc56,0xac5afd816016558b3fb2,0x6438159562d7fc0b00b2,0x7058bddb22b2ae0b15bf,0x76c8acbb82c5eef91595,0x6e2b17bbe4565dc162f],#[0x5bed956037158b7db28c,0x18059562f76c2300b2ac,0x58bddf28c02cab17bb65,0xc1300b2aa7eec9760165,0xcaa9fd76498059553fae,0x5d846016554febf24c02,0x59553faeca300b2aa7f,0x73ff04b8ae0b2fd7e518,0x6e2b82cb9ff845c57059,0xb2e7fe13715c165cffc1,0x905c970596bfb29b8ae0,0xc165bdfca304b82cb7fb,0xf720ba2e0b2ddfe55825,0x8b82cbdfb905d170596f,0xddfe55845c165bf7c930,0x60371596bff20b92e2b2,0x659ffca301b8acb9fd72,0x4c06e2b2d7fe4172dc5,0x8acb5ff92603715973fb,0xfe5180dc565cfec2301b,0x3715973fb24c06e2b2d7,0xcfeca301b8acb9ff9260,0xc16e2b2e7fe5180dc565,0xb00085002980002bff20,0x382018400988042801,0xc7805ac028e01230085,0x27810a007d603a301b30,0x9028b813940966047602,0x6530310817380b0c054,0xec60731037a01b080d0a,0x2410ae082503e901e800,0x264c12ac090e045d822],#[0x557029f014940a1804fe,0xb05d682d9416240ae00,0xa0d2b06668326c18a60c,0x1c4a0de806d5836101ab,0xd2c1e060ec6074f83988,0xa0425c209e0ffc07cf03,0x90a8473422f41127086,0x3bf09bb84c38258c1252,0xe815370a880527028501,0xc2d8016780b0d0571c2a,0x60f82fd617ae0bad85c4,0x2b0675c32dc18fa0c3d8,0xd0db586c34355e1a720d,0x1c860e1f07004379e1b9,0xc1e1dd20ec5074dc39b2,0x103ecc1efd0f65879b43,0x8440417a206a100607f,0x14c888ec43fc21ab10b7,0x9b121e88f2446aa22ec1,0xa259a12bf0955c49dc24,0x4e8826f113548992c4bd,0x150501827f013df09e30,0x80a5a4528428e414488a,0x155d8a974541429b714c,0xbf715d78adc8566a2b0e,0x2d4e16780b27458aa2,0xc5d142e4216fd0b6f45b,0xbec05f122f41177c8bb1,0x6b0c29060fa303517f68,0x218df8c608628a30fd18,0x32fb195f0ca046472321,0x84233d919ce0cda86670],#[0x1c69fe34c21a480d14c6,0x8d8946bba35b61abc8d5,0xbcc0dd146de436aa1b2b,0xb1c670e1ec706637e01,0x43a0a1ce68e64072a639,0x77263b561d870ea9474a,0x470797c3c761e0c0ef40,0x60f7bc7b643d801ea70f,0x1fb68fc3c7da43e741f1,0xbf2046900e87ffa3fc0,0x9e419220b0104b881e24,0xc8678430a2156108b483,0x13f089524456220c90e3,0x2c918448b92458c22a79,0xb23b711cf08dd246a123,0x48ec244192118902847a,0x5424a6f2513926f892ec,0x5097ae4b8f25a392b789,0x135549a044caf262e130,0x753939a89c704de526d4,0xa127b793d209e164ee42,0xc507f2816140149fa64f,0xa3345168288a943b8a14,0xcb8a58a5293292b14864,0xb95214a83853ea29cb94,0x2aca9558caa7854e92a5,0x7292b70959b4ac3455e8,0x3057fc2be515e08aeb65,0x8b2de58f02c5416128b0,0x6d14b5e45a7e2d101670,0x5117194b8505bd52db61,0x82ec597590ba4e5cd42e],#[0x5ea62f3f97934bc0a5dc,0xf565f842fae97c54bdc6,0xc8c1286036300217f74b,0x987c4c37e618d309d183,0x17b18b68c52462553111,0x2731f518eb4c69e631d3,0x8659f32a09938cc92064,0xcdb6669333259980ccbb,0x240d06467ea33bb19cb8,0x11a6c0d3126941346c1a,0x355a9a95cd4766a0934f,0xbba35c99adb0d68a6afd,0xaa6c8d362d9b0d0d7ee6,0xcdb666d6b36a79b474d9,0xbc14dd4e6e6a371c1b7e,0x5d1c170e03e6fc137b71,0x238dc9c56ce23c70f738,0x732c397d1caf4e4d4722,0x912745739fc9ce98e6e8,0x1cebaa75a33aa81d39ce,0x1db10ed0e76603b171d8,0xc3c9e0c4ef90778b3b9c,0x733c9b1e43cf1ba78ab3,0x67a7d3d2b1e7b4f38c79,0xf8a67c163ddc1ed10f5b,0x458f9f47cc83e509f1e8,0x9fa90fc4a7dd23ebf9f,0x400b9ff3cff0e7f603f7,0x1ed40d2a04f101a6808b,0x68830d416da0aa504968,0x5085083d541d1a0dc506,0x15e90a4e84df424ba119],#[0x6621a3d0c8e860a42e12,0x43fba1e650e76870943,0x896a4491223951124886,0x5368a3244efa270d134e,0x6517ce8bb545b122be51,0x2348d19f88c9e4625a30,0x745a39391c228dc946b0,0x4047eba3de51e8e8ef44,0x910848602423920b890,0x24ca922848f02463522a,0xfe527a4937f499624b39,0x4a53312908943c4a0aa4,0x4b30258612b3295464a8,0x7bd4bbaa5ce12df696be,0x3498f34c60a61e530209,0xd34a09a1e4cdaa658932,0x6f65370c9b544d80a6b3,0xcca746939789c744e212,0x24f67a79f13c109dcb4e,0xa084501e27fd13f2c9f2,0x430a1c550b9284a94198,0xd54670a2da514ea89554,0x292294858a3ce51ce28d,0x2e3296254a98a504525e,0xd65352299c94c54a5f85,0x2a7a953c129d154e26a6,0x524ea8c954462a0e54fe,0xcd155eeaa7854f72a5bd,0xa2b285589cabfb55c92a,0x57152b7b55b34ad47567,0xfc957bb2bce55d8aae88,0xb2b091582a2c0b55fe0a],#[0x56460b1dd58c52c4dd61,0xcfc1670eb334597baca6,0x802d2e168cab43e5a0ba,0x25affad7356b36b55e5a,0xb7515b7f2db056d1eb65,0x104b8505c0f2df856f74,0xcd7294b92e5c7e2e2fd7,0xae9ed747cba225cf2ae6,0xdcb2ed917664baf55d61,0x145e6baf1e5784cbbd35,0x4be345ef0af6917aa2bd,0x7f4ebf5f5f912fc197d2,0x46981bac0a06026affbd,0x63089183fac1aa60b130,0x61c0b0d3d860ec2b4613,0x4de624b3116587f6c3b3,0x3cc64b62fc316698a4cc,0xd8f66c776639731b998d,0x249991bcc8966421b1fe,0x52329719412c9ab64b73,0x65cc32d999668caf765,0xcd4d667d332459892cbe,0xcbace3666f73371d9b14,0xc59f3ccf56678cb3ac19,0xb433da13ad060680c33f,0x8e4b4631a2cad1336880,0x68697fb4a59a486d2066,0x4d47d6a2034fe1a760d3,0xab9ed5666a94b53b1a97,0xc59adc8d6b26b3ab5889,0x335fd1af9ad7906ba9b5,0x6c8d362f1b12ad86e6c1],#[0xa406d073679db33ed962,0xa0db1e6d70b6a91b4e4d,0x1b804dbc56dcf36db1b6,0x73c5b97edc8d6e28370d,0xf5b768dbae2dd3f6e8c3,0xb6f5f37a5dbc9ede126e,0xdfce6fce37d7dbe86def,0x1e8e0c27042b814dc02c,0x9c336e17470a6b84c5c,0xb8aadc4f2e23c7105387,0x1c238d1dc62ae2d87163,0xe1724cb9145c828e3cc7,0xee5d572d1b9599ca3ce4,0xcd5ce687732ab98b9cc0,0xef9cf02e7657399b9bd9,0xc3a245d0a8e82d73f839,0x74c5ba565d222e8ea745,0xaa6753a3a909d3dee9bd,0xfeeb6e7598bac55d5c6e,0xdd878ec0a75ec3aec5d6,0xb481d9c6ecbc76453b18,0xd3b7cddb98ed8f76a93,0xd7760bba95dce6ee4c77,0xefb077bf3bcd9ddf2eed,0x154f078782e3c0a9dfda,0x5de260f1147876bc319e,0xbc7f9e382f1a578bf3c5,0x9453c9b9e4a4f22b7907,0x79799e3cbfde56ef2a67,0xcf40a79f73cf49e782f3,0xe984f49b7a453d18de84,0x539ea7af5217a7d3d34d],#[0xebd8b1ebdef5bd7ac5bd,0x7b463d9edecd4f64e7b1,0x77b7ba4bdc89edf6f6be,0xef7eb7be7bdecdef2ef,0xdf146f8717c2abe0b9f0,0xe5f1f294f92e7c7e3e2f,0x1fbe809f3a0f9b47cd1b,0x17d62beaa5f504fa667d,0xfb727dab3ece9f626fae,0x896fc247dfebef2df748,0xdf9cefcc07e4cbf1c9f,0xbf701fb32fd727ea03f4,0xf36bf945fc80fe037ef3,0x307f8a3fb89fd60fe7e7,0xeffab7fc7bfdcdfeaeff,0x8500267ffa3ff8dff8,0x416019100ac8048401d2,0xa406de02f5015e809bc0,0x8163c0a2a049b022680f,0x37481a6c0cc605ff02ee,0xf30447820ac0f6207210,0x20aaf051a8269412da08,0x199e0c6b060e82e34165,0xab41c660de506cb83474,0x483ee41e7e0f07076783,0x8f7846dc224e10c3082,0x35f098884b642516123d,0xca14810a0e84f9427021,0x42d1616270aec855d429,0x61a4300a17a10b9e85b6,0x2e8683c3356195d0c668,0x70dbf86c6c359a1a7f0d],#[0x1dcb0e9d872ac38621bb,0x861fc90f9c87afc3c8a,0x8c43fe219b1090882f44,0x88ec4469a22ff1158889,0x335898744b4624fd1220,0xb7141389eb44e9226cf1,0x62acb151d8a704528e28,0x5a022c7116068aefc56b,0xc2c5cf62e0116ce8b4e4,0xb8c31c609a2fe917ac8b,0x19688c9b463e631d118a,0x4db1a468d154678a3335,0xf636ad1b2f8d73c6aaa3,0x47116383d1bd68dd7c6d,0xe844732e395f1c888e36,0x28eedc76fe3b1b1d458,0x91eb48f46c796e3c691e,0x3f051f718fa547c8e3df,0x1f240d720399003c7f2a,0x5c8512420f20d59051c8,0x90fe487ae43b521a890b,0x293913bc894244532218,0xd9232f917948b8645752,0x248ab240291dd48e4e46,0x943649cd24bf924c491f,0xf8c96fe4b47257c929a4,0x5934c499c64c7f262392,0x279d93b5c9d124e2526d,0x1452886942a4a05e4f89,0x4e532d294e94834a3525,0xca9ea54912a2194f7ca7,0x5ba4ad36560b2ade955b],#[0x6396134afd257b12ba69,0x92d6d96984b376596d2c,0x5ccf2e3597074b7465b2,0xdde5e5f2efd9765cba92,0xdcc0a6601b2fd097d4cb,0x98974c3f261693082982,0x20798eacc712630f3160,0xd732b9993e4c8fe64473,0xe67a933ad99c34cd2665,0xd20668cb343e9a114cfe,0xa24d47669d734cf9a59c,0xd9ae54d68e6b0f35609a,0x36c49b494d9da6cb5361,0xf25376b9b9ccdc766dc1,0x5e70e138549bfb4dee66,0x4e4ce720338da9c59ce2,0xd0bce76a737d39979cad,0x119d6a4ea3274e13a549,0x13b8c9db2ced26765b3b,0x785d3bfc9df04eee6775,0x36e79693c989e38cf12a,0xcf7127b0f3d4a9e814f,0x9f90cfb0e7cf73e339f0,0x26a0054ff627f793f69,0x6d410fa06ed022a80b14,0x2841341d7a0cd505ce82,0xb32854b427ea12bd08c,0xd2d0da286994325a179d,0xa241d10c2881343e2a1,0x4572a2ab5146689cf44c,0xcd94645a309d175a8b49,0xf28e954718a36dd1a7a8],#[0x520e68ff947bfa3d1d1d,0x4c05253a923948d4a446,0x85a529d282e939d49a7a,0xb4b58a59e52c2a95854a,0x98e74c36a5fcd2f1e972,0x58a9a774d09a6665326a,0x8537fa9baf4db0a6c4d3,0xa797d3bf69d554e6da71,0x8a7f0d3ebe9f114f61,0x520bc7a82e54102a0495,0xe072208c213423c18320,0xf84f0447c1c8f423c183,0x283207249c402360d0c,0xf060f81c8e47c1f0390c,0x8307c0e4503b60b80f08,0xcf84f0447c1c8e017847,0x81602f2280c840540160,0x91ac238243a0bc0f8391,0x2c1b007821448740f83,0xe83919c121db0a07c1f,0xbc1083217c2508f07e09,0x5801c241f07232114000,0x842081c203e0842820b0,0x41f039084183e0721083,0xe07220a283be0a0f8391,0x5e0087c1b09e0f0403,0x83e0f8a0338021f06c2,0x834e1108c1f1815384e0,0x82c11e0f800391c1520f,0x270004e0aa0a080abc27,0x8e7c1f0bc001382a43e,0x58004509503b11c18408],#[0xa81d88443c3004a28100,0x4103c351407c2f86f024,0x312a1fc37812540ec400,0x82008e37c1804f020bdc,0x9fc35140802400076e1,0x2f06c3840f0d4501f08,0x903618c6f83f0216851,0x1b8a04014c6f83f020bc,0x21685102f06c480404fe,0x72100231a013c1f02f0,0xa8a0401015786a281004,0x713c3110a281004221e1,0x51406649c4f0d4501992,0xc6f83f020c9c31271fc3,0xa5c6f83f02e18200c0a5,0xbe0c00781064e1893900,0xf02637c183206c303971,0x8df07e041901206c3039,0xc81b11e181571408021,0x6c202900bc0bc098df06,0x3e0027c1b060b78009f0,0xfc082a0602f008280d8,0xaa37c1f8104e0cc551be,0x98361646f83f020c01b0,0x41569f2601c8df07e041,0x56283005e05c004f8361,0x68504e3f86d080438068,0x178392346f83f03c0343,0xf8705406b00588f07e08,0xc3039b1be0d00781b0c0,0x7c283931be0fc092207,0x83f020f87073e04c6f83],#[0x1f8107c384f044074c6f,0x6c30401c2701d072637c,0xd8190c0e6c6f83401e0,0x280d8178a0a7c3582b28,0x3f0213dc303e2ac1786b,0x3e181492243b215c6f8,0xc303e2414b8df07e05c3,0x21d073411c6f83f02139,0xc483971be0fc0b8607c3,0x1cf82245e07c198d07,0x9e0cc6e8509c0f8aa098,0x9e0f8a2440741cf81a0,0xa0a491485f03c10c6f83,0x789f072289f05e0e4303,0x20ec2f70a27c7c01e081,0x7617b851423d8206508,0x30741783222c1032841,0x391a0f86b05237c1a00f,0xc8d70a0bc7059077c0f8,0xc081d07c302cf03077c1,0x691102f06c383991be0f,0x16141f09f1546f83f021,0xc01e0b8203e13e3f82c0,0x82c016141f0a1150e82d,0x3782f03e0dc2c8d07c5f,0xdc28152a110150590764,0x642283be07c1c8df040b,0x7c1f82f02e140e83e241,0xc13c1c8d07c5c2207323,0xa0e81905980243782f03,0x4e00252c28a114178390,0xf8109bc1380046054470],#[0xc0900d0c0bc5510a37c1,0xb78009f07c268d209e0f,0xa107c222243a27c1f080,0x6781f072341f0a8890e8,0xc2680291be0fc083e181,0x8246f83e09c01178391,0x7e040868de09c02c290,0x651be0fc0d8505e3e86f,0x84691be0fc083e182784,0xe468df07e074303d1427,0x888ec85e09e0b8003e13,0x7e0782700021a1b42904,0x292095c319407a268df0,0x1071be0fc0b86e09c034,0x810d1bc138058520268,0xfc1d88b020f86d0de0fc,0xe090ef83b100e4803b41,0x33623c18391e83f84065,0xf43a0c8178e0abc27824,0xa1d0640bc851be0fc084,0xe83e1546f83b05e0427,0xe46b840643c8df07e06,0x7e040e83e141678183be,0xf07e060e83205e448df0,0x8df060c81b0f6090048d,0xf8351a0f89052033c0a,0x81f1580282f82144877c,0x28a2f03803c1a8db0816,0xd46f820656100c948768,0x741f100b01121df03e0,0x5e3829f05613c0a8df06,0xe2646f83073e060e8320],#[0xbe09c248df07e041c83,0x1603e0b0383907c1c86a,0x3546f83f03c03828271c,0x4417c0a8df060c81b101,0x201e074303214e4039d0,0x8df07e041f0c0e746f83,0xf8351b610190e1380ea,0x7c1f81b080c8605808bc,0xe1246f8307c0e4409ca3,0xe460720f8291be0c1c83,0x20f8503b237c184e07c0,0xe01c14138e13a46f83f0,0xe0b6108d1be0fc0e86,0xf8320f43783f0204346f,0x420f83a0087c1f060bd0,0x3f0213a0eb840643d004,0x41df07835c20321f06f8,0xc084f83ae1417900b027,0xf06b8505e3820c1be0f,0xa0be0f8320c1604f83be,0xa1d150bb84b0a8760f8,0x7c1f8107c32177096161,0xe0f06d84064404e03b83,0x7c0741c8c1341621df03,0xdf07e041f0e04bc1e0d0,0xe0db0a0bc809e1180ee0,0x8f836102682c43be07c1,0xac203e23a87c5019c00,0x321bc211d09e0b60f8be,0x78321a04e08f060d8160,0xb4004b1504e08f060d90,0x834003e0962032f09e0],#[0xdc23c1f0104fc14118c,0x1f0646b4110506c07c19,0x178168023e0d85e0447c,0xc0e686f83f03a001b0c2,0xf060b3c0f83a1ba001b0,0xc4283683e0c8444047c1,0x205a0fa0f8c0da0f8320,0x38007c0b60f8ac09c070,0xc3e0df07e041c83e1490,0xc16085f03e0f06b8006,0x834320bc1c8c0d90f832,0x1a1951947c148b42381d,0x3e2d83432e1014d1f16c,0x3046100470960c08829a,0x5e02103c183e1380f8,0xc230178dc0400023f061,0x9180bc1c88c3c1978370,0x44033e0e4621105e2f83,0x23108839160cb1f9180a,0x22e1bc188c05e3419f07,0x1f0bc23c183907c24190,0xc1c83e0c0e839e03608,0x816f81f08e020e41f0de,0x303205e3f834236181f0,0x41c83e1846229423e0ec,0x866c10391f8401df07c0,0xda15088ee1381a1ce02,0x170c0d86432e13c1d82b,0x103b040d8705a867c1c1,0xc183907c3386e0210406,0x67c189c046381a611c0d,0x7c041f0391408f017050],#[0x39066c231f052305be0,0x45833e0ec22110722927,0xc81c8a0741f584e020e,0x7c041f039180cd84e02,0x9e07c044e0391c08d84e,0x832e11c041c920d81181,0x80839182d83605f613c1,0xc1f039140ef08065613,0xa0fac27010722c11b09e,0x465e0ec2386822864643,0x1922040dc3011b09a148,0x8f08f076138083218208,0x40c91020643ec3685230,0x911c221da280e4470810,0x91405e0e440234241783,0xc281d8236120f832140e,0x2340bc603a0b00fb8207,0x84b0a0b0803ba1fc182c,0x2c1f142d02f0648740fb,0x1f68623440117080fac,0x450190e07608983d0ee1,0x280c8512f04687a1db08,0x343a630178a87408d84a,0xf83b04876c282f1f83f8,0xc2006a280bc1c8804783,0x83b4501f0a07508d1407,0x840736090883e1008b84,0xc041c83e17c181db040f,0xee0f8083907c4707b05,0x27080bc211607508f077,0xaa11816421840e14c102,0x7b040b108b8483e0c888],#[0x8783b07c5003e120e89,0xe6582305c04197840721,0x74c6707f0684780b8505,0x22801f0a0b0103876530,0xb0e28b808391f83f0107,0x87b09c041c8fc1c1901d,0x23e020e4705fc1c0ed,0x8108a207228a2e0f6100,0x460e8a26280c8540016,0x8d07784032b088441c8c,0x1c8dc201901db09c041c,0x441c8c08c0cf07e02288,0xe0441c8e0bd0ed8443f0,0x43e0d8407c0f2c201d20,0x11c11a0ccb8321780016,0x8a1ab0903ec170043e4a,0x7047830720f84b2f4420,0x583e485b0b407c1603e1,0x3483ec1423220e138068,0x8709c0d41f00b0da14c4,0x41f1908a0fb0449c4860,0xc3685250d20fe01a16c1,0x21141f82381a83e0160a,0xc202d70fe0f8002c06c3,0x59a14178bc000621f06,0x8b07613800392704783,0x1c11072305b06dc0c196,0x78000f43e3387b080fbc,0x3f8021a43e2a23507a1,0x3404488584d0a87c6446,0xac116101f783e000e470,0xe08607c01c300fd0a381],#[0x400ff06e1b42a111c93,0x22c2083022e180d0e49f,0xe4438000fd0b07c51218,0xc10243c1f0001f61b428,0x10f839160a21132f87c4,0xa0e08a1f0722e83b09c0,0xa8c12e281105387c3b09,0xe231f12e0c83f07c0411,0xe020c85b89401c2c9763,0xc1907e0f8082316e2783,0xc23c1840e020f87d08c7,0x8b71a0a0970641882e0d,0x8f8320fc1f07e0dc0411,0xc51701e100e41f0fa12,0x392fc1f0807c0e440b7c,0x441c0f84584105c07800,0xa20421681c8a166138a2,0x20220b42820f83e148b0,0x2881c93c218883907c,0x92613c20119c0f84701e,0x20c0d017000b228a0f83,0x405c020f8a20b638424,0x449a220e50f83e101621,0x1010785ee17c1d84d0c4,0x7c2097b0987c1909a08,0x84d05a18888fe0f84039,0x251fe000d8320ee17c1d,0x56181b0e1078061406c,0x23e0d8440fe0f80f00d,0xf0000e00f410361c20f0,0x17f08e03c001c9410780,0x841c8c08b8185b06c0c8],#[0x20f81c8889c0e684e004,0x83e1b8083e0721a84e0,0x10f839102704050be0f8,0x5545040b61082221c0,0x83c40fc0780039234270,0x8068423f614607da13c1,0x780586b0ba10b082843,0x8384107804003803005c,0x200800700600b4238607,0x243c0e110709c0342c1f,0x5e0f80686d0a03c808,0x1e00e17435842808007,0x403e1c2081000e00c017,0xc1f0760420586409e0ec,0x4410260022967c9c0867,0xdc0b420e05c0a812b0a,0x62280f85c2b848c3e00b,0x38870ae341d8a8001858,0xc0f87808e39c403b1202,0x7c2c04702e37c184070,0x86a180bc370d011c083b,0xf85e048890a99f06c2b,0x48541b0c1030270233e,0x3080e181f08e1ac1a22e,0x685103614510360801f8,0xc288c684007c20174001,0xb076181170282ae14138,0x5e2702b0c0f8382a8481,0x482a2881b0761b813850,0x10659f23c1f02b0c0f8,0x5a148033612c18122208,0x1b0ce1230f60700586e0],#[0x3e1c14d1005a864cfd14,0x960500586f07620198,0x202b8d0762386f060a82,0xd07c2400818e21c708e2,0xb8171a1001f0b409c438,0x81383702e341983e19c1,0xf081681b0400c2003e0a,0x6c2386054418db061001,0x481b0a0b414f02f0686,0x5611c3032150cf8370d,0x1f078001cd8606c4f83e,0xd86e040d878336340678,0x6af0013e405a02bc0c1c,0x114f914420782de09c08,0xc2d17a24a1688502e016,0x2240d8305ba07800d506,0x1a41ee138002a93e309f,0x301a90a83dc231293e30,0x83805e05a07800d506c,0xc1a8bd1250f40b43700b,0xe862a89287d03a1b8050,0x5624c15c2702e01a0643,0xb8490fa1b40b12198bb1,0x8030490fa074330c2182,0x1f40e8670ac486632c4b,0x9c0340e8670bc0896092,0x8290481b0c21c15826e0,0x4493e0d8180616411186,0xc30a0390f80584c280e,0x27080160405467c2008,0x160a2f07e0646a1206c4,0xa7c1f8191a8481b0c164],#[0x761781700d11a0f468c4,0x182a53e100313e0d8200,0x19c024f836168929f06c,0x36080cf8049f06c282d0,0x1c6a836080202a93e100,0xc08ac3702139c00138da,0x816487907e002881b0,0x6c361206c110f20fa182,0x606c3781d1be0f437000,0xe86080290f20fe0f8068,0x8170005327c421e41fc1,0xd0a4205609802c6d9417,0x38670a987b03802c3704,0xb0760817a04053802cf9,0x2d053c110c99f1c0e019,0x8f86b11e0c1f110bec18,0x7c183a07c2840b020580,0x46c4783b020f8808004,0x23e0c1e03e142001ab0c,0x4602f141cc8c07c18400,0x9c3415054421d052c0e,0x760815120b414a19f076,0x19c368508c43c0670420,0x4e1c11386b048560c827,0x70a055c3704c01a14138,0x6c683b1102b04c01622c,0x4d82588b1a0f86b10a1,0x3e1e09d8331a0f84036,0x1f10089c6f83f02075c3,0x504072075c6f83f02e18,0x20741f100f81c9220b42,0x7c492231b413c1f8107],#[0x5637c1781f07802c3039,0x31b217c081df060f8704,0xc2309e0e0ed8607c2022,0xe120ed8607c181d02a13,0x82cb280f8383b61b4283,0xc354a09c0b10e89f07c2,0xb01101d09d8004fd8507,0xa0f90ef04b0235470b40,0x43b45a0889f07c282c05,0x16823e17c102f02a27c9,0x81113e1381d0c354509,0x84208d14213821083545,0x707363017882345084e0,0x804f83e174318c07c1f0,0x32340e84e07c398283a2,0xf12a181d83e0dc1b8107,0x83b030494690409c0741,0x2181f1004a0e83e0c105,0x9c48d570405646f83f03,0xe050c83991a411c281d0,0x323700039b0a0f8a706,0xd90c0f8883a08bc1f82f,0x82f146ac1d033e0fc0c8,0x46e8607a1e1dd1ba1ac2,0xb0a0fa0e87a374303d0f,0x74568d0b827009280a84,0x3c16f02e083578009f2,0x105a0889f07c3d2f035,0xae01a046a83e1c4d285e,0x70025fa144f960b41621,0x5244474230a020413f82,0x46a96a6a0782aa2aa7c],#[0x9111d41e0178270007da,0x7c303f1aa0f8309e118,0x82a2a304e081e0d80681,0xc87d0c5785d0da0543d,0x1c632c578270070ac0b4,0x4b0290fa05c2e8662a33,0xc13702e09a05c2e86e00,0xa0c8cf04e0127c910e0a,0x16174f8c0f51791c41f,0x1e0027c1f1004341f04e,0x82fb0a40462444770b61,0x1f0985b08e81d0fa1bc1,0xc1d00f09e2040f060e8,0xa093e0a8508727c1f076,0x204908727c1f09c13800,0x4027c1f0e10c1049f07c,0x93e0a8508c8890ec821,0x4908727c1f082838270,0xc301df07e041cc8d07c3,0x9e3a02253e0fc0c8d07,0x461911b835041202109f,0x683e185091570aa244f8,0xc2303e154148df07e042,0xe0fc084607c302203a13,0x5ba081561533e28a091b,0x4a09c138068233e0a850,0x2c36820544704e000aa,0x1a08151083d03f04f07c,0x54484641e63782203e0,0xdc138000f00e00c00e82,0x50461f827000600a8408,0xa4f8a03c03803003a081],#[0x4744f83e198002de080f,0xc081f49f1642f00244,0xa3e88d1c149f07c1704e,0x2545f04d07c0344585d1,0xba37c1d00d0c0e74283e,0x121a1b42d81e08422283,0x2d0da16c09203fc1b00,0xe83e1f8270000e043c18,0x81e8835511587e00e0d0,0xa37c1e8607a268df07a1,0x700054382203a13c2309,0x8068623c0e8df07a1b82,0xf8307de0c8790750bc13,0xdc134368509a2b00d0c0,0xf07e0780686d0a134907,0x2f020f8268c04346f04,0xf704e01a18268ba37c18,0xa490f20fe0f4303e141,0xbc8810f50dc1081f00d,0xe00c0100109a0f8751a,0x42900e58068607c200f0,0xb2263ae19c3b837020bf,0xc6f83f03c01c3685c2a4,0x7e0f84b0c0f8209a08d,0x46b0d6041e8531020783,0x1346b02626c3d86f060f,0xc0f4570ee19c1b8107a,0xb710e0dc68ee37c1f817,0xb837020f46d0bc138018,0xc1f8170c0f45040e19c3,0x1c01801d0a042c112e37,0xe2342810238270001e0],#[0x706e207702e1b82783e0,0x850203e85e09c00c138d,0x683e0fc1f8171bc13806,0x61341f076181f05e04c,0x608c0f90ef82d0d6146f,0xbc5d1be0fc082fb0a134,0x96241f0ba1b418323120,0xb11e0c1c83e1f83e8305,0x32f060641c9746a08a1d,0x236048d588f09e08430,0x480236234183909e0f06,0x158806541ec0a1d70906,0x84281d20f6074303e141,0x909e108507360c4f84f0,0xf83b02c320e8d60c4f83,0xc1a19b02e120e8e2410c,0x13c1e86b03c14914e073,0xe874178c23f00019120e,0x51b4301f080e40910509,0x10e82f180cd0c05e1a1d,0xe0c5003e1c1481950743,0x3a13c1f12609c0c1d711,0xe122a839044e0dc0c8d0,0x84f03a0f8bd06a341983,0x5072082c1d81824a3482,0x70118e04827c1d07c225,0xa13c403ba1b41b828324,0xf038014683e1c1c83e43,0x8191b2181f120890ef83,0x105a101c8a283a057c1f,0x741e86b080c8691a8005,0xa37c0f8350c0f88c3ba3],#[0xb6100e84f2c1cd82032,0x9541cd83b0228a0aa8d2,0x390962815b090742788,0xc47837020b4a11ae0f00,0xf8706421882b84704845,0xc3820f020e7c1c8d2180,0x2909105705237c183907,0x5e05c278391b8001c83e,0xf06e101f0392051022f0,0x3923227c610de0a82c8d,0xe86e014306035e13c10,0xf40f84d0d4646a32a1f4,0xc1740e86709c008b04a1,0xfa0743319198e31990e,0xfd076108ca9f1dc23029,0xe83511c00148f0bc1140,0x447830720f8510de0c16,0x7743f83d020e41f0c86b,0x32202001af060f01f0a4,0xc3584740e87d0de0ec20,0x81c8606b447830720f05,0x92103e81b0c0f84b0613,0x4581ec2032b07a238003,0x806560ec2700e0a0b080,0xf8600e00c1603e110868,0xbc603d01fc1e8170c0,0x5a0f85033815c0f8314,0xff07a181f0a0a4c1e82,0xf84b11e0c1c83e10218,0xfe0f4303e1bc1e86052,0x4d05e0c1c83e10218290,0xc5003e140e839d040f8],#[0xb623c183907c2043b03e,0xc83e0ec0832f06280178,0x641588f060e41f0de0c1,0x10c94907f07a181f0c87,0x7207646b8314416c1f0e,0x1f11237c18a20b40f850,0x2c60680980c8d144164,0xa588d707083800390963,0x15c2420f06e238038105,0xa0d81cf003188a8910c4,0xa10282144e13c0f8391,0xde0e46b84e000e4ba0ba,0x7c28a062a21b4142006,0x3913e138803b237c1839,0x8392421223706a08258,0x1d232e11c1f00512e21c,0xca8291be0fc084d07c3c,0x41cc8df07e042703e1c1,0x7646f83f022801f0e07,0xe00ec0f00e0a0b07073,0x6a0b6138002709c3e820,0xf00b0dc17410271c0bb8,0xc6f00e0a09c270a83d03,0x1c01801e01c141384d20,0x4e138070506609c501e0,0xe00c00e82e01c14139,0x1b510a341f0a136c300f,0x2f00b09a2341e8d1f41c,0xc0f853060e41f06a2f8,0x50320e427060b7c1829b,0x882d8d6181cf0007c138,0xda106c9007546d830722],#[0xe0a3839d1b60c82900d0,0x391c48046d09e0f43581,0x48f08c0cf00b11e0f420,0x49121a13c1e86b03c001,0x201000e00c0168605360,0x3c0a8df06a181f1011b4,0x61fc1a1d07c283914407,0xae0f41e8407c0e47073,0x307c08b83f000724c8d2,0xf8307216830b6e1c4378,0xf234270390e4683907c1,0x3ae1d42700073c14270,0x8804fa37807050b32886,0xf10f20ea13c1700e0ba1,0x7c230011e20f4303e141,0xf20fa181f08c17c1e860,0x28d50c44380705144390,0xc230011e20f4303e1419,0xd08e18190ac17c1e8607,0x87706e07420321dc6f83,0xf83d08e1b0c92c75c33,0xc1c83e0c26823544e37c,0x910067838320e41b0be0,0x78307c0e44a01e0c1f03,0xc2829819e0f4303e15c2,0x720f84053e0f4358407,0x407d8124270390a80083,0x270002001c01802d0dc1,0x21341f0a4a50ed8207c,0x26d84142683e0b46f83f,0x6c204d0643129d0dc14,0xba1b8004db08268df07e],#[0x784212447039120e41f0,0x40f02c09e108403c0b02,0xd83e381d09e4820f83e1,0x3e1c8bc2025fa15c211,0x27101340ed06d11e0d4d,0x82c120a0c41688534474,0xa0bc501903c8ea5506c2,0xd0b608178e21f40f06d0,0x3e4aa4745095a0403803,0x183ed0b613830f03ec20,0x7c1d84e00268807821fc,0xc1b42d84280ee8807c0e,0x81e68109404003803005,0xdd0613827842142704b0,0x40d709a0cc104f084340,0xe440dd06609c284e0843,0x1a0781a8216138038543,0x1c0178370ba04230e1,0xe8a23c43f06d0a0bc502,0x74103e1b8682f09b2328,0x802683e181601d30e0b,0x70802683e1dc3b83703,0x643b07c1f06075c3b81f,0xf860920802691183e0f8,0xa0bc7b0f6050ef838400,0x7c3783905622c082070,0x1f07c2111119623c1839,0x322243b0841f088890ec,0x7c4090113a0a0ea1f072,0xe6c1b83b02e070684d0,0x832181160d09e1181f0a,0xe84e1826911b080b10f],#[0x160e82c288cf83c1a0e4,0x4808930860f413817116,0xb0c1981c1b0742703e20,0x8e23c1d850580bc705a0,0xc242174111f07c391111,0x22041a0a8683e1827a20,0x6020a1a13e0e83e18161,0x49151510a87c8e84f181,0xf07c302d6002320f83e1,0x70083e331210ae0816c1,0xc241f05a3b8205ae101f,0x77420391842b82e000f9,0xb6142741d180a832c1a0,0xa1ba1027c1d181682cc1,0x8283b8341c83e1416022,0xe9157080cb06d0007243,0x5c2222c1b4001c8e88a0,0x810e900c1a0f8607d07,0x5308b06a1db09a147152,0x407ce1043d00072283e1,0xd51f13c181ac120f8,0xb81fc1d824340f8615fa,0x40e2bfc1e80b0c868903,0x82d016190d0ce12c1020,0x3f83d00069c31281fc1d,0xb4003f1c1fd8407c0760,0xe4258a04003803004e1,0x8501c84b15c2382700,0x2a836185025507c1b847,0x545003e0f4111ae03601,0x2e01c22820640e4258e9,0xe00c01686e0b6009e0],#[0x8043a0b60f8bc0425010,0x7f83b03a1b8282f1b81b,0xc03e86f07c1417d811c4,0xa43e0f86c280f8218603,0xf8307c10c508703f8101,0xc202de0507c1f0801f40,0x4e0a88f88c0816c1f07,0xc1f0623f40036a3e2212,0x10c1003943e0f8508787,0x4317c1e81040e14178a,0x810390963887d03e0c1f,0x10f82d260eb83b0087e,0xc4c1d322c2542b84a056,0x76c1b83b02e070683907,0xae0ec1e0d0720f864450,0x153077c1f81c1a0f8683,0x85b0f60ec08394400f86,0xe41f0a88bc1e0d0720f,0x1be0c1c83e12c3b87b06,0x258a44b06f830720f85c,0x1016c1f2606d834400e4,0xa3c55e04e010e9102126,0x1ec2580f07622c0a2005,0xa23c43f06f07a16c082f,0xf83e101698070587c1f0,0x6c0382c3e0d8405a64b0,0xec3e282d7080fac061f1,0x38407d87c5b00e101683,0xe0d8405b87c1f07603c1,0xb000f816e1f1ac020cc3,0xc1f070330f83e0dc2182,0xe0fc1580e0dc14805b87],#[0xb60dc12971b4081000f,0xe42443ec1b82148f10f5,0x91e42a43dc2583704311,0xb608882051108d820641,0xb8321242a05b04440490,0x10888c0720bc5b048044,0x31206029603608190b03,0x448240302064846c103,0xa0c9808330c9641240b4,0xf039100eb010320e41f0,0x20e4502a0f82423c041,0xdb080e50c885644e211e,0x3f80866088790107c201,0x8207c221d6020f8307c4,0x3415b096080e08846c25,0x7c192c82a816c2582e02,0xd02243dc203e16c13010,0x833064e11c1229e02301,0x8e0914f0115c17010641,0x3284514f01708303e70,0xdc160022c290905e101d,0x1a0fb8252e0c8442443,0xb84160f91a42443dc160,0x984046241f23485487,0x101181d025c04c20a25f,0x8243e08c512f804c1032,0x25c1907608190495494d,0x8970641e0116e08c3b04,0x119873060c087f011b00,0xe024a4504687487f0110,0x82c020e4178808c0918c,0x421fc04505e083905e11],#[0x82c305c0417880cc1198,0x9c046058c06c103203a2,0xc0045860460481601d30,0x1c00608582443d03582,0x8984c0043f808c61280b,0x41181203a4a50f8c0480,0x11894b01c0060a808a95,0x90f1409011c0043cc2f0,0xaf01252202310d80408,0x721819b080e50e88074,0xf80880fb431290c51701,0xa181f10fe02183e30443,0x81d14160a012e8445105,0x517010722019308c041c,0x3a4a50f8bc041184844,0x45252c04c2501112a815,0xe0811860540890f30bc0,0x60640890fe02e105e02,0xfa05b044404b0540019,0xa00800480c87ec11100d,0x1fb05400480887d41d82,0x818c10903f41e0630822,0x1fa0ec150043e3c0fd07,0x483c03d03582112aa118,0xccbe061741900121818,0x5a0cc1606052201e01fa,0xf011d0603f030ba0e118,0x6c7c4b9110642029040,0x8eb087060784232e140d,0x21210360ec0d07c8410,0xd07c82120bb060641817,0x24202817421208360ec0],#[0x60002e040423e41581e8,0xe2907207a080b8101741,0x22040306e04183b0301,0x30a04e1015017022182c,0x205226020520bc320e04,0x4006052081c84c1d81c8,0x1144c441c8a04346040,0x83076064082080f182cf,0x2203c52040b008810100,0xe41e418148b408410230,0xa4209c0f814906102d83,0x39082c83e453618409c0,0xa102d061382db860f808,0x99f4240d8333f810212f,0x460ccfe040cc0836c081,0x8e04b0661b810a67f020,0x99fc081a12b061583040,0x209025830ac1a040ac1,0x810c1910e04358306c1a,0x24168c370205e284230f,0x810c0bf02502302c0854,0x9c70204b020840b4443,0x50158e0ac7204090958e,0x6c199f108048886041,0x408986e041e04045104,0x6c190f0e0958324e1d83,0x8870216c18360c878481,0x44c3702064204230e60c,0x10e042832a0460581080,0xe0ac702e381024044429,0x244404b1c0d8e0502d8,0x2a134848c6b831442e02],#[0x8482d0360d0938105418,0x70221e105a05bc081b08,0xf93e100f93e149f6081,0x40d4082aa081c1e01e10,0x41508a7e8204a0d4fd0,0x9f01e2a8105410d50598,0x629f034040406004141a,0x6a7c2d0271140836081,0x4040206c0a9f04e04835,0x7e811406681054c00402,0x81520fd021833054c110,0x8205a0d4fd040c0805a0,0x820a1341884134185a0c,0xb41a0f0882e8341e1c12,0x362ec5589384118e3120,0x568268384e2319624c30,0x8303c03c390841341863,0xa0c07e9f0e07e8353e1e,0x68303c03c381fa0d4f87,0x84341b0093e2e8313e1,0x7c9f0d8268341f27c404,0x3c03c3d0603f4f87a0d0,0x9010c082d8e40816830,0x702816c705638133e05c,0x2027c40240330001012c,0x21aa8490809f11c1a124,0xd1c13046240d836240d8,0x1c1007d1c1007d1c1104,0x3c406c0e052201687d,0x800f104fc10098081202,0x24040205404822020cc0,0x808710603c510c0d820],#[0x4e183033e0400788048,0xe4fb00170903608cf812,0x44102d8313e291202160,0xc9f0d8258301f27c4224,0x4f912020025800b60c07,0x60818d52214090289f16,0xc0130001e249f041749f,0x293e0498206048080527,0x4043d0410603c693e040,0x805808986b0685450240,0x1982052201a02261b820,0x888685b06608878a08ec,0x230e60c42a151ac1f040,0x84a08461cc1f04142384,0xc0f8402c0440a98607c2,0x30d812c083e1a0883a70,0x81d090440b03e0c2790f,0x4141f411078184f022e1,0x411034181a0220f8c370,0xb6041e0a138c303e0c1f,0x168571c138e042701110,0xb4458c6b8308e2b8ee08,0x505b411c160008c0f860,0x55c0880a44d18d706128,0x5215c160007c302910a8,0x7b8182a1c8507c102d04,0x1fc11c08643dc08460c8,0xc0b81453c10383a0f822,0x8842084f8160220f8407,0xc0c0421e1384303e100,0xf8220e9c2c151817a129,0xf837056064303e106a89],#[0x60f808b8507424110740,0x8c8db06078411b60c210,0x8e044823236c1841120,0x4252e0c2509f130010fe,0xb0003e186a92942a27c,0x821ac2a150c2302d90ce,0x7f04702183f704a181f0,0xe8a0f80687d14183e048,0x101a22003e4f8840b43,0x9010842f0013e280fe0,0x278c0fa0b386e010445,0x440a8c0f84f89a01fc0,0x56088a27e0b283e01,0xf02c0478009f144fc16e,0x3c620ca041501a81e284,0x40405094a0c4101053e0,0x54068078aa7c4102c03,0x4585806740b04124129f,0x61b800835491681e0047,0x860f98120fd02203e41f,0xc183e09b618307c83f40,0xe0016827386102970009,0x4813cc5d8900fd072186,0xa83a13f059c2e83e0104,0x807e83705c02434811c6,0xc0c0b08670bc00088a27,0xc23d072088109c028ad0,0x16084a2f45689700b042,0x20ba0e07a9f1543a8302,0x1070ba0e4101e01e3410,0x2b1c632c55c170070a30,0x27c585207741c9f608],#[0x3e0127c8c8c83e82e83e,0x283e0027ec28c3548e68,0xe1e8360483e4f8812021,0x82ba0f8069f1341a0f93,0xc203ca1d41d82e016146,0xf102683dd07a7c401ea7,0xf504040507ba0c8169,0x1781e50ea0d410da0c0f,0x942e146d060780786134,0x82902040408e10443f00,0x3486d03c001d03e14100,0x228d513f2178003a41e,0x1d0bc001305c001f00fd,0x3f4083a1102582059c00,0x851b8002907c0e844220,0xf00f1823887107c0020d,0xd0158e080d486103c001,0x944a44f8ae0511e820,0xd5e000b44fb1515c1f0,0xc188d706e07800480843,0x808e1403d8e0c04c8630,0x823682054199f01e2080,0xe0c16d8690ae0b8003e1,0x382e01a1f47072178003,0x87d1c1102d0fa383d0fa,0x4105453411c1a9f0942e,0x45064168c8a54f81122b,0xd2080760c890750e1004,0x114281da08181907c141,0x8313e0683135236c181e,0x3e4f8760d8100f93e25,0x3b35416c9f033c106b06],#[0x6aa0513e1885b0281830,0xec9f1a4f820ea4fb020c,0x7f04142302a2053541,0x3464f81560424d193e00,0xf8393e082301e20b8009,0x80e9c128607c2485e000,0x2f0090a290fd0bc004f8,0x7c290f13e118302a2194,0x2e000f84045a1b42b000,0x2040f8207c083e042358,0x1ee04308c1001f060f81,0x4310207c180f70217000,0x7b81141f020758003e0d,0xb4170030c2887107c000,0x7c18530800f8303521,0xb8209a6181f581182984,0x1f83c05e6081d3861c07,0x1ee04209a1001f06134,0xf80029b02184d0800f83,0x608dc001f061190e83e0,0xc308e21c41f00083614,0x85b02201a7041009310e,0x100f05f609c08811807b,0x868024304f064200f702,0xd01190c0f8506521819,0x1208b84b020f01c8a0e4,0x3e8220f037056064303e,0x41c1f060f808b8407820,0x1b60ec084f0820e4708d,0x4072236c1d810842c119,0x11090330a08c8db06104,0x292340fc442ae11c103d],#[0x101da0ae0b0003e181f0,0x42d02c13c235c1847181,0x7d1414867058002303e1,0x3e430688c0d30090c268,0x81141481a023218413c0,0xd384022189e01ee0a434,0x240410d08f41c820c0,0x4a3344a860612d43a83a,0xc08582101489ed06430,0x8303c03c4d06e10250ea,0x3b1c632c55c138415c26,0xc25841052a1d41d00108,0x2053a048c8fa0f4fc190,0xa83b05610513c47341d8,0x20e45d06078078607943,0x601a041c8a08341b00d0,0xa410812820b840c11683,0x8002789001829825020c,0x481020203250c0cc3a00,0x8304e072a181f0808041,0x22204e07206b40a0007,0x45d020f01f060f81cc1a,0xf01c8486ac26810780e,0xfd02198207c03f4088,0xf06b05a054303e101f,0xb080f04044816c128140,0x30452041f03c101f01a,0x5a4308101e284a08361,0x6002002400609638107c,0x390962e0005216820641,0x1381e000b4511ae0f800,0x724223703a081c8888d4],#[0x16c4f08d706e042d0470,0x8390c46b8370212c210a,0xa0cc3065a081987075c0,0x258e0804c8630c183223,0x880400784e1003d8e0dc,0xc1687d1c101001fa09c0,0x4860b40e83e0322007d1,0x20e4305a0f82c00e041,0x8281d508181507c16847,0x7846d83b0216c238391e,0x29081c89e11b60c0b0a2,0xe0c1c84b100e03e08230,0x5057040f857020b4211a,0xa0674208a12800408a43,0x8390c16a8483a182d03,0x16e86d08c001f0ba11c,0xb45101de0aa13806862,0x401440f830800f8207c,0x3e0f4268207c184007c1,0x181690da08c308477410,0x34635c1b00154268207c,0x7b810882a0f70218472,0x96283991b60d8004b14,0x426000b4291b60d80039,0x880e111e0160466000b,0x416816d84838c00505a,0x70741f040741f04e081f,0xf8143a0f820440a6c08,0x44012e10207c876c206,0x810c0b382080800f3056,0xe042072e12c08603cc25,0x1d822182c03c108301e],#[0x9141f5351548e84f1a0f,0x23a29201349548e84f14,0xd020e452442692a84f,0x301c601a041c880a8063,0x40341e81ba0f40a1109c,0x9e441e81ba0f408a72,0xd0784840d119a0f40b0,0xc20f07a06e83d022a890,0x3020780e60f40dd07a06,0x290821810600e0840200,0xb04120e074102c10230,0x2876414201c48381d04,0x143b2081c8811911315b,0x820ea82160eb810721d8,0x8215805810581890b0a8,0x482cb02201602120b802,0xa61430126124207c002,0x611f0dc183423e18099,0x90a6143c00e041606556,0xc8f860fdc1b0023e2016,0x83e12c501ee0422aa83,0xb0007307c258a0e6c1b0,0xec00168707d8002d0ec1,0x5a0880e111e0107c783,0x430b40b6c24226002c55,0xe541701064201c05960,0x82a081cd01602600190a,0xe4584a02c04c00391380,0xc0bc0487911140cf0121,0xf0f87c0cc0039c3e200c,0xf178198007387c421fc0,0x10fc3e281d309c0c87e1],#[0x11b8360447c4041c0cc0,0x9210c32aa88d8491f11,0xe8103909628430521023,0x48d0fb02a040b4570687,0xaa0b40e90922107f810e,0x6424841c1e8023e26868,0x8042aac274011f90a614,0xa47c4cc2011c1a2323f0,0x18a970a184932a10c32a,0x2a322205b075c2580142,0xd708204d065075c23023,0x11050b075810a13816c1,0x15419c0a0b6c020c1910,0x7040c82708e081983210,0x1f0887016c197096005,0xb6c0419708238470560,0x80f1404d8390147d400a,0x8f8103041816b072028f,0x100a105a3e0454218412,0x1d433c15400947c08984,0x136c10320c26e1d0641a,0x85905aa00343a8654006,0xa867405841026e1d0641,0xa04741c82c3e03c509,0x70f8191f0f809104040c,0x60140080740b384b0195,0x787c08182b00261f012,0x8261f3086003c3e041c1,0x20e11c1079470f80070,0x1ee102704e102020e082,0x61f004e0030]]
set_option maxRecDepth 16000 in
def g251H8 := limbs80 #[#[0x306810161700010342c,0x1c1089800810300000,0x4480604014000910000,0xd020000011808263e028,0x30283000020000806000,0x8110186c10001a8200a0,0xc0800058000a030c8000,0x40009098a40c23000c,0xb02c08084702c220902,0x4060000c540884cbc16,0x5203050f482013001c1e,0x6420020c800020f00040,0xd8700e2004800000d090,0x2838320b058002c052,0x6500113c020f038a0940,0x3802000209e24058280,0x80c045b0004802240b80,0xb87804050012c00431a,0x10701c061b368101c01,0x6100f00824020700c1a,0x6814162203000170480c,0x182028050700022029b0,0xc1902018115100852060,0x140c01c0e012b07c582,0xc480105004fa10121580,0x83c4c240001c126a0001,0x895812582b874340712,0x520b000065a0f010220a,0x1e03398001c020080c98,0xe93c781327864410f048,0xbfcb782740400623a008,0x167bb09d37ac6edd25a8],#[0x3b4560477a0330100002,0xaa0000a064528809732a,0x6e7b22e35bb166ad8ac0,0x82b23d12698f9badaab7,0xe2758000014d98000814,0xd505047a932b23c00079,0xc379c000000012440965,0x9c64ddb20ced4ca35c21,0x58be9ee80e6000038372,0xd2418e380000722f2541,0x821482487c0000000c33,0x11fb15d3088f84d0a0d0,0x284400000000ba0c,0x430b2604000680f000,0x89b450ac3b8000000000,0x98aa3ce498c1e3bc0001,0x27604ce71d2cfa4dbd04,0x9a9166b34fa68821de2,0xfc211168e48e190e0001,0xc5a0fb319000018aee4d,0xdc89ec60e0001c7ce9,0xfe6e09427a8873a304a1,0xda641360c450939d281a,0xd7a513251cdc327cbd42,0x5c8e3d5515b49a27c146,0x10049349c783beabb02c,0x44a2a99434a066400001,0x1abad936e0b6000147a5,0x25837d17540001530000,0x43de945000133eb885f0,0x2f16b04e355b25faa7a9,0xe3fa668dd4b0f0770f],#[0xcd7cd98000160bf2bd80,0x8c58126c207198a88310,0xca3c2000144b506cf9f,0xd3f024ff36e35c40b1e7,0xff408c0a6b0263c92752,0x70fb422a6868c9568f42,0xc9cc0047295e2c129f61,0xa000397769e3a0cb6205,0x65f874b2e91836b14f3b,0x4868000e3e2000000052,0xdd369847bd0095202a85,0x13b5f582e4d618000519,0x14b000000031225a,0x7002a0a72d48438d0814,0xf33f647781b0000e0b,0xf36dd1a2e14000000000,0x812f2859d8fd00000003,0x5e55bf22d547ac2ecb15,0xbf005f824845a4c6e01,0x600032be1abd93e601ba,0xd9a32c7551ee1fab7dc6,0x5314280d1e6c2eb06fd2,0x64ac6110000092522b91,0xa2718ac1e85246c2c344,0x27ca2258614000389be2,0x804e20685c3ca42a67d7,0xc99524f6b00005859edb,0x6316fd1516bc4ced2,0x393e1ec11a9100000000,0x8b1b1ba97c00072e7144,0x14f5cf04d4e000351efd,0x182f76d37a3eb620a2ca],#[0xf5a617165bb230000000,0xe3c19dff9aa098e803aa,0xc1c410664d64e2224b4f,0x79057cb16ff288898c28,0x4f38000e101b8f508e45,0x4ebaa066867e54a19691,0x938a187666d0ef8992af,0xceb95455cfeabcd8d848,0x3ab30428309ac22b95cb,0xe4e841159e42d6cd9dcc,0x50d414ce46290f952324,0x809cc000206d486053b2,0xb2910b690e6e5d2a6e06,0x8c98adbc5b8228401abd,0xaea1800020fb035a0000,0xd2ece155bcca17a8ff0a,0xc68800021f40003d3418,0x47af2636a2f8e936896a,0x504f4c2980000000bad,0x72dfdb7e1360038d63b6,0x118711308000a9380701,0xd828ebd34c0806990b09,0x10fab574ad9c3528f11,0xe0000986800011c4b19f,0xfc09a8105dd60fe3e31d,0x55c22caa3f6d3fa4ed7a,0x34548802aa024b732686,0xb77030fbddeea1e2aa23,0x8fa1a32b4eba430779e4,0x26177d0e490222752ba0,0xdc43980001e1a4a29f26,0x1d8c4a59dc],#[0xcab207186a941d20000,0x20574a900003986c46,0xd33367b0000000000000,0x6e33c00008f23c6dc128,0xd28f36334dfa0374b7,0x47c3aff6bc0018000000,0x312980000000a199,0x392537e6d397b70e5000,0xed9c240563147dfcaff0,0x1e0ca4b2f4b821dabbc0,0x9205c1a370ffc983000,0xd2c28011259f75f45100,0xceb60000691604660001,0x131477a4800f6828b807,0x900adc78300c79880839,0x35701161fc000102ad,0xc8449da0a1cbb8000000,0x50db01341dc000000018,0xd26ea6cf7abf3b9a2a1e,0x769989e5200001c2dd3e,0x5586a6a62eb415d41ee8,0x46a4e87b422b5b800003,0x6499f60003d76b44bf91,0x6390625afb45ee555b8,0xcb74606d0000a2c80001,0x480ead053cb8ba2af08,0x4d5fb04d203874fa38ba,0x1e9c1b32eaf95ba4c691,0x5430869a2290b79f802d,0x934f85e101b993e615d1,0xf74f2cff4afeb1d82380,0xa9d0966649952c867915],#[0x878fa0a7c5a64ef0c889,0x7246b86ce9bc162545f0,0xfe10670e0b0c8bbf1a,0x91e71cf22a7c8b457480,0x25bc784efcc72d621049,0x607b20e8db6d43255621,0xc2481e5a3add1f5c0eaa,0xae42210000be2de634,0xd4056c220d81fc074000,0x55a000009743c7f08,0x2d207e81de8b33deea8c,0x6c439ce5e341c2aa9031,0x53ab00fb44cc2000009,0xfabc94fd0000d32fa3a9,0x819c3c149c26880330f,0x8840000c3f2000085e3a,0xfe7c090a293f0001c5bb,0x5ca964639c05a58e1753,0x50382dee150571b1457a,0x745c94549242d317a0a8,0x420b5440540004d5a414,0xcdf12548b0a23784638,0x166980000cdd0000c226,0x1206a0383a0e70f,0x1730000305376faefc80,0xc0001d3ec017241e01bd,0x23e50a04f7559201c217,0x487d577a58ad33cd87b9,0xcc32c8182cbdb15ac9ca,0xdd7a7b8b884a4c28c059,0xe610958d5aac59dc7e08,0xd55b8a80c1ac00012244],#[0x1962abb174293c29d298,0x8a7fc01b5eecb5841da2,0xc8501c2b60863afe82e2,0xbacb4f446fb888aa7161,0x843a14d1567594ee64c6,0x94781a39416f484334a2,0xc18cd8e0b00004405eca,0xc460232304700c00029,0x600000005cff92d40003,0x74a5a8591ec935176441,0x8480869f5c78b9746f22,0x7c62bc93a105eb5a0818,0x7814f3586051ca8b7701,0xd92a52450534182bad5,0x4968daabb1cb93aab695,0x2c5623e9b14ab803a700,0x890b06a6117a1f08db0e,0x171ae449788a297210d9,0x2d01e8e6546b1da18c4f,0x582e918412be3a313e59,0x4a0d2114103c919291e,0x451025c0cc108809f000,0xd2a5ae1192028a2d060c,0x7962bb7dc22c1ac5836f,0x5bc2b62107d77ea34bbb,0x434299a4962e631c2a12,0x8447aeb6207263881762,0x5c13d6d06b01e38e4057,0x8d7000085a4c9310acfc,0xc50f30611d9726107ca,0x7ec812a3584c38000000,0xf71c4845dce743aecdcd],#[0x58309aa1d21e24950116,0x16c30984f909a0000390,0xc52e3011d3e230c27a38,0x644aba70292e00018a56,0x56c328c018429a28e24f,0x885630c055e0002d4481,0x20b400005ea00000000,0xe8d389ae5668000a08,0x8bc89b1e420f6e800000,0x5ab400015706,0x61445e0000100200c000,0x5620cbe2d77984a34630,0xf578b14a418e00003656,0x7dd04e6bc56cbece2323,0xe2800002b9904ceca219,0xee301a6b8dc200006570,0xf3b03d2729285b8ebb4e,0x1f4454266c,0x14a60083a24da0c60000,0x1433903af4a276ae095e,0xcb9ba768257232b56325,0x6f8340358642039a2b0b,0xb340140f912e62,0x79dbd41a00010bf80,0xe46d400061c221e0a318,0xb125742990ea1796b609,0x6b83afb14bd607ea86e8,0x800014cc0dd3000083fc,0x5d20b868ded3fa1aac33,0x37ec84e05a0c1fb45042,0x1a99c2379ad753720002,0xd6834000008ba6104435],#[0xd1130d813d0056a1131c,0xaa95d265681132294a35,0x58055deb2cee7282072d,0xd22b12f652f87b2a3328,0x93c860623dc]]
set_option maxRecDepth 16000 in
def g251D9 := limbs80 #[#[0xee96258110e4d6554d62,0xfa94250120f555354510,0xcef7658920f695254120,0xee96258140f395454140,0xced7658940eb96458140,0xee962581509ef825d540,0xe6d6558950e796558150,0xeeb8058960ced7658950,0xece5358960ecd5358960,0xcef7558960cef7458960,0xf555354521e5d6554d60,0xe6d6558951e756558551,0xe5d6554d629dd85dcd61,0xe6f7559562aef8059562,0xff14154110ff12154110,0xf795254110ff16154110,0xfea6254110fe96254110,0xdfb7254110df97254110,0xdf97454110f795454110,0xf796554110dfb7454110,0xdfb7654110df97654110,0xbfb8654110bf98654110,0xff14158110ff12158110,0xef96258110ff15158110,0xdf97458110ef96458110,0xef96558110dfb7458110,0xbfb8558110dfb7558110,0xfe56248510fe55248510,0xdf57448510fd55348510,0xbf58448510df77448510,0xdf77548510df57548510,0xbf58648510bf58548510],#[0xfe66250510fe56250510,0xfd55350510df77250510,0xdf57550510fd65350510,0xdf57650510df77550510,0xfe56254510df77650510,0xdf57254510fe66254510,0xbf78254510df77254510,0xdf77454510df57454510,0xf756554510bf78454510,0xdf77654510df57654510,0xbf78654510bf58654510,0xdf77458510df57458510,0xdf77558510ef56558510,0x9fd8750910bfb8050910,0xded7258910ded7254910,0x9fd8758910def7258910,0xeed6458910fe58158910,0xdef7458910ded7458910,0xdef7558910eed6558910,0xdee8758910ded8758910,0xdef7498910ded7498910,0xddd535c910def7598910,0x9ff855c9109ff845c910,0xddd53dc9109ff865c910,0x9fd85dc9109fd84dc910,0xddd7454d109fd86dc910,0xddd7494d10ddf7454d10,0x9fd8759110ddf7494d10,0x9ff855d1109ff825d110,0x9fd82dd1109ff865d110,0x9fd86dd1109fd85dd110,0x9ff8759510cfd7659510],#[0x9ff845d5109ff825d510,0x9fd84dd5109fd82dd510,0x9ff825d9109fd86dd510,0x9ff855d9109ff845d910,0x9fd84dd9109fd82dd910,0xfe96250120fe95250120,0xfda5350120fd95350120,0xfb96450120fb95450120,0xdfb7550120df97550120,0xbfb8550120bf98550120,0xdfb7650120df97650120,0xfe94254120dfb7154120,0xf795454120fe96254120,0xdfb7454120df97454120,0xf796554120bfb8454120,0xdfb7654120df97654120,0xbdf8358520f5d5354520,0xded62dc520ded52dc520,0x9fd84dc520ddd53dc520,0x9fd86dc5209fd85dc520,0xfce5350920fcd5350920,0xdef7550920ded7550920,0xdef7650920ded7650920,0xded7454920f6d5454920,0xded7654920def7454920,0xbed8654920def7654920,0xfce5358920fcd5358920,0xded7458920eed6458920,0xbef8458920def7458920,0xded7558920eed6558920,0xbef8558920def7558920,0xddf7454d20ddd7454d20],#[0xddd7654d20f5d6554d20,0xddd7494d20ddf7654d20,0xddd7694d20ddf7494d20,0xd7d7555120ddf7694d20,0xcfd76591209fd8755120,0x9ff815d1209fd8759120,0x9ff865d1209ff855d120,0x9fd85dd1209fd81dd120,0xcfd76595209fd86dd120,0x9ff815d5209fd8759520,0x9ff865d5209ff845d520,0x9fd84dd5209fd81dd520,0x9ff815d9209fd86dd520,0x9ff855d9209ff845d920,0x9fd84dd9209fd81dd920,0x9fd85dc9309fd85dd920,0x9fd82dd5309fd85dd130,0xdfb71541409fd84dd530,0xfe96254140f795254140,0xdfb7254140fea6254140,0xfb96454140bfb8254140,0xdf97654140f796554140,0xbf98654140dfb7654140,0xdfb7158140bfb8654140,0xbfb8258140ef96258140,0xfda5358140fd95358140,0xdf97558140ef96558140,0xbfb8558140dfb7558140,0xf5d5354540def7248540,0xded62dc540bdf8358540,0x9fd82dc540dee62dc540,0xdde53dc540ddd53dc540],#[0x9fd86dc5409fd85dc540,0xdef7258940d7d7554940,0xfe98058940cfd7658940,0xfce5358940fcd5358940,0xded7558940eed6558940,0xeed7658940def7558940,0xdee8758940ded8758940,0xfce5398940fcd5398940,0xdef7598940ded7598940,0xddd53dc9409fd81dc940,0x9fd85dc940dde53dc940,0xf5d6554d409fd86dc940,0xddf7654d40ddd7654d40,0xddf7694d40ddd7694d40,0xcfd7659540d7d7559540,0x9ff87595409fd8759540,0x9ff815d540bef825d540,0xdef825d540dec825d540,0x9ff865d5409ff825d540,0x9fd82dd5409fd81dd540,0x9ff815d9409fd86dd540,0x9ff855d9409ff825d940,0x9fd82dd9409fd81dd940,0xdfb71581509fd85dd940,0xf795258150bfb8158150,0xbfb8258150ef96258150,0xef96458150f795458150,0xbfb8458150dfb7458150,0xbdf8358550f6d5248550,0xded62dc550e7d6558550,0x9fd82dc550dee62dc550,0xd7d65dc5509fd84dc550],#[0xf6d62549509fd86dc550,0xb7d8654950d7f7454950,0xe7d6558950def7258950,0xfe98058950cfd7658950,0xeed6458950f6d5458950,0xf6d8558950def7458950,0xded8758950eed7658950,0xf6d5498950dee8758950,0x9fd81dc950def7498950,0x9fd84dc950d7d54dc950,0xd7d76551509fd86dc950,0xe7d6559150d7f7655150,0xbef825d150cfd7659150,0x9fd82dd1509fd81dd150,0x9fd86dd150d7d65dd150,0xb7f8259550f7b8059550,0xbfb805d950b7f8459550,0x9ff815d950dfb805d950,0x9ff845d9509ff825d950,0x9fd84dd9509fd82dd950,0xeed6254560eed6248560,0xeed625c560e7d6554560,0x9fd84dc5609fd82dc560,0x9fd85dc560cfd65dc560,0xafd8654960eed6254960,0xede5358960edd5358960,0xaff8458960cff7458960,0xaff8558960cff7558960,0xeef8158960eed8158960,0xeed8458960eed7458960,0xeed7558960eef8458960,0xeef8558960eed8558960],#[0xddd53dc9609fd81dc960,0xcfd64dc960dde53dc960,0xcfd65dc9609fd84dc960,0xedd6454d609fd85dc960,0xedd6494d60ddf7454d60,0xcff7559160ddf7494d60,0x9fd82dd1609fd81dd160,0x9fd85dd160cfd65dd160,0xaff8259560efb8059560,0xbfb805d560aff8459560,0x9fd82dd5609fd81dd560,0xbf780545219fd84dd560,0xf756554521fe56254521,0xded7654921df57654521,0xeed6558921bed8654921,0xcfd7659521bef8558921,0x9ff805d9219ff805d521,0xdf561dc1519ff855d921,0xdee62dc151ded62dc151,0x9fd84dc1519fd82dc151,0x9fd86dc151d7d65dc151,0xe7d6558951def7258951,0xdee8758951fe58158951,0x9fd86dc9519fd80dc951,0x9ff825d9519ff805d951,0xef78159561ddf7354961,0xbef8158952bef8058952,0x9ff815d9529ff805d952,0xddd53dc1629fd81dc162,0x9fd84dc162dde53dc162,0x9fd85dc162cfd65dc162,0xcfd65dc5629fd80dc562],#[0xaff80595629fd85dc562,0x9fd81dd5629fd80dd562,0xfcd535c162bef815c162,0xded745c162fce535c162,0xbef845c162def745c162,0xded755c162eed655c162,0xbef855c162def755c162,0xbed81dc162eef865c162,0xfce53dc162fcd53dc162,0xeed65dc162bed84dc162,0xbed85dc162ded75dc162,0xeed655c562bef805c562,0xdef755c562ded755c562,0xbed80dc562bef855c562,0xded75dc562eed65dc562,0xeed8059562bed85dc562,0xeed8159562eef8059562,0xbef805d562eef8159562,0xbed80dd562bef815d562,0x9fd82dc153bed81dd562,0x9fd80dc9539fd84dc153,0xbdd84dc153bdd82dc153,0xf5d8059553bdd80dc953,0xf5d8259553f5f8059553,0x9fd81dc165f5f8259553,0x9fd84dc1659fd82dc165,0x9fd82dc5659fd80dc565,0x9fd81dc9659fd80dc965,0xff96254110ff94254110,0xff96454110ff98254110,0xff98654110ff98454110,0xff95258110ff94258110],#[0xff95458110ff98258110,0xff98558110ff98458110,0xff55250510ff56448510,0xff54254510ff56250510,0xff56454510ff56254510,0xff55258510ff54258510,0xfed5250910ff55458510,0xfdd5350910fed6250910,0xdfd7550910fbd5450910,0xbfd8550910dff7550910,0xdfd7650910bff8550910,0xbfd8650910dff7650910,0xfed6254910bff8650910,0xdfd7454910f7d5454910,0xdfd7654910dff7454910,0xbfd8654910dff7654910,0xdfd7458910efd6458910,0xbff8458910dff7458910,0xdff7558910efd6558910,0xfed5458910bff8558910,0xfef8458910fed8458910,0xfef8558910fed8558910,0xdfd645c910fed5498910,0xdfd65dc910dfd64dc910,0xbff8255110ff58155110,0xf7d6555110fbd6455110,0xdff7655110dfd7655110,0xbff8655110bfd8655110,0xdfe8755110dfd8755110,0xbff8259110ff58159110,0xdff7559110efd6559110,0xdfd8759110bff8559110],#[0xbff825d110dfe8759110,0xdfd65dd110dff825d110,0xbff845d510bff825d510,0xff96150120ff95150120,0xff95350120ff98150120,0xff96550120ff96350120,0xff96154120ff98650120,0xff94354120ff98154120,0xff98354120ff96354120,0xff98654120ff96454120,0xfed4254520ff56154520,0xdfd7454520fed6254520,0xbff8454520dff7454520,0xdfd7654520f7d6554520,0xbfd8654520dff7654520,0xfed4258520bff8654520,0xdfd7458520fed5258520,0xefd6558520dff7458520,0xdff7558520dfd7558520,0xfed5350920dfd64dc520,0xfed6550920fed6350920,0xfed6354920fed4354920,0xdfd7550d20fed6454920,0xdff7454d20dfd7454d20,0xfdd6454d20bff8454d20,0xfdd6494d20fdf8454d20,0xdff7458d20dfd7458d20,0xdff7558d20dfd7558d20,0xf7d6555120fbd6455120,0xbff8159120bfd8655120,0xefd6559120fed8259120,0xdff7559120dfd7559120],#[0xdfd8759120bff8559120,0xdfd655d120dfe8759120,0xbff8159520dfd65dd120,0xbff8459520fed8259520,0xdfe8759520dfd8759520,0xdff815d920bff815d920,0xbff8255130f7d5454930,0xff93154140dfe8755130,0xff97154140ff96154140,0xff96354140ff98154140,0xff98354140ff97354140,0xff98654140ff97654140,0xff95158140ff92158140,0xff98158140ff97158140,0xff97258140ff95258140,0xff97558140ff98258140,0xdfd7648540ff98558140,0xdff754c540dfd754c540,0xff57154540ff56154540,0xfee6254540fed6254540,0xf7d6554540dff7254540,0xdff7654540dfd7654540,0xbff8654540bfd8654540,0xbff8754540bfd8754540,0xdff7258540ff57158540,0xdfd7558540efd6558540,0xbfd8758540dff7558540,0xfee625c540fed625c540,0xfdd535c540dfd725c540,0xdfd755c540fde535c540,0xdfd765c540bff855c540,0xdfd7654940bff865c540],#[0xfef8158940bff8158940,0xdfd53dc940dfd765c940,0xdfd65dc940dfd63dc940,0xfdd7654d40bff8754d40,0xfdd7694d40fdf8754d40,0xdff7558d40dfd7558d40,0xff98059540dfd755cd40,0xf7d7559540bff8159540,0xdfd8759540efd7659540,0xdfe8759540bfd8759540,0xdfd765d540bff8759540,0xdfd835d540dfd815d540,0xbff815d940dfd865d540,0xdfd815d940bff855d940,0xdfd825d940dff815d940,0xdfd855d940dff825d940,0xff92158150dff855d940,0xff98158150ff97158150,0xff98258150ff97258150,0xff98458150ff97458150,0xdfd7648550f7d6548550,0xdff744c550f7d544c550,0xf7d5258550ff57158550,0xf7d5458550dff7258550,0xbfd8758550dff7458550,0xfed625c550f7d525c550,0xdfd725c550fee625c550,0xdfd745c550f7d545c550,0xf7d655c550bff845c550,0xbff865c550dfd765c550,0xf7d6354950dfd64dc550,0xf7d6454950f7d7354950],#[0xbff8158950f7d7654950,0xdfd735c950fef8158950,0xdfd765c950f7d655c950,0xdfd64dc950dfd63dc950,0xdff7458d50f7d5458d50,0xdfd745cd50f7d545cd50,0xf7d7655150bff845cd50,0xbff8159150ff98059150,0xf7d8559150fbd7459150,0xdfd8759150efd7659150,0xdfe8759150bfd8759150,0xf7d655d150bff8759150,0xf7d8159550dfd765d150,0xf7d8259550f7f8159550,0xf7d8459550f7f8259550,0xffb805d950f7f8459550,0xbff845d950bff815d950,0xdff815d950dfd815d950,0xdff825d950dfd825d950,0xdff845d950dfd845d950,0xfed5248560ff55148560,0xdff7448560efd6448560,0xdff7548560efd6548560,0xff57154560bfd8748560,0xdff7254560efd6254560,0xefd6454560bff8254560,0xbff8454560dff7454560,0xefd625c560bff8754560,0xefd645c560dfd725c560,0xefd655c560dfd745c560,0xdfd52dc560dfd755c560,0xefd6454960fed7254960],#[0xbfd8754960dff7454960,0xefd7558960efd7458960,0xfdd535c960bff815c960,0xefd645c960fde535c960,0xbff845c960dfd745c960,0xdfd755c960efd655c960,0xfdd7454d60bff855c960,0xefd7559160fdd7494d60,0xbff825d160bff815d160,0xdfd755d160efd655d160,0xefd8159560bff855d160,0xefd8259560eff8159560,0xefd8459560eff8259560,0xffb805d560eff8459560,0xbff825d560bff815d560,0xdfd62dc151bff845d560,0xfed8058951bff8058951,0xf7d8059551fef8058951,0xefd8059561f7d8259551,0xdff815d952efd8259561,0xefd8059562bff815c162,0xefd8159562eff8059562,0xbff815d562eff8159562,0xfef815d562fef815c162,0xdff715c165dfd715c165,0xdff725c165dfd725c165,0xdfd745c165bff825c165,0xbff845c165dff745c165,0xbfd82dc165dfd72dc165,0xdfd82dc165bfd84dc165,0xdfd725c565dfd84dc165,0xdfd72dc565bfd80dc565],#[0xdfd80dc565bfd82dc565,0xbff805c965dfd82dc565,0xffd6550910bfd80dc965,0xffd7650910ffd7550910,0xffd8655110ffd6454910,0xffd8559110ffd8259110,0xffd5458520ffd6454520,0xffd7558520ffd7458520,0xffd7558d20ffd5458d20,0xfff8159520ffd8159520,0xfff8459520ffd8459520,0xffd7654540ffd754c540,0xffd7258540ffd5258540,0xffd655c540ffd7558540,0xffd865c540ffd855c540,0xffd7558d40ffd6354940,0xfff8159540ffd8159540,0xfff8759540ffd8759540,0xffd855d940ffd815d940,0xffd7258550ffd744c550,0xffd645c550ffd7458550,0xffd7458d50ffd635c950,0xffd8759150ffd8159150,0xfff815d950ffd815d950,0xfff845d950ffd845d950,0xffd7548560ffd7448560,0xffd7454560ffd7254560,0xffd725c165fff815d560,0xfff825c165ffd825c165,0xffd845c165ffd745c165,0xb000700000fff845c165,0x6d002e4013a007c002],#[0x1bb00ca8058002600105,0x38027b01258086c03d60,0xc06540304016f00af405,0xf8c0766038801b380d2,0x46811b008aa043402048,0x5029c8143809c604b302,0x60102eb016c00aec055,0xd88069e0339819340c44,0x580ec20727038081b800,0x202c0fe807d303db81e,0x43f0218810a008340411,0xf6046d022e4114e08900,0xe096604a5024cc122408,0x142a09f904ec026b4130,0xac015140a690526828b0,0x602dac166c0b01056b02,0x60f82ff817a60bb205c,0xcce06568324418cc0c3b,0x960d2f068c0340419d40,0x41be40dcc06d3035b01a,0x3a201ce20e5a071f0387,0x7d83b901da40ec007520,0xe07ae03cd81e3e0f0d07,0xff207eb03ec01f1e0f6,0x12e1080082f840d02030,0x90229011180876843302,0x47b4239811a608c5045,0x93f04974248c12250902,0x14097c04b84258012950,0x2139d09c084d94269213,0x283e140809fb04f7c277,0x2ac291e14780a2e05114],#[0x9855202a3a15010a6d85,0xae0056b82b3815800ab,0x63d0b10858282bdc15d7,0x9216ad0b4b059fc2cb21,0xc2ec217360b8805b942d,0x60042fc017b50bc505dc,0x5d0625030e618480c110,0x20c928644c31da18d60c,0x19840cb6865583288193,0x4661a170cf1066dc3340,0xe835281a7d0d33069283,0x6d0c36581b150d7286a,0xdec86ef4372e1b800db2,0x740e29870dc384a1bff0,0xa1cfd0e6b872ec392a1c,0x3b581d860eb2875103a5,0xa343ce21e370f0387734,0x587ca83e081ee80f6107,0xffe07ef43f1a1f6c0fa,0xc9104f081e040c22031,0x82212a1084883dc41c02,0xc4380219510bf0859c42,0x898044742228110b087a,0x9b88c3045ae22ac11430,0xc11e008e5446de235311,0x2488122489064480423d,0xa4625071273093284952,0x744bf825d612cb895744,0x89ad44d0a26691329098,0x3c109d844e4e270b136d,0x63141e8a0484fe227b21,0x82923147c0a320513028],#[0x541c29de14d48a5d0528,0xaf4554c2a8a152d0a8bc,0x60ad2c56402afa156c8a,0x15ff8af64575c2b8815b,0xcb316468b19c58962c25,0xd82d5016928b3d459b22,0x45c262de316e10b65c5a,0xbc205da62e9e17410b93,0xed0be945ee02f5417920,0xe18368c13060382ffb17,0x314e18918c3a4617c308,0x40e31dc18db0c62c62e8,0x14653e327419298c88c6,0xccc0661e32fd19758cb,0x9f48cf0c6744337719ab,0xd41a548d1d068a634231,0x235301a8f0d43069ea34,0x6bdc35c31ace8d5dc6aa,0xac46d16365b1b1d0d83c,0x40dd886e82370c1b6e0d,0x1c128dfe86fa837b81bc,0x8cf1c598e25c70f6385f,0xa2393a1c918e43071d63,0x4736439911cbd0e5a072,0xe9ac74a83a1f1d018e77,0x920ebf875ba3aad1d438,0xf1dcf0ede076b83b4a1d,0x3c4d1e138f01877ca3bb,0x9943ca41e490f21478dc,0x807a883d321e888f3ac7,0xf7907b903da71ec08f5,0xf3d0f93c7c5c3e081efb],#[0x4c1f930fbec7daa3eaa1,0x63fb71fc60fde87ed03f,0x80ae4036200f8ffd07fa,0x378818e40a62045101e0,0x31060082b44125208490,0x21219086083ee41cc20d,0x2d9216110a8484f6425f,0x6435d219e10c6c85fe4,0x885e43ff21e790ea487,0x13f0899844b022451119,0xf1116c88afa4543228c1,0x235d91a048c98461722,0x475623a211c8c8e2246f,0x5a480c23eb91e748f0c,0xc09194489a243c9214c9,0x925e492a6492d2483923,0x51b9284493ea49d924d4,0xe6256292a6894f24a5d2,0xa4b5b259f92ca096184a,0x97c44bc625d512e2496d,0x21c98d64c4a260a92ff8,0xb1340499c04cc9265693,0x26f3937189b224d61269,0xebe2751139f09cb64e21,0xc4f65279a93c509db44,0x4a0004fda27df13e889f,0x42e4a130507228239408,0xaf144cca22450ec286a9,0x728f614740a354518928,0x52b42949949b4a484521,0x6bc5342298b94bd8a5aa,0x70a7e253c629d294dd4a],#[0x95398a95854812a2d950,0xad2155f8aace55372a88,0x492b1695830abd655cf2,0x656dc2b5615a68acde56,0xaec6574c2b9315c28ade,0x84aff657d02bd795e24,0x4962d0b0f458592c1e96,0x2cc316544b260590f2c7,0xa492d1916830b3b859b6,0xd25ac32d51169f0b4c05,0x8b7525b832da716c64b5,0x7188b88c5c1b2df596f2,0x9297424b9c65cc72e469,0xd2ee8976e8bb145d552e,0x5e8a2f37178d0bc085de,0xef45f4a2f8597b6cbd4c,0xa8c05660002fef97ee4b,0x984a8c1fe60bb3045981,0xf418730c342618530b4,0x14316f98a1cc4a4620e3,0x8638931b698d58c67e63,0xc88e642b320298f40c76,0x3d8c9a064b93244991b4,0xd19700cb206560329599,0x335d199d8cca0662f32f,0x77833a419c74cdf866db,0x76680633f799efccf326,0xd1c468bc343e9a170d0,0xa720d362697734a11a42,0x391a930d44c6a0f34f49,0xa358a1ab90d5726a8e35,0x6bd735d39adf0d6b66b3],#[0x9e86cc436401b118d82c,0x78db046d5c36a01b490d,0x9b838dbda6dd636dd1b6,0x7661bac0dd146e4b3717,0x8037aa9bcbcde126eed3,0x2702c38031bf94df6a6f,0xe20670d338591c230e0c,0x77ce386719338af1c4e0,0x51ca68e4d4723f390a1c,0x39b89cd40e64072eb396,0x4343a0c1cff0e7ca73ab,0x8074a43a419d188e88c7,0xeab075233a7e9d384e9,0xd880ebfe75de3ade9d62,0x5d9da40ece876583b1b9,0x33bac1dc8cedfa76e13b,0x77fd3bf09df14ef52778,0x20278c73c491e188f05a,0x24f350797d3cab9e4c4f,0x1e9d4f4a87a1f3cf51e7,0xdab1ec70f5ec7ac63d4b,0x2d3dfc1ef5cf74e7b863,0xc7c983e409f194f8a67c,0xfa987d2b3e851f390f97,0x7ecfba07daa3ec71f5a0,0x69fa4cfcc67e383f109f,0x3fcb9fd38fe467f023f6,0x6e4021a007500027fc7,0x76810b406da02c101148,0x9039c81a340c12057102,0xa1d04d6823b410aa07a,0x9b20c2d05d482c94151a],#[0xb41d820e5106f0835741,0x845a4217a104d07f883d,0xa628506426b212ad0900,0x350bc485b742cb215990,0xa1a810cea865e4319a18,0x3aa21cb90e1086e74360,0x1c43f8a1f190f2c87704,0xe88784430a2129106688,0x124488f74470222e9111,0xf8b1342898044ad2250d,0xc2f080f978110bc27000,0x2a842c1400100590883b,0xdc27050883507e000f8e,0x7c2f0d002284207c1d8,0x191a1b024370c0922806,0xc3707007021f1010703c,0x9c191a0e87c400bc1209,0x3c191a0a92c1041c0e0,0xf021f141103bc2f05007,0x8440ed04016098011bc1,0x4821c3707c0e098050a3,0xc1041c083bc191b8287c,0x900705c0f064683248aa,0x3c191b8007c48aa0ef0,0xe018287c48ab4104082f,0xf040303b4100446f07c0,0xc287c0f8dc0f070683a1,0x58030a1f042343b41600,0x906f07c087c0e8f0ed0,0x41bc1f02c287c0e8e0bb,0x2a3a42f09c16000f8c06,0x2a83e341e0d07d0483e],#[0x9c06022a901cf09c170,0x30b80e0c484082d041cf,0xf03e380e1584dc2705c0,0x1c87c40afc270042e041,0xc100c0941bc1f02c050a,0x101c87c210bc0f070687,0xb09007068407c1c8cc1a,0x4b0700433c270414a3e3,0xc305308e11c187d80918,0x500603847061f0724033,0x384706c10801c9102b0,0x206028641c86c2c0b006,0x1f16c1611c18640886c3,0xc170d8405308f06c2602,0x2b09c187c1c8e0c823,0x10c27074287c08910061,0xf09c10328f872370dc16,0x2c010cf09c10528f9008,0xc270408e11c187238540,0x3c270580f07840724433,0x419611c18321c8e0e83,0xc8d0ec01c22281c8b80f,0xf8583f050043ac203e1,0xa1f2285c01c27050eb0a,0xbc2f09000400f8590883,0x440ef0bc1422c203e50a,0x704c243e1c8c2a842161,0x3443c2f04c20842c3b00,0x221082af09c103a0f872,0x87c27041c8842709c107,0x88121783e190b0405e1c,0x160530a0b4103e1f060],#[0x28148808c281f06c260,0x1907234121607c1e0016,0x646058178a08c1304706,0x8cc30000a052178b0410,0xa0722508c16000f85e1c,0x7c2d800281b0b026000,0x42386c195098003e148c,0x58442d08d080a600c28,0xc8c1904f047078030b42,0x10852286504707420221,0xd420220f872204f80508,0x8582b058050a0f87c160,0x1e001606c3600c150a0f,0xd411c18221b0f0400a8,0xf08c11c1834178ec101f,0x11c1b098050a1610c101,0x50b047061f022505e154,0x187c0d150d01fc3704c2,0x342207f0d80704c2411c,0xe0f8fc27050470780072,0x3e160c15709c16014281,0xe000783e4709c150a088,0xf834160c11f0841f0542,0xc260014c3e2f09c16000,0x3c2d07c130808c3e4506,0x941f058003e1c9017c4,0x709c102214c3e28aa08f,0x148a80223c370a4bc283,0xb8004e1c894260016428,0x8550f898004f0f854200,0x30078004f0f8522e0013,0xc0f96888128005e10864],#[0x2105058885851600c207,0x4c26010f85e1c8e2a84,0x841413088887d0f8e105,0x20a416001f03e1c9110,0x41611c187c8887230aa1,0x550f8881e0013c3e150b,0xf8ac26010a0722600138,0x412221c8a82b090a2230,0x5c1b078023e1b0784707,0x70721e11c186c17090a0,0x10a06c26008f86c1c281,0x58470780e001b0e0360,0x530f8d0a06c2106035,0x42a221f43e3054813098,0xa88e010a50b108ec2205,0x8ec242942a23108a8b22,0xa0a08006015098043e14,0x426001c9003509800548,0x8f87230200160384707,0x29420541708080054260,0xe11c3704c28a81f02252,0x870bc1508210c1e50801,0xc2207c16000f87242420,0x1c1e014350a07921500b,0x5800aa138a08709c161,0xd0b80704c207c2a8f42b,0x1c8f847074284e170b80,0x2210c08611c1f04c2022,0x4e1543e200fc2007c105,0x4420870bc1308210d800,0xf8803f0910f04148843,0x4c243e08872360013855],#[0x86c404fc322820080800,0xf0c0ab1bc1c09c0b0c17,0x1b0762081023078133e1,0x409081c36281f0b02228,0x1bc1f03811442d30c1f1,0x84fc30098a080282a093,0x8a07c2f0c027021b0762,0xc17f02c28762881c3605,0x1bc1809c085ec306c3f0,0x1872200602076c308023,0xc1906c3855c322820088,0x818a07c20721031bc1b0,0xb0802f0c15628200bc30,0xc3628c20642f0d8a0661,0x20cb1bc1c24c307c4867,0x1bc1864c306c3e041cf0,0x52c6f06c3080285202b,0x905468935c26058013e4,0xc2f098150243e0143118,0x6c0913e1c8a1c8801625,0x342820060d93e2007018,0x10a072200e1cc2820080,0x88c18550233e200a0260,0x30090a0802c080a0541d,0x43f0c02702150762821c,0x80231bc1f02c36014205,0xf0c13c28200900076c30,0x604e280bc30210a0802,0x2c36010604e470d0a025,0x1c0b0c200e14b1bc1f0,0xb0c06600139014b1bc1c,0x26004f86c1872c6f07c0],#[0x646e001b11436000a06c,0x14305440b409145c0f0,0x241b0c1651bc1f02c26,0xe001006c351bc1f0343,0xc0f0646e001b0f46f07c,0x7c0e0143018139009073,0x7c0d0c0906c305946f0,0xd1bc1f03800401b0f46f,0x1b0802d061553e200a1c,0x5c26018113e3d074fa24,0x88016004f86c185b8905,0x894281b070a0541d864f,0xd42876230d804281b08,0x80204fc3628200b0a3,0xc191b8006c470c086282,0x9436001514026042d145,0x28281f46f0603807c0d0,0x70215076200f8005814a,0x8a08078021db0c200bc3,0xfc362813866260016052,0x1007b0dc1f02c68241b0,0x8538100bc0f0646e001b,0x251bc1f038050d4284e4,0xe19880380616080201e0,0x1bc1f02c3080370d8a04,0xd88c470616054170a07b,0xc0b1a0906c3f0dc08541,0x9816001493e281ec3707,0x1f46f07c0d0d8006c380,0x81f46f07c0d0d8006c38,0x8774308028524f85c1,0xc07d1bc1f0343080301e],#[0x8503e078041106854128,0x684e28200130b0402706,0x4027068563e010450b0,0x2c47060a872482001309,0x18ca07c205481f0417c3,0x72c6c09c1b0c1f0dc31,0x190e1cb1b02706c30803,0x2178c14d0bc3304ca608,0xac307c5e08c170cca03,0x321c82bc131bc1f02915,0x73c0b1bc1e08c307c48,0x270627b0d4287c5833c1,0xc307c28529103bc0b1b8,0xa2730d8207c5052c6f06,0xc1f0e0e872c6f07c0d0,0x93e1c8a1cb1a02707c0b,0x191ac103a1f0f8270417,0xc1f021783a1b0d8209dc,0xdc143b8230a1f13e351b,0x87c4f050ee08c287c508,0x720ef05c0f0646e08c2,0x17038270746b0b4307c6,0x4330a0a950e8320a859c,0xa4859c0c3bc1d1bc105f,0x346f07c17038230a1f03,0x7c4f8f8260015128207,0x3e01431068935c160980,0x17872262bc2f05825024,0x601c0f801281c890193e,0x370130b0a93e3128150,0x178723928c2c2a508815,0xe4f872200e01f0582600],#[0x54470c465281f080105,0xf101651bc1f038260143,0x409a1103a46f07c0d041,0x1051bc1a09c0d0c1786c,0xf801421f078013e1f06,0xf0e82e001cf03c191a1f,0x178e1604146f07c0d0c1,0xa1f101651bc1f02c2d0c,0x54508d800440ef03c191,0x1bc1a0e81f0382601430,0xf07c0d0d826001510165,0x2e098030b4113e285946,0x3430803e098050cc2928,0x4c2a2a40580151bc1f0,0x524a0a1651bc1f03435,0x1d04cfc2a150f8260016,0x44c0c1542a4a0814836c,0xe03b0b4170d826014a05,0x1c1f02c6f0a23504601,0x7c4f8c0809a07b0d826,0x150a1f13e305bc160980,0x1520542a2a4f8a9123bc,0x422a448ef054287c508c,0xd1b4307c58548150a8a9,0x8380c859c170382601c1,0xe018211bc189f4287c5,0xc1f034687c60440e853c,0x2680407e098050d42f05,0xd820058051bc187c1c8e,0x8585601c3707c0d0a178,0x311c180e01f058260142,0xc087a284bc33281e8808],#[0x980329428204805c3707,0x2c307c381e03f0cc160,0x60142858481e0131bc1f,0x2876282001302c470782,0xc0b0c2782a5f0dc08214,0xe308c078054285ec6f07,0x151208005826001493,0x1807b0546f07c0d0d826,0x60946f07c089ec2d0c1f,0x26001493e308c0780580,0xc0e098050c1510080058,0xbc1f034307c381f46f07,0x6c430343032501e0151,0xb020e9283f09c10650ef,0x61215709c1432c470782,0xc89fc0c3b46f074307c8,0x8289fc191ac103a1f100,0x214d1bc18640e86c30ab,0x5c0d1b0ef06c250c1f1,0x703c191ac260a1f140cf,0x950cc203250aa5103bc1,0xe92167030ef0746f041,0x14f05c0d1ac27078287c,0xc40194470619112178c,0x938cf09c160b4090f805,0x865418728cf09c16004f,0x200903c0740b0c1f0a2a,0x1c1d02138662c0ec3128,0x8e2000d447074087c351,0x61103f0419511c1e001c,0x300944707c1601828641,0x2178ac6819c1b0c1905e],#[0x61930c178fc34194a03,0xe014360a139141000c6f,0x6f074107c385946f07c0,0xc1f034107c38ab807024,0xbc1d0c1906c389a0e91b,0x146f074307c28721051,0x8aa51045c0f064687c3a,0x385946f07c0b09430643,0xc28188051bc1d0c1905e,0x18284e483bc0f064687,0x84e40588251bc1f03436,0xa1651bc1f034360182,0x435048c908051bc1d0c2,0xb41058405946f07c0b09,0x1b0c02302c47078060,0x6018284e4b094170d4a6,0x2d04581e03b094170d4a,0x7f08c6f07c089cc36018,0xc0e002730d4207c50200,0x7c0b0c1f0b02a3ac6f07,0x3c191b426001f14c6f0,0x89d4207c50aa82945c17,0x90a5103bc0f0646e0182,0x82d081613c3703c1d081,0x8198a08004c0b11c1e01,0x654230c0c95c3020ca50,0x32505811702c6f07c10,0x1e01064c6f07c0b0c27,0x3709c151bc18321c8d42,0x21f121cd1bc18654305e,0xdc170346b09c1e014307,0x72351bc1f04190321c8],#[0x360a07920ed1bc183227,0x139008709c1311c1e014,0xc581f46f07c0d0d8060a,0x546f07c0e018289d4307,0x38060b4304e430807f0,0xf07c0d0c1f0e07d1bc1f,0x420c1792819080780546,0x1023ac150b8003e1f0aa,0x8ef09c107340e002a8e,0xaa1181ac1043c2f08211,0x343e4e0d8004e1512828,0x344207821c2b09c16002,0xc149015709c16000f872,0x5e3821c2705447078060,0x5e389e8ef03c1a1a460,0xf87c189e8ef03c1a1a46,0x40e87c340c4a07c1d040,0x3bc1c1a1f0f06f07c0d0,0xf034103a1f0cc2504274,0x2f03417070687c441bc1,0x44a001783e190c27c3ac,0x24143b8007c0f8403b06,0x941703c1c1a1f03a584,0xc1ac2064490426844233,0x7c343a0bd05c0a01c1,0x687c0e950ef03c1c1a1,0xe40ab411042730bc0f07,0xd0e919c0a01c1c1ac285,0x884243bc0f07068401f0,0x1b078023e1b060392814,0x4917068683a1b0d80128,0x1f86f07c0e0d8006c38b],#[0x8520670286f060e86c38,0x401f86f07c0e0d8006c3,0x9123ac270542e001f03e,0x4243088150a8e87d0f8c,0x8c9123ac270542e001f0,0xf03a4b088150a1f4428e,0x3c4542705c0f0706b0a1,0x44020018054260014a3e,0x207e1bc1f03836014205,0x286f07c1508c287c0e9,0xf07c0b0a2707c0e9414f,0x683a27872301f4200586,0xef0706d0a178fc27070,0x706b09428721f13c0873,0x1a0e89c1c8b80705c0f0,0xf0801f0407d0a210fc1e,0x6f07c0e0d8050a139003,0xc1f034289e1f03a581f8,0x20d07c288cc201e0161b,0x340486c0f8642c11c1c1,0xf8642c13c1c101f07228,0x484f06046280a1b01e0,0x843b0c1381904846330c,0x86c1006424121b03e190,0x17868203e1b228190980,0x3e190817c3e190784706,0x709c15000d23e30061b4,0x150184706c307d0d1019,0x8470740304c34343840c,0x345611c1d00138682c09,0x740610c2705c30a41f0,0x962f09c150025881f8],#[0x4304f828463821c27054,0x1c87c2ac124a0fc1e03,0x6c0f864304082f0980f0,0x60213e0a118e8d012828,0x470780e0a178e83f0743,0x258a0105e2586035058,0x213e0a118e08709c130,0x20f83603460c03f07436,0x2705c005a0f8523f09c0,0x46f07c08410605e3607c,0x5e3b11c185ec0841060d,0x81e301f46f07c0d0d828,0x4a3e1788c47074360a17,0xf832281f068f87c10061,0xc07e1bc1f02c2040190,0x5e3d01c0841c1a1a1f,0x1f43e301f86f07c0b0a1,0xa1f03e1c86078870a300,0x721f0d447078307c148,0xb001006c3c1bc1f0381,0xc086d83064301f86f07c,0x78106d4023e1c8a03806,0x50f402421b074023e1b0,0x1b0d86f07c0e0cc25001,0x18306c461bc1f0340040,0x1b121602586f07c0d0,0x901c8258110bc0f0686d,0x87386f07c0e0d4030a13,0x407386f07c0d001006c3,0x1602586f07c0d018306c,0xa10703c1a1a13824150e,0x23e1f060490617a3e190],#[0xc20401911012421f0701,0xa1007c28580be1bc1f02,0x7c0b0a1005e3703c1a1,0x61bc1f02c2840179186f,0x190c0485f0f864205806,0xec284635070490a1b03e,0xa1b43e1906c3e0d4084,0x7d0f8c049061b43e19,0x1007c0f872244221b001,0x486503c1d10c285e1010,0x87c5041447061f072293,0x3ac060542f03c1c1a1c,0x605c1c1ac007c1c8e81,0xc1e05c203fc0072258e1,0x2a90a84f09c003e168e,0x580661bc1f038350a179,0xb1181311c1d0a1785830,0x28580961bc1f02c00401,0xb0404e28124186c8f864,0x904037068483d0106e0,0xe0b06c101184a3020013,0xd8483c1b040481a8981,0x1068642854413090441a,0x5bc2704c043e303612c1,0x80bc2704c005b0f8c0c8,0x3c0ac2300168181f43e3,0x63b08c13002b87c16c3e,0x4e480fc2007c101f4009,0x1ec161bc1f0383501828,0xf05c0f0786d001c87c48,0x4706c060d82d02560d82,0x40e0a118e07821c27054],#[0xd82872178e038078304f,0x60785e258a03807c0e0,0xb044bf07808642012038,0x1611c18721f0b08d0e42,0x8e10c1707808661f10c,0x4c270780e101f0725825,0x78087c50b608c0b0030,0x922002b08b0cc2305847,0xe11c270419707808321c,0x643a4bc228a3090f940e,0x43e02c607254aa11b0a1,0x821140ee0ec3b08c1c01,0xa21859000400930ac222,0xec3b06c1309808725ca,0x44c208450238387c0ed,0x10d2a88c164420ab0ac1,0xa072183380f09c10722,0x781d06c1c101c85e305f,0xd070406420120a072178,0xf8581f090d422c120181,0xc16014287c0f8585b040,0x98043e50b62d03408b08,0xd2ab2e4830b0881e0a30,0x8523b0941e00c643e148,0x1880382341b04c26010f,0x8f864360383109c1e101,0x14130a8f920bc1f08d08,0x21f0f11d2f088534260,0x2aa20098310584706206,0x3505c1864888803d0419,0x60dc1e10118803a0e8,0xd80e0dc1e104b8643e02],#[0xa8281f0a6008f89c489,0x50b4223f0a222482e085,0x8d088f8642aaa8282e08,0xe392e0881e8f880281e0,0x7c384087f078430c4605,0x872285383611c1919808,0x1a234605e320f4670617,0x81e008fd18149083a0dc,0x1c1d1888872302142208,0x1fc1e10c3118178f4261,0xc88160442d4281f0a088,0x412230f87c28410a05e1,0x3e1c87c29410f87c1841,0xd07412221c87c30ab410,0x1f0a08e11c18721f0b43,0x2c243e190a88e11c1872,0x85e51045043e1f081622,0x404622294f078450cc2,0x2a2241611c18721f0c16,0x8f86c3a23847061c880,0x8f86c28b2170581160,0xf0d8023e1b07220b2116,0x4e04650340b211c18721,0x430238301ec1611c1e02,0x62d94580e101f6001c90,0x3c1e11426001f0724e0,0x505426008f852520d816,0x1a221c8c2104e81a040e,0x8087d800725d0584509c,0x25945420b208905c1e11,0x381105c1e1180e004e07,0x5847061c87c306c1182],#[0x538470dc1a221f0e08a,0x190a0b044108b41c8a20,0x98003e1c960881f4243e,0xc2a86c17a0a2d8645150,0x724d07416101f2221c8,0x60441023847061f60051,0x2d8a818858043e2c8723,0x2160528a0a166010f944,0x8f4260016228148b4242,0x78d013041f5088fc221c,0x8858380584707428581,0x6c407c4046419058450b,0x8cf8e20408c0b0d8170,0x2281f0c8830b0ac248a5,0x430ac6876286102022c3,0xc1f0f0231cc40762408c,0x761f0d02302c6f062030,0x22942b3e4401023020e8,0x40661f108830814c3309,0xc6876330208b0d81706c,0xb81310c70f0cb108c50a,0x4c431a1f0b0cc250050,0x404c1b02c68801f1009e,0xeb06c0b1a1987c40b4c3,0x811ab8050a4f91814000,0xc82707440803a2007e09,0x1e096004f86c35021550,0x5034370744054200d0d4,0x200d43511c1d028906c3,0x1409aa410e437061b134,0x3e1b0a1605b820558160,0x8340793e20080d01f801],#[0x90218250b8013e68c284,0x4fe09816006a93431080,0xa8ba2408029803094f90,0x941824086008653e450,0x81e82b09804294f98895,0x953e38608ba2a8902142,0xc293e401f42a0b0a3088,0x94f9614c2016e090a600,0x2890214250607a098021,0x882506c2a254f9019a3,0x844c26010a07238b407d,0x430b803074231a48b303,0x231cc407620210bc24c,0xc3408c0f06c6854200f,0x20c1c24c4600c2418c69,0x38803425803110631c28,0x4451a138d00306c0b1a1,0x74405546876283180219,0x36c250b46d0689510380,0x2181110c26004693640,0x8011a4d921b13e200609,0xc1d88142208960444309,0xa82d1d44076230d0a06,0x6511470e82b094722544,0x475101d888ca25802088,0xa5150f02b0c1b0803b0b,0xab43c09c1b0c1b08039a,0x11043906408b41b08031,0x393e4282582821802285,0x284146a000b9442d06c,0x1a1388029454191a1b08,0xd03468242d06c350740d],#[0x1e0240825801441b1741,0x2c9441b141ce0e43e064,0x385946a021820e81e00,0x8030b21604fc08765108,0xc241b0cc3303c1b1a150,0x50b8113e530cc0f06c6,0x1b126881f82108090218,0x107021cd1a0670743600,0x2820b4439064086c200e,0x819f0346f07436001b1,0x855c0d1bc1d0c200e14a,0x4f85426001393e150814,0xe4e1198461a1d8b8004e,0x8c08026c161180139868,0x6b2838561450a8421a1d,0x42b3e4c330ac0142e08c,0xc505ec1b0414c330ae09,0x40ab0208f0c0b311c187,0xc0d311c1b021f142007,0xe08c431c38801e60808b,0x9d0ac687634330ac0142,0x9e08c431a1f0d0cb100,0xac6f07c082ac307c4836,0x1bc0f06c307c408c1103,0x43ac493e1f0a0e8720cb,0x743a4fb0b8207c6a9016,0x8b70bc105e0a93e58582,0x22708429aa1d1430e822,0xe8250cc605e38224694,0xc3a0950c1d87c28730ee,0x9306c0d1a8209c0e87c4,0xad1bc1f034307c50400],#[0x8c283a27126ac3a0cb04,0x281f080cb06c087346a0,0x2388ca2b46d282a448ed,0x42e004f92c2a2b46d282,0x61f169783407e05821ab,0x44d70d42e000b0224470,0xb804341613e1f0a2007,0xa2a1515804341613e20,0x4a0c0d50c07b05447074,0xd05b8107d82503801aa,0x98009e07d0a1f13e6058,0x2a4f929123a232040d60,0x98152040d5049781f42a,0x9040ae0542e09801a24f,0x26006a93438961181e41,0x805026a87c30584fe058,0x14470dc19341f100d105,0xb0228a93e608007e0,0x8c6a87417943c2d07c16,0x293e482007f0a4a22b4f,0x6c5f4185a14e0582600c,0x41d0407a0582600c2d3e,0xa8ad3e407a17a388ca2b,0x2a4f9817d074120407b0,0x75800902104650f0bc12,0xe010b4224f87c29a2230,0x4a07c46010b4224f8802,0xe1f0a8bc2c8942343060,0x28c2c2a508f8042d0893,0xd0dc1d021f1b8042d089,0x750b422c3b0cc160143,0x70cc2d11c18741f1420],#[0xc105e0a93e88800b0238,0x8ec2d0881f8050ac2d04,0x44f87451aa2307491142,0x6a8465082c08e01c2f0,0x448e85283a0680d18179,0x13e1f09801404f87c22,0x42448eb021d87c2e005,0xa0d820c1d04c6b0b0ab1,0x42a15154170ac742ac40,0x85300b0216d04c6f06c3,0x28501260044136468763,0x4687c3e009123a4f87c,0x3a5087c2850126004d91,0xe09802054451c4e00912,0x2d1d4407622388ca2ac2,0x1ea388cc314451a1d8ec,0xb46f061cd0b436081f14,0x1f42e098013e5705c083,0xd0c1f1268847811040a8,0xf126a839c0e000cd1bc1,0x3703800440ed0bc191a1,0xc0d1bc1d0b8050c1f162,0x7c0d0c1f148105382705,0x7c31a22305b8008146f0,0xd1a1f0e14f0346f07430,0xb0c1f1a1ce0143707c0,0xed0f41503801aac3b06c,0x2070dc1b101f0c232448,0xc12b0418b10c687c3302,0x88c4080c6f07c0b0c1f0,0xf121194207e01c2f044f,0x103b8030bc1f034688c1],#[0xc381ec18902113e278c1,0x7c485e5081fc2f044f88,0x1bc1b0446b07c0860268,0x330a2694c108c2687c25,0x307cc151b82707c0e014,0x21f0c1103a0ab0a2788c,0x60c872643b83d061cb1,0x22c0a34c4709c110c197,0x82246b060e89e210f0e8,0xe82546d07430661f0e1c,0xc1b0346a0a2783a1f170,0x3c1d0c1f152a87210024,0x9e58730e82ac103346f0,0x2ac1b025151a82b080e8,0xf0d447061c87c24aa1c8,0x46d283a3a1ca0e81d121,0xa8cd2822388ca0ac2601,0x23c270414a324f8ec251,0xd0941a33802194f8e0d0,0x4f9007f084a2334f8a11,0xe405f41d048e232c2601,0x217d074120407b088cd3,0x8411907c27048c8524f9,0x83543511c1a181f0e258,0x343508d11c18721f0d40,0x61f110d423447061c880,0x7c4c3508d0343d0dc186,0x801e0354302344707408,0xb0cc150f437074087c60,0x18781f12200790d422c3,0x1c962003408f0cc2511c,0x40d1043709c1065c1832],#[0x4197060cd021c9a0d023,0x28ed0e435094130ec230,0x23c27054410dc18721e1,0xb061151140b0c1f120d0,0xce00c4418c70a2cc0f01,0x81f0e0dd04c431a1f0b0,0x181f0a2db0cc0f06c6c1,0x303c19401f0ac0f06c6c,0x1f08c4303c19401f0ac4,0x9c1b0c1987c3066c431a,0x3ac3b06c08661f0cc681,0xc84e6505c23110cb1c2a,0x340700b06c0d041131b0,0x82b0980511470e2c858c,0xcc220544233470a8e232,0x87c283609b094451a1f0,0x19104687c3806c151146,0xc0f06c307c3b090dc274,0xac182a510b6403a0cb1b,0x38060a51141c83b46e0,0x7c48464103381311c1b,0x7251039c082b46f0743,0x1f0f46f0780038510b43,0x42c94517020ed09c191a,0x881a048087d46e018294,0x525151bc0f074307c405,0x20680d1a2c9441f0e200,0x485346f03c19441f0c16,0xe5040cb1bc0f06c307c,0x540b0ec0f06c307c5072,0x780072258e1ca3b43d0,0x7078030216940d43246b],#[0xc87c486443308c1432c4,0x284143201c0d1a067061,0x21f600530546f061c87c,0x5150dc170346b09c187,0xdc151bc187cc26001c9,0xd1bc2704197060c87241,0x4709c1707430530c920e,0x46f03c1d0c1f1211b02c,0x61c93e270c16b0814c3b,0x9c1f04c08725084c189,0x89a1f121943b0ce00c47,0xf0c1cb08c151bc1f0219,0xc209a5d1bc1f02c109a1,0x1cb0546f07c0d0d8060a,0x7c0d0d8060ac209c587c,0x580f87c203a0c87346f0,0xf0b8191344072178a448,0x8ed281f069123a835281,0x121f0c8e8734483e1f0a,0x5f0f864307283a068ed,0xf0580889e210a2285c4a,0xc283a2783ec10aa1f0c0,0xc4d05e383407e010f86,0x87d800aa509a0ed11c1e,0xe922d09c9123ac203f42,0x10354101f42b081f43e8,0x80707443081f60c4d148,0x9441348e89c309a0ee05,0x460f9282709e210c4185,0x10906d060789c2788430,0x41b082109e301a1089c2,0xb418720f89e210a07c1b],#[0xc3ac61106d061c89c210,0xe89e3c08c20214470740,0x4605e28721061a0905e8,0x680a3b4605e3a448ea1b,0x1a26a3a4605e505283a0,0x89a1f10198584210640e,0x687c3844c1b0306d040e,0x4a0722b06c0c1b4103a2,0x1095048f87c2e01c243a,0x87c4c410960c4a07c2c4,0x4141d030921a4209c0e,0x1b0740b03869042687c5,0x961a2743a1f13831094,0xa2783a1f141604041902,0x7c58721050740c248690,0xb41b0740b0386904268,0x8258689f0e87c4873831,0x287d0fa3a38581010640,0x4287d10a3a3e00917054,0xa4230a0e89c460091705,0x50ea3e1c8cc1b028cc1,0xb054243a268643047427,0xc2a8690b4203a279586,0xed08c289a5072115074,0xe230c1cd06c1d02c0e1a,0x1c89630458682ac289,0x43b8003e16930eb060fe,0x69181f122a86442b08c1,0x1f0e1043a807021cf070,0xd801642b050ec1bc1872,0x5c1702c270706d0a1c87,0x61f41b803081c930e84],#[0xe1a0e872270d0e90bc17,0x1311c1d0a1643a4833c1,0xed0a2685e3046c0f09c,0x640e1b42c3a271586b05,0x50d07c385a16032c210,0x9410f87c184184706c33,0xf87c20588d3010f86c2,0x2c2304c0072258e41141,0x2c230006072258f8083,0xb00c23040ec3e1c8f02e,0x3040c23010fa281c8d81,0x48a0b43706c404f06046,0x7306e041f0f4004f1005,0x707068721f0a0ef03c18,0x709c003e1ca28258f81,0x15441c27000fa1216911,0x443f0613d0b1004638aa,0xd0a11914004e8f854260,0xc8964c18c460dc1b0213,0x5c3b0cb074023f425041,0xc2305405094112216a3e,0x386f068607c50650ec32,0x721f0d0ee0cc09014087,0xd00c106c443a4961bc18,0x207d401c14e0dc0f0786,0x1502c0e0d82f061ce1ac,0xc187cc20724a450ed04c,0xc1f3085c3ac15054061b,0x30ed01c0e1bc1f0582e0,0x72382586f061c87c285,0x7240400661bc1d001b,0x1f0a91309c161bc187d4],#[0x1f3081c8e0161bc1872,0x86072259186f07c150,0x30016c3e4a4141c3ec23,0xf85a4caa1523a8cf09c1,0x32408650940308c01130,0xf0f8f2a8408606d0f864,0x1f0f8d28e0bc2704c001,0xe1b0607c460bc2700c10,0x18721f0a1484183703c1,0x8fc224ba2219114161bc,0xf4123207a223c2f412aa,0x74123a07a2248468d12,0x9181c85e28468f12e843,0x39458087c888722c1888,0x23058505084ba22510b4,0xaa1b0c2c939809448887,0x2384e224413f09134891,0xaa24080d419aa1393d09,0x19a1889020322f418608,0xa8e40e43a25470a8cd06,0x2244f908ca248650f470,0x513e31a24d3078105a15,0x510801b09811aa16a241,0x1440b4432082006c28b4,0x8e8e2328ab058030b43d,0x6109123b8013e1f1346a,0x45078005211c3c8a9188,0x180468bd07802248ad3e,0x941b05801aa8ca2b4f92,0x6a8741c93e1f101ea3,0xb0540e001d134542d08e,0x407421121e85f0b42207],#[0xc70c2301e4430740e002,0xb43d1c46010aa0e43c18,0x944f908e2328ab058030,0x93e39a24d608c1e00148,0x7c422a429ab8260016,0x1f082305b823054350b8,0x2408d0a884410d8050a,0x58043a1f0c1d11ac1e0,0xa2ac130943d14388d113,0x950614a194fa3232388c,0x8e506c122a14a334f8e8,0xa1f43508b09408781c8e,0x50f470f0cc250630ec70,0xd88e1c928e2328ab04c2,0x1f102d13c4b11ac1b022,0x4408d4360b4230580144,0x8258790c91ac1b021c88,0x3050e87c243b0cb021c8,0x4485e205ac243a1f0851,0x9e423a1cd1219089123b,0x8e9043e4d6012aa248e8,0xc889143e4d4aa8aa3a27,0x16c3b40218443b0cb021,0x8c1066190c152410ce0a,0xe26c3ac1064209b0eb0,0xf0c9123816c3b0cb0940,0xcb08309b0eb08c15001,0x2705b4043b]]
set_option maxRecDepth 16000 in
def g251H9 := limbs80 #[#[0x4083051604d0e1604001,0x400e0008010106002,0x820404102040400310,0x700203951200422083,0x800214400000c2170c04,0x404201a008007800a0c0,0x100c20d00180820000e0,0xe005010e0028f0208003,0x587000408d00144000,0xc8031c38000000000b02,0x4800e54086021048d002,0x8100881800a0c2010404,0x10004080001840100346,0x8d8a1a04b80061800,0x40800104080080200000,0x88812a041020404c801,0x400008080001c4008608,0x8200006800004282005,0x1912000000018f2238d0,0x70a401801c0010500740,0x185030f00101811c2008,0x21c10400009820e34004,0xea10200184082c0830,0x8c8908041871eac3010c,0x10002343030205715002,0x228540174608f01020c,0x90200001020418202000,0x341408102202060a1818,0xc3400b0008201040c306,0x39a8700141000000d800,0x920a0204000020840102,0x1812a20081046ce10004],#[0x8d180838400245021058,0xe04c05004848100801,0x22e8100164c204060420,0x60080004047810414308,0x5c185021419704040020,0x4d00112c40004e,0x7861c0c00d1a0090f081,0x1400342ad083458a0218,0x14804307401408d06016,0x6c481b100400b0a0050,0x34bc7d1381a30008181,0xda80b02c388148000000,0x23c3251443a62fd3636a,0xf101100fe0834d14d60a,0x4694740002c6f024a5ca,0x6ccf8dc25741295129b6,0x50384c5a2fe60f,0x30d6c11d9ce90000000,0x3066c0000000000,0x2486903528e71c4bc00,0x7a8e4000000000000000,0x1d62c0000852c000086,0xa00003edbc0000000000,0x10bf40000000041,0xd2b505df5a000,0x6a0c91826ecd614b3400,0xa044258ea0cffc000100,0x954af6c39b8dbfc3cf8c,0x671096d1c80003eea7e4,0x28c9670878d970c6647,0x1ee90000048c0000000,0xfd951593e24c38c12000],#[0x515800002e9f60850e,0xb9cba40002b0d4120c00,0x1044c161546d5ef03d42,0x60e0a95d1f06e5c4d,0x0,0x98000000024b8012cc00,0x1c6700001065d2e,0xa005644480000000000,0xfc00006a83a49302134b,0xd40001ad56309815a2c8,0xac501ecf784800000322,0xe6a4ac463c0000000029,0x5680b7e97c0003ef570f,0x180003a97400000003b6,0x17cd00453c00000003e3,0x16d06605000000000e1,0x70b5c8e07bd628000000,0xbc0000000000000001e4,0x1ccee38d7d4968000302,0x43824e4fcecfae079b81,0xec000000000003cf4500,0x248c5445600001cba382,0xa24ed02f4000008fab45,0x1400005659c78c0000b3,0x28d5c8a4a47500001c4,0x220186e15dc6db829400,0x28c34b334bc4e1b02e82,0x14e79f5,0x54000000000000000000,0x23874553f000000003ce,0x34d58395f00001847067,0xfda17eefaf543f50d585],#[0x307e0000000026823f0,0x386562c2d40003c35800,0x8dd252cbda921d7402d4,0x3115c0000b032d228c1,0x8d4f01c8f80000000000,0x1112f194d0000000024c,0xcc6a2c00000000000184,0x1823c0000000287,0x900000e9240000000000,0xc0000000000000000302,0x111800000000000243,0xe7a58400000904000000,0xa4000196540000000121,0x2a4cc000038eb0000114,0xb8000085c800028b7dd5,0x6405429069d37ee725c6,0x880000cfec0000000344,0xd594c496080000000235,0xba083388dc0002c12751,0x9b0cf80002ccc552c14f,0x5f41ac00000000000186,0x805c6682c01b81,0xc0003eb46c8b98b4000,0x2d40d52d453388b,0xc710107597d054000000,0xdac984000089ec000345,0x280000c598f35d466a8e,0x2c90fc0000d003162204,0x5c000265700001d1558a,0x6400000000000000028a,0x789209e93bc4da123911,0x7ac46dd0e40000ec9e85],#[0xc5c1044a644748083784,0x7a006ff10168f40e3928,0x2d09c244fba9a8034302,0xafc68904ae93b28dd690,0x34958000000036c3711,0xd980cd09ac0000aa3800,0x4000000000001479f02,0x2d06c0d380002cea94f,0xf74268aa50deb836c00,0xf4897548be4bd353a148,0x6347918c07298f8b27c1,0x1be15105af872605330b,0x219015e72b270000028b,0x1f56680000c1638f9d15,0xfc00000003699c000116,0x9696647034e420000143,0xe20dc035ed2bf5876d20,0x2ef3dc1e4c960000211,0xcb88980000b243535400,0x2000000001ce6dee4740,0x37546feaa800014b30c0,0x24e600001675e89498c,0x780002491e9288000000,0x38929c4840002d3,0x30c000025403d20400,0x8c00028cbe82ddc62800,0x1c448c000228ee8edd45,0x5022c000045a98a6d48,0x1050c6429c208d0,0xac7e52c78d49c05800,0xbc9100000070a6ad6d89,0x14640e6c24bf905],#[0xa71168a33f4594000000,0xe80000c6d400016c0012,0x3b72345231ca38000368,0x2ec189c927c9c5d185c1,0x5800000000c2184226c1,0x88ece3eb06,0xeb03b00001a63d8d1400,0x3426cd8784000393748f,0x1124fc70312de4763ab,0x815000028db800,0xb80000000384c6872800,0x155a400002abd42fab4,0x800a8c933c0000000000,0x19643e480e13ee57d21,0x2094000000000000000,0x18c60000000026de000,0x7b90740000000254c000,0x8883e9109c0000634a16,0xfab5dc00038c000001e7,0xe5140b0b4fae500002e3,0xf4c4000004754d,0xc395a9492000016d0c00,0x28bc800019244d610d0,0x2150387c8129800,0xdad3d994238136eeac00,0x39c1c175c40001432da5,0x5c000295e7c6a164d6c9,0x6a63a502e40003056852,0x1345800000000000274,0x900000000125b0000000,0xcfd0229c00004a,0xc0000000000000000000],#[0x66070bcf3dd29c000105,0x250ef63f154,0x3d05800000003ee2800,0xd5de895454cf86c000,0x8d14dad508067e8c6800,0x18e0595c3f634000009,0x7440400002580000000,0x740000000347efd3bee6,0x1c180000000020c7395,0x18e6a4282c7a304e800,0x9bc5cc000186c8000000,0xdc5585c195cbec000240,0x5ed0640f0dd10713956a,0x120b8747809275c39cd4,0x26ad3b91a0497f85bb40,0xb000028e4dd3a7d31b22,0x58b0ad8d80c25b848b24,0x103800003647c000015,0xc848000000,0x54800003854400,0xa4000000000000000000,0x3ab1207ae8b9800038c,0xdc000350c65200000000,0x254c800000000c5,0x355c5c498911e701000,0xd4000000bc0000000000,0x3a5b64c854a57eb5c81,0xb40000483c0000000000,0xaff605394dcb2e,0x3e55c000060ac882400,0x88a3d39000024a0000,0x14831348ab0ac4000000],#[0x24e800002f0,0x5800016344147e901800,0xacfd426c8,0xd8000000018ed40d0800,0x1144c000290b0000285,0x6d09e283e0000272c000,0x8866398c83833d8f824b,0x68d88297be55000008a,0x3913394b9b510e7a44b,0x4f821587f7d41f881800,0xd40000000253cc000360,0x1cce8408800032b1dcb,0x0,0x3b343f58c000000,0x417800,0xd94ef0d50c0000000000,0xa64db210a8000000008a,0x1504f567c4f1d672ec3,0x4c0001679400036e5800,0x1c8,0xcc00000002c7d290bc00,0x4f9493c604000000038b,0xe34f94000126e6904311,0x6c13528c0001d49d01,0x2cc3c000000,0xa41c0002cc6ec19000,0x1ec6706c4ce1e0dfc00,0x152cb0950000000,0x3e35800000000000000,0xd8000000000000000000,0x2d38c00018f,0x1255800000000000000],#[0xc00000001d16c275800,0x2dd53720d80ee604d447,0x2450bc87000010c4254,0xd80000edd9817d20b000,0x248068ac000028c,0x1c00000000e458000000,0xf9a39be027a1114a0d05,0x768510000092546dfa81,0xa4000000000003681d0a,0x38ae3836389dfce9580,0x5349424348b04e8c00,0x5316072f94ada66c00,0x3bafc28c13c99c93f400,0x192e383a2119340d546,0x202a6abc80003ccec00,0x6c00000000000382e800,0x3fcf1400032d9000036e,0x3c33000004b48000396,0x1e2f4000000,0x555cec400004f2800,0x80001f5e40000000000,0x4532de62ed8da80000ad,0xf0e6208cd74eed4616f1,0x29561c6e52cf3468e83,0x192389861a8909d26c00,0x53cab74df40003096c45,0x4921fc0000000094f448,0x3256c944a4660000302,0xdb41a400000000000000,0x248d40003083989,0xd417000000000000000,0x18000014980f880001b0],#[0xbece7c000148400002cf,0x919943540000eb,0x9e4c2e55c90978000000,0x2810c55d00000802741,0x5f5053c95c0000000000,0x9ed3ba4aa3cb1640dd84,0x2d45bc053a996155f02,0x1e833a0ec28228000000,0x9c74bfef514bf30bbca7,0x24df80001cd04828a35,0x5c00000000ea1c559400,0x5101b4000292f40002b0,0x80000eed00890000253,0x2400000002049489326c,0x49a4a36c4cc2b6cd9391,0x49ce8a0e1700440f2590,0xb40ad7f29f0c3000da26,0x75e1598a418f5481f275,0x2c0002936c00004e74e0,0x1d6704944004d8c0833,0x7b40e68a151568abc400,0xab4f6400000001c38a80,0x30b6400032b58000263,0x4000002dec0000000000,0x2686fc2bb2c71c000141,0x9ccb2dc8ccd178000016,0x5791aaa43f4c28000055,0x24c4c8fc06fec000115,0xfc000000000002c27543,0x780003c9f48d3dc63389,0x1516000024b565487ee,0x60000000004ccc000000],#[0x6c4a6848f00000000048,0x6495b66e57e3f5441ea1,0xc400000000000000036f,0x700000000311b0000043,0x1edcc0000000095,0x7000000a9c0000000000,0xd6c9a4000149700001c2,0xf3cadc00024ac80001eb,0xf80000000372cd223449,0x95e085a68158ce,0xffe062c21c0000000000,0x36ad7154c0001c0646c,0x340001309330f4000193,0x3fca1c00000000000021,0xb502c7860a7054af9568,0x4f9b42d2eda053,0x22eb18c8847b000,0xd93c36598000386bc00,0xe61117d3252eda5148f6,0xfec7dc05140f30000191,0x941651c45a0ae44b7553,0x80000000000000c30a46,0x9315fc0000000314bc96,0x18cf000038676900e40,0x34656aa1800,0x459c0000000000,0x83551c0003256941d000,0x2ca26cf117685c11940,0xabc20400000002c77000,0x6c0000000000000001a4,0x3c0f282ff416c000170,0x45c6340002248a85e800],#[0xf8000301080003ea1115,0xdc858348945308038591,0xc8000067e043dc00038d,0x940003d5f5837803ae62,0x8f09425081ff160c89,0x1d5ef751555d400,0x88000000035615765800,0x90000000000000903f50,0x8f4917d0f44e30000115,0x7f44000002d2940000ab,0x40000124d144a80ab087,0xb2523fc664462c000044,0xadf134fc0003947b44,0x299210d43507d4000000,0x24648000000000000ea,0xc6c61dce29ca10486400,0xdce7fca4c380a813376f,0xb475814abe53e4842d22,0x8b66bbb590000143bde9,0x3110ff06a8da249d726,0xe02a09e6de0d5082c800,0xba51a40335ce87d4736f,0x32d3d4438fa5bd9507ab,0x77c3700003abdc0000a5,0xce882c0000adb8ee61c7,0x8000018d3000000001c9,0x20823000030234000150,0x1e6b400000000000247,0x103280000000000,0x20000000000003165c00,0x14a7194f1e5798aff0f,0x680002e7300000000000],#[0x10844000103040003ad,0x18000000016bf0000000,0xccff443d9060000107,0x18d568588c98800,0xe40000232da2ad839400,0x95ccb8000344380003e2,0xf68db400034815ce496e,0xde84a150a105d493dd0f,0xf8ec70000344cfb09dcb,0x26279a9b20788000393,0xac875401c711bdd63800,0xc7d3ec0001c9836f9008,0x6b40001a6f800020f,0x5fd4e022b7c9c8d1d000,0x2c15633cdd9a6e987,0x25c6924881a166407000,0x1366286dc000235cc0e,0x2848100ec000394ec00,0x51ee22064c0001256400,0xb4431fc0d34a63ade4cf,0x1c074000004b708,0xa4000208c8d31160a000,0xfc00020fd68e35213988,0x1dcf494ef4000309a807,0xe400000002d27e4d77a6,0x8c0003b66400010ea7c7,0xaa836800000003e38150,0x54e9c89b54028000381,0x7d70de903044fc0002f4,0x38731ed9c0002558aa6,0xbdd3d18e5c2e0c4d2000,0xb59142af088d71efa547],#[0x9defb88de026c8000311,0x20bb712ff52670f2fea,0x363422b1a5649b23000,0x3abfe46820cdd071400,0x5000024e98d5f8000000,0xf20645745790868aee2d,0x580b45d5b8a38c887522,0x21687001c6c1970666d,0xbfecf81445027e047c00,0x7000000002d2ec0001d2,0x5212a1ec474c226b7910,0x145e1934c00fa94a9cb,0x6b4c190c4646ead35c00,0x1473f076b837434c02e,0x65c857166000034be800,0xb0c3d8000000000003c5,0x306d1dc7130ad19220f4,0xbed1f4000000010a0a44,0xe9148853c601dceb6015,0x2c1b8474091dc000293,0x1c35cb4640003cc5c00,0xff52b4f5da6bcd8f5c00,0x218d9cca29c8124b03e5,0x1501d9cbff509af24490,0xab4d4e10ddc5904e2201,0x354e4020000014c,0x15380000000,0x200000000000004f9000,0x61c2380000c2f2d5270b,0x8000292480000000082,0x45cfa204d341c9e5e80e,0x44ef117c000164bd4a],#[0x9c08e40000ccf4a538c5,0x31487d22bf4174000124,0x7b0dec0aab403c000180,0xd9492f614f2f741533cb,0x1a0167488e89b0533352,0x4ae4148f4c857624f4c3,0x1000002ed6e25bc4cb2f,0x1093c0001734689,0xa2d373f04c209c000000,0x315d987971024b0abe2,0x1131c0000c58400,0xf612842419ee4d809400,0x12e0945e68d7b485cc6,0x130400000000000,0xfb429800000001cdd000,0x40ce1b8b8c0000000312,0x34886c000210b8c15712,0xeb4a7e0f380001b5f0c4,0x2961a813ca43388,0x263ef069c000000,0x380003edb5a6c4000000,0x6202640002e6440003e0,0xc3c80003d40601bd8f,0xec000248d2cc0cf29400,0xfe8fdc473400012fe905,0x44cd1c6da40000000091,0xe42690d592b940002e1,0x91af380000000083bb40,0x4eca4c0003ca5848f6a9,0x7c0000000123b481ec01,0xfd4b6911340000000050,0xafc7db4b3d15180002ef],#[0xf080adae8000038ecd4b,0xe000028d6b1636529204,0x93e46f8c9c0000000142,0xc3446a51221346a99990,0x150dbc41ac0c46c5ccb,0x340002c9d2ea75088800,0x557c000000000001d2,0x291c48038000000,0x382b1d4b00000000000,0xaa8603acf4235c000000,0x13ad04200000cf7cc7,0xe48c492b9a5d1c68400,0x7eccd28a3cb0c8f0e62a,0x640da6ee8ecb2a926345,0x8f07c68004caac0002ad,0x2462000000000953de6,0x840000000324f0000000,0x290eb8f3635,0x3047fa4c7906d343f800,0xbf608b8a51cc9ace11ec,0x65284fc7f06d94c99bf0,0x8b8145d2ad3270e9a253,0x1ce468000040e95177f3,0x2cc7f51ed46a6ae,0x8703abd64c02878a7800,0x9b81cec5220a35c3b6c0,0x8c85a2154000024e46e4,0x3bcafb8e6415e8000082,0x156bb400034446d41815,0x688153cac3ec000000,0x840001c6afe8e4c3f400,0x2d46945f667071386e4],#[0x1122c00,0xd32cb5b1b0cc00,0x7c00000000000143d000,0x34008000000016e,0x6185b0d5ac0003cce000,0x190a548e2cfa7c0,0xe40b5d15783048000000,0x1e59c000346e0ac,0x64c54950c80000000000,0x41cbb3adac00000003ae,0x4c00028b91d58c0002cd,0x8a5195271360f8cf8547,0x76480002c2a9287dd1,0xcc000000030130000000,0xd452800018b3b646262,0x9cc964d28044530a1882,0x177193e1401552094ecb,0x5140c0000146cc000143,0x346e8b65542fc99644ce,0x280001aa000001d5138d,0xf2ee8d2c0000000248,0xbbf0238991122443e400,0x5000008dc40001e10ea9,0xcf4b1c0002ee740002d1,0x40000000000003956d42,0x6eb39d8ee80001efbe13,0x285d05270000196,0xe965f1ea308dcc000141,0x30e0c00020c53432389,0x63b0d0cc14000250cc00,0xc70262f180f76ad1384,0x5fe884000145fbabe0c4],#[0x9f06eef2bf148e8c7445,0x3e94f88f58102809e704,0xf9009f4dadc87a112cd1,0x99808c8c26873aeacf70,0xf07040ead4f6a8ebfca,0x1bc5731304e695077a34,0xd00800000000000212,0xb88000295b0000000,0x249bf47a40884c7b400,0x6800030a040000455000,0xb0939a26740000000313,0x3514fe8be2b4b687c38f,0xb30a3152e400000001af,0xb00001825c0000000106,0xba110b542bcab80001c1,0x8c000000034d24000091,0xa0930c030e80e0407da0,0x5a2ffb1494afdec2a1c9,0xf40000000204e60918af,0x289f8d1e80821c2,0x1933f74ffa2404000000,0xc800000000b3c000020d,0x3287bb556683d522fe0f,0x2cdf00003c4dc0001e1,0xe8000000035358436400,0x9050d090780001d454c1,0xc1e4b54000ca85d0ace0,0x36921788092fcf044d91,0x1045400000000000150,0x18344000000,0xf8000384bacfbf00f400,0x10ce504f400028f4010],#[0x5a0d8c0001d460875800,0x8c0001d4106c2bd18e72,0x192e8000186fa1183af,0xb9400028ec800,0x5ccb2402df08812a800,0x15065089bb8ae8000356,0x344eb4c54d80a21269ed,0x3cd0d4bb8000080b800,0xb000008be754dc000000,0x386a800004cb40002e2,0xa5c5fc0000000245f000,0x34000000000000000069,0x2138800000000000109,0x7fd54b8fb40003461000,0xebab13aa2c5bab8643,0x58000000000001d27800,0x26ce3952d11cc8e,0xf1b5e00d644b724c4800,0x9800032889440be4414f,0xf2889cc169ab6400030d,0x248db75eb939d337de6,0xff42afcf70f1e72a1400,0x80c24554b5514723cf80,0xf8505a48d5602c19b0a,0x9a212400038391d43009,0x306052b34490296815,0x170f3cb10000000,0x91706e840000000000,0xa80003856c0000000000,0x54119f301f211800030b,0xb7f0a313200002455b64,0x5000034b5accc88c1d90],#[0x2c4a54049ce2c0002d4,0x1cd8785b40003d5cc00,0xe00001ce000002aea000,0x756dc40001a6abf2aed0,0x9152d0000047ebef7016,0x3c000011100000a8b866,0xa80002932800004eba0e,0x2400009415d4e800032d,0x14d44000000032d2186,0x74504400006e4b6d7400,0x1925800000000d4a22c,0xccac000210f000]]
set_option maxRecDepth 16000 in
def g251D10 := limbs80 #[#[0xf73587aea9aa3bb58960,0x2ac5f394d62f9aa6b15d,0x53f9ca7317cd5398b76b,0x7f960443fca8221d7595,0xaa8a21fd50510fea4288,0x8910fdac4887f561443f,0x885ff72442feb9221fb9,0x2feba221f794d10fbaa6,0xfdd510bfaea885ff7444,0x80905ff76442febb2217,0x482ffb8a41fe54120ff2,0x1fb58920fdaa4907ed42,0xfae8907de53483eea9a4,0x75482febaa417fdd120b,0x2617fdd920bfaec905ff,0xbfeea985ff744c2ffb9,0xff71503fcb0281fe5414,0xb9281fb98940fdac4a05,0x540fbca6a07dd53502ff,0x5fd76502ffbaa817f5d,0xffb8aa1fe58150bfeeca,0x98950fdac4a877d52542,0x8a877d54542ffb92a1fb,0x42febb2a1df59550bfee,0xbf58960bfee2b05ff765,0xca6b07dd53582ffb92c1,0x5582ffba2c1bf59160fb,0x43fd54521bfeeab06fd6,0xfbaa690fed62487f6a92,0xf70546febb2437f5d521,0x12a3fb58951feac2a8df,0x51efacaa8dff72547f73],#[0x6fd65586ffbb2a37f5d9,0xfb82c57f5d952fdac4a9,0x4d62fbaa6b15ff7158af,0xb15ff7558b7eb2ac5f79,0xbf6b8ac5fbdc162fdae0,0xbdd562fdaeab17ef7158,0xe0a9dff7254effb82a7f,0x596ffb82cbf7dc953fbe,0x1ff50910bfee4b2dff71,0xfae4887fd62443fea922,0x74443feb2221ff55110f,0x221ff5d510ffaca887fd,0xffac2907fd51483febb,0xfd53483fea1a41ff5c52,0xaa241ff5cd20ffac6907,0x520ffae8907fd64483fe,0x87fd76483febaa41ff59,0xfe90a81ff55130ffaa49,0x58540ffaa2a07fd31503,0x4a07fd32503feb8a81ff,0x3feb9281ff58940ffaa,0xff5cd40ffac6a07fd535,0xaeca07fd75503feb2a81,0x1543fe98aa1ff48550ff,0xa1ff4c950ffae2a87fd6,0xffac6a87fd72543feb12,0xd74543feb22a1ff5cd50,0x8ac1ff48560ffaeca87f,0x60ffaa4b07fd71583fea,0xffd75583feba2c1ff5c9,0xea92c3ff58951ffaca90,0xc562ffae0b17fd6354bf],#[0xb2ffd70597febaac5ff5,0x7ffb8acbff5c565ffee0,0x138000ffee4b2ffd7259,0xd818304f810b03600930,0x3060b4c27c08701e906,0x522130847410503b40d5,0xe41aa066317a05a31578,0x121cc82e1f5c7921ca46,0x2940a0b26d0954243c8c,0x1b0c1e2eb0b672bf8ac2,0x24de03624d293390ca83,0xfd83e28f3c3c00ea939,0x2214705161444d0aa417,0x104f093624c992c64975,0xa573156c54c14d951c14,0x5df172e5ba5692595961,0x48d8e762ad84b603d7c1,0x4da856925a0467219836,0xdc3e6f79b996d75b186b,0xe0976a5d6d74c5cf5729,0x1c7ecdf777c39eb7795d,0x3858e12783ae0af81ce0,0x8eb23438b6a27188461c,0x74657a94b24de91b23e8,0x267609cb66f19a8e61f9,0x2961a44e898a14e80e9f,0xb50ac76ac6a9e2a21a77,0x51b432cd9b19ec07ae32,0xbbbcaea4b97edffb6c6d,0xc4830c0c21303fbf36f5,0xc1b2afc9ab225c6f3192,0x3f4e6d263441cfab381c],#[0xb72fdbcf693d8ab5b8d5,0x8dfe247855dfd77c2de1,0x8ea6fa29e79398de523,0xf1d041dc2e13038306c0,0x1e0c3814a21ac260b001,0x804287c5c2e130580808,0x51e0584c0214422c0b09,0x83e2c0b0981c060c1a8,0x84c04190a1417098042c,0x380a14a02e1305800f8b,0x7c9148642386c260a118,0x2954422c0e8470b84c10,0xa12003920223e800e428,0x60f80214a0b0470408c1,0x7cac3613041a088230,0xa2a8850785c26081e118,0x850420164470b848007c,0x2c88e1709000a07c82a8,0x8e40a04c34006c1428aa,0xa04c30d8281118a21208,0x38a62384c14010a1f1c0,0xe4d1344709000a21442,0x88180b01c160e108480,0x70508c1a102239442c15,0x7c26090b01801546c361,0xf9786c260a118342844,0x1d089080a21c260a0029,0x9544385c2608221f1ca2,0xa120061a0514420f8764,0x40670d0209216283e1c2,0x1040038180b841c85024,0x83e1b0a1709040290042],#[0xd8ac361020120a4001,0x982c10401246e0f02868,0xc362a89612010242a7c,0xc1544b0d8480214283a,0x1c0b02c3212002a8a0c,0xf86c2c510812182e1509,0x381067868009e280c2c0,0xd848a21424394432120,0x46e0f0286800d8c1d81f,0x10c1220401d090140902,0x8069586028111b83c090,0xd080806960602c0d040,0x4010ed0a080684c702c,0x8030586c0e0e08851f14,0xb82c0e0d1b044312190a,0x7e0b06881c854b0e8570,0x861f14070301406811,0x201282104151b83c0c12,0x4682c111b83c0a0a0086,0x54f8f8803e1b0a824a05,0x850a3b21061bc1412008,0x83c08f8e1f2510704802,0x32150101f0504806190b,0xc360f058142854828870,0x70782c0c1200862c0e2f,0x2c0a182a40883a15c2a3,0x37068682942fc2a37078,0x810c94550e8670982c0a,0xc07018cb0d844460f04,0x861f1619c3401283e06,0x8aa8210413028dc1c160,0x4c0a370705414010c402],#[0x280f8641611281918ab0,0x1902e0b0d81c1a12003e,0x8cb0d83c160508192038,0x384c16051b8380218a03,0x1e0b030082a18b2a8143,0x2860c92510e867088dc,0xe87c62a8cb088dc1e0b,0xc1b00410f8a10e170982,0x11b0748c2e10401dc0e0,0x10a1f180a0441437078,0x84c14010a211a3b84c14,0xe170581c18350900263b,0xb0dc1e0b02840e8e220e,0xee130581c18360085230,0x918486e0f05814287470,0x836181e1ac18210a3e04,0xf8bc28561b0708178241,0x3e31546c2082c1200320,0x42824aa34120085848f8,0x1850a0bc3e5010002f,0x8c1a003439446c201901,0xb01052a87c6c3613050,0x204161301050f9547c26,0xf0d1184c04143e822a8c,0x4aa3810018641423062,0x52887c7028e70982c04,0x600aa1a0f8c03c260b01,0x639c260b00850f8f84c1,0x811b83c0a185e0c2a0,0x1b83c0a185e0c2cab048,0x400f840415ca22002001,0x300200f8c05024370781],#[0x4c04090a3e0f8c14c2e1,0x1f1584c04190a3e0a0d8,0x57c26004181c18350b02,0x10010dc1e050a3e1010,0xa84104370781832006c5,0x14370781400f8404c090,0x21048c85e1f2d0a840,0xc00803e31546c2042a11,0x70781832145e58870b84,0x51f08092aa1100200643,0x34363210048086e0f028,0xd178203636130480040,0x61304800403436301000,0x725211000d1f020363,0x415f0305c24370782832,0x94572883f0982c04143e,0x41000730dc1e060c2f2b,0x44697c361509000a1604,0x8c1c02028c2c2f110784,0xf8285944231114e1b090,0xa8470b841040059110f8,0x8f8e090445814148b862,0x14e1b0500c1c21088580,0x705004207cc288722211,0x920aa2108a8845111661,0xe480b0550484130b0222,0x2c240a5508e1305000f8,0x101a0ce1305838421422,0x47074238441e083e2921,0xb0d8440a15a300444485,0x4800513e414534830d40,0x9c282a170c120844b0b8],#[0x4b82861108d1d8a12088,0xa8258441c0a008842a3,0x985814007688470e1b89,0x384c1688150491a271e0,0x968d438730c121b45080,0xc2c0b038343212008d13,0xb0c84c08a87640894412,0x342c491b00151a170a84,0xcc72b8487302c26050d8,0x12151219096181914138,0x4208102183b83c0a344e,0xd0d24b013c240e010d46,0xf0b0309e090b00424207,0x90046a5060ac1a00941,0x42c1200d1440f8d8ae16,0x13e514534830d61b0481,0xbd421541c570b828240,0x281c3617042fc1a202a6,0x221168d1f0b001d0582,0x1507800570c94460bc78,0x824011b830ae0504861f,0xc25000ae19283b1f1020,0x28220e0088428ed1a505,0x1609001da211c38bc370,0x13c2c010688468ec8816,0xa37070442c010c3e2c30,0xb86c1e047c60547382c0,0xa98400e0642a87414010,0x20ee151b8317e0b02860,0x183288c1a247c3c008c2,0xca8ce120b0046a50628c,0x6506558ce13050082a7],#[0x384c10cb06881c864c19,0x422d1a3e10781a08a190,0x1810ca370682430f8b4,0x661866941f0e5510416,0x7098282c01108e1c3212,0x3c220c6582440651a4c6,0x37068482c010c3e34361,0x831f16550ca884582c0a,0x801c0c8550e824261b03,0xc20cb058146e0d0c1924,0x50a848ec003e3e4a121d,0xdc260a00850f95482a87,0x370982c28849c422c351,0x8186c011859549e1d088,0x74c2a8749f1d8361307,0x100490a8441607070d1f,0xb038386a109e1d2c8700,0xd429383a51184415c2e0,0x247231543384c1607070,0x820f8f8aa495ca23e0fc,0x601191f18401ac26020a,0x584c023a188814a303c2,0x940a1b83c0a004e20151,0x90200a09c461f150c1d0,0x2595e1b83c089c182011,0x70306c260a0b8386a007,0x5c260b070d400e470e86,0x690784c107f003925920,0x52ae1305800f8b47288,0x2020d81c1c34723e0618,0xb83410f872415e0a2042,0x844015e1]]
set_option maxRecDepth 16000 in
def g251H10 := limbs80 #[#[0x10680024480001c2416,0x180003034000b2080400,0x2c000401018460000000,0xc002900064002d000,0x800008262b020c83e040,0x21802010021d1a0200e0,0x1400020342e09100280,0x8000409010040c150200,0xe918000b11000180232,0x2000401401268700405,0x6630048400a020789c44,0x7c402f0281470223186c,0x2018120c0400400041e0,0x63f8002a4f220544c060,0xa120e8b00c3800004040,0x1031940404250580,0xf83a00020446c051ba4,0x20000020118144260904,0x1702824020308000060e,0x4c0346004140e1780c10,0x18362e028040e0b080dc,0x8a432040000c000a008,0x65803010001112454190,0xc2670808de00020000a1,0xc00280582ca00d15004a,0x34020c88820431686,0x661936800040605,0x6010180401298100e17,0x2f0b0080603029042a,0x22a22824001721000,0xad00814000180e90118,0x41b984040200090a8060],#[0x6fd050a000080b018324,0x40605118553c3c06809b,0x8241e1b082ac8596032f,0x1298cac0008060016118,0x635cc00003e00808025d,0x837e00016462f960829e,0x1a8bb845f64b92d96975,0x50b4555d1c2d72040239,0xaf726ce0ca1c0000065d,0x7c445e1db126a66d9300,0x175c06d45ab2959cc1,0xd2dc5aefb7d0c3e31860,0x291d638d45e5b8ab057,0x29402cdcc2788e000000,0xa7ac21c20003daa29543,0xbdc2ed45ae5a5e9e04b4,0x57b2b5d475fc42518e88,0x79a9034c08a9911a2828,0x5bbc5a60963f92c06f30,0x6e27e49f86f980caaa19,0xdad6b05648265a098926,0x4510d9ab8186e0003fc4,0x54e84cb182285758a8b7,0x9a46aa0001979e1e81,0x9399ed13392ff331e02a,0x84880de1d65b38f6eca9,0x7d8b5410082f82d963f2,0xf2947928d5041ad9c71e,0x3fbbfff94215c9943c2,0xdd69370b0a1394a5b263,0x69f43a915b338cbe7d4c,0xc17fa7e062c8f95cb219],#[0x3bb451ab8753885b258d,0xaace1b0bee251dd56d63,0xafecb4f8681004fc9425,0x6614c73424de15a53b73,0xacb041922f091c9ad4e5,0x4d3c6475de000000002d,0x28a62b25ba604f19b052,0xa000004b6b81a13cee7b,0x6a5e47b91e727b00004b,0x934492f043fd89e623f2,0x830e0392cc0e9d89145c,0x58ae3315cdf466710fc4,0x22299d210bd547c3e4f8,0xbfef6a5561448e1edd81,0xce81990f6319b03ba84,0x85e0508800029d33b59c,0xaa31b9607d5f4a7068c7,0x1cf108d8434775,0x8000a5fdc6ac12ade800,0xc00030526550684118b,0x4e0001e464591000062,0x82be1282000000026175,0x8c5bbeab301f780aa0dd,0x6bbcb630b88a500175d3,0x60d3a3bc80e800069bc9,0x4c000715a95d3e0242ff,0x9ea0ec80005b6f1561aa,0x1a020001f86bc9700000,0x74000724b97000933084,0x27c00000006cd2f6d030,0x228b4064610000007604,0xb400008b23af0675bd9e],#[0x63fb2285a3c9e61c4ebb,0xc9df01089a36d8c00002,0x1bcffc9766ae22b02067,0xed269d5834ae7eb02589,0x7b96a099207780a4,0x180001885332e0000000,0x59b83c2a23800016f0c7,0x616de330000118c907e7,0x915a410f1e3b2c042c61,0xcf6c62fe2afa0a53434d,0x9bf639c2d471c61e48d,0x6a15cc63459685118000,0x91d6e950c85b08597b0b,0xef8d621cc74800000000,0xa31437c8f5176a694719,0x333c59817bb3987709a9,0xb5b871400025c7528ee,0x840000b0c41e545f8da7,0xbed290882b7b24c4f2c5,0xf2ac532681c800071235,0x76ce9f2349d380002d5a,0x6e1cc0e8cea09ff51449,0x298c7578e1bc20844d1b,0x43f87500831a44cf980a,0x98124ac45a800057336b,0xff65358822c3483e0535,0x37bb10b95a4258836ea6,0x37518db57dc393de02b1,0x887ac68a784e6a9320fe,0x2f57e000074f8bc77d60,0x5f0c4483db9f1a8efde0,0x817544e1ca8c9cb0000d],#[0xf52f67205e9324dba026,0x4ade4f980002c51b9,0x845c8144c22303ba26a0,0x8aa35eb6d05341053167,0x6258b7c011a3a147552e,0xd9eebb6d62fc52dd03f6,0x3c852187fc6127281d8e,0x9297e23cee4a4a8d3aad,0x2b3215220003c7363169,0x26439d5a3e34ffa3c000,0x8a16408024cce50001b1,0xc343e707e03153d00002,0x4e42caae55150e3a1930,0xd330681e1f9055b2272d,0xdcc9850c000796f9,0xe6b119819e2f98367707,0xdd0a54b08ea09bd21301,0xff32354577e286ff9f86,0xe1985e9944b84f392662,0xeabdd83a57e107364,0xc10a99d4e4e73b880000,0xb38afe1e1129bb146c92,0x6eab6e6f8109f0c3a3eb,0x61c7749e2e2e0c733bbe,0x1521e62c9db6176d21c4,0xa3a53ec4b2d41119026,0x4c64e12e0002c9a00000,0xc4b7b0000d2380000111,0x5dc2230000001a711420,0x6f5ab46520c000000005,0x9511df673e00a65925ac,0xca85e548f96064725bec],#[0x800048a4659d073c0609,0xd60933a6c902f365c538,0xbc60002156bd0506d488,0x9b49b75f0e92968f0429,0x7bcec386b204b8ce7017,0x3d4206d30ae095000189,0xb34c696639f193be85c1,0x61ae546966435452fdb0,0x656b98ddabe3ab18707d,0x14ef0db39afb5f6,0xdaed2d962842f6324000,0x4724a0748d8000e3fd4e,0x4f29db4712314f9ef9,0x1d995000000014a8423f,0x5fbfba6c950815c5aae0,0x6173d49140d963061929,0xd8af2e1308e338ed4000,0x2a0cb8348d3b29402784,0xa0388292a2ba676403de,0x83eefd06a80692624b42,0x674f2b00d9f0e00723ec,0x69f71eafb9e55ce46810,0xde8dba15e7b8d8874000,0x7639580493c13d21efec,0xc22752ba61a2119ad358,0xba9dc00000000654d01d,0x6b899ca4c50000230566,0x4688a4a400000000000e,0xa56dea9e69e089ba117,0x363f9ab8dec0c3442867,0x800000000089860aa607,0x40ee832a6c162d5ce675],#[0x3d6d11692b30811c5a4d,0x6b9200000001b23e81ca,0x8780f000000000000000,0x33537040cfa0dce9e462,0x2390b22de3e800058d64,0x16bc2fb81ac1935ec000,0x5c2c8a0e55e02cc32b65,0x82f400009268aafc157a,0x865640784b0a12e83c10,0x1cb887b800fe00018c,0xa071b6bdca2214000000,0xac0007c90d9765a5046e,0xe03ca533d00008c4079,0x79582,0x93152c099000046b0000,0x87a9da58e00ad34cc8b,0x8000c713f4e30d68a303,0x47db33b6000000001807,0xe8e5721954c98d000128,0x8000b098150c8a300002,0x9148405a36c70792c9d,0x46d0335966296cc5cc10,0xb84600010cd6b4d00001,0x4c90f2944ec76ab53510,0xf060000b2da39f71d3c8,0x214c0000a7a7c4f4b426,0xa8a1ccc3aa0b8cc01,0xa8800007078be9e00,0x637fdc60bde04f2c9310,0xe5d8df9b0059662ad5b1,0xec0e51929d207913974,0xe4486861c75e126b13ad],#[0xfe87e40ef91c6000094b,0x67e35d55cbe86e416d64,0xacba5585b2a995ff43b2,0x7c0000aa0219400010e2,0x3a78c400052620000bd,0x8000c2c0000000030b7c,0x507a3f8c575a3a4c1b9,0x3e3a6aad0ad9a2f87da1,0x29f4475ccaac51ee84ee,0x3216f237aa773181081f,0x7618c0005a4e00012a,0x94c9548ba36897780007,0xc89a0525abc591235191,0x6f2992512fe34a946fcd,0x32195a68036cf0ca225d,0x2acf07583b05bd8ea5dd,0xd180002d6c8226ae72ab,0xf374ea9770c4aa4ee26f,0x3400058de6c14eea5c00,0x28018450b43a92f1222d,0xb4ae000097524dc4315a,0x186c22d000111fc3b0,0x5300003c5e8000266600,0xe1b90000acc2c77561d2,0x6ac8316382369bbf5f2e,0x5e3ecb7d3fd1a4870d27,0xe86a2b6555c00078b48,0xd4031035d28fd12d502,0xe2265f7c67700054b26a,0x9458821a00000007deef,0xf2973800032dd45ad8fd,0x23d5a2d970000a101f5],#[0x6a000000e0f37668a577,0xa55d0b2735e1058d42c,0x16e9e2493b5a180eee,0x6e0f92f2783706334b50,0xc000049f9202ccaa8385,0x1e62ec286a390f453ffc,0xa165f20b7a5a45c1015,0xb40005917b392623c000,0x6f9e21899a61296b5c81,0xb0e2b097a281c4a00007,0x5988fef9302f70a6c888,0x14b78ac12071cd0001cd,0x41ed636a03d90124956d,0x455ceff0f000000016de,0x439f515072f231000030,0x430123eb466,0x60528e0c421c88c38506,0x4dfb2c5748bab6000102,0x5d580000e73df8f29658,0x630c5b1155ec33a4e73,0x3a1ce7897fea418eacf3,0xc99e0000b6fa855300da,0xb0e30ab140001a99486b,0x6d8f12a55dd04ae45762,0x27135396aca2963f8c0b,0xb604e800000000003fca,0x4e400028143610000039,0x30a9722000027190a7d2,0x9c1bdd0b8de3941d5075,0x5bac178ebcf1be34da49,0x2889447d6cc7338ae4cf,0xd4e49966c00000003b1f],#[0xf035d66121d87d90d9a7,0xd919740c000154480006,0x24d9000016fa6952ad0,0x586c117d522cad224200,0x114898bb84503bb680e8,0xda0315b2faa74228e522,0x62032e6cfb30cbec3fec,0xa018e627c20859659006,0x1984852ae4067c9d050f,0x3cf3d8ca4beb69730f15,0x1ba8d3f563b5a12a76a2,0xd80002a0e520b3e2872f,0xb98c862f8d80003248b9,0xa17a629c0bb400003a35,0xa2881f3b34834b71547a,0x184000327e3c9746,0x3773161f6c2a27380000,0xf4000797402e1ac8a8b9,0xb7400008fe9a9652b283,0xae78435e6d2dad00a036,0xc48468000a70f0bab924,0x538774e4e4000076774a,0x14ef530683b2023bb8fe,0xbb54e9ddb1284e623583,0xbac49cc0006893320900,0x302c34491600008,0x582d26a950001e98c000,0x1d3d1d8f0000585a46]]
def g251D11 := limbs80 #[#[0x10f794fdd53fb98bed62,0xfd50ff503fd30ff483fd,0x87fd51ff4c7fd21ff583,0xf54ffd62ff54bfd32ff5,0x8423023000ff597fd63f,0xad133218394630a30f81,0x22f4107b4e91b33105c4,0x1610360e06001889a527,0x85840d8381800602200a,0x10514180e120a00147c6,0x1208220c000490384802,0x2868584001420461a16,0x6140e120800203470712,0x90715868583828104002,0x241c661a120a060c1400,0x51d85848281830d0006,0x584800d14161a1612005,0x6a1a120a0021441404a8,0x62103858482801f1c0c,0x480140c1a161200342c2,0x16120e06003408907868,0x8482800305080d1c801a,0x305062216120a0020386,0x848281800d8]]
set_option maxRecDepth 16000 in
def g251H11 := limbs80 #[#[0x233000201105200210,0x72b30001100002120003,0x620620202334126e2,0xf19000000005002,0xd7e0d04986a400000000,0x6,0x0,0x16ae0000000000000,0xdd278001d28484000727,0xabc6797d00038dc00005,0x82e25f800000004c18,0x240a00000000000000,0x10a0004b48,0x80c0000000000000,0x51e0000000000dcd,0x3c9,0x25309fc00092700,0x324800000000045100,0x410dcc9a180000000,0xe14b0ec0007413018000,0x2742407b8fa2a4164000,0x34da000000000,0xddf4a000b56800000000,0x183cb3a510132e2,0x1da7c33b00030f20,0x3020,0xf80000000004cb4000,0x470f04880000000006bd,0x121900000018a,0x4e0b4000043802a21e00,0x35980800000000019d1d,0x42c2b5000000223627b4],#[0x5ae80000000000000002,0x80006400005934000008,0x624b0002c7ac1a845898,0x145912f3a7ac3963,0x31dc000000e1d00,0xe9355000000000000000,0x69b24409c40000000007,0x9a4000000000000130e,0xe0000000000000caf000,0x75b40000006bba00213,0xe2100000000f000000,0x44a00000000000,0xcaa00000000000003710,0xc0c0000002,0x1c26000000391c000,0xd000021c000000d0b800,0x165a000022400147,0xc2a0001c4400000000,0x4800000000000002c300,0xf70e1fc94fc968270002,0x10500000005aa84e6,0x28c4001ca0000,0xad191c9400000028e000,0x109a851da00000a3051,0x88000000000000119c0,0x81400003080038fce24e,0x30bc,0x3a580000003234001e2b,0x4264000000000000,0x8c48c000000000000000,0x14440004493d3f5,0x11509c44100078240000],#[0x2970000001f0945f92ba,0x80000000000006a74000,0xe0008418000000000e37,0x783543,0xe50b01238001c8659c00,0x55b00028,0x128200026600000000,0x584e52bf0d1bad180,0x710000,0x80586d11e07a000116,0xab935fc00000,0xb89ccf0cdcf1900000,0x8e4000000eba00000000,0x5851d560000004,0x1b20000003ec8,0x0,0x5d2ceccdc6c628d4eecd,0x424c00000070,0x40480000000005c500,0x162e00000000000000,0x0,0xc928000000000,0x6f8b8000000000785800,0xe9d29af685,0x416c000000b2200,0xb3500000000,0x0,0x0,0xa528000000000000,0x28b400,0xf40da96d1a11800000,0xd580a100016080],#[0x14e80000000,0xe00f18c001c200000000,0x454508a00010b0000000,0x5fc0c88c000000000648,0x80017b30000000001a7,0x9f958800000000000071,0x368f9,0xa9000000030e00000000,0x80000000000000003903,0x19226b5]]
def g251D12 (j : Nat) := if j=0 then 0x305080c101003ff else 0
def g251H12 := limbs80 #[#[0xc280000000704000002,0x3440,0xa600000000000000,0x1c00020e000000000,0x581c0000000000000000,0x3e,0x38fd18000000,0x2400000214000000,0x30000000000000000000,0x35,0x3c800000000000000,0x0,0x7a40030c00000000000,0xb4800000000010b0000,0x893390c13c9000cd0000,0x42000000012]]
def g251L : Nat → Packing
  | 5 => (9,7,7,0,0,6,0,g251D5)
  | 6 => (115,6,7,0,0,11,0,g251D6)
  | 7 => (793,5,7,0,0,15,0,g251D7)
  | 8 => (1442,4,7,0,0,17,0,g251D8)
  | 9 => (957,3,7,0,0,17,0,g251D9)
  | 10 => (184,2,7,0,0,14,0,g251D10)
  | 11 => (20,1,7,0,0,11,0,g251D11)
  | 12 => (1,0,7,0,0,0,0,g251D12)
  | _ => emptyPacking
def g251I : Nat → Nat → Option (Nat × Nat)
  | 6 => lookupWord 3 53 2 9 4 1 g251H6
  | 7 => lookupWord 40 223 6 12 7 1 g251H7
  | 8 => lookupWord 268 1229 9 15 10 1 g251H8
  | 9 => lookupWord 486 2887 7 16 11 1 g251H9
  | 10 => lookupWord 326 1489 9 15 10 1 g251H10
  | 11 => lookupWord 62 631 4 13 8 1 g251H11
  | 12 => lookupWord 6 127 1 10 5 1 g251H12
  | _ => fun _ => none
def g251 : Forest := ⟨251,12,fun i => g251Y[i]?.getD (0,0),g251C,g251A,g251L,g251I⟩
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P5_0 : block g251 5 0 9=true := by
  apply cellsBlock (ar:=6) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B5 : block g251 5 0 9=true := g251P5_0
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
theorem g251P6_100 : block g251 6 100 15=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=2)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B6 : block g251 6 0 115=true := (@block_merge g251 6 0 4 111 g251P6_0 (@block_merge g251 6 4 96 15 g251P6_4 g251P6_100))
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
theorem g251P7_98 : block g251 7 98 31=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_129 : block g251 7 129 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_225 : block g251 7 225 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_321 : block g251 7 321 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_417 : block g251 7 417 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_513 : block g251 7 513 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_609 : block g251 7 609 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P7_705 : block g251 7 705 88=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B7 : block g251 7 0 793=true := (@block_merge g251 7 0 321 472 (@block_merge g251 7 0 98 223 (@block_merge g251 7 0 2 96 g251P7_0 g251P7_2) (@block_merge g251 7 98 31 192 g251P7_98 (@block_merge g251 7 129 96 96 g251P7_129 g251P7_225))) (@block_merge g251 7 321 192 280 (@block_merge g251 7 321 96 96 g251P7_321 g251P7_417) (@block_merge g251 7 513 96 184 g251P7_513 (@block_merge g251 7 609 96 88 g251P7_609 g251P7_705))))
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_0 : block g251 8 0 96=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_96 : block g251 8 96 87=true := by
  apply cellsBlock (ar:=7) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_183 : block g251 8 183 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_279 : block g251 8 279 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_375 : block g251 8 375 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_471 : block g251 8 471 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_567 : block g251 8 567 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_663 : block g251 8 663 96=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_759 : block g251 8 759 34=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_793 : block g251 8 793 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_889 : block g251 8 889 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_985 : block g251 8 985 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1081 : block g251 8 1081 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1177 : block g251 8 1177 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1273 : block g251 8 1273 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P8_1369 : block g251 8 1369 73=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B8 : block g251 8 0 1442=true := (@block_merge g251 8 0 759 683 (@block_merge g251 8 0 375 384 (@block_merge g251 8 0 183 192 (@block_merge g251 8 0 96 87 g251P8_0 g251P8_96) (@block_merge g251 8 183 96 96 g251P8_183 g251P8_279)) (@block_merge g251 8 375 192 192 (@block_merge g251 8 375 96 96 g251P8_375 g251P8_471) (@block_merge g251 8 567 96 96 g251P8_567 g251P8_663))) (@block_merge g251 8 759 322 361 (@block_merge g251 8 759 130 192 (@block_merge g251 8 759 34 96 g251P8_759 g251P8_793) (@block_merge g251 8 889 96 96 g251P8_889 g251P8_985)) (@block_merge g251 8 1081 192 169 (@block_merge g251 8 1081 96 96 g251P8_1081 g251P8_1177) (@block_merge g251 8 1273 96 73 g251P8_1273 g251P8_1369))))
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
theorem g251P9_412 : block g251 9 412 92=true := by
  apply cellsBlock (ar:=8) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_504 : block g251 9 504 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_600 : block g251 9 600 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_696 : block g251 9 696 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_792 : block g251 9 792 96=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_888 : block g251 9 888 13=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=1)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem g251P9_901 : block g251 9 901 56=true := by
  apply cellsBlock (ar:=10) (rows:=0) (d:=3)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B9 : block g251 9 0 957=true := (@block_merge g251 9 0 412 545 (@block_merge g251 9 0 124 288 (@block_merge g251 9 0 1 123 g251P9_0 (@block_merge g251 9 1 27 96 g251P9_1 g251P9_28)) (@block_merge g251 9 124 96 192 g251P9_124 (@block_merge g251 9 220 96 96 g251P9_220 g251P9_316))) (@block_merge g251 9 412 284 261 (@block_merge g251 9 412 92 192 g251P9_412 (@block_merge g251 9 504 96 96 g251P9_504 g251P9_600)) (@block_merge g251 9 696 192 69 (@block_merge g251 9 696 96 96 g251P9_696 g251P9_792) (@block_merge g251 9 888 13 56 g251P9_888 g251P9_901))))
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
theorem g251P10_112 : block g251 10 112 72=true := by
  apply cellsBlock (ar:=9) (rows:=0) (d:=4)
  simp only [cells,boxes]
  repeat' apply And.intro
  all_goals decide +kernel
theorem g251B10 : block g251 10 0 184=true := (@block_merge g251 10 0 105 79 (@block_merge g251 10 0 9 96 g251P10_0 g251P10_9) (@block_merge g251 10 105 7 72 g251P10_105 g251P10_112))
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
